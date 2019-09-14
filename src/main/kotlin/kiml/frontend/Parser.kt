package kiml.frontend

import kiml.frontend.Token.Companion.get
import kiml.syntax.*


class Parser(tokens: Iterator<Spanned<Token>>) {

    val iterator = PeekableIterator(tokens)

    fun parseInput(): Pair<List<TypeDeclaration>, Expression> {
        val typeDeclarations = mutableListOf<TypeDeclaration>()
        while (iterator.peek().value is Token.Type) typeDeclarations.add(parseTypeDeclaration())

        return typeDeclarations to parseExpression()
    }

    fun parseTypeDeclaration(): TypeDeclaration {
        expectNext<Token.Type>(expectedError("expected type"))
        val name = parseUpperName()

        val typeVariables = mutableListOf<TyVar>()
        while (iterator.peek().value is Token.Ident) typeVariables.add(parseTyVar())

        expectNext<Token.LBrace>(expectedError("expected open brace"))
        val dataConstructors = commaSeparated(::parseDataConstructor) { it !is Token.RBrace }
        expectNext<Token.RBrace>(expectedError("expected closing brace"))

        return TypeDeclaration(name, typeVariables, dataConstructors)
    }

    fun parseDataConstructor(): DataConstructor {
        val name = parseUpperName()
        expectNext<Token.LParen>(expectedError("expected left paren"))
        val fields = commaSeparated(::parseType) { it !is Token.RParen }
        expectNext<Token.RParen>(expectedError("expected right paren"))

        return DataConstructor(name, fields)
    }

    private fun parsePolytype(): Polytype {
        val vars = mutableListOf<TyVar>()
        val t = iterator.peek()
        if (t.value is Token.Forall) {
            iterator.next()
            while (true) {
                vars += parseTyVar()
                if (iterator.peek().value == Token.Dot) {
                    iterator.next()
                    break
                }
            }
        }
        val ty = parseType()

        return Polytype(vars, ty)
    }

    private fun parseType(): Monotype {
        val arg = parseTypeAtom()
        return when (iterator.peek().value) {
            is Token.Arrow -> {
                iterator.next()
                val res = parseType()
                Monotype.Function(arg, res)
            }
            else -> arg
        }
    }

    private fun parseTypeAtom(): Monotype {
        val (start, nextToken) = iterator.peek()

        return when (nextToken) {
            is Token.LParen -> {
                iterator.next()

                val type = parseType()
                expectNext<Token.LParen>(expectedError("missing closing paren"))
                type
            }
            is Token.Ident -> {
                val tyVar = parseTyVar()
                Monotype.Var(tyVar)
            }
            is Token.UpperIdent -> {
                Monotype.Constructor(parseUpperName(), emptyList())
            }
            else -> throw RuntimeException("expected type found $nextToken at $start")
        }
    }

    private fun parseName(): Name {
        val ident = expectNext<Token.Ident>(expectedError("expected identifier"))
        return Name(ident.value.ident)
    }

    private fun parseUpperName(): Name {
        val ident = expectNext<Token.UpperIdent>(expectedError("expected uppercase identifier"))
        return Name(ident.value.ident)
    }

    private fun parseTyVar(): TyVar {
        val ident = expectNext<Token.Ident>(expectedError("expected identifier"))
        return TyVar(ident.value.ident)
    }

    private fun parseVar(): Expression.Var = Expression.Var(parseName())


    private fun parseInt(): Expression.Int {
        val (_, intToken) = expectNext<Token.IntToken>(expectedError("expected int literal"))
        return Expression.Int(intToken.int)
    }

    private fun parseBool(): Expression.Bool {
        val (_, boolToken) = expectNext<Token.BoolToken>(expectedError("expected boolean literal"))
        return Expression.Bool(boolToken.bool)
    }


    private fun parseLambda(): Expression.Lambda {
        iterator.next()

        val binder = parseName()
        expectNext<Token.Dot>(expectedError("expected dot"))

        val body = parseExpression()

        return Expression.Lambda(binder, body)
    }

    fun parseExpression(): Expression {
        val atoms = mutableListOf<Expression>()
        while (iterator.hasNext()) {
            parseAtom()?.let {
                atoms += it
            } ?: break
        }

        return when {
            atoms.isEmpty() -> throw RuntimeException("failed to parse expression")
            atoms.size == 1 -> atoms.first()
            else -> atoms.drop(1).fold(atoms[0]) { func, arg ->
                Expression.App(func, arg)
            }
        }

    }

    private fun parseAtom(): Expression? {
        return when (iterator.peek().value) {
            is Token.LParen -> {
                iterator.next()
                val expr = parseExpression()
                expectNext<Token.RParen>(expectedError("missing closing paren"))

                expr
            }
            is Token.Lam -> parseLambda()
            is Token.Ident -> parseVar()
            is Token.IntToken -> parseInt()
            is Token.BoolToken -> parseBool()
            is Token.Let -> parseLet()
            is Token.If -> parseIf()
            is Token.UpperIdent -> parseDataConstruction()
            is Token.Match -> parseMatch()
            else -> null
        }
    }

    private fun parseLet(): Expression.Let? {
        iterator.next()
        val binder = parseName()
        expectNext<Token.Equals>(expectedError("expected equals"))
        val expr = parseExpression()
        expectNext<Token.In>(expectedError("expected in"))
        val body = parseExpression()

        return Expression.Let(binder, expr, body)
    }

    private fun parseIf(): Expression.If? { // if true then 3 else 4
        iterator.next()
        val condition = parseExpression()
        expectNext<Token.Then>(expectedError("expected then"))
        val thenBranch = parseExpression()
        expectNext<Token.Else>(expectedError("expected else"))
        val elseBranch = parseExpression()

        return Expression.If(condition, thenBranch, elseBranch)
    }

    private fun parseDataConstruction(): Expression.Construction {
        val type = parseUpperName()
        expectNext<Token.DoubleColon>(expectedError("expected double colon"))
        val dtor = parseUpperName()
        expectNext<Token.LParen>(expectedError("expected open paren"))

        val exprs = commaSeparated(::parseExpression) { it !is Token.RParen }
        expectNext<Token.RParen>(expectedError("expected closing paren"))

        return Expression.Construction(type, dtor, exprs)
    }

    fun parseMatch(): Expression.Match {
        iterator.next()
        val expr = parseExpression()
        expectNext<Token.LBrace>(expectedError("expected open brace"))
        val cases = commaSeparated(::parseCase) { it !is Token.RBrace }
        expectNext<Token.RBrace>(expectedError("expected open brace"))
        return Expression.Match(expr, cases)
    }

    fun parseCase(): Case {
        val pattern = parsePattern()
        expectNext<Token.Arrow>(expectedError("expected fat arrow"))
        val body = parseExpression()

        return Case(pattern, body)
    }

    fun parsePattern(): Pattern {
        return if (iterator.peek().value is Token.Ident) {
            Pattern.Var(parseName())
        } else {
            val ty = parseUpperName()
            expectNext<Token.DoubleColon>(expectedError("expect double colon"))
            val dtor = parseUpperName()
            expectNext<Token.LParen>(expectedError("expected open paren"))
            val fields = commaSeparated(::parsePattern) { it !is Token.RParen }
            expectNext<Token.RParen>(expectedError("expected open paren"))
            Pattern.Constructor(ty, dtor, fields)
        }
    }

    private fun <T> commaSeparated(parser: () -> T, cont: (Token) -> Boolean): List<T> {
        val result = mutableListOf<T>()
        while (cont(iterator.peek().value)) {
            result += parser()
            if (iterator.peek().value == Token.Comma) {
                iterator.next()
            } else {
                break
            }
        }
        return result
    }

    private fun expectedError(msg: String): (Spanned<Token>) -> String = { token ->
        "$msg saw ${token.value} at ${token.span}"
    }

    private inline fun <reified T> expectNext(error: (token: Spanned<Token>) -> String): Spanned<T> {
        val (span, token) = iterator.next()

        get<T>(token)?.let {
            return Spanned(span, it)
        } ?: throw RuntimeException(error(Spanned(span, token)))
    }
}