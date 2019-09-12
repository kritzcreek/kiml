package kiml.frontend

import kiml.frontend.Token.Companion.get
import kiml.syntax.*


class Parser(tokens: Iterator<Spanned<Token>>) {

    val iterator = PeekableIterator(tokens)

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

                val type = when (tyVar.v) {
                    "Int" -> Monotype.int
                    "Bool" -> Monotype.bool
                    else -> Monotype.Var(tyVar)
                }

                type
            }
            else -> throw RuntimeException("expected type found $nextToken at $start")
        }
    }

    private fun parseName(): Name {
        val ident = expectNext<Token.Ident>(expectedError("expected identifier"))
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