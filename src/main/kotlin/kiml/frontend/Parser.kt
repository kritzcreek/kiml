package kiml.frontend

import kiml.frontend.Token.Companion.get
import kiml.syntax.*
import java.io.File


class Parser(tokens: Iterator<Spanned<Token>>) {

    val iterator = PeekableIterator(tokens)

    fun parseInput(): Pair<List<Declaration.TypeDeclaration>, Expression> {
        val typeDeclarations = mutableListOf<Declaration.TypeDeclaration>()
        while (iterator.peek().value is Token.Type) typeDeclarations.add(parseTypeDeclaration())

        return typeDeclarations to parseExpression()
    }

    fun parseTypeDeclaration(): Declaration.TypeDeclaration {
        expectNext<Token.Type>(expectedError("expected type"))
        val name = parseUpperName()

        expectNext<Token.LAngle>(expectedError("expected open brace"))
        val typeVariables = commaSeparated(::parseTyVar) { it !is Token.RAngle }
        expectNext<Token.RAngle>(expectedError("expected closing brace"))

        expectNext<Token.LBrace>(expectedError("expected open brace"))
        val dataConstructors = commaSeparated(::parseDataConstructor) { it !is Token.RBrace }
        expectNext<Token.RBrace>(expectedError("expected closing brace"))

        return Declaration.TypeDeclaration(name, typeVariables, dataConstructors)
    }

    fun parseDataConstructor(): Declaration.DataConstructor {
        val name = parseUpperName()
        expectNext<Token.LParen>(expectedError("expected left paren"))
        val fields = commaSeparated(::parseType) { it !is Token.RParen }
        expectNext<Token.RParen>(expectedError("expected right paren"))

        return Declaration.DataConstructor(name, fields)
    }

    fun parseValueDeclaration(): Declaration.ValueDeclaration {
        expectNext<Token.Let>(expectedError("expected let"))
        val name = parseName()
        expectNext<Token.Colon>(expectedError("expected type"))
        val ty = parsePolytype()
        expectNext<Token.Equals>(expectedError("expected equals"))
        val expr = parseExpression()
        expectNext<Token.Semicolon>(expectedError("expected semicolon"))
        return Declaration.ValueDeclaration(name, ty, expr)
    }

    fun parseDeclaration(): Declaration {
        val (span, token) = iterator.peek()
        return when (token) {
            is Token.Type -> parseTypeDeclaration()
            is Token.Let -> parseValueDeclaration()
            else -> throw RuntimeException("Expected a let or type to start a declaration at $span")
        }
    }

    fun parseImport(): Import {
        iterator.next()
        val moduleName = parseModuleName()
        return Import.Qualified(moduleName, moduleName)
    }

    fun parseModule(): Module {
        expectNext<Token.Module>(expectedError("expected module"))
        val (namespace, mname) = parseNamespace()
        val name = mname ?: throw Exception("expected modulename")

        val imports = mutableListOf<Import>()
        while (iterator.peek().value is Token.Import) {
            imports += parseImport()
        }

        val declarations = mutableListOf<Declaration>()
        while (iterator.peek().value !is Token.EOF) {
            declarations += parseDeclaration()
        }
        return Module(Namespace(namespace.components + name), imports, declarations)
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
                expectNext<Token.RParen>(expectedError("missing closing paren"))
                type
            }
            is Token.Ident -> {
                val tyVar = parseTyVar()
                Monotype.Var(tyVar)
            }
            is Token.UpperIdent -> {
                val (qualifier, name) = parseNamespacedUpper()
                var args = emptyList<Monotype>()
                if (iterator.peek().value is Token.LAngle) {
                    expectNext<Token.LAngle>(expectedError("expected open brace"))
                    args = commaSeparated(::parseType) { it !is Token.RAngle }
                    expectNext<Token.RAngle>(expectedError("expected closing brace"))
                }
                Monotype.Constructor(qualifier, name, args)
            }
            else -> throw RuntimeException("expected type found $nextToken at $start")
        }
    }

    fun parseNamespace(): Pair<Namespace, Name?> {
        var component: Name? = null
        val components = mutableListOf<Name>()
        while (iterator.peek().value is Token.UpperIdent) {
            component = parseUpperName()
            if (iterator.peek().value is Token.DoubleColon) {
                iterator.next()
                components += component
                component = null
            } else {
                break
            }
        }
        return Namespace(components) to component
    }

    fun parseModuleName(): Namespace {
        val (ns, name) = parseNamespace()
        if (name == null) throw Exception("expected a modulename")
        return Namespace(ns.components + name)
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

    private fun parseVar(namespace: Namespace = Namespace.local): Expression.Var = Expression.Var(namespace, parseName())

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
            is Token.UpperIdent -> {
                val (namespace, dtor) = parseNamespace()
                when {
                    dtor != null -> parseDataConstruction(namespace, dtor)
                    iterator.peek().value is Token.Ident -> parseVar(namespace)
                    else -> null
                }
            }
            is Token.Match -> parseMatch()
            else -> null
        }
    }

    private fun parseLet(): Expression {
        iterator.next()
        var isRecursive = false
        if (iterator.peek().value is Token.Rec) {
            iterator.next()
            isRecursive = true
        }
        val binder = parseName()
        var type: Polytype? = null
        if (iterator.peek().value is Token.Colon) {
            iterator.next()
            type = parsePolytype()
        }
        expectNext<Token.Equals>(expectedError("expected equals"))
        val expr = parseExpression()
        expectNext<Token.In>(expectedError("expected in"))
        val body = parseExpression()

        return if (isRecursive) {
            Expression.LetRec(binder, type, expr, body)
        } else {
            Expression.Let(binder, type, expr, body)
        }
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

    private fun parseDataConstruction(namespace: Namespace, dtor: Name): Expression.Construction {
        expectNext<Token.LParen>(expectedError("expected open paren"))

        val exprs = commaSeparated(::parseExpression) { it !is Token.RParen }
        expectNext<Token.RParen>(expectedError("expected closing paren"))

        return Expression.Construction(namespace, dtor, exprs)
    }

    private fun parseNamespacedUpper(): Pair<Namespace, Name> {
        val (namespace, name) = parseNamespace()
        return namespace to (name ?: throw Exception("expected upper name"))
    }

    fun parseMatch(): Expression.Match {
        iterator.next()
        val expr = parseExpression()
        expectNext<Token.LBrace>(expectedError("expected open brace"))
        val cases = commaSeparated(::parseCase) { it !is Token.RBrace }
        expectNext<Token.RBrace>(expectedError("expected closing brace"))
        return Expression.Match(expr, cases)
    }

    fun parseCase(): Case {
        val pattern = parsePattern()
        expectNext<Token.Arrow>(expectedError("expected arrow"))
        val body = parseExpression()

        return Case(pattern, body)
    }

    fun parsePattern(): Pattern {
        return if (iterator.peek().value is Token.Ident) {
            Pattern.Var(parseName())
        } else {
            val (namespace, dtor) = parseNamespace()
            if (dtor == null) throw Exception("expected a constructor pattern")
            expectNext<Token.LParen>(expectedError("expected open paren"))
            val fields = commaSeparated(::parsePattern) { it !is Token.RParen }
            expectNext<Token.RParen>(expectedError("expected open paren"))
            Pattern.Constructor(namespace, dtor, fields)
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

    companion object {
        fun parseType(input: String): Polytype = Parser(Lexer(input)).parsePolytype()
    }
}

fun main() {
    val listModule = File("stdlib/List.kiml").readText()

    println(Parser(Lexer(listModule)).parseModule())

    println(Parser(Lexer("Data::Option")).parseNamespace())


}