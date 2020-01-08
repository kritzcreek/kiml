package kiml.syntax

import pretty.*

sealed class Expression {
    data class Int(val int: kotlin.Int) : Expression()
    data class Bool(val bool: Boolean) : Expression()
    data class Var(val name: Name) : Expression()
    data class Lambda(val binder: Name, val body: Expression) : Expression() {
        fun foldArguments(): Pair<List<Name>, Expression> {
            return when (body) {
                is Lambda -> {
                    val (innerArgs, closureBody) = body.foldArguments()
                    listOf(binder) + innerArgs to closureBody
                }
                else -> listOf(binder) to body
            }
        }
    }

    data class App(val function: Expression, val argument: Expression) : Expression() {
        fun unfoldApps(): Pair<Expression, List<Expression>> {
            return if (function is App) {
                val (func, args) = function.unfoldApps()
                func to args + listOf(argument)
            } else {
                function to listOf(argument)
            }
        }
    }

    data class Let(val binder: Name, val type: Polytype?, val expr: Expression, val body: Expression) : Expression()
    data class LetRec(val binder: Name, val type: Polytype?, val expr: Expression, val body: Expression) : Expression()
    data class If(val condition: Expression, val thenCase: Expression, val elseCase: Expression) : Expression()
    data class Construction(val ty: Name, val dtor: Name, val fields: List<Expression>) : Expression()
    data class Match(val expr: Expression, val cases: List<Case>) : Expression()

    fun pretty(): String = show().pretty(60, 0.4F)

    fun show(): Doc<Nothing> = showInner(0)

    fun showInner(depth: kotlin.Int): Doc<Nothing> = when (this) {
        is Int -> int.toString().text()
        is Bool -> bool.toString().text()
        is Var -> name.show()
        is Lambda -> {
            var res = (("\\".text<Nothing>() + binder.show() + dot()).group() + space() + body.show()).group().nest(2)
            if (depth > 0) res = res.enclose(lParen(), rParen())
            res
        }
        is App -> {
            val (func, args) = unfoldApps()
            var res = ((listOf(func) + args).map { it.showInner(1) }).sep().group().nest(2)
            if (depth > 0) res = res.enclose(lParen(), rParen())
            res
        }
        is Let ->
            "let".text<Nothing>() + space() + binder.show() + space() + equals() + space() +
                    expr.show() + space() + "in".text() + line() +
                    body.show()
        is LetRec ->
            "letrec".text<Nothing>() + space() + binder.show() + space() + equals() + space() +
                    expr.show() + space() + "in".text() + line() +
                    body.show()
        is If -> (("if".text<Nothing>() + space() + condition.show() + space() + "then".text()).group() +
                space() + thenCase.show()).group().nest(2) +
                space() + ("else".text<Nothing>() + space() + elseCase.show()).group().nest(2)
        is Construction -> {
            val dt = ty.show() + "::".text() + dtor.show() + lParen()
            val fs = fields.fold(nil<Nothing>()) { acc, it -> acc + it.show() + comma() + softLine() }
            dt + fs.nest(2) + rParen()
        }
        is Match -> {
            val header = "match".text<Nothing>() + space() + expr.show() + space() + lBrace()
            val showCase = { case: Case ->
                case.pattern.show() + space() + "=>".text() + space() + (line<Nothing>() +
                        case.expr.show()).nest(2)
            }
            val myCases = cases.fold(nil<Nothing>()) { acc, it -> acc + showCase(it) + comma() + line() }
            header.group() + (line<Nothing>() + myCases).nest(2) + rBrace()
        }
    }

    fun freeVars(): HashSet<Name> {
        return when (this) {
            is Int -> hashSetOf()
            is Bool -> hashSetOf()
            is Var -> hashSetOf(name)
            is Lambda -> body.freeVars().also { it.remove(binder) }
            is App -> function.freeVars().also {
                it.addAll(argument.freeVars())
            }
            is Let -> body.freeVars().also {
                it.remove(binder)
                it.addAll(expr.freeVars())
            }
            is LetRec -> expr.freeVars().also {
                it.addAll(body.freeVars())
                it.remove(binder)
            }
            is If -> condition.freeVars().also {
                it.addAll(thenCase.freeVars())
                it.addAll(elseCase.freeVars())
            }
            is Construction -> {
                val res = hashSetOf<Name>()
                fields.forEach { res.addAll(it.freeVars()) }
                res
            }
            is Match -> expr.freeVars().also { res ->
                cases.forEach { res.addAll(it.freeVars()) }
            }
        }
    }
}

data class Case(val pattern: Pattern, val expr: Expression) {
    fun pretty(): String = "${pattern.pretty()} => ${expr.pretty()}"
    fun freeVars(): HashSet<Name> {
        val res = expr.freeVars()
        res.removeAll(pattern.binders())
        return res
    }
}

sealed class Pattern {
    data class Constructor(val ty: Name, val dtor: Name, val fields: List<Pattern>) : Pattern()
    data class Var(val v: Name) : Pattern()

    fun pretty(): String = when (this) {
        is Constructor -> "$ty::$dtor(${fields.joinToString(", ") { it.pretty() }})"
        is Var -> v.toString()
    }

    fun binders(): HashSet<Name> {
        return when (this) {
            is Constructor ->
                hashSetOf<Name>().also { res ->
                    fields.forEach { res.union(it.binders()) }
                }
            is Var -> hashSetOf(v)
        }
    }

    fun show(): Doc<Nothing> {
        return when (this) {
            is Constructor -> ty.show() + "::".text() + dtor.show() + fields.map { it.show() }.encloseSep(
                lParen(),
                rParen(),
                comma()
            )
            is Var -> v.show()
        }
    }
}


inline class TyVar(val v: String) {
    override fun toString(): String = v
}

inline class Name(val v: String) {
    override fun toString(): String = v
    fun show(): Doc<Nothing> = v.text()
}

data class TypeDeclaration(
    val name: Name,
    val typeVariables: List<TyVar>,
    val dataConstructors: List<DataConstructor>
)

data class DataConstructor(val name: Name, val args: List<Monotype>)

sealed class Monotype {
    data class Constructor(val name: Name, val arguments: List<Monotype>) : Monotype()
    data class Unknown(val u: Int) : Monotype()
    data class Var(val v: TyVar) : Monotype()
    data class Function(val argument: Monotype, val result: Monotype) : Monotype()

    fun pretty(): String {
        return when (this) {
            is Constructor -> "${this.name}" + if (arguments.isNotEmpty()) {
                "<${this.arguments.joinToString(", ") { it.pretty() }}>"
            } else {
                ""
            }
            is Unknown -> "u${this.u}"
            is Var -> this.v.v
            is Function -> "(${this.argument.pretty()} -> ${this.result.pretty()})"
        }
    }


    private fun unknownsInner(acc: HashSet<Int>) {
        when (this) {
            is Constructor -> this.arguments.forEach { it.unknownsInner(acc) }
            is Var -> {
            }
            is Unknown -> acc.add(this.u)
            is Function -> {
                argument.unknownsInner(acc)
                result.unknownsInner(acc)
            }
        }
    }

    fun unknowns(): HashSet<Int> {
        val res = HashSet<Int>()
        unknownsInner(res)
        return res
    }

    fun subst(scrutinee: TyVar, ty: Monotype): Monotype =
        when (this) {
            is Var -> if (scrutinee == v) ty else this
            is Function -> Function(argument.subst(scrutinee, ty), result.subst(scrutinee, ty))
            is Constructor -> Constructor(name, arguments.map { it.subst(scrutinee, ty) })
            else -> this
        }

    fun subst_many(tys: List<Pair<TyVar, Monotype>>): Monotype {
        return tys.fold(this) { acc, (name, ty) ->
            acc.subst(name, ty)
        }
    }

    companion object {
        val int = Constructor(Name("Int"), listOf())
        val bool = Constructor(Name("Bool"), listOf())
    }
}

data class Polytype(val vars: List<TyVar>, val type: Monotype) {
    fun unknowns(): HashSet<Int> = type.unknowns()
    fun pretty(): String = if (vars.isEmpty()) {
        type.pretty()
    } else {
        "forall ${vars.joinToString()}. ${type.pretty()}"
    }

    companion object {
        fun fromMono(monotype: Monotype): Polytype = Polytype(emptyList(), monotype)
    }
}

fun main() {
    println(
        Expression.App(
            Expression.App(
                Expression.App(Expression.Var(Name("x")), Expression.Var(Name("y"))),
                Expression.Var(Name("z"))
            ), Expression.Var(Name("v"))
        ).pretty()
    )
}