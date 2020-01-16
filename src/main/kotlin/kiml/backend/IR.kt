package kiml.backend

import kiml.frontend.Lexer
import kiml.frontend.Parser
import kiml.frontend.TypeInfo
import kiml.frontend.TypeMap
import kiml.syntax.Case
import kiml.syntax.Expression
import kiml.syntax.Name
import kiml.syntax.Pattern
import pretty.*

sealed class LNName<A> {
    data class Free<A>(val v: A) : LNName<A>()
    data class Bound<A>(val ix: Index) : LNName<A>()

    data class Index(val depth: Int, val breadth: Int) {
        fun shift(i: Int = 1): Index = this.copy(depth = depth + i)
    }

    fun show(): Doc<Nothing> =
        when (this) {
            is Free -> v.toString().text()
            is Bound -> lAngle<Nothing>() +
                    ix.depth.toString().text() +
                    comma() + space() +
                    ix.breadth.toString().text() + rAngle()
        }
}


sealed class IR {
    sealed class Expression {
        data class Int(val int: kotlin.Int) : Expression()
        data class Bool(val bool: Boolean) : Expression()
        data class Var(val name: LNName<Name>) : Expression()
        data class Application(val func: Expression, val argument: Expression) : Expression() {
            fun unfoldApps(): Pair<Expression, List<Expression>> {
                return if (func is Expression.Application) {
                    val (func, args) = func.unfoldApps()
                    func to args + listOf(argument)
                } else {
                    func to listOf(argument)
                }
            }
        }

        data class Pack(val tag: kotlin.Int, val values: List<Expression>) : Expression()
        data class Match(val scrutinee: Expression, val cases: List<Case>) : Expression()
        data class If(val condition: Expression, val thenCase: Expression, val elseCase: Expression) : Expression()
        data class Let(
            val binder: LNName.Free<Name>,
            val expr: Expression,
            val body: Expression
        ) : Expression()

        data class GetLocal(val ix: kotlin.Int) : Expression()

        fun instantiate(replacements: List<Expression>): Expression =
            instantiateInner(0, replacements)

        fun instantiateInner(depth: kotlin.Int, replacements: List<Expression>): Expression {
            return when (this) {
                is Int, is Bool, /*is MakeClosure,*/ is GetLocal -> this
                is Var -> when (this.name) {
                    is LNName.Free -> this
                    is LNName.Bound ->
                        if (this.name.ix.depth == depth)
                            replacements[this.name.ix.breadth]
                        else
                            this
                }
                is Application -> Application(
                    func.instantiateInner(depth, replacements),
                    argument.instantiateInner(depth, replacements)
                )
                is Pack -> Pack(
                    tag,
                    values.map { it.instantiateInner(depth, replacements) }
                )
                is Match -> Match(
                    scrutinee.instantiateInner(depth, replacements),
                    cases.map { it.instantiateInner(depth, replacements) }
                )
                is If -> If(
                    condition.instantiateInner(depth, replacements),
                    thenCase.instantiateInner(depth, replacements),
                    elseCase.instantiateInner(depth, replacements)
                )
                is Let -> Let(
                    binder,
                    expr.instantiateInner(depth, replacements),
                    body.instantiateInner(depth + 1, replacements)
                )
            }
        }

        fun over(f: (Expression) -> Expression): Expression {
            return f(when (this) {
                is Int, is Bool, is Var, is GetLocal -> this
                is Application -> Application(
                    func.over(f),
                    argument.over(f)
                )
                is Pack -> Pack(
                    tag,
                    values.map { it.over(f) }
                )
                is Match -> Match(
                    scrutinee.over(f),
                    cases
                )
                is If -> If(
                    condition.over(f),
                    thenCase.over(f),
                    elseCase.over(f)
                )
                is Let -> Let(
                    binder,
                    expr.over(f),
                    body.over(f)
                )
            })
        }

        fun subst(name: Name, replacement: Expression): Expression = over {
            if (it is Var && it.name is LNName.Free && it.name.v == name) replacement
            else it
        }

        fun show(): Doc<Nothing> {
            return when (this) {
                is Int -> int.toString().text()
                is Bool -> bool.toString().text()
                is Var -> name.show()
                is Application -> func.show() + space() + argument.show().enclose(lParen(), rParen())
                is Pack -> "Pack".text<Nothing>() + (listOf(tag.doc<Nothing>()) + this.values.map { it.show() }).encloseSep(
                    lParen(),
                    rParen(),
                    comma<Nothing>() + space()
                )
                is Match -> "match".text<Nothing>() + space() + scrutinee.show() + cases.map { it.show() }.encloseSep(
                    lBrace(), rBrace(), comma()
                )
                is If -> "if".text<Nothing>() + space() + condition.show() + space() + "then".text() +
                        space() + thenCase.show() +
                        space() + "else".text() + space() + elseCase.show()
                is Let ->
                    "let".text<Nothing>() + space() + binder.show() + space() + equals() + space() +
                            expr.show() + space() + "in".text() + line() +
                            body.show()
                is GetLocal -> "GetLocal($ix)".text()
                else -> this.toString().text()
            }
        }
    }

    data class Case(val tag: Int, val binders: List<Name>, val body: Expression) {
        fun instantiateInner(depth: Int, replacements: List<Expression>): Case =
            Case(tag, binders, body.instantiateInner(depth + 1, replacements))

        fun show(): Doc<Nothing> =
            (tag.doc<Nothing>() + space() + binders.map { it.show() }.encloseSep(
                lParen(),
                rParen(),
                comma<Nothing>() + space()
            ) + space() + "->".text()).group() + body.show()
    }

    data class Declaration(
        val name: Name,
        val arguments: List<Name/* add Type here*/>,
        val body: Expression
    ) {
        fun show(): Doc<Nothing> {
            val header = ("fun".text<Nothing>() + space() +
                    name.v.text() +
                    arguments
                        .map { it.v.text<Nothing>() }
                        .encloseSep(lParen(), rParen(), comma<Nothing>() + space())).group()
            return (header + space() + lBrace() + line() + body.show()).nest(2) + line() + rBrace()
        }

        fun pretty(): String {
            return show().pretty(90, 0.4F)
        }
    }
}

class Lowering(val typeMap: TypeMap) {
    var freshSupply: Int = 0
    val liftedDeclarations = mutableListOf<IR.Declaration>()

    fun freshName(name: String): Name {
        return Name("$${name}_${freshSupply++}")
    }

    fun tagForDtor(type: Name, dtor: Name): Int {
        val tyInfo = typeMap.tm[type] ?: throw Exception("Unknown type name $type")
        val ix = tyInfo.constructors.indexOfFirst { dtor == it.name }
        return if (ix != -1) ix else throw Exception("Unknown dtor name $dtor")
    }

    private fun liftFunction(
        topName: Name,
        capturedVars: List<Pair<Name, LNName.Bound<Name>>>,
        lambda: Expression.Lambda
    ): IR.Expression {
        val (arguments, body) = lambda.foldArguments()
        val allArguments = capturedVars.map { it.first } + arguments
        val tmpEnv = HashMap<Name, LNName.Index>()
        allArguments.forEachIndexed { ix, arg ->
            tmpEnv[arg] = LNName.Index(0, ix)
        }
        liftedDeclarations += IR.Declaration(
            topName,
            allArguments,
            lowerExpr(body, tmpEnv)
        )
        val fn: IR.Expression = IR.Expression.Var(LNName.Free(topName))
        return capturedVars.fold(fn) { acc, (_, bound) ->
            IR.Expression.Application(acc, IR.Expression.Var(bound))
        }
    }

    fun lowerExpr(expr: Expression, env: MutableMap<Name, LNName.Index>): IR.Expression {
        return when (expr) {
            is Expression.Int -> IR.Expression.Int(expr.int)
            is Expression.Bool -> IR.Expression.Bool(expr.bool)
            is Expression.Var -> IR.Expression.Var(
                env[expr.name]?.let { LNName.Bound<Name>(it) } ?: LNName.Free(expr.name)
            )
            is Expression.Lambda -> {
                val topName = freshName("lifted")
                val capturedVars =
                    // We only keep non top-level bound names
                    expr
                        .freeVars()
                        .mapNotNull { env[it]?.let { index -> it to LNName.Bound<Name>(index) } }
                liftFunction(topName, capturedVars, expr)
            }
            is Expression.App -> IR.Expression.Application(
                lowerExpr(expr.function, env),
                lowerExpr(expr.argument, env)
            )
            is Expression.LetRec -> {
                if (expr.expr !is Expression.Lambda) {
                    throw Exception("Only functions may be defined recursively")
                }
                val topName = freshName("${expr.binder}")
                val capturedVars =
                    expr
                        .freeVars()
                        .mapNotNull {
                            if (it == expr.binder) null
                            else env[it]?.let { index -> it to LNName.Bound<Name>(index) }
                        }

                val exprFn: Expression = Expression.Var(topName)
                val replacement = capturedVars.fold(exprFn) { acc, (name, _) ->
                    Expression.App(acc, Expression.Var(name))
                }
                val loweredExpr = liftFunction(topName, capturedVars, expr.expr.substLam(expr.binder, replacement))

                val tmpEnv = HashMap<Name, LNName.Index>()
                env.mapValuesTo(tmpEnv) { it.value.shift() }
                tmpEnv[expr.binder] = LNName.Index(0, 0)
                IR.Expression.Let(
                    binder = LNName.Free(expr.binder),
                    expr = loweredExpr,
                    body = lowerExpr(expr.body, tmpEnv)
                )
            }
            is Expression.Let -> {
                val tmpEnv = HashMap<Name, LNName.Index>()
                env.mapValuesTo(tmpEnv) { it.value.shift() }
                tmpEnv[expr.binder] = LNName.Index(0, 0)
                IR.Expression.Let(
                    binder = LNName.Free(expr.binder),
                    expr = lowerExpr(expr.expr, env),
                    body = lowerExpr(expr.body, tmpEnv)
                )
            }
            is Expression.If -> IR.Expression.If(
                lowerExpr(expr.condition, env),
                lowerExpr(expr.thenCase, env),
                lowerExpr(expr.elseCase, env)
            )
            is Expression.Construction ->
                IR.Expression.Pack(tagForDtor(expr.ty, expr.dtor), expr.fields.map { lowerExpr(it, env) })
            is Expression.Match -> {
                IR.Expression.Match(
                    lowerExpr(expr.expr, env),
                    expr.cases.map { lowerCase(it, env) }
                )
            }
        }
    }

    private fun lowerCase(case: Case, env: MutableMap<Name, LNName.Index>): IR.Case {
        if (case.pattern !is Pattern.Constructor) {
            throw Exception("Non constructor pattern")
        }

        val binders = case.pattern.fields.map {
            if (it !is Pattern.Var) throw Exception("Non var pattern")
            it.v
        }

        val tmpEnv = HashMap<Name, LNName.Index>()
        env.mapValuesTo(tmpEnv) { it.value.shift() }
        binders.forEachIndexed { ix, b ->
            tmpEnv[b] = LNName.Index(0, ix)
        }

        return IR.Case(
            tagForDtor(case.pattern.ty, case.pattern.dtor),
            binders,
            lowerExpr(case.expr, tmpEnv)
        )
    }

    fun lowerProg(expr: Expression): List<IR.Declaration> {
        val main = lowerExpr(expr, hashMapOf())
        liftedDeclarations.add(IR.Declaration(Name("main"), emptyList(), main))
        return liftedDeclarations
    }

}

fun main() {
    val input =
        """
type Maybe<a> { Nothing(), Just(a) }
type Either<a, b> { Left(a), Right(b) }
type List<a> { Cons(a, List<a>), Nil() }

let fromMaybe : forall a. a -> Maybe<a> -> a =
  \def. \x. match x {
    Maybe::Just(x) -> x,
    Maybe::Nothing() -> def
  } in
let emptyList : forall a. List<a> =
  List::Nil() in
let rec map : forall a b. (a -> b) -> List<a> -> List<b> = 
  \f. \ls. match ls {
    List::Nil() -> emptyList,
    List::Cons(x, xs) -> List::Cons(f x, map f xs),
  } in
map isEven (map (sub 1) List::Cons(1, List::Cons(2, List::Nil())))
"""
    val input2 =
        """
let identity = \x. x in
let rec f = \x. identity f x in
f 10
"""


    val (tys, expr) = Parser(Lexer(input2)).parseInput()

    val typeMap = TypeMap(HashMap())
    tys.forEach { typeMap.tm.put(it.name, TypeInfo(it.typeVariables, it.dataConstructors)) }

    val lowering = Lowering(typeMap)
    val prog = lowering.lowerProg(expr)
    prog.forEach {
        println(it.pretty())
    }
}