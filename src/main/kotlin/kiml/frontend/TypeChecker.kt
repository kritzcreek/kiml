package kiml.frontend

import kiml.syntax.*
import kotlin.Exception

data class Substitution(val subst: HashMap<Int, Monotype>) {
    fun apply(ty: Monotype): Monotype =
        when (ty) {
            is Monotype.Unknown ->
                subst[ty.u]?.let(::apply) ?: ty
            is Monotype.Function ->
                Monotype.Function(apply(ty.argument), apply(ty.result))
            is Monotype.Constructor ->
                ty.copy(arguments = ty.arguments.map { apply(it) })
            else -> ty
        }

    override fun toString(): String =
        "{ " + subst.toList().joinToString("\n, ") { (u, ty) -> "u$u ↦ ${ty.pretty()}" } + "\n}"
}

data class Environment(val env: HashMap<Name, Polytype> = hashMapOf()) {
    fun unknowns(): HashSet<Int> {
        val res = HashSet<Int>()
        for ((_, ty) in env) {
            res.union(ty.unknowns())
        }
        return res
    }

    fun insertMono(name: Name, ty: Monotype) {
        env[name] = Polytype(listOf(), ty)
    }
}

data class TypeInfo(val tyArgs: List<TyVar>, val constructors: List<DataConstructor>) {
    companion object {
        val empty = TypeInfo(listOf(), listOf())
    }
}

data class TypeMap(val tm: HashMap<Name, TypeInfo>)

data class CheckState(
    var environment: Environment = {
        val res = Environment()
        res.insertMono(Name("isEven"), Monotype.Function(Monotype.int, Monotype.bool))
        res.insertMono(Name("eq"), Monotype.Function(Monotype.int, (Monotype.Function(Monotype.int, Monotype.bool))))
        res.insertMono(Name("mul"), Monotype.Function(Monotype.int, (Monotype.Function(Monotype.int, Monotype.int))))
        res.insertMono(Name("sub"), Monotype.Function(Monotype.int, (Monotype.Function(Monotype.int, Monotype.int))))
        res
    }(),
    val substitution: Substitution = Substitution(HashMap()),
    val typeMap: TypeMap = TypeMap(
        hashMapOf(
            Name("Int") to TypeInfo.empty,
            Name("Bool") to TypeInfo.empty
        )
    ),
    var fresh_supply: Int = 0
)

class TypeChecker {
    private val checkState = CheckState()

    private fun freshUnknown(): Monotype = Monotype.Unknown(++checkState.fresh_supply)

    private fun zonk(ty: Monotype): Monotype = checkState.substitution.apply(ty)

    private fun lookupName(v: Name): Monotype =
        checkState.environment.env[v]?.let(::instantiate) ?: throw Exception("Unknown variable $v")

    fun addType(tyDecl: TypeDeclaration) {
        checkState.typeMap.tm.put(tyDecl.name, TypeInfo(tyDecl.typeVariables, tyDecl.dataConstructors))
    }

    private fun lookupType(ty: Name): TypeInfo = checkState.typeMap.tm[ty] ?: throw Exception("Unknown type $ty")

    private fun lookupDataConstructor(ty: Name, dtor: Name): Pair<List<TyVar>, List<Monotype>> {
        val tyInfo = lookupType(ty)
        val dataConstructor = tyInfo.constructors.find { it.name == dtor }
            ?: throw Exception("Unknown dtor $ty::$dtor")
        return tyInfo.tyArgs to dataConstructor.args
    }

    private fun instantiate(ty: Polytype): Monotype {
        var result = ty.type
        for (v in ty.vars) {
            result = result.subst(v, freshUnknown())
        }
        return result
    }

    private fun generalise(ty: Monotype): Polytype {
        val ty = zonk(ty)
        val niceVars = "abcdefghijklmnopqrstuvwxyz".iterator()
        val quantified: MutableList<TyVar> = mutableListOf()
        val subst: HashMap<Int, Monotype> = HashMap()
        val envUnknowns = checkState.environment.unknowns()
        for (free in ty.unknowns()) {
            if (!envUnknowns.contains(free)) {
                val tyVar = TyVar(niceVars.nextChar().toString())
                quantified.add(tyVar)
                subst[free] = Monotype.Var(tyVar)
            }
        }
        return Polytype(quantified, Substitution(subst).apply(ty))
    }

    private fun <A> bindNamesMono(names: List<Pair<Name, Monotype>>, action: () -> A): A =
        bindNames(names.map { (v, ty) -> v to Polytype.fromMono(ty) }, action)

    private fun <A> bindNames(names: List<Pair<Name, Polytype>>, action: () -> A): A {
        // Store the previous environment
        val tmp = Environment(HashMap(checkState.environment.env))
        names.forEach { (v, ty) -> checkState.environment.env[v] = ty }
        val res = action()
        // restore the environment
        checkState.environment = tmp
        return res
    }

    private fun <A> bindNameMono(v: Name, ty: Monotype, action: () -> A): A =
        bindNamesMono(listOf(v to ty), action)

    private fun <A> bindName(v: Name, ty: Polytype, action: () -> A): A =
        bindNames(listOf(v to ty), action)

    private fun occursCheck(u: Int, ty: Monotype) {
        if (ty is Monotype.Unknown) return
        if (ty.unknowns().contains(u)) {
            throw Exception("Occurs check failed for u$u and ${zonk(ty).pretty()}")
        }
    }

    private fun solveType(u: Int, ty: Monotype) {
        occursCheck(u, ty)
        checkState.substitution.subst[u] = ty
    }

    data class UnifyException(val ty1: Monotype, val ty2: Monotype, val stack: MutableList<Pair<Monotype, Monotype>>) :
        Exception() {
        override fun toString(): String {
            return """
Failed to match ${ty1.pretty()} with ${ty2.pretty()}
  ${stack.joinToString("\n  ") { (t1, t2) -> "while trying to match ${t1.pretty()} with ${t2.pretty()}" }}"""
        }
    }

    private fun unify(ty1: Monotype, ty2: Monotype) {
        val ty1 = zonk(ty1)
        val ty2 = zonk(ty2)
        if (ty1 == ty2) return
        when {
            ty1 is Monotype.Constructor && ty2 is Monotype.Constructor -> {
                if (ty1.name != ty2.name) throw UnifyException(ty1, ty2, mutableListOf())
                try {
                    ty1.arguments.zip(ty2.arguments) { t1, t2 ->
                        unify(t1, t2)
                    }
                } catch (ex: UnifyException) {
                    ex.stack.add(ty1 to ty2)
                    throw ex
                }
            }
            ty1 is Monotype.Unknown -> solveType(ty1.u, ty2)
            ty2 is Monotype.Unknown -> solveType(ty2.u, ty1)
            ty1 is Monotype.Function && ty2 is Monotype.Function -> {
                try {
                    unify(ty1.argument, ty2.argument)
                    unify(ty1.result, ty2.result)
                } catch (ex: UnifyException) {
                    ex.stack.add(ty1 to ty2)
                    throw ex
                }
            }
            else -> throw UnifyException(ty1, ty2, mutableListOf())
        }
    }

    private fun subsumes(ty1: Polytype, ty2: Polytype) {
        // Without higher-rank types this is very simple to implement
        unify(instantiate(ty1), ty2.type)
    }

    private fun infer(expr: Expression): Monotype {
        return when (expr) {
            is Expression.Int ->
                Monotype.int
            is Expression.Bool ->
                Monotype.bool
            is Expression.Var ->
                lookupName(expr.name)
            is Expression.Lambda -> {
                val tyBinder = freshUnknown()
                val tyBody = bindNameMono(expr.binder, tyBinder) { infer(expr.body) }
                Monotype.Function(tyBinder, tyBody)
            }
            is Expression.App -> {
                val tyResult = freshUnknown()
                val tyFun = infer(expr.function)
                val tyArg = infer(expr.argument)
                unify(tyFun, Monotype.Function(tyArg, tyResult))
                tyResult
            }
            is Expression.Let -> {
                var tyBinder = Polytype.fromMono(infer(expr.expr))
                if (expr.type != null) {
                    subsumes(tyBinder, expr.type)
                    tyBinder = expr.type
                }
                bindName(expr.binder, tyBinder) { infer(expr.body) }
            }
            is Expression.LetRec -> {
                val envBinder = expr.type ?: Polytype.fromMono(freshUnknown())
                var tyBinder = bindName(expr.binder, envBinder) {
                    Polytype.fromMono(infer(expr.expr))
                }
                if (expr.type != null) {
                    subsumes(tyBinder, expr.type)
                    tyBinder = expr.type
                }
                bindName(expr.binder, tyBinder) { infer(expr.body) }
            }
            is Expression.If -> {
                val tyCond = infer(expr.condition)
                unify(tyCond, Monotype.bool)
                val tyThen = infer(expr.thenCase)
                val tyElse = infer(expr.elseCase)
                unify(tyThen, tyElse)
                tyThen // Could just as well be tyElse
            }
            is Expression.Match -> {
                val tyExpr = infer(expr.expr)
                val tyRes = freshUnknown()
                expr.cases.forEach {
                    val typedNames = inferPattern(it.pattern, tyExpr)
                    val tyCase = bindNamesMono(typedNames) { infer(it.expr) }
                    unify(tyRes, tyCase)
                }
                tyRes
            }
            is Expression.Construction -> {
                val (tyArgs, fields) = lookupDataConstructor(expr.ty, expr.dtor)
                val freshVars = tyArgs.map { it to freshUnknown() }
                expr.fields.zip(fields).forEach { (expr, ty) ->
                    unify(ty.subst_many(freshVars), infer(expr))
                }
                Monotype.Constructor(expr.ty, freshVars.map { it.second })
            }
        }
    }

    private fun inferPattern(pattern: Pattern, ty: Monotype): List<Pair<Name, Monotype>> {
        return when (pattern) {
            is Pattern.Constructor -> {
                val (tyArgs, fields) = lookupDataConstructor(pattern.ty, pattern.dtor)
                val freshVars = tyArgs.map { it to freshUnknown() }
                unify(ty, Monotype.Constructor(pattern.ty, freshVars.map { it.second }))
                pattern.fields.zip(fields).flatMap { (pat, ty) -> inferPattern(pat, ty.subst_many(freshVars)) }
            }
            is Pattern.Var -> listOf(pattern.v to ty)
        }
    }
    
    fun inferExpr(expr: Expression): Monotype = zonk(infer(expr)).also { println(checkState.substitution) }
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
let rec map : forall a b. (a -> b) -> List<a> -> List<b> = 
  \f. \ls. match ls {
    List::Nil() -> List::Nil(),
    List::Cons(x, xs) -> List::Cons(f x, map f xs),
  } in
map isEven (map (sub 1) List::Cons(1, List::Cons(2, List::Nil())))
"""
    val (tys, expr) = Parser(Lexer(input)).parseInput()
    val tc = TypeChecker()
    tys.forEach { tc.addType(it) }
    println("${expr.pretty()} : ")
    println("   ${tc.inferExpr(expr).pretty()}")
}