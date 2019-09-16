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

    fun apply(ty: Polytype): Polytype = ty.copy(type=apply(ty.type))

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
    val environment: Environment = {
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
        names.fold(action) { k, (name, ty) ->
            { bindNameMono(name, ty, k) }
        }()

    private fun <A> bindNameMono(v: Name, ty: Monotype, action: () -> A): A =
        bindName(v, Polytype(listOf(), ty), action)

    private fun <A> bindName(v: Name, ty: Polytype, action: () -> A): A {
        val prev = checkState.environment.env.put(v, ty)
        val res = action()
        // If the name wasn't previously bound...
        if (prev == null) {
            // we need to remove it from the environment again
            checkState.environment.env.remove(v)
        } else {
            // otherwise we need to restore the previous binding
            checkState.environment.env[v] = prev
        }
        return res
    }

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

    data class UnifyException(val ty1: Monotype, val ty2: Monotype, val stack: MutableList<Pair<Monotype, Monotype>>): Exception() {
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
        val skolems: MutableList<Int> = mutableListOf()
        subsumes_inner(ty1, ty2, skolems)
        for (skolem in skolems) {
            when(val ty = zonk(Monotype.Unknown(skolem))) {
                is Monotype.Unknown -> {}
                else -> throw Exception("Tried to match skolem u$skolem with type ${ty.pretty()}")
            }
        }
    }

    private fun subsumes_inner(ty1: Polytype, ty2: Polytype, skolems: MutableList<Int>) {
        when {
            ty1 == ty2 -> {}
            ty1.vars.isNotEmpty() ->
                subsumes_inner(Polytype.fromMono(instantiate(ty1)), ty2, skolems)
            ty2.vars.isNotEmpty() -> {
                val skolemStart = checkState.fresh_supply;
                val skolemized = instantiate(ty2)
                val skolemEnd = checkState.fresh_supply;
                (skolemStart..skolemEnd).forEach { skolems.add(it) }

                subsumes_inner(ty1, Polytype.fromMono(skolemized), skolems)
            }
            else ->
                unify(ty1.type, ty2.type)
        }

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
                if(expr.type != null) {
                    subsumes(tyBinder, expr.type)
                    tyBinder = expr.type
                }
                bindName(expr.binder, tyBinder) { infer(expr.body) }
            }
            is Expression.LetRec -> {
                if(expr.type != null) {
                    val tyBinder = bindName(expr.binder, expr.type) { infer(expr.expr) }
                    subsumes(Polytype.fromMono(tyBinder), expr.type)
                    bindName(expr.binder, expr.type) { infer(expr.body) }
                } else {
                    val tyBinder = freshUnknown()
                    val inferredBinder = bindNameMono(expr.binder, tyBinder) { infer(expr.expr) }
                    unify(tyBinder, inferredBinder)
                    bindNameMono(expr.binder, tyBinder) { infer(expr.body) }
                }
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
let 
  fromMaybe : forall a. a -> Maybe<a> -> a = \def. \x. match x {
    Maybe::Just(x) -> x,
    Maybe::Nothing() -> def
  } in
let identity : forall a. a -> a = \x. x in
let rec map : forall a b. (a -> b) -> List<a> -> List<b> = \f. \ls. match ls {
  List::Nil() -> List::Nil(),
  List::Cons(x, xs) -> List::Cons(f x, map f xs),
} in
map isEven (map (sub 1) List::Cons(1, List::Cons(2, List::Nil())))
}
"""
    val (tys, expr) = Parser(Lexer(input)).parseInput()
    val tc = TypeChecker()
    tys.forEach { tc.addType(it) }
    println("${expr.pretty()} : ")
    println("   ${tc.inferExpr(expr).pretty()}")
}