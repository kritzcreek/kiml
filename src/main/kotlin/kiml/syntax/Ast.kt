package kiml.syntax

sealed class Expression {
    data class Int(val int: kotlin.Int) : Expression()
    data class Bool(val bool: Boolean) : Expression()
    data class Var(val name: Name) : Expression()
    data class Lambda(val binder: Name, val body: Expression) : Expression()
    data class App(val function: Expression, val argument: Expression) : Expression()
    data class Let(val binder: Name, val type: Polytype?, val expr: Expression, val body: Expression) : Expression()
    data class LetRec(val binder: Name, val type: Polytype?, val expr: Expression, val body: Expression) : Expression()
    data class If(val condition: Expression, val thenCase: Expression, val elseCase: Expression) : Expression()
    data class Construction(val ty: Name, val dtor: Name, val fields: List<Expression>) : Expression()
    data class Match(val expr: Expression, val cases: List<Case>) : Expression()

    fun pretty(): String = when (this) {
        is Int -> "$int"
        is Bool -> "$bool"
        is Var -> this.name.v
        is Lambda -> "(\\${this.binder} -> ${this.body.pretty()})"
        is App -> "(${this.function.pretty()}) ${this.argument.pretty()}"
        is Let -> "(let $binder ${type?.let { ": ${it.pretty()}" } ?: ""} = ${ expr.pretty() } in ${ body.pretty() })"
        is LetRec -> "(let rec $binder ${type?.let { ": ${it.pretty()}" } ?: ""} = ${ expr.pretty() } in ${ body.pretty() })"
        is If -> "(if ${condition.pretty()} then ${thenCase.pretty()} else ${elseCase.pretty()})"
        is Construction -> "${ty}::${dtor}(${fields.joinToString(", ") { it.pretty() }})"
        is Match -> "match ${expr.pretty()} { ${cases.joinToString(", ") { it.pretty() }} }"
        }
    }

    data class Case(val pattern: Pattern, val expr: Expression) {
        fun pretty(): String = "${pattern.pretty()} => ${expr.pretty()}"
    }

    sealed class Pattern {
        data class Constructor(val ty: Name, val dtor: Name, val fields: List<Pattern>) : Pattern()
        data class Var(val v: Name) : Pattern()

        fun pretty(): String = when (this) {
            is Constructor -> "$ty::$dtor(${fields.joinToString(", ") { it.pretty() }})"
            is Var -> v.toString()
        }
    }


    inline class TyVar(val v: String) {
        override fun toString(): String = v
    }

    inline class Name(val v: String) {
        override fun toString(): String = v
    }

    data class TypeDeclaration(
        val name: Name,
        val typeVariables: List<TyVar>,
        val dataConstructors: List<DataConstructor>
    )

    data class DataConstructor(val name: Name, val args: List<Monotype>)

    sealed class Monotype {
        data class Constructor(val name: Name, val arguments: List<Monotype>) : Monotype()
        data class Unknown(val u: kotlin.Int) : Monotype()
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
            public val int = Constructor(Name("Int"), listOf())
            public val bool = Constructor(Name("Bool"), listOf())
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