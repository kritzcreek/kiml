package kiml.backend

sealed class IR {
    sealed class Expression {
        data class Int(val int: kotlin.Int) : Expression()
        data class Bool(val bool: Boolean) : Expression()
        data class Var(val name: String) : Expression()
        data class Application(val func: Expression, val argument: Expression) : Expression()
        data class Pack(val tag: Int, val values: List<Expression>) : Expression()
        data class Match(val scrutinee: Expression, val cases: List<Case>) : Expression()
        data class Let(val recursive: Boolean, val binder: String, val expr: Expression, val body: Expression) :
            Expression()
    }

    data class Case(val tag: Int, val binders: List<String>, val body: Expression)

    sealed class Declaration

}