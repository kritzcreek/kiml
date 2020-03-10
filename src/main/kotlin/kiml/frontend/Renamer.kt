package kiml.frontend

import kiml.syntax.*

data class RenameScope(val values: HashMap<Name, Namespace>, val types: HashMap<Name, Namespace>) {

    companion object {
        fun fromInterface(iface: Interface, namespace: Namespace): RenameScope {
            val valueScope = HashMap<Name, Namespace>()
            val typeScope = HashMap<Name, Namespace>()
            iface.values.env.mapValuesTo(valueScope) { namespace }
            iface.types.tm.mapValuesTo(valueScope) { namespace }
            return RenameScope(valueScope, typeScope)
        }

        val empty = RenameScope(hashMapOf(), hashMapOf())
    }
}

class Renamer(
    val interfaces: HashMap<Namespace, Interface>,
    var toplevel: Namespace = Namespace.local
) {
    private val scope: HashMap<Namespace, RenameScope> =
        hashMapOf(Namespace.local to RenameScope.empty) // TODO: globals

    fun renameModule(module: Module): Module {
        toplevel = module.namespace
        for (import in module.imports) {
            when (import) {
                is Import.Qualified -> scope[import.qualifier] =
                    RenameScope.fromInterface(
                        interfaces[import.module] ?: throw Exception("Unknown module ${import.module}"),
                        import.module
                    )
            }
        }

        return module.copy(declarations = module.declarations.map(::renameDeclaration))
    }

    private fun renameDeclaration(declaration: Declaration): Declaration {
        return when (declaration) {
            is Declaration.TypeDeclaration -> {
                scope[Namespace.local]!!.types[declaration.name] = toplevel
                withTypeVars(declaration.typeVariables) {

                }
            }
            is Declaration.ValueDeclaration -> TODO()
        }
    }

    private fun <A>withTypeVars(typeVariables: List<TyVar>, action: () -> A): A {
        val res = action()
        return res
    }

    fun qualify(namespace: Namespace, x: Expression.Var): Expression.Var =
        x.copy(namespace = namespace)

    fun qualify(namespace: Namespace, x: Monotype.Constructor): Monotype.Constructor =
        x.copy(namespace = namespace)

    fun qualify(namespace: Namespace, x: Pattern.Constructor): Pattern.Constructor =
        x.copy(fullNamespace = namespace.copy(components = namespace.components + x.ty))

    fun qualify(namespace: Namespace, x: Expression.Construction): Expression.Construction =
        x.copy(fullNamespace = namespace.copy(components = namespace.components + x.ty))

}