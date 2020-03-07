package kiml.frontend

import kiml.syntax.Module
import kiml.syntax.Name
import java.io.File

enum class CodegenTarget {
    Wasm,
    Interpet
}

data class Config(val codegenTarget: CodegenTarget, val outputDirectory: String)

class Graph(val vertices: List<String>, edges: List<Pair<Int, Int>>) {

    private val numVertices = vertices.size
    private val adjacency = List(numVertices) { BooleanArray(numVertices) }

    init {
        for (edge in edges) adjacency[edge.first][edge.second] = true
    }


    private fun hasDependency(r: Int, todo: List<Int>): Boolean {
        for (c in todo) if (adjacency[r][c]) return true
        return false
    }

    fun topoSort(): List<String>? {
        val result = mutableListOf<String>()
        val todo = MutableList(numVertices) { it }
        try {
            outer@ while (todo.isNotEmpty()) {
                for ((i, r) in todo.withIndex()) {
                    if (!hasDependency(r, todo)) {
                        todo.removeAt(i)
                        result.add(vertices[r])
                        continue@outer
                    }
                }
                throw Exception("Graph has cycles")
            }
        } catch (e: Exception) {
            println(e)
            return null
        }
        return result
    }

    companion object {
        fun fromModules(modules: List<Module>): Graph {
            val vertices = modules.map { it.name.v }
            fun vertexIndex(n: Name): Int = vertices.indexOf(n.v).also {
                if (it < 0) throw Exception("Unknown module $n")
            }

            val edges = modules.flatMap { module ->
                module.imports.map { vertexIndex(module.name) to vertexIndex(it.name()) }
            }
            return Graph(vertices, edges)
        }
    }
}

class Pipeline {
    fun compileModules(files: List<File>, config: Config) {
        // parse
        val parsedModules = files.map { Parser(Lexer(it.readText())).parseModule() }
        //toposort
        val topoOrdered = Graph.fromModules(parsedModules).topoSort() ?: throw Exception("Import cycles")
        val topoModules = parsedModules.sortedWith(Comparator { o1, o2 ->
            topoOrdered.indexOf(o1.name.v).compareTo(topoOrdered.indexOf(o2.name.v))
        })
        // renaming
        // typechecking
        val typeChecked: HashMap<Name, Pair<TypeMap, Environment>> = hashMapOf()
        topoModules.forEach {
            typeChecked[it.name] = TypeChecker(CheckState.initial(typeChecked)).inferModule(it)
        }

        // codegen

        // linking

        println(topoModules.map {it.name})
    }
}

fun main() {
    Pipeline().compileModules(
        listOf("list", "option", "prelude").map { File("stdlib/$it.kiml") },
        Config(CodegenTarget.Wasm, "")
    )
}