package kiml.frontend

import kiml.syntax.Module
import kiml.syntax.Namespace
import java.io.File

enum class CodegenTarget {
    Wasm,
    Interpet
}

data class Config(val codegenTarget: CodegenTarget, val outputDirectory: String)

class Graph(private val vertices: List<String>, edges: List<Pair<Int, Int>>) {

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
            val vertices = modules.map { it.name }
            fun vertexIndex(s: String): Int = vertices.indexOf(s).also {
                if (it < 0) throw Exception("Unknown module $s")
            }

            val edges = modules.flatMap { module ->
                module.imports.map { vertexIndex(module.name) to vertexIndex(it.name().toString()) }
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
            topoOrdered.indexOf(o1.name).compareTo(topoOrdered.indexOf(o2.name))
        })
        // renaming
        // typechecking
        val typeChecked: HashMap<Namespace, Interface> = hashMapOf()
        topoModules.forEach {
            typeChecked[it.namespace] = TypeChecker(CheckState.initial(typeChecked)).inferModule(it)
        }
        println(topoModules.map {it.name})
        // codegen
        // linking
    }
}

fun main() {
    Pipeline().compileModules(
        listOf("list", "option", "prelude").map { File("stdlib/$it.kiml") },
        Config(CodegenTarget.Wasm, "")
    )
}