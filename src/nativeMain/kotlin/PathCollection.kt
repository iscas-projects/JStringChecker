import soot.*
import soot.jimple.*
import soot.jimple.internal.JAssignStmt
import soot.options.Options
import soot.toolkits.graph.Block
import soot.toolkits.graph.BlockGraph
import soot.toolkits.graph.ExceptionalBlockGraph
import java.util.*

/// note here the representation of a path is List<Block>
/// with the tail appear at path[0]

fun <T> listWrapper(items: Collection<T>): Set<List<T>> {
    return items.map { listOf(it) }.toSet()
}

fun <T> Set<List<T>>.updateThoseEndWith(
    name: T,
    isKeepOriginalPath: Boolean,
    policy: (List<T>) -> List<List<T>>
): Set<List<T>> {
    val bipart: Pair<List<List<T>>, List<List<T>>> =
        this.partition { it.isEmpty() || it[0] == name }
    val updated: List<List<T>> = bipart.first.map { policy(it) }
        .flatten()
    //updated += bipart.second;
    return (updated + if (!isKeepOriginalPath) bipart.second else this).toSet()
}

fun <T> Set<List<T>>.updateByEachIndependentInsertion(
    name: T,
    items: List<T>,
    isKeepOriginalPath: Boolean
): Set<List<T>> {
    return this.updateThoseEndWith(
        name,
        isKeepOriginalPath
    ) { l: List<T> -> // copy list For Each item And Insert the item At Head
        items.map { // (l.asReversed() + it).asReversed()
            val temp = l.toMutableList()
            temp.add(0, it)
            temp
        }
    }
}

fun <T> Set<List<T>>.getAllVariablesShownInChains(): Set<T> {
    return this.flatten()
        .toSet()
}

// used to unfold the program loop for `times`
fun <T> Set<List<T>>.getItemsAppearingInEachPathsNoMoreThan(items: Set<T>, times: Int): List<T> {
    return items.filter { item ->
        this.all { lst -> lst.count { it == item } <= times }
    }
}

fun constructPath(cfg: BlockGraph): Set<List<Block>> {
    var items = cfg.heads.toSet()
    if (items.isEmpty()) return emptySet()
    var growingPaths = listWrapper(items)
    val finalPaths = emptySet<List<Block>>().toMutableSet()
    while (items.any { !cfg.tails.contains(it) }) {
        items = growingPaths.mapNotNull { it.firstOrNull() }.toSet()
        items = growingPaths.getItemsAppearingInEachPathsNoMoreThan(items, 2).toSet()
        items.forEach { block ->
            growingPaths = growingPaths.updateByEachIndependentInsertion(block, cfg.getSuccsOf(block), false)
        }
        finalPaths += growingPaths.filter { cfg.tails.contains(it.first()) }
    }
    return finalPaths
}

fun <T> Set<List<T>>.filterOutNotContainAny(items: Collection<T>): Set<List<T>> {
    return this.filter { path: List<T> -> path.any { items.contains(it) } }.toSet()
}

class Slicer(val programPath: List<Block>) {
    private val stmts = programPath.asReversed().map { it.toList() }.flatten()
    private var constraintChain: List<Condition>? = null

    private fun getStringRelatedVars(): List<Value> {
        return stmts.filter { unit ->
            (unit as Stmt).containsInvokeExpr() &&
                    unit.invokeExpr.method.let {
                        it.name.contains("toString") ||
                                it.signature.contains("java.lang.String")
                    }
        }.flatMap { it.defBoxes }
            .map { it.value }
    }

    fun getStringRelatedSlice(): List<Unit> { //TODO: some refactor as this may have an idiom in kotlin
        var concernedVars = getStringRelatedVars().toSet()
        var updatedVars: Set<Value> = emptySet()
        val valueEquivGroups = stmts.map { getParameterAndReceiver(it as Stmt) }
        while (concernedVars != updatedVars) {
            concernedVars = concernedVars.union(updatedVars)
            updatedVars =
                concernedVars.flatMap { variable -> valueEquivGroups.filter { group -> group.contains(variable) } }
                    .flatten()
                    .toSet()
        }
        return stmts.zip(valueEquivGroups)
            .filter { (_, group) ->
                group.intersect(concernedVars).isNotEmpty()
            }.map { it.first }
    }

    fun getPathConstraints(): List<Condition> {
        if (constraintChain == null)
            constraintChain = programPath.asReversed().zipWithNext().map { (prev, next) ->
                prev.tail.let { jumpStatement ->
                    if (jumpStatement is IfStmt && jumpStatement.fallsThrough())
                        if (jumpStatement.target == next.head)
                            Single(jumpStatement.condition)
                        else Negate(Single(jumpStatement.condition))
                    else if (jumpStatement is GotoStmt)
                        Nop()
                    else Nop("DEBUG: $jumpStatement")
                }
            }
        return constraintChain as List<Condition>
    }

    // zip the statements and conditions together, statements should be n + 1 if conditions are n
    fun getPath(): List<PathItem> {
        val exceptLastOne = programPath.asReversed().dropLast(1)
        return exceptLastOne.zip(getPathConstraints()).map { (block, cond) ->
            block.map { Statement(it as Stmt) } + cond
        }.flatten() +
                (programPath.getOrNull(0)?.map { Statement(it as Stmt) } ?: emptyList())
    }

    private fun getApiTypes(): Map<SootMethod, Int> {
        return stmts.mapNotNull { unit ->
            if ((unit as Stmt).containsInvokeExpr())
                unit.invokeExpr.method
            else null
        }.filter {
            it.name.contains("toString") ||
                    it.signature.contains("java.lang.String") ||
                    it.signature.contains("CharSequence")
        }.groupBy { it }
            .mapValues { it.value.count() }
    }

    private fun getApiChains(): List<List<PathItem>> {
        fun relatedWithVar(apiSeq: List<PathItem>, localVar: Value): Boolean {
            if (apiSeq.isEmpty()) return false
            return apiSeq[0].let {
                (it is Statement && it.stmt.useBoxes.any { use ->
                    use.value == localVar
                }) ||
                (it is Condition && it.getValues().any { value ->
                    value.useBoxes.any { use ->
                        use.value == localVar
                    }
                })
            }
        }

        val pathStmts = programPath.asReversed().flatten().asReversed()
        return getPathConstraints().flatMap { condition ->
            condition.getValues().mapNotNull { value ->
                if (value is BinopExpr) {
                    val apiSeqs: MutableList<List<PathItem>> = mutableListOf(listOf(condition))
                    val workList = mutableListOf(value.op1, value.op2)
                    val visitedList = mutableListOf<Value>()
                    while (workList.isNotEmpty()) {
                        val item = workList.removeAt(0)
                        visitedList.add(item)
                        val related = pathStmts.firstOrNull { it.defBoxes.map { it.value }.contains(item) } ?: continue
                        workList.addAll((related.useBoxes + related.defBoxes)
                            .map { useBox -> useBox.value }
                            .filterIsInstance<Local>()
                            .filter { !visitedList.contains(it) })
                        apiSeqs += apiSeqs.filter { apiSeq -> relatedWithVar(apiSeq, item) }
                            .map {
                                it.asReversed().plus(Statement(related as Stmt)).asReversed()
                            }
                            .toMutableList()
                    }
                    apiSeqs
                } else null
            }.flatten()
        }
    }

    fun getStatistics() = "involved APIs: ${getApiTypes().entries.joinToString("\n")}\n" +
            "API chains: ${getApiChains().joinToString("\n")}\n"
}

fun getParameterAndReceiver(stmt: Stmt): List<Value> {
    val result: MutableList<Value> = mutableListOf()
    if (stmt is JAssignStmt)
        result.add(stmt.leftOpBox.value)
    if (stmt.containsInvokeExpr())
        result.addAll(stmt.invokeExpr.args)
    return result
}

fun hasStringOps(bl: Block): Boolean {
    return bl.any { unit ->
        (unit as Stmt).containsInvokeExpr() &&
                unit.invokeExpr.method.let { it.name.contains("toString") || it.signature.contains("java.lang.String") }
    }
//        if (u.getUseAndDefBoxes().stream().anyMatch { box: ValueBox ->
//                box.value.type.toString().contains("String")
}

fun main() { // test use
    G.reset()
    Options.v().set_prepend_classpath(true)

    Options.v().set_src_prec(Options.src_prec_class)
    //Options.v().set_src_prec(Options.src_prec_apk);
    //Options.v().set_android_jars(android_jars);
    Options.v().set_process_dir(Collections.singletonList("datasets/Src003/"))
    Options.v().set_allow_phantom_refs(true)
    Scene.v().addBasicClass("java.lang.String", SootClass.BODIES)
    Scene.v().loadNecessaryClasses()
    val pathsOfFunc = HashMap<String, List<String>>()

    PackManager.v().getPack("jtp").add(Transform("jtp.mySlicer", object : BodyTransformer() {
        override fun internalTransform(b: Body?, phaseName: String?, options: MutableMap<String, String>?) {
            val blockCFG = ExceptionalBlockGraph(b)
            var paths = constructPath(blockCFG)
//            val blocksWithStringOps = blockCFG.blocks.filter { hasStringOps(it) }
//            paths = paths.filterOutNotContainAny(blocksWithStringOps)
            val slicers = paths.map { Slicer(it) }
            if (b?.method?.name != null)
                println(slicers.map {
                    it.getStatistics() + "\n\n" +
                            it.getPath().joinToString("\n")
                })
        }
    }))
    PackManager.v().runPacks()
}