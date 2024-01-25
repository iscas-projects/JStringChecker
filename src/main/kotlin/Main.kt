import soot.*
import soot.options.Options
import soot.toolkits.graph.ExceptionalBlockGraph
import java.io.File
import java.util.*


fun main(args: Array<String>) {

    for (pathsOfFunc in slice("C:\\Users\\yyzha\\Desktop\\lucene-9.9.1\\lucene-9.9.1\\modules\\lucene-analysis-icu-9.9.1.jar")) { // write to .path files
        val dir = File("paths" + File.separator + "method-" + pathsOfFunc.key.replace("<", "《").replace(">", "》"))
        if (dir.isDirectory() || dir.mkdir()) {
            pathsOfFunc.value.forEachIndexed { index, slicer ->
                File(dir, "$index.path").writeText(compatibleCpathTransformer(slicer))
            }
        }
    }
}

fun plainReportTransformer(slicer: Slicer) = slicer.getStatistics() + "\n\n" +
        slicer.getPath().joinToString("\n")

fun conditionExpander(condition: Condition): String = when (condition) {
    is Intersect -> "(${conditionExpander(condition.leftCond)} && ${conditionExpander(condition.rightCond)})"
    is Negate -> "!(${conditionExpander(condition.cond)})"
    is Nop -> "()"
    is Single -> "(${condition.value})"
    is Union -> "(${conditionExpander(condition.leftCond)} || ${conditionExpander(condition.rightCond)})"
}
fun compatibleCpathTransformer(slicer: Slicer) = slicer.getPath().joinToString("\n") { pathItem ->
    when (pathItem) {
        is Intersect -> "@${conditionExpander(pathItem)};"
        is Negate -> "@${conditionExpander(pathItem)};"
        is Nop -> "@${conditionExpander(pathItem)};"
        is Single -> "@${conditionExpander(pathItem)};"
        is Union -> "@${conditionExpander(pathItem)};"
        is Statement -> transformSingleStmtToCppCompat(pathItem.stmt)
    }
}
    .postProcess()

/// produce raw info of every method, which contains the program path, path conditions
// and some statistics
fun slice(classPath: String): HashMap<String, List<Slicer>> {
    // init soot
    G.reset()
    Options.v().set_prepend_classpath(true)

    Options.v().set_src_prec(Options.src_prec_class)
    //Options.v().set_src_prec(Options.src_prec_apk);
    //Options.v().set_android_jars(android_jars);
    Options.v().set_process_dir(Collections.singletonList(classPath))
    Options.v().set_allow_phantom_refs(true)
    Scene.v().addBasicClass("java.lang.String", SootClass.BODIES)
    Scene.v().loadNecessaryClasses()
    val pathsOfFunc = HashMap<String, List<Slicer>>()

    PackManager.v().getPack("jtp").add(Transform("jtp.mySlicer", object : BodyTransformer() {
        override fun internalTransform(b: Body?, phaseName: String?, options: MutableMap<String, String>?) {
            val blockCFG = ExceptionalBlockGraph(b)
            var paths = constructPath(blockCFG)
//            val blocksWithStringOps = blockCFG.blocks.filter { hasStringOps(it) }
//            paths = paths.filterOutNotContainAny(blocksWithStringOps)
            val slicers = paths.map { Slicer(it) }
            if (b?.method?.name != null)
                pathsOfFunc[b.method?.name!!] = slicers
        }
    }))
    PackManager.v().runPacks()
    return pathsOfFunc
}