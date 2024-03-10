import soot.*
import soot.options.Options
import soot.toolkits.graph.ExceptionalBlockGraph
import java.io.File
import java.util.*


fun main(args: Array<String>) {

    for (pathsOfFunc in slice(args[0])) { // write to .path files
        val dir = File("paths", "method-" + pathsOfFunc.key.replace("<", "《").replace(">", "》"))
        if (dir.isDirectory() || dir.mkdir()) {
            pathsOfFunc.value.forEachIndexed { index, slicer ->
                val (normal, deviants) = compatibleSmtlibTransformer(slicer)
                File(dir, "$index.path").writeText(normal)
                deviants.forEachIndexed { num, text ->
                    File(dir, "$index-deviant-$num.path").writeText(text)
                }
            }
        }
    }
}

fun compatibleSmtlibTransformer(slicer: Slicer) = slicer.smtExpand()

/// produce raw info of every method, which contains the program path, path conditions
// and some statistics
fun slice(classPath: String): HashMap<String, List<Slicer>> {
    // init soot
    G.reset()
    Options.v().set_prepend_classpath(true)

    Options.v().set_src_prec(Options.src_prec_class)
    //Options.v().set_output_format(Options.output_format_shimple)
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
            if (b?.method?.signature != null)
                pathsOfFunc["${b.method.declaringClass.name}__${b.method.name}__${b.method?.signature.hashCode()}"] = slicers
        }
    }))
    PackManager.v().runPacks()
    return pathsOfFunc
}