import soot.*
import soot.options.Options
import soot.toolkits.graph.ExceptionalBlockGraph
import java.util.*


fun main(args: Array<String>) {
    // args: [path]
//    File("C:\\Users\\yyzha\\Desktop\\elasticsearch\\server\\build")
    Options.v().set_prepend_classpath(true)

    Options.v().set_src_prec(Options.src_prec_class)
    //Options.v().set_src_prec(Options.src_prec_apk);
    //Options.v().set_android_jars(android_jars);
    Options.v().set_process_dir(Collections.singletonList("C:\\Users\\yyzha\\Desktop\\spring-boot\\spring-boot-3.2.1.jar"))
    Options.v().set_allow_phantom_refs(true)
    Scene.v().addBasicClass("java.lang.String", SootClass.BODIES)
    Scene.v().addBasicClass("java.util.Spliterator\$OfInt", SootClass.SIGNATURES)
    Scene.v().addBasicClass("java.util.function.DoubleBinaryOperator", SootClass.SIGNATURES)
    Scene.v().loadNecessaryClasses()
    Options.v().set_exclude(listOf("org.elasticsearch.index.translog.TranslogWriter",
        "org.elasticsearch.index.translog.Translog", "org.elasticsearch.indices.IndicesService",
        ""))
    val pathsOfFunc = HashMap<String, List<String>>()

    val classes = Scene.v().classes

    slice("C:\\Users\\yyzha\\Desktop\\elasticsearch\\server\\build")

    for (sc in classes) {
        if (listOf("java.", "sun.", "javax.", "android.", "androidx.").any { sc.name.contains(it) }) continue
        for (sm in sc.methods) {
            println(sm.retrieveActiveBody())
        }
    }

//    for (pathsOfFunc in slice(args[0])) { // write to .path files
//        val dir = File(args[0] + File.separator + "method-" + pathsOfFunc.key.replace("<", "《").replace(">", "》"))
//        if (dir.isDirectory() || dir.mkdir()) {
//            pathsOfFunc.value.forEachIndexed { index, path ->
//                File(dir, "$index.path").writeText(path)
//            }
//        }
//    }
}

/// produce a report of every method, which contains the program path, path conditions
// and some statistics
fun slice(classPath: String): Map<String, List<String>> {
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
    val pathsOfFunc = HashMap<String, List<String>>()

    PackManager.v().getPack("jtp").add(Transform("jtp.mySlicer", object : BodyTransformer() {
        override fun internalTransform(b: Body?, phaseName: String?, options: MutableMap<String, String>?) {
            val blockCFG = ExceptionalBlockGraph(b)
            var paths = constructPath(blockCFG)
//            val blocksWithStringOps = blockCFG.blocks.filter { hasStringOps(it) }
//            paths = paths.filterOutNotContainAny(blocksWithStringOps)
            val slicers = paths.map { Slicer(it) }
            if (b?.method?.name != null)
                pathsOfFunc[b.method?.name!!] = slicers.map { it.getStatistics() + "\n\n" +
                        it.getPath().joinToString("\n") }
        }
    }))
    PackManager.v().runPacks()
    return pathsOfFunc
}