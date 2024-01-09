import soot.jimple.AssignStmt
import soot.jimple.IfStmt
import soot.jimple.InvokeExpr
import soot.jimple.Stmt
import soot.jimple.internal.JIdentityStmt
import soot.jimple.internal.JReturnStmt
import java.io.File

@JvmOverloads
fun<T> Collection<List<T>>.displayCollectionToFile(header: String, logFilePath: String = ".\\path.txt") {
    var content = header + "\n";
    content += this.mapIndexed { index, path ->
        "\n*****************\n\n" +
        "path $index\n" +
        path.asReversed().joinToString { "$it\n" } +
        "\n*****************\n\n"
    }.joinToString()
    displayToFile(content, logFilePath)
}

fun<T> List<T>.displaySummary() {
    this.forEach { print(" " + it.hashCode()) }
    println("")
}

//
//fun<T> List<List<T>>.displaySummary() {
//    this.forEachIndexed { index, path ->
//        println("path $index")
//        path.forEach { print(" " + it.hashCode()) }
//    }
//}

fun<T> Collection<List<T>>.display() {
    this.forEachIndexed { index, path ->
        println("path $index")
        path.asReversed().forEach { print(" " + it.toString()) }
    }
}

@JvmOverloads
fun<T, E> Collection<List<T>>.displayZippedToFile(header: String, tags: List<List<E>>, logFilePath: String = ".\\path.txt") {
    var content = header + "\n"
    content += this.zip(tags).mapIndexed { index, (path, tag) ->
            "\n*****************\n\n" +
            "path $index\n" +
            path.asReversed().zipWithNext().zip(tag).joinToString { "\n$it\n\n" } +

            "\n\nthen begins the complete path and constraint chain\n\n\n" +
            path.asReversed() + "\n" +
            tag + "\n" +

            "\n*****************\n"
        }.joinToString()
    displayToFile(content, logFilePath)
}



fun inlineStringOps(expr: InvokeExpr): String {
//    Scene.v().loadClassAndSupport("java.lang.String")
//    val stringClass = Scene.v().getSootClass("java.lang.String")
    return if (expr.methodRef.declaringClass.name.contains("java.lang.String")) {
        with (expr.methodRef.declaringClass.name) {
            when {
                else -> expr.method.toString() + "(${expr.args})"
            }
        }
    } else {
        expr.method.toString() + "(${expr.args})"
    }
}

fun transformSingleStmtToCppCompat(stmt: Stmt): String {
    return when (stmt) {
        is JIdentityStmt -> stmt.rightOp.type.toString() /* ThisRef / ParameterRef */ + " " + stmt.leftOp + ";"
        is AssignStmt -> stmt.rightOp.let { if (it is InvokeExpr) inlineStringOps(it) else it }.let {
            stmt.leftOp.type.toString() + " " + stmt.leftOp.toString() + " = " + it + ";"
        }
        is IfStmt -> ""
        is JReturnStmt -> "$stmt;"
        else -> stmt.toString() + stmt.javaClass.typeName
    }
}

fun transformSingleCondToCppCompat(cond: Condition): String {
    return when (cond) {
        is Single -> "@(" + cond.cond + ");"
        is Negate -> "@!(" + cond.cond + ");"
        is Nop -> ""
        else -> cond.toString()
    }
}

fun String.postProcess(): String { // trim the $, <, >, and other symbols
    return this.replace("$", "___")
}

fun displayToFile(content: String, logFilePath: String = ".\\path.txt") {
    File(logFilePath).printWriter().use { out ->
        out.println(content.postProcess())
    }
}

fun emitCppCompatPath(slicers: List<Slicer>) {
    slicers.forEach { slicer ->
        val conditionPlusNull = slicer.getPathConstraints() + Nop()
        displayToFile(slicer.programPath.asReversed().zip(conditionPlusNull).joinToString("\n") { (bl, c) ->
            bl.joinToString("\n") { transformSingleStmtToCppCompat(it as Stmt) } + "\n" +
                    transformSingleCondToCppCompat(c)
        } + slicer.programPath.asReversed())
    }
}


//fun getPathConstraints(paths: Collection<List<Block>>): Collection<List<Condition>> {
//    return paths.map {
//        it.asReversed().zipWithNext().map { (prev, next) ->
//            prev.tail.let { jumpStatement ->
//                if (jumpStatement is IfStmt && jumpStatement.fallsThrough())
//                    if (jumpStatement.target == next.head)
//                        Single(jumpStatement.condition)
//                    else Negate(Single(jumpStatement.condition))
//                else if (jumpStatement is GotoStmt)
//                    Nop()
//                else Nop("DEBUG: $jumpStatement")
//            }
//        }
//    }
//}