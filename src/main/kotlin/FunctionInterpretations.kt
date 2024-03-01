import soot.Scene

sealed interface SExpression {
    fun toStringWithTransformedName(t: (Any) -> String): String
}

class Atom(private val value: Any): SExpression {
    override fun toString(): String {
        return value.toString()
    }

    override fun toStringWithTransformedName(t: (Any) -> String): String {
        return t(value)
    }
}
class SList(vararg exps: Any): SExpression {
    private val value = exps.toList().map { if (it is SExpression) it else Atom(it) }
    override fun toString(): String {
        return "(${value.joinToString(" ")})"
    }

    override fun toStringWithTransformedName(t: (Any) -> String): String {
        return "(${value.joinToString(" ") { it.toStringWithTransformedName(t) }})"
    }
}

fun predefineFunctions(): Map<String, SExpression> {
    val funcs = mutableMapOf<String, SExpression>()

    funcs["startsWith"] = SList(
        "define-fun",
        "startsWith",
        SList(
            SList("s", Scene.v().getSootClass("java.lang.String")),
            SList("prefix", Scene.v().getSootClass("java.lang.String"))
        ),
        "Bool",
        SList(
            "str.prefixof",
            "prefix",
            "s"
        )
    )

    return funcs
}

fun preconditionOfFunctions(name: String, args: List<String>): SList? {
    return when (name) {
        "substring" -> if (args.size == 3) {
            val s = args[0]
            val begin = args[1]
            val end = args[2]
            SList(
                "assert",
                SList(
                    "and",
                    SList(
                        ">=",
                        begin,
                        "0"
                    ),
                    SList(
                        ">=",
                        SList(
                            "str.len",
                            s
                        ),
                        end
                    ),
                    SList(
                        ">=",
                        end,
                        begin
                    )
                )
            )
        } else { null }
        else -> null
    }
}