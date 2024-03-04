import soot.IntType
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

//<java.lang.String: void <clinit>()>
//<java.lang.String: void <init>()>
//<java.lang.String: void <init>(java.lang.String)>
//<java.lang.String: void <init>(char[])>
//<java.lang.String: void <init>(char[],int,int)>
//<java.lang.String: void <init>(int[],int,int)>
//<java.lang.String: void <init>(byte[],int,int,int)>
//<java.lang.String: void <init>(byte[],int)>
//<java.lang.String: void checkBounds(byte[],int,int)>
//<java.lang.String: void <init>(byte[],int,int,java.lang.String)>
//<java.lang.String: void <init>(byte[],int,int,java.nio.charset.Charset)>
//<java.lang.String: void <init>(byte[],java.lang.String)>
//<java.lang.String: void <init>(byte[],java.nio.charset.Charset)>
//<java.lang.String: void <init>(byte[],int,int)>
//<java.lang.String: void <init>(byte[])>
//<java.lang.String: void <init>(java.lang.StringBuffer)>
//<java.lang.String: void <init>(java.lang.StringBuilder)>
//<java.lang.String: void <init>(char[],boolean)>
//<java.lang.String: int length()>
//<java.lang.String: boolean isEmpty()>
//<java.lang.String: char charAt(int)>
//<java.lang.String: int codePointAt(int)>
//<java.lang.String: int codePointBefore(int)>
//<java.lang.String: int codePointCount(int,int)>
//<java.lang.String: int offsetByCodePoints(int,int)>
//<java.lang.String: void getChars(char[],int)>
//<java.lang.String: void getChars(int,int,char[],int)>
//<java.lang.String: void getBytes(int,int,byte[],int)>
//<java.lang.String: byte[] getBytes(java.lang.String)>
//<java.lang.String: byte[] getBytes(java.nio.charset.Charset)>
//<java.lang.String: byte[] getBytes()>
//<java.lang.String: boolean equals(java.lang.Object)>
//<java.lang.String: boolean contentEquals(java.lang.StringBuffer)>
//<java.lang.String: boolean nonSyncContentEquals(java.lang.AbstractStringBuilder)>
//<java.lang.String: boolean contentEquals(java.lang.CharSequence)>
//<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>
//<java.lang.String: int compareTo(java.lang.String)>
//<java.lang.String: int compareToIgnoreCase(java.lang.String)>
//<java.lang.String: boolean regionMatches(int,java.lang.String,int,int)>
//<java.lang.String: boolean regionMatches(boolean,int,java.lang.String,int,int)>
//<java.lang.String: boolean startsWith(java.lang.String,int)>
const val startsWith_sig = "<java.lang.String: boolean startsWith(java.lang.String)>"
//<java.lang.String: boolean endsWith(java.lang.String)>
//<java.lang.String: int hashCode()>
//<java.lang.String: int indexOf(int)>
//<java.lang.String: int indexOf(int,int)>
//<java.lang.String: int indexOfSupplementary(int,int)>
//<java.lang.String: int lastIndexOf(int)>
//<java.lang.String: int lastIndexOf(int,int)>
//<java.lang.String: int lastIndexOfSupplementary(int,int)>
//<java.lang.String: int indexOf(java.lang.String)>
//<java.lang.String: int indexOf(java.lang.String,int)>
//<java.lang.String: int indexOf(char[],int,int,java.lang.String,int)>
//<java.lang.String: int indexOf(char[],int,int,char[],int,int,int)>
//<java.lang.String: int lastIndexOf(java.lang.String)>
//<java.lang.String: int lastIndexOf(java.lang.String,int)>
//<java.lang.String: int lastIndexOf(char[],int,int,java.lang.String,int)>
//<java.lang.String: int lastIndexOf(char[],int,int,char[],int,int,int)>
const val substring1_sig = "<java.lang.String: java.lang.String substring(int)>"
const val substring2_sig = "<java.lang.String: java.lang.String substring(int,int)>"
//<java.lang.String: java.lang.CharSequence subSequence(int,int)>
//<java.lang.String: java.lang.String concat(java.lang.String)>
//<java.lang.String: java.lang.String replace(char,char)>
//<java.lang.String: boolean matches(java.lang.String)>
//<java.lang.String: boolean contains(java.lang.CharSequence)>
//<java.lang.String: java.lang.String replaceFirst(java.lang.String,java.lang.String)>
//<java.lang.String: java.lang.String replaceAll(java.lang.String,java.lang.String)>
//<java.lang.String: java.lang.String replace(java.lang.CharSequence,java.lang.CharSequence)>
//<java.lang.String: java.lang.String[] split(java.lang.String,int)>
//<java.lang.String: java.lang.String[] split(java.lang.String)>
//<java.lang.String: java.lang.String join(java.lang.CharSequence,java.lang.CharSequence[])>
//<java.lang.String: java.lang.String join(java.lang.CharSequence,java.lang.Iterable)>
//<java.lang.String: java.lang.String toLowerCase(java.util.Locale)>
//<java.lang.String: java.lang.String toLowerCase()>
//<java.lang.String: java.lang.String toUpperCase(java.util.Locale)>
//<java.lang.String: java.lang.String toUpperCase()>
//<java.lang.String: java.lang.String trim()>
//<java.lang.String: java.lang.String toString()>
//<java.lang.String: char[] toCharArray()>
//<java.lang.String: java.lang.String format(java.lang.String,java.lang.Object[])>
//<java.lang.String: java.lang.String format(java.util.Locale,java.lang.String,java.lang.Object[])>
//<java.lang.String: java.lang.String valueOf(java.lang.Object)>
//<java.lang.String: java.lang.String valueOf(char[])>
//<java.lang.String: java.lang.String valueOf(char[],int,int)>
//<java.lang.String: java.lang.String copyValueOf(char[],int,int)>
//<java.lang.String: java.lang.String copyValueOf(char[])>
//<java.lang.String: java.lang.String valueOf(boolean)>
//<java.lang.String: java.lang.String valueOf(char)>
//<java.lang.String: java.lang.String valueOf(int)>
//<java.lang.String: java.lang.String valueOf(long)>
//<java.lang.String: java.lang.String valueOf(float)>
//<java.lang.String: java.lang.String valueOf(double)>
//<java.lang.String: java.lang.String intern()>
//<java.lang.String: int compareTo(java.lang.Object)>

fun predefineFunctions(): Map<String, SExpression> {
    val funcs = mutableMapOf<String, SExpression>()

    funcs["startsWith/${startsWith_sig.hashCode()}"] = SList(
        "define-fun",
        "startsWith/${startsWith_sig.hashCode()}",
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

    funcs["substring/${substring2_sig.hashCode()}"] = SList(
        "define-fun",
        "substring/${substring2_sig.hashCode()}",
        SList(
            SList("s", Scene.v().getSootClass("java.lang.String")),
            SList("begin", "Int"),
            SList("end", "Int")
        ),
        Scene.v().getSootClass("java.lang.String"),
        SList(
            "str.substr",
            "s",
            "begin",
            SList(
                "-",
                "end",
                "begin"
            )
        )
    )

    funcs["substring/${substring1_sig.hashCode()}"] = SList(
        "define-fun",
        "substring/${substring1_sig.hashCode()}",
        SList(
            SList("s", Scene.v().getSootClass("java.lang.String")),
            SList("begin", "Int")
        ),
        Scene.v().getSootClass("java.lang.String"),
        SList(
            "str.substr",
            "s",
            "begin",
            SList(
                "-",
                SList(
                    "str.len",
                    "s"
                ),
                "begin"
            )
        )
    )

    return funcs
}

fun preconditionOfFunctions(name: String, args: List<String>): SList? {
    return when (name) {
        "substring/${substring2_sig.hashCode()}" -> {
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
        }
        else -> null
    }
}