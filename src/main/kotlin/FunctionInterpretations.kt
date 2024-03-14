import soot.*

sealed interface SExpression {
    fun toStringWithTransformedName(t: (Any) -> String): String
}

class Atom(private val value: Any): SExpression {
    override fun toString(): String {
        return value.toString()
    }

    override fun toStringWithTransformedName(t: (Any) -> String): String {
        return if (value is String) value else t(value)
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

class TopLevel(private vararg val commands: SExpression): SExpression {
    override fun toString(): String {
        return commands.joinToString("\n")
    }

    override fun toStringWithTransformedName(t: (Any) -> String): String {
        return commands.joinToString("\n") { it.toStringWithTransformedName(t) }
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
const val length_sig = "<java.lang.String: int length()>"
const val isEmpty_sig = "<java.lang.String: boolean isEmpty()>"
const val charAt_sig = "<java.lang.String: char charAt(int)>"
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
const val startsWith0_sig = "<java.lang.String: boolean startsWith(java.lang.String,int)>"
const val startsWith_sig = "<java.lang.String: boolean startsWith(java.lang.String)>"
const val endsWith_sig = "<java.lang.String: boolean endsWith(java.lang.String)>"
//<java.lang.String: int hashCode()>
const val indexOf1_sig = "<java.lang.String: int indexOf(int)>"
const val indexOf2_sig = "<java.lang.String: int indexOf(int,int)>"
//<java.lang.String: int indexOfSupplementary(int,int)>
//<java.lang.String: int lastIndexOf(int)>
//<java.lang.String: int lastIndexOf(int,int)>
//<java.lang.String: int lastIndexOfSupplementary(int,int)>
const val indexOf3_sig = "<java.lang.String: int indexOf(java.lang.String)>"
const val indexOf4_sig = "<java.lang.String: int indexOf(java.lang.String,int)>"
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
const val trim_sig = "<java.lang.String: java.lang.String trim()>"
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


const val next_sig = "<java.util.Iterator: java.lang.Object next()>"

fun predefineFunctions(functions: MutableMap<String, Pair<List<Any>, Any>>): List<SExpression> {
    fun listOfCasts(): Map<String, SExpression> {
        val funcs = mutableMapOf<String, SExpression>()

        return funcs
    }

    fun listOfStringApis(): Map<String, SExpression> {
        val funcs = mutableMapOf<String, SExpression>()

        funcs["length/${length_sig.hashCode()}"] = SList(
            "define-fun",
            "length/${length_sig.hashCode()}",
            SList(
                SList("s", "String")
            ),
            "Int",
            SList("str.len", "s")
        )

        funcs["charAt/${charAt_sig.hashCode()}"] = SList(
            "define-fun",
            "charAt/${charAt_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("index", "Int")
            ),
            "Int",
            SList("str.at", "s", "index")
        )

        funcs["isEmpty/${isEmpty_sig.hashCode()}"] = SList(
            "define-fun",
            "isEmpty/${isEmpty_sig.hashCode()}",
            SList(
                SList("s", "String")
            ),
            "Int",
            SList(
                "=",
                SList("str.len", "s"),
                0
            )
        )

        funcs["startsWith/${startsWith_sig.hashCode()}"] = SList(
            "define-fun",
            "startsWith/${startsWith_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("prefix", "String")
            ),
            "Bool",
            SList(
                "str.prefixof",
                "prefix",
                "s"
            )
        )

        funcs["startsWith/${startsWith0_sig.hashCode()}"] = SList(
            "define-fun",
            "startsWith/${startsWith0_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("prefix", "String"),
                SList("toffset", "Int")
            ),
            "Bool",
            SList(
                "and",
                SList(
                    ">=",
                    "toffset",
                    "0"
                ),
                SList(
                    ">=",
                    SList(
                        "str.len",
                        "s"
                    ),
                    "toffset"
                ),
                SList(
                    "str.prefixof",
                    "prefix",
                    SList(
                        "str.substr",
                        "s",
                        "toffset",
                        SList(
                            "-",
                            SList(
                                "str.len",
                                "s"
                            ),
                            "toffset"
                        )
                    )
                )
            )
        )

        funcs["endsWith/${endsWith_sig.hashCode()}"] = SList(
            "define-fun",
            "endsWith/${endsWith_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("suffix", "String")
            ),
            "Bool",
            SList(
                "str.suffixof",
                "suffix",
                "s"
            )
        )

        funcs["indexOf/${indexOf1_sig.hashCode()}"] = SList(
            "define-fun",
            "indexOf/${indexOf1_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("c", "Int")
            ),
            "Int",
            SList(
                "str.indexof",
                "s",
                SList(
                    "str.from_code",
                    "c"
                ),
                "0"
            )
        )

        funcs["indexOf/${indexOf2_sig.hashCode()}"] = SList(
            "define-fun",
            "indexOf/${indexOf2_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("c", "Int"),
                SList("fromIndex", "Int")
            ),
            "Int",
            SList(
                "str.indexof",
                "s",
                SList(
                    "str.from_code",
                    "c"
                ),
                "fromIndex"
            )
        )

        funcs["indexOf/${indexOf3_sig.hashCode()}"] = SList(
            "define-fun",
            "indexOf/${indexOf3_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("subs", "String")
            ),
            "Int",
            SList(
                "str.indexof",
                "s",
                "subs",
                "0"
            )
        )

        funcs["indexOf/${indexOf4_sig.hashCode()}"] = SList(
            "define-fun",
            "indexOf/${indexOf4_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("subs", "String"),
                SList("fromIndex", "Int")
            ),
            "Int",
            SList(
                "str.indexof",
                "s",
                "subs",
                "fromIndex"
            )
        )

        funcs["substring/${substring2_sig.hashCode()}"] = SList(
            "define-fun",
            "substring/${substring2_sig.hashCode()}",
            SList(
                SList("s", "String"),
                SList("begin", "Int"),
                SList("end", "Int")
            ),
            "String",
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
                SList("s", "String"),
                SList("begin", "Int")
            ),
            "String",
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

        // refer to but later changed from:
        // https://github.com/yanxx297/jpf-symbc/blob/9fa4eff5d25b5d29919a64432422f912dff0a609/doc/trim.smt#L4
        // or https://github.com/yanxx297/jpf-symbc/blob/9fa4eff5d25b5d29919a64432422f912dff0a609/src/main/edu/ucsb/cs/vlab/translate/smtlib/from/z3str3/Z3Translator.java#L265
        // to approximate standard java:
        // https://github.com/openjdk/jdk/blob/master/src/java.base/share/classes/java/lang/String.java
        // https://github.com/openjdk/jdk/blob/master/src/java.base/share/classes/java/lang/StringUTF16.java#L75
        // https://github.com/openjdk/jdk/blob/master/src/java.base/share/classes/java/lang/StringLatin1.java#L856
        funcs["trim/${trim_sig.hashCode()}"] = TopLevel(
            SList(
                "define-fun",
                "is-whitespace",
                SList(
                    SList(
                        "char",
                        "String"
                    )
                ),
                "Bool",
                SList(
                    "<",
                    SList(
                        "str.to_code",
                        "char"
                    ),
                    "33" // ASCII space
                )
            ),

            SList(
                "define-fun-rec",
                "trim-left",  // TODO: temporarily only deal with ASCII characters
                // also, use the recursive version might cause performance issues
                SList(
                    SList(
                        "s",
                        "String"
                    )
                ),
                "String",
                SList(
                    "ite",
                    SList(
                        "=",
                        "s",
                        "\"\""
                    ),
                    "\"\"",
                    SList(
                        "ite",
                        SList(
                            "is-whitespace",
                            SList(
                                "str.substr",
                                "s",
                                "0",
                                "1"
                            )
                        ),
                        SList(
                            "trim-left",
                            SList(
                                "str.substr",
                                "s",
                                "1",
                                SList(
                                    "-",
                                    SList(
                                        "str.len",
                                        "s"
                                    ),
                                    "1"
                                )
                            )
                        ),
                        "s"
                    )
                )
            ),
            SList(
                "define-fun-rec",
                "trim-right",
                SList(
                    SList(
                        "s",
                        "String"
                    )
                ),
                "String",
                SList(
                    "ite",
                    SList(
                        "=",
                        "s",
                        "\"\""
                    ),
                    "\"\"",
                    SList(
                        "ite",
                        SList(
                            "is-whitespace",
                            SList(
                                "str.substr",
                                "s",
                                SList(
                                    "-",
                                    SList(
                                        "str.len",
                                        "s"
                                    ),
                                    "1"
                                ),
                                "1"
                            )
                        ),
                        SList(
                            "trim-right",
                            SList(
                                "str.substr",
                                "s",
                                "0",
                                SList(
                                    "-",
                                    SList(
                                        "str.len",
                                        "s"
                                    ),
                                    "1"
                                )
                            )
                        ),
                        "s"
                    )
                )
            ),
            SList(
                "define-fun",
                "trim/${trim_sig.hashCode()}",
                SList(
                    SList(
                        "s",
                        "String"
                    )
                ),
                "String",
                SList(
                    "trim-right",
                    SList(
                        "trim-left",
                        "s"
                    )
                )
            )
        )

        return funcs
    }

    val funcs = listOfStringApis()
    // only the used functions of above (as well as their helpers) are included
    return functions.map { (name, types) ->
        funcs[name] ?: SList(
            "declare-fun",
            name,
            SList(
                *types.first.toTypedArray()
            ),
            types.second
        )
    }
}

fun preconditionOfFunctions(name: String, args: List<String>): SExpression? {
    return when (name) {
        "substring/${substring2_sig.hashCode()}" -> {
            val s = args[0]
            val begin = args[1]
            val end = args[2]
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
        }
        "substring/${substring1_sig.hashCode()}" -> {
            val s = args[0]
            val begin = args[1]
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
                    begin
                )
            )
        }
        "charAt/${charAt_sig.hashCode()}" -> {
            val s = args[0]
            val index = args[1]
            SList(
                "and",
                SList(
                    ">",
                    SList(
                        "str.len",
                        s
                    ),
                    index
                ),
                SList(
                    "<=",
                    "0",
                    s
                )
            )
        }
        else -> null
    }
}

// TODO: remove soot dependency in this file at best effort
// post condition might produce new constants as some of the objects might be re-assigned, which cannot be predicted,
// so the function needs to know how to produce one by applying `getNewName` to one of the args
inline fun postconditionOfFunctions(funcName: String, args: List<Value>, getName: (Value) -> String, addReDeclarationOf: (Value) -> String): SExpression? {
    return when (funcName) {
        "next/${next_sig.hashCode()}" -> {
            val iteratorObject = args[0]
            val iteratorName = getName(iteratorObject)
            TopLevel( // TODO: fix the assertions
                Atom(addReDeclarationOf(iteratorObject)), // work around, use `transformDefine()` to add re-declaration
                                                // for consistency and modularity, so the product is a string like
                                                // "(declare-const A B)", and can be directly inserted into the TopLevel
                                                // without SList's adding parentheses
//                SList(
//                    "assert",
//                    SList()
//                )
            )
        }

        else -> null
    }
}

fun isNotSameTypeButCastable(subType: Type, topType: Type, strict: Boolean = false): Boolean =
    (subType is RefType && topType is RefType && subType.merge(topType, Scene.v()) != subType) || // true subtype
            (topType == RefType.v("java.lang.String") && !strict) || // xxx.toString() method
            (topType is ArrayType && subType is ArrayType && isNotSameTypeButCastable(subType.baseType, topType.baseType)) || // array of subtype
            (topType == RefType.v("java.util.Collection") && subType.toString().contains("(List|Array|Map)".toRegex())) // collections
