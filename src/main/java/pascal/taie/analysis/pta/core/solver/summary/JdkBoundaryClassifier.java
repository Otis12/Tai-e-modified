/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import pascal.taie.language.classes.JMethod;

import java.util.List;
import java.util.Objects;

/**
 * Classifies JDK platform methods for the JDK summary-only boundary.
 */
public class JdkBoundaryClassifier {

    private static final List<String> DEFAULT_INCLUDES = List.of(
            "java.",
            "jdk.",
            "sun.",
            "com.sun.",
            "org.w3c.dom.",
            "org.xml.sax.",
            "org.ietf.jgss.",
            "javax.crypto.",
            "javax.net.",
            "javax.naming.",
            "javax.security.",
            "javax.sql.",
            "javax.xml.",
            "javax.management.",
            "javax.imageio.",
            "javax.sound.",
            "javax.swing.",
            "javax.tools.",
            "javax.script.");

    private static final List<String> DEFAULT_EXCLUDES = List.of(
            "javax.servlet.",
            "javax.websocket.",
            "javax.validation.",
            "javax.persistence.",
            "javax.transaction.",
            "org.springframework.",
            "org.mybatis.",
            "com.baomidou.",
            "com.alibaba.fastjson.",
            "com.fasterxml.jackson.",
            "org.apache.");

    private static final List<String> DEFAULT_INTERNAL_INCLUDES = List.of(
            "jdk.",
            "sun.",
            "com.sun.");

    private static final List<String> STRING_FAMILY_CLASSES = List.of(
            "java.lang.String",
            "java.lang.AbstractStringBuilder",
            "java.lang.StringBuilder",
            "java.lang.StringBuffer",
            "java.lang.CharSequence",
            "java.lang.StringLatin1",
            "java.lang.StringUTF16",
            "java.lang.StringCoding",
            "java.lang.StringConcatHelper",
            "java.lang.invoke.StringConcatFactory",
            "java.util.StringJoiner",
            "java.util.StringTokenizer",
            "java.util.Formatter",
            "java.util.regex.Pattern",
            "java.util.regex.Matcher",
            "java.util.Locale",
            "java.util.Objects");

    private static final List<String> CONTAINER_PREFIXES = List.of(
            "java.util.Collection",
            "java.util.List",
            "java.util.ArrayList",
            "java.util.LinkedList",
            "java.util.Set",
            "java.util.HashSet",
            "java.util.LinkedHashSet",
            "java.util.Map",
            "java.util.HashMap",
            "java.util.LinkedHashMap",
            "java.util.TreeMap",
            "java.util.Iterator",
            "java.util.Enumeration",
            "java.util.Collections");

    private final List<String> extraIncludes;

    private final List<String> extraExcludes;

    public JdkBoundaryClassifier() {
        this(List.of(), List.of());
    }

    public JdkBoundaryClassifier(List<String> extraIncludes,
                                 List<String> extraExcludes) {
        this.extraIncludes = normalize(extraIncludes);
        this.extraExcludes = normalize(extraExcludes);
    }

    /**
     * @return true if {@code className} is covered by the JDK platform boundary.
     */
    public boolean isJdkPlatformClass(String className) {
        Objects.requireNonNull(className, "className");
        if (matchesOverrideInclude(className, extraIncludes)) {
            return true;
        }
        if (matchesAny(className, extraExcludes)
                || matchesAny(className, DEFAULT_EXCLUDES)) {
            return false;
        }
        return matchesAny(className, DEFAULT_INCLUDES);
    }

    /**
     * @return true if {@code method}'s declaring class is covered by the JDK
     * platform boundary.
     */
    public boolean isJdkPlatformMethod(JMethod method) {
        Objects.requireNonNull(method, "method");
        return isJdkPlatformClass(method.getDeclaringClass().getName());
    }

    /**
     * @return true if {@code className} is a JDK internal class.
     */
    public boolean isJdkInternalClass(String className) {
        Objects.requireNonNull(className, "className");
        return isJdkPlatformClass(className)
                && matchesAny(className, DEFAULT_INTERNAL_INCLUDES);
    }

    /**
     * @return true if {@code method}'s declaring class is a JDK internal class.
     */
    public boolean isJdkInternalMethod(JMethod method) {
        Objects.requireNonNull(method, "method");
        return isJdkInternalClass(method.getDeclaringClass().getName());
    }

    /**
     * @return true if {@code className} is one of the String-family classes
     * that are useful for selected JDK boundary experiments.
     */
    public boolean isStringFamilyClass(String className) {
        Objects.requireNonNull(className, "className");
        return STRING_FAMILY_CLASSES.stream()
                .anyMatch(prefix -> className.equals(prefix)
                        || className.startsWith(prefix + "$"));
    }

    /**
     * @return true if {@code method}'s declaring class is String-family.
     */
    public boolean isStringFamilyMethod(JMethod method) {
        Objects.requireNonNull(method, "method");
        return isStringFamilyClass(method.getDeclaringClass().getName());
    }

    /**
     * @return true if {@code className} is a common JDK container class.
     */
    public boolean isJdkContainerClass(String className) {
        Objects.requireNonNull(className, "className");
        return isJdkPlatformClass(className)
                && matchesAny(className, CONTAINER_PREFIXES);
    }

    /**
     * @return true if {@code method}'s declaring class is a common JDK
     * container class.
     */
    public boolean isJdkContainerMethod(JMethod method) {
        Objects.requireNonNull(method, "method");
        return isJdkContainerClass(method.getDeclaringClass().getName());
    }

    private static List<String> normalize(List<String> prefixes) {
        return Objects.requireNonNull(prefixes, "prefixes")
                .stream()
                .filter(Objects::nonNull)
                .map(String::trim)
                .filter(prefix -> !prefix.isEmpty())
                .toList();
    }

    private static boolean matchesAny(String className, List<String> prefixes) {
        return prefixes.stream().anyMatch(className::startsWith);
    }

    private static boolean matchesOverrideInclude(String className,
                                                  List<String> includes) {
        return includes.stream().anyMatch(include -> {
            if (include.endsWith(".")) {
                return className.startsWith(include);
            }
            return className.equals(include) || className.startsWith(include + "$");
        });
    }
}
