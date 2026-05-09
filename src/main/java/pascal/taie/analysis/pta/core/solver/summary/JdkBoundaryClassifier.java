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
        if (matchesAny(className, extraIncludes)) {
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
}
