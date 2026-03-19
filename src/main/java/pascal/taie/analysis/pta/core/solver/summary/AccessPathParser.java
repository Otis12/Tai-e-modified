/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;

import javax.annotation.Nullable;

/**
 * Parser for converting string representations to {@link AccessPath} objects.
 *
 * <p>Supported formats:
 * <ul>
 *   <li>{@code "base"} - receiver object (this)</li>
 *   <li>{@code "result"} - return value</li>
 *   <li>{@code "0", "1", ...} - parameter by index</li>
 *   <li>{@code "base.fieldName"} - field of receiver</li>
 *   <li>{@code "0.fieldName"} - field of parameter</li>
 *   <li>{@code "base[*]"} - array elements of receiver</li>
 *   <li>{@code "0[*]"} - array elements of parameter</li>
 * </ul>
 */
public class AccessPathParser {

    private static final Logger logger = LogManager.getLogger(AccessPathParser.class);

    public AccessPathParser(ClassHierarchy hierarchy) {
        // ClassHierarchy is used indirectly via JClass.getSuperClass()
    }

    /**
     * Parses a string to an AccessPath.
     *
     * @param method the method context (used to resolve parameter types and fields)
     * @param text   the string representation (e.g., "base.name", "0", "result")
     * @return the parsed AccessPath, or null if parsing fails
     */
    @Nullable
    public AccessPath parse(JMethod method, String text) {
        if (text == null || text.isBlank()) {
            logger.warn("Empty access path for method {}", method);
            return null;
        }

        text = text.trim();

        // Check for array access suffix [*]
        if (text.endsWith(AccessPath.ArrayAccess.ARRAY_SUFFIX)) {
            String baseStr = text.substring(0,
                    text.length() - AccessPath.ArrayAccess.ARRAY_SUFFIX.length());
            int baseIndex = parseBaseIndex(baseStr);
            if (baseIndex == Integer.MIN_VALUE) {
                logger.warn("Invalid base index '{}' in access path '{}' for method {}",
                        baseStr, text, method);
                return null;
            }
            return AccessPath.ofArray(baseIndex);
        }

        // Check for field access (contains '.')
        int dotIndex = text.indexOf('.');
        if (dotIndex > 0) {
            String baseStr = text.substring(0, dotIndex);
            String fieldName = text.substring(dotIndex + 1);

            int baseIndex = parseBaseIndex(baseStr);
            if (baseIndex == Integer.MIN_VALUE) {
                logger.warn("Invalid base index '{}' in access path '{}' for method {}",
                        baseStr, text, method);
                return null;
            }

            // Resolve the field
            JField field = resolveField(method, baseIndex, fieldName);
            if (field == null) {
                logger.warn("Cannot resolve field '{}' in access path '{}' for method {}",
                        fieldName, text, method);
                return null;
            }
            return AccessPath.ofField(baseIndex, field);
        }

        // Simple variable access (base, result, or parameter index)
        int baseIndex = parseBaseIndex(text);
        if (baseIndex == Integer.MIN_VALUE) {
            logger.warn("Invalid access path '{}' for method {}", text, method);
            return null;
        }
        return AccessPath.ofVar(baseIndex);
    }

    /**
     * Parses base index from string.
     *
     * @return the index, or Integer.MIN_VALUE if invalid
     */
    private int parseBaseIndex(String s) {
        try {
            return InvokeUtils.toInt(s);
        } catch (NumberFormatException e) {
            return Integer.MIN_VALUE;
        }
    }

    /**
     * Resolves a field name in the context of a method and base index.
     *
     * @param method    the method containing the access
     * @param baseIndex the base variable index
     * @param fieldName the field name to resolve
     * @return the resolved JField, or null if not found
     */
    @Nullable
    private JField resolveField(JMethod method, int baseIndex, String fieldName) {
        Type baseType = getBaseType(method, baseIndex);
        if (baseType == null) {
            return null;
        }

        if (baseType instanceof ClassType classType) {
            JClass clazz = classType.getJClass();
            // Search for field in class hierarchy
            return findFieldInHierarchy(clazz, fieldName);
        }

        return null;
    }

    /**
     * Gets the type of the base variable.
     */
    @Nullable
    private Type getBaseType(JMethod method, int baseIndex) {
        return switch (baseIndex) {
            case InvokeUtils.BASE -> {
                // 'this' - the declaring class type
                if (method.isStatic()) {
                    logger.warn("Cannot use 'base' for static method {}", method);
                    yield null;
                }
                yield method.getDeclaringClass().getType();
            }
            case InvokeUtils.RESULT -> {
                // return type
                yield method.getReturnType();
            }
            default -> {
                // parameter
                if (baseIndex < 0 || baseIndex >= method.getParamCount()) {
                    logger.warn("Parameter index {} out of bounds for method {}",
                            baseIndex, method);
                    yield null;
                }
                yield method.getParamType(baseIndex);
            }
        };
    }

    /**
     * Searches for a field in the class hierarchy.
     */
    @Nullable
    private JField findFieldInHierarchy(JClass clazz, String fieldName) {
        JClass current = clazz;
        while (current != null) {
            JField field = current.getDeclaredField(fieldName);
            if (field != null) {
                return field;
            }
            current = current.getSuperClass();
        }
        return null;
    }
}
