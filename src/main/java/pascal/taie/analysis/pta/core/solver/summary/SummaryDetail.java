/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import pascal.taie.language.classes.JMethod;

/**
 * Represents a summary rule for a method, specifying how points-to information
 * should be propagated from source to target.
 *
 * <p>When a summarized method is called, instead of analyzing the method body,
 * the solver retrieves the points-to set of the source access path and propagates
 * it to the target access path.
 *
 * <p>Examples:
 * <pre>
 * // String getName() { return this.name; }
 * // source = base.name, target = result
 * new SummaryDetail(method, "base.name", "result", sourcePath, targetPath)
 *
 * // void setName(String s) { this.name = s; }
 * // source = 0, target = base.name
 * new SummaryDetail(method, "0", "base.name", sourcePath, targetPath)
 *
 * // String identity(String s) { return s; }
 * // source = 0, target = result
 * new SummaryDetail(method, "0", "result", sourcePath, targetPath)
 *
 * // List.add(Object) - container add
 * // source = 0, target = base[*]
 * new SummaryDetail(method, "0", "base[*]", sourcePath, targetPath)
 *
 * // List.get(int) - container get
 * // source = base[*], target = result
 * new SummaryDetail(method, "base[*]", "result", sourcePath, targetPath)
 * </pre>
 *
 * @param method    the method this summary applies to
 * @param sourceStr original string representation of source (for debugging)
 * @param targetStr original string representation of target (for debugging)
 * @param source    parsed source access path
 * @param target    parsed target access path
 */
public record SummaryDetail(
        JMethod method,
        String sourceStr,
        String targetStr,
        AccessPath source,
        AccessPath target
) {

    /**
     * Creates a SummaryDetail with parsed AccessPaths.
     */
    public static SummaryDetail of(JMethod method, String sourceStr, String targetStr,
                                   AccessPath source, AccessPath target) {
        return new SummaryDetail(method, sourceStr, targetStr, source, target);
    }

    @Override
    public String toString() {
        return method.getSignature() + ": " + sourceStr + " -> " + targetStr;
    }
}
