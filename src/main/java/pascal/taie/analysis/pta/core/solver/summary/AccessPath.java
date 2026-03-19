/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.language.classes.JField;

import java.util.List;
import java.util.Objects;

/**
 * Represents an access path in summary rules, such as "base.field" or "0[*]".
 *
 * <p>Examples:
 * <ul>
 *   <li>{@code "base"}           - base=-1, elements=[]</li>
 *   <li>{@code "result"}         - base=-2, elements=[]</li>
 *   <li>{@code "0"}              - base=0,  elements=[]</li>
 *   <li>{@code "base.name"}      - base=-1, elements=[FieldAccess(name)]</li>
 *   <li>{@code "0.data"}         - base=0,  elements=[FieldAccess(data)]</li>
 *   <li>{@code "base[*]"}        - base=-1, elements=[ArrayAccess]</li>
 *   <li>{@code "0[*]"}           - base=0,  elements=[ArrayAccess]</li>
 * </ul>
 *
 * <p>The {@code elements} list is designed to support multi-level access paths
 * in the future (e.g., "base.field1.field2"), but currently only single-level
 * access is implemented.
 */
public record AccessPath(
        int base,                      // -1=this, -2=result, 0..n=parameter index
        List<PathElement> elements     // access chain (currently 0 or 1 element)
) {

    /**
     * Sealed interface for path elements in an access path.
     */
    public sealed interface PathElement permits FieldAccess, ArrayAccess {}

    /**
     * Represents field access (e.g., ".name" in "base.name").
     */
    public record FieldAccess(JField field) implements PathElement {
        @Override
        public String toString() {
            return "." + field.getName();
        }
    }

    /**
     * Represents array element access (e.g., "[*]" in "base[*]").
     */
    public record ArrayAccess() implements PathElement {
        public static final String ARRAY_SUFFIX = "[*]";

        @Override
        public String toString() {
            return ARRAY_SUFFIX;
        }
    }

    // ==================== Factory Methods ====================

    /**
     * Creates an access path for a simple variable (base, result, or parameter).
     *
     * @param index the variable index (-1=base, -2=result, 0..n=parameter)
     * @return an access path with no field/array access
     */
    public static AccessPath ofVar(int index) {
        return new AccessPath(index, List.of());
    }

    /**
     * Creates an access path for a single field access.
     *
     * @param index the base variable index
     * @param field the field to access
     * @return an access path like "base.field"
     */
    public static AccessPath ofField(int index, JField field) {
        Objects.requireNonNull(field, "field cannot be null");
        return new AccessPath(index, List.of(new FieldAccess(field)));
    }

    /**
     * Creates an access path for array element access.
     *
     * @param index the base variable index
     * @return an access path like "base[*]"
     */
    public static AccessPath ofArray(int index) {
        return new AccessPath(index, List.of(new ArrayAccess()));
    }

    // ==================== Query Methods ====================

    /**
     * @return true if this is a simple variable access (no field/array)
     */
    public boolean isSimpleVar() {
        return elements.isEmpty();
    }

    /**
     * @return true if this access path involves field access
     */
    public boolean hasFieldAccess() {
        return !elements.isEmpty() && elements.get(0) instanceof FieldAccess;
    }

    /**
     * @return true if this access path involves array access
     */
    public boolean hasArrayAccess() {
        return !elements.isEmpty() && elements.get(0) instanceof ArrayAccess;
    }

    /**
     * Gets the first field in the access path.
     *
     * @return the field, or null if not a field access
     */
    public JField getFirstField() {
        if (!elements.isEmpty() && elements.get(0) instanceof FieldAccess fa) {
            return fa.field();
        }
        return null;
    }

    /**
     * @return true if this access path refers to the base (this) variable
     */
    public boolean isBase() {
        return base == InvokeUtils.BASE;
    }

    /**
     * @return true if this access path refers to the result variable
     */
    public boolean isResult() {
        return base == InvokeUtils.RESULT;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(InvokeUtils.toString(base));
        for (PathElement elem : elements) {
            sb.append(elem.toString());
        }
        return sb.toString();
    }
}
