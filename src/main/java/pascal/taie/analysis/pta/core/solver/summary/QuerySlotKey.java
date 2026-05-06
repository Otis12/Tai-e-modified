/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.StringLiteral;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;

import java.util.Objects;

/**
 * Lightweight key abstraction for query-builder slot writes.
 *
 * <p>The current implementation only needs a conservative key identity for
 * connectivity-style propagation. Unknown keys intentionally collapse to the
 * wildcard bucket rather than blocking the flow.
 */
public final class QuerySlotKey {

    private static final String WILDCARD = "*";

    public enum Kind {
        STRING_KEY,
        STRING_ARG,
        LAMBDA_KEY,
        DERIVED_KEY
    }

    public record Resolved(String slotId, boolean precise) {
    }

    private final Kind kind;

    private final String value;

    private final int argIndex;

    private QuerySlotKey(Kind kind, String value, int argIndex) {
        this.kind = Objects.requireNonNull(kind);
        this.value = value;
        this.argIndex = argIndex;
    }

    public static QuerySlotKey string(String value) {
        return new QuerySlotKey(Kind.STRING_KEY, Objects.requireNonNull(value), -1);
    }

    public static QuerySlotKey stringArg(int argIndex) {
        return new QuerySlotKey(Kind.STRING_ARG, "", argIndex);
    }

    public static QuerySlotKey lambdaArg(int argIndex) {
        return new QuerySlotKey(Kind.LAMBDA_KEY, "", argIndex);
    }

    public static QuerySlotKey derived(String value) {
        return new QuerySlotKey(Kind.DERIVED_KEY, Objects.requireNonNull(value), -1);
    }

    public Kind kind() {
        return kind;
    }

    public Resolved resolve(Invoke callSite) {
        return switch (kind) {
            case STRING_KEY, DERIVED_KEY -> new Resolved(value, true);
            case STRING_ARG -> resolveStringArgument(callSite);
            case LAMBDA_KEY -> resolveLambdaArgument(callSite);
        };
    }

    private Resolved resolveStringArgument(Invoke callSite) {
        Var var = getArg(callSite, argIndex);
        if (var != null
                && var.isConst()
                && var.getConstValue() instanceof StringLiteral literal) {
            return new Resolved(literal.getString(), true);
        }
        return new Resolved(WILDCARD, false);
    }

    private Resolved resolveLambdaArgument(Invoke callSite) {
        Var var = getArg(callSite, argIndex);
        if (var == null) {
            return new Resolved(WILDCARD, false);
        }
        String lambdaId = var.getType() == null ? var.toString() : var.getType().toString();
        return lambdaId == null || lambdaId.isBlank()
                ? new Resolved(WILDCARD, false)
                : new Resolved("lambda:" + lambdaId, false);
    }

    private static Var getArg(Invoke callSite, int argIndex) {
        if (callSite == null || argIndex < 0) {
            return null;
        }
        InvokeExp invokeExp = callSite.getInvokeExp();
        if (invokeExp == null || argIndex >= invokeExp.getArgCount()) {
            return null;
        }
        return invokeExp.getArg(argIndex);
    }

    @Override
    public String toString() {
        return switch (kind) {
            case STRING_KEY -> "string(" + value + ")";
            case STRING_ARG -> "stringArg(" + argIndex + ")";
            case LAMBDA_KEY -> "lambdaArg(" + argIndex + ")";
            case DERIVED_KEY -> "derived(" + value + ")";
        };
    }
}
