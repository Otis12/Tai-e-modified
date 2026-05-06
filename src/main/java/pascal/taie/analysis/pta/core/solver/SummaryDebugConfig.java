/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver;

import pascal.taie.language.classes.JMethod;

import javax.annotation.Nullable;
import java.util.function.Supplier;

/**
 * Centralized switch for temporary summary debugging.
 *
 * <p>Debug logging is disabled by default. To enable it for a single method,
 * set {@value #DEBUG_METHOD_PROPERTY} to the exact callee container signature.
 */
public final class SummaryDebugConfig {

    public static final String DEBUG_METHOD_PROPERTY = "taie.summary.debug.method";

    private SummaryDebugConfig() {
    }

    public static String configuredMethodSignature() {
        return System.getProperty(DEBUG_METHOD_PROPERTY, "").trim();
    }

    public static boolean matchesMethod(@Nullable JMethod method) {
        return method != null && matchesSignature(method.getSignature());
    }

    public static boolean matchesSignature(@Nullable String signature) {
        String configured = configuredMethodSignature();
        return signature != null && !configured.isEmpty() && configured.equals(signature);
    }

    public static <T> @Nullable T computeIfEnabled(
            @Nullable String signature, Supplier<T> supplier) {
        if (!matchesSignature(signature)) {
            return null;
        }
        return supplier.get();
    }
}
