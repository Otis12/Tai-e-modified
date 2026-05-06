/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;
import pascal.taie.analysis.pta.core.solver.SummaryDebugConfig;

import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SummaryDebugConfigTest {

    private static final String MALL_PAY_SUCCESS =
            "<com.macro.mall.portal.service.impl.OmsPortalOrderServiceImpl: java.lang.Integer paySuccess(java.lang.Long,java.lang.Integer)>";

    @AfterEach
    void clearDebugProperty() {
        System.clearProperty(SummaryDebugConfig.DEBUG_METHOD_PROPERTY);
    }

    @Test
    void debugIsDisabledByDefaultAndDoesNotComputeMessages() {
        AtomicBoolean invoked = new AtomicBoolean(false);

        String message = SummaryDebugConfig.computeIfEnabled(
                MALL_PAY_SUCCESS,
                () -> {
                    invoked.set(true);
                    return "debug-message";
                });

        assertFalse(SummaryDebugConfig.matchesSignature(MALL_PAY_SUCCESS));
        assertNull(message);
        assertFalse(invoked.get(), "debug supplier should stay lazy when no method is configured");
    }

    @Test
    void configuredMethodEnablesExactSignatureMatching() {
        System.setProperty(SummaryDebugConfig.DEBUG_METHOD_PROPERTY, "  " + MALL_PAY_SUCCESS + "  ");
        AtomicBoolean invoked = new AtomicBoolean(false);

        String message = SummaryDebugConfig.computeIfEnabled(
                MALL_PAY_SUCCESS,
                () -> {
                    invoked.set(true);
                    return "debug-message";
                });

        assertTrue(SummaryDebugConfig.matchesSignature(MALL_PAY_SUCCESS));
        assertFalse(SummaryDebugConfig.matchesSignature("<other: void nope()>"));
        assertEquals("debug-message", message);
        assertTrue(invoked.get(), "configured debug target should trigger supplier evaluation");
    }
}
