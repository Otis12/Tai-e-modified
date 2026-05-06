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
import pascal.taie.language.classes.JMethod;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.List;

/**
 * Shared lightweight summary IR for query-builder style connectivity families.
 */
public record QuerySummaryDetail(
        JMethod method,
        Kind kind,
        int receiverIndex,
        Role role,
        List<Integer> subjectIndexes,
        List<Integer> targetIndexes,
        @Nullable QuerySlotKey slotKey,
        @Nullable String metaKey) {

    public QuerySummaryDetail {
        subjectIndexes = List.copyOf(subjectIndexes);
        targetIndexes = List.copyOf(targetIndexes);
    }

    public enum Kind {
        QB_LINK,
        QB_ATTACH,
        QB_WRITE_SLOT,
        QB_WRITE_META,
        QB_RESET,
        QB_READ
    }

    public enum Role {
        CARRIER,
        EXECUTOR
    }

    public static QuerySummaryDetail linkResult(JMethod method) {
        return new QuerySummaryDetail(
                method,
                Kind.QB_LINK,
                InvokeUtils.BASE,
                Role.CARRIER,
                List.of(InvokeUtils.RESULT),
                List.of(),
                null,
                null);
    }

    public static QuerySummaryDetail linkArgument(JMethod method, int argIndex) {
        return new QuerySummaryDetail(
                method,
                Kind.QB_LINK,
                InvokeUtils.BASE,
                Role.CARRIER,
                List.of(argIndex),
                List.of(),
                null,
                null);
    }

    public static QuerySummaryDetail attachArgument(JMethod method, int argIndex) {
        return new QuerySummaryDetail(
                method,
                Kind.QB_ATTACH,
                InvokeUtils.BASE,
                Role.EXECUTOR,
                List.of(argIndex),
                List.of(),
                null,
                null);
    }

    public static QuerySummaryDetail writeSlot(
            JMethod method, QuerySlotKey slotKey, int carrierIndex, int... valueArgIndexes) {
        return new QuerySummaryDetail(
                method,
                Kind.QB_WRITE_SLOT,
                carrierIndex,
                Role.CARRIER,
                toList(valueArgIndexes),
                List.of(),
                slotKey,
                null);
    }

    public static QuerySummaryDetail writeMeta(
            JMethod method, String metaKey, int carrierIndex, int... valueArgIndexes) {
        return new QuerySummaryDetail(
                method,
                Kind.QB_WRITE_META,
                carrierIndex,
                Role.CARRIER,
                toList(valueArgIndexes),
                List.of(),
                null,
                metaKey);
    }

    public static QuerySummaryDetail resetCarrier(JMethod method, int carrierIndex) {
        return new QuerySummaryDetail(
                method,
                Kind.QB_RESET,
                carrierIndex,
                Role.CARRIER,
                List.of(),
                List.of(),
                null,
                null);
    }

    public static QuerySummaryDetail readCarrier(
            JMethod method, int carrierIndex, int... targetIndexes) {
        return new QuerySummaryDetail(
                method,
                Kind.QB_READ,
                carrierIndex,
                Role.CARRIER,
                List.of(),
                toList(targetIndexes),
                null,
                null);
    }

    public static QuerySummaryDetail readExecutor(
            JMethod method, int executorIndex, int... targetIndexes) {
        return new QuerySummaryDetail(
                method,
                Kind.QB_READ,
                executorIndex,
                Role.EXECUTOR,
                List.of(),
                toList(targetIndexes),
                null,
                null);
    }

    private static List<Integer> toList(int... indexes) {
        List<Integer> values = new ArrayList<>(indexes.length);
        for (int index : indexes) {
            values.add(index);
        }
        return values;
    }
}
