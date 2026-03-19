/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Lists;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.List;

/**
 * Configuration for method summaries, similar to {@link pascal.taie.analysis.pta.plugin.taint.TaintConfig}.
 *
 * <p>A SummaryConfig contains a list of {@link SummaryDetail} rules that specify
 * how points-to information should be propagated for summarized methods.
 *
 * <p>This configuration can be loaded from YAML files or provided programmatically
 * through plugins.
 */
public record SummaryConfig(List<SummaryDetail> summaryDetails) {

    /**
     * Empty configuration singleton.
     */
    public static final SummaryConfig EMPTY = new SummaryConfig(List.of());

    /**
     * Merges this configuration with another, combining all summary rules.
     * Duplicate rules are removed.
     *
     * @param other the other configuration to merge with
     * @return a new merged configuration
     */
    public SummaryConfig mergeWith(SummaryConfig other) {
        return new SummaryConfig(
                Lists.concatDistinct(summaryDetails, other.summaryDetails)
        );
    }

    /**
     * Builds an index from methods to their summary rules for efficient lookup.
     *
     * @return a MultiMap from JMethod to its SummaryDetail rules
     */
    public MultiMap<MethodRef, SummaryDetail> buildMethodIndex() {
        MultiMap<MethodRef, SummaryDetail> index = Maps.newMultiMap();
        for (SummaryDetail detail : summaryDetails) {
            index.put(detail.method().getRef(), detail);
        }
        return index;
    }

    /**
     * @return true if this configuration has no summary rules
     */
    public boolean isEmpty() {
        return summaryDetails.isEmpty();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("SummaryConfig:");
        if (!summaryDetails.isEmpty()) {
            sb.append("\nSummaries (").append(summaryDetails.size()).append("):\n");
            summaryDetails.forEach(detail ->
                    sb.append("  - ").append(detail).append("\n"));
        } else {
            sb.append(" (empty)");
        }
        return sb.toString();
    }
}
