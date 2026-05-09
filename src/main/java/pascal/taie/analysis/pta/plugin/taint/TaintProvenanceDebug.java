/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Locale;
import java.util.Set;
import java.util.function.Supplier;

/**
 * Debug-only provenance logger for selected taint objects.
 *
 * <p>Enable with {@code -Dtaie.taint.provenance.sources=...}. Filters are
 * comma/semicolon separated substrings:
 * <ul>
 *   <li>{@code taie.taint.provenance.sources}: source point substrings</li>
 *   <li>{@code taie.taint.provenance.methods}: optional pointer/method filters</li>
 *   <li>{@code taie.taint.provenance.sinks}: optional sink filters</li>
 * </ul>
 */
public final class TaintProvenanceDebug {

    private static final Logger logger = LogManager.getLogger(TaintProvenanceDebug.class);

    private static final String SOURCE_FILTER_PROPERTY = "taie.taint.provenance.sources";

    private static final String METHOD_FILTER_PROPERTY = "taie.taint.provenance.methods";

    private static final String SINK_FILTER_PROPERTY = "taie.taint.provenance.sinks";

    private static final int DEFAULT_LIMIT = 12000;

    private static final boolean LOG_CALL_EDGES = Boolean.getBoolean(
            "taie.taint.provenance.callEdges");

    private static final boolean ENABLED =
            !tokens(System.getProperty(SOURCE_FILTER_PROPERTY, "")).isEmpty();

    private static final Set<String> SOURCE_FILTERS =
            tokens(System.getProperty(SOURCE_FILTER_PROPERTY, ""));

    private static final Set<String> METHOD_FILTERS =
            tokens(System.getProperty(METHOD_FILTER_PROPERTY, ""));

    private static final Set<String> SINK_FILTERS =
            tokens(System.getProperty(SINK_FILTER_PROPERTY, ""));

    private static final int LIMIT = Integer.getInteger(
            "taie.taint.provenance.limit", DEFAULT_LIMIT);

    private static int eventCount;

    private static boolean limitNoticePrinted;

    private TaintProvenanceDebug() {
    }

    public static boolean enabled() {
        return ENABLED;
    }

    public static void logPropagate(String solverName, Pointer pointer, PointsToSet diff) {
        if (!enabled() || !methodMatches(pointer.toString())) {
            return;
        }
        diff.objects()
                .filter(csObj -> matchesSource(csObj.getObject()))
                .forEach(csObj -> log("propagate",
                        () -> String.format("solver=%s pointer=%s taint=%s",
                                solverName, pointer, sourceOf(csObj.getObject()))));
    }

    public static void logEdge(String solverName, PointerFlowEdge edge,
                               PointsToSet input, PointsToSet output) {
        if (!enabled() || !methodMatches(edge.toString())) {
            return;
        }
        boolean inputMatches = input != null && input.objects()
                .anyMatch(csObj -> matchesSource(csObj.getObject()));
        boolean outputMatches = output != null && output.objects()
                .anyMatch(csObj -> matchesSource(csObj.getObject()));
        if (inputMatches || outputMatches) {
            log("edge",
                    () -> String.format("solver=%s edge=%s input=%s output=%s",
                            solverName, edge, describeTaints(input), describeTaints(output)));
        }
    }

    public static void logCallEdge(String solverName, Invoke callSite,
                                   JMethod callee, String action) {
        if (!enabled() || !LOG_CALL_EDGES) {
            return;
        }
        String text = callSite + " -> " + callee;
        if (!methodMatches(text)) {
            return;
        }
        log("call-edge", () -> String.format("solver=%s action=%s call=%s callee=%s",
                solverName, action, callSite, callee));
    }

    public static void logTransfer(Invoke callSite, TaintTransfer transfer,
                                   PointsToSet input, PointsToSet output) {
        if (!enabled()) {
            return;
        }
        boolean inputMatches = input != null && input.objects()
                .anyMatch(csObj -> matchesSource(csObj.getObject()));
        boolean outputMatches = output != null && output.objects()
                .anyMatch(csObj -> matchesSource(csObj.getObject()));
        if (!inputMatches && !outputMatches) {
            return;
        }
        String text = transfer.method() + " @ " + callSite;
        if (!methodMatches(text)) {
            return;
        }
        log("transfer", () -> String.format("method=%s call=%s from=%s to=%s input=%s output=%s",
                transfer.method(), callSite, transfer.from(), transfer.to(),
                describeTaints(input), describeTaints(output)));
    }

    public static void logSummary(Invoke callSite, Object methodRef,
                                  String summaryKind, Object summary,
                                  PointsToSet input) {
        if (!enabled()) {
            return;
        }
        if (input == null || input.objects().noneMatch(csObj -> matchesSource(csObj.getObject()))) {
            return;
        }
        String text = methodRef + " @ " + callSite;
        if (!methodMatches(text)) {
            return;
        }
        log("summary", () -> String.format("kind=%s method=%s call=%s summary=%s input=%s",
                summaryKind, methodRef, callSite, summary, describeTaints(input)));
    }

    public static void logSink(Invoke sinkCall, Sink sink, Obj obj) {
        if (!enabled() || !matchesSource(obj)) {
            return;
        }
        String text = sink + " @ " + sinkCall;
        if (!sinkMatches(text)) {
            return;
        }
        log("sink", () -> String.format("sink=%s call=%s source=%s obj=%s",
                sink, sinkCall, sourceOf(obj), obj));
    }

    public static boolean matchesSource(Obj obj) {
        if (!isTaintObj(obj)) {
            return false;
        }
        String source = sourceOf(obj).toLowerCase(Locale.ROOT);
        return SOURCE_FILTERS.stream().anyMatch(source::contains);
    }

    public static String describeTaints(PointsToSet pointsToSet) {
        if (pointsToSet == null) {
            return "[]";
        }
        Set<String> sources = new LinkedHashSet<>();
        pointsToSet.objects()
                .map(CSObj::getObject)
                .filter(TaintProvenanceDebug::matchesSource)
                .map(TaintProvenanceDebug::sourceOf)
                .forEach(sources::add);
        return sources.toString();
    }

    private static boolean isTaintObj(Obj obj) {
        return obj instanceof MockObj mockObj
                && "TaintObj".equals(mockObj.getDescriptor().string());
    }

    private static String sourceOf(Obj obj) {
        return obj instanceof MockObj mockObj
                ? String.valueOf(mockObj.getAllocation())
                : String.valueOf(obj);
    }

    private static boolean methodMatches(String text) {
        return matchesOptionalFilter(METHOD_FILTERS, text);
    }

    private static boolean sinkMatches(String text) {
        return matchesOptionalFilter(SINK_FILTERS, text);
    }

    private static boolean matchesOptionalFilter(Set<String> filters, String text) {
        if (filters.isEmpty()) {
            return true;
        }
        String normalizedText = text.toLowerCase(Locale.ROOT);
        return filters.stream().anyMatch(normalizedText::contains);
    }

    private static void log(String kind, Supplier<String> message) {
        if (eventCount >= LIMIT) {
            if (!limitNoticePrinted) {
                logger.info("[taint-provenance] limit reached at {} events", LIMIT);
                limitNoticePrinted = true;
            }
            return;
        }
        eventCount++;
        logger.info("[taint-provenance] {} {}", kind, message.get());
    }

    private static Set<String> tokens(String raw) {
        Set<String> result = new LinkedHashSet<>();
        if (raw == null || raw.isBlank()) {
            return result;
        }
        Arrays.stream(raw.split("[,;]"))
                .map(String::trim)
                .filter(token -> !token.isEmpty())
                .map(token -> token.toLowerCase(Locale.ROOT))
                .forEach(result::add);
        return result;
    }
}
