/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Sets;

import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Supplier;

/**
 * Lightweight state store for query-builder connectivity summaries.
 *
 * <p>Writes only mutate state. Reads pull from the current state snapshot.
 */
public final class QuerySummaryStore {

    private final Supplier<PointsToSet> pointsToSetFactory;

    private final Map<CSObj, Map<String, PointsToSet>> carrierToSlotValues = Maps.newMap();

    private final Map<CSObj, Map<String, PointsToSet>> carrierToMeta = Maps.newMap();

    private final MultiMap<CSObj, CSObj> carrierToLinkedCarriers = Maps.newMultiMap();

    private final MultiMap<CSObj, CSObj> linkedCarrierToOwners = Maps.newMultiMap();

    private final MultiMap<CSObj, CSObj> executorToAttachedCarriers = Maps.newMultiMap();

    private final MultiMap<CSObj, CSObj> attachedCarrierToExecutors = Maps.newMultiMap();

    public QuerySummaryStore(PointsToSetFactory pointsToSetFactory) {
        this(Objects.requireNonNull(pointsToSetFactory)::make);
    }

    public QuerySummaryStore(Supplier<PointsToSet> pointsToSetFactory) {
        this.pointsToSetFactory = Objects.requireNonNull(pointsToSetFactory);
    }

    public void linkCarriers(CSObj owner, PointsToSet linkedCarriers) {
        Objects.requireNonNull(owner);
        Objects.requireNonNull(linkedCarriers);
        linkedCarriers.forEach(linked -> {
            carrierToLinkedCarriers.put(owner, linked);
            linkedCarrierToOwners.put(linked, owner);
        });
    }

    public void attachCarriers(CSObj executor, PointsToSet carriers) {
        Objects.requireNonNull(executor);
        Objects.requireNonNull(carriers);
        carriers.forEach(carrier -> {
            executorToAttachedCarriers.put(executor, carrier);
            attachedCarrierToExecutors.put(carrier, executor);
        });
    }

    public void addSlotValues(CSObj carrier, String slotId, PointsToSet values) {
        Objects.requireNonNull(carrier);
        Objects.requireNonNull(slotId);
        Objects.requireNonNull(values);
        if (values.isEmpty()) {
            return;
        }
        carrierToSlotValues
                .computeIfAbsent(carrier, __ -> Maps.newMap())
                .computeIfAbsent(slotId, __ -> pointsToSetFactory.get())
                .addAll(values);
    }

    public void addMetaValues(CSObj carrier, String metaKey, PointsToSet values) {
        Objects.requireNonNull(carrier);
        Objects.requireNonNull(metaKey);
        Objects.requireNonNull(values);
        if (values.isEmpty()) {
            return;
        }
        carrierToMeta
                .computeIfAbsent(carrier, __ -> Maps.newMap())
                .computeIfAbsent(metaKey, __ -> pointsToSetFactory.get())
                .addAll(values);
    }

    public PointsToSet loadCarrierValues(CSObj carrier) {
        Objects.requireNonNull(carrier);
        PointsToSet result = pointsToSetFactory.get();
        collectCarrierValues(carrier, result, Sets.newHybridSet());
        return result;
    }

    public PointsToSet loadExecutorValues(CSObj executor) {
        Objects.requireNonNull(executor);
        PointsToSet result = pointsToSetFactory.get();
        executorToAttachedCarriers.get(executor)
                .forEach(carrier -> result.addAll(loadCarrierValues(carrier)));
        return result;
    }

    public void resetCarrier(CSObj carrier) {
        Objects.requireNonNull(carrier);
        carrierToSlotValues.remove(carrier);
        carrierToMeta.remove(carrier);
        Set<CSObj> linkedCarriers = Set.copyOf(carrierToLinkedCarriers.get(carrier));
        carrierToLinkedCarriers.removeAll(carrier);
        linkedCarriers.forEach(linked -> linkedCarrierToOwners.remove(linked, carrier));
        Set<CSObj> attachedCarriers = Set.copyOf(executorToAttachedCarriers.get(carrier));
        executorToAttachedCarriers.removeAll(carrier);
        attachedCarriers.forEach(attached -> attachedCarrierToExecutors.remove(attached, carrier));
    }

    public Set<CSObj> linkedOwners(CSObj linkedCarrier) {
        return linkedCarrierToOwners.get(linkedCarrier);
    }

    public Set<CSObj> attachedExecutors(CSObj carrier) {
        return attachedCarrierToExecutors.get(carrier);
    }

    public Set<CSObj> attachedCarriers(CSObj executor) {
        return executorToAttachedCarriers.get(executor);
    }

    public Map<String, PointsToSet> snapshotSlotValues(CSObj carrier) {
        return snapshotOf(carrierToSlotValues.get(carrier));
    }

    public void clear() {
        carrierToSlotValues.clear();
        carrierToMeta.clear();
        carrierToLinkedCarriers.clear();
        linkedCarrierToOwners.clear();
        executorToAttachedCarriers.clear();
        attachedCarrierToExecutors.clear();
    }

    private void collectCarrierValues(CSObj carrier, PointsToSet result, Set<CSObj> visiting) {
        if (!visiting.add(carrier)) {
            return;
        }
        snapshotOf(carrierToSlotValues.get(carrier)).values().forEach(result::addAll);
        snapshotOf(carrierToMeta.get(carrier)).values().forEach(result::addAll);
        carrierToLinkedCarriers.get(carrier)
                .forEach(linked -> collectCarrierValues(linked, result, visiting));
    }

    private Map<String, PointsToSet> snapshotOf(Map<String, PointsToSet> state) {
        Map<String, PointsToSet> snapshot = Maps.newMap();
        if (state == null) {
            return snapshot;
        }
        state.forEach((key, value) -> snapshot.put(key, value.copy()));
        return snapshot;
    }
}
