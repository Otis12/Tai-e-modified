/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.Collection;
import java.util.Map;
import java.util.Objects;
import java.util.function.Supplier;

/**
 * Summary-side container state keyed by concrete container objects.
 *
 * <p>This first slice is host-sensitive but not selector-sensitive:
 * all values stored in the same container object are merged into one bucket.
 */
public final class ContainerSummaryStore {

    private final Supplier<PointsToSet> pointsToSetFactory;

    private final Map<CSObj, PointsToSet> mapWildcardValues = Maps.newMap();

    private final Map<CSObj, Map<KeySelector, PointsToSet>> keyedMapValues = Maps.newMap();

    private final Map<CSObj, PointsToSet> mapAllValues = Maps.newMap();

    private final Map<CSObj, PointsToSet> listValues = Maps.newMap();

    private final Map<CSObj, PointsToSet> collectionValues = Maps.newMap();

    private final MultiMap<CSObj, CSObj> iteratorToContainers = Maps.newMultiMap();

    private final MultiMap<CSVar, CSObj> iteratorVarToContainers = Maps.newMultiMap();

    public ContainerSummaryStore(PointsToSetFactory pointsToSetFactory) {
        this(Objects.requireNonNull(pointsToSetFactory)::make);
    }

    public ContainerSummaryStore(Supplier<PointsToSet> pointsToSetFactory) {
        this.pointsToSetFactory = Objects.requireNonNull(pointsToSetFactory);
    }

    public PointsToSet putMapValues(CSObj container, PointsToSet values) {
        return putMapValues(container, KeySelector.wildcard(), values);
    }

    public PointsToSet loadMapValues(CSObj container) {
        return loadAllMapValues(container);
    }

    public PointsToSet removeMapValues(CSObj container) {
        return loadAllMapValues(container);
    }

    public PointsToSet putMapValues(CSObj container, KeySelector key, PointsToSet values) {
        Objects.requireNonNull(key);
        PointsToSet previous = loadMapValues(container, key);
        if (values.isEmpty()) {
            return previous;
        }
        mergeInto(mapAllValues, container, values);
        if (key.isWildcard()) {
            mergeInto(mapWildcardValues, container, values);
        } else {
            mergeInto(keyedMapValues.computeIfAbsent(container, __ -> Maps.newMap()), key, values);
        }
        return previous;
    }

    public PointsToSet loadMapValues(CSObj container, KeySelector key) {
        Objects.requireNonNull(key);
        if (key.isWildcard()) {
            return loadAllMapValues(container);
        }
        PointsToSet result = pointsToSetFactory.get();
        result.addAll(snapshotOf(mapWildcardValues, container));
        Map<KeySelector, PointsToSet> keyedValues = keyedMapValues.get(container);
        if (keyedValues != null) {
            PointsToSet keyedBucket = keyedValues.get(key);
            if (keyedBucket != null) {
                result.addAll(keyedBucket);
            }
        }
        return result;
    }

    public PointsToSet removeMapValues(CSObj container, KeySelector key) {
        return loadMapValues(container, key);
    }

    public PointsToSet loadAllMapValues(CSObj container) {
        return snapshotOf(mapAllValues, container);
    }

    public PointsToSet setListValues(CSObj container, PointsToSet values) {
        PointsToSet previous = loadListValues(container);
        mergeInto(listValues, container, values);
        return previous;
    }

    public PointsToSet loadListValues(CSObj container) {
        return snapshotOf(listValues, container);
    }

    public void addCollectionValues(CSObj container, PointsToSet values) {
        mergeInto(collectionValues, container, values);
        // Phase 1 only registers collection writes on concrete list classes
        // (ArrayList/LinkedList), so the same host-sensitive bucket should
        // also be visible to positional list reads.
        mergeInto(listValues, container, values);
    }

    public PointsToSet loadCollectionValues(CSObj container) {
        return snapshotOf(collectionValues, container);
    }

    public void bindIteratorToContainers(CSObj iterator, PointsToSet containers) {
        Objects.requireNonNull(iterator);
        Objects.requireNonNull(containers);
        containers.forEach(container -> iteratorToContainers.put(iterator, container));
    }

    public void bindIteratorVarToContainers(CSVar iteratorVar, PointsToSet containers) {
        Objects.requireNonNull(iteratorVar);
        Objects.requireNonNull(containers);
        containers.forEach(container -> iteratorVarToContainers.put(iteratorVar, container));
    }

    public PointsToSet loadIteratorValues(CSVar iteratorVar, PointsToSet iteratorObjects) {
        Objects.requireNonNull(iteratorVar);
        Objects.requireNonNull(iteratorObjects);
        PointsToSet result = pointsToSetFactory.get();
        var varBoundContainers = iteratorVarToContainers.get(iteratorVar);
        if (!varBoundContainers.isEmpty()) {
            collectContainerValues(varBoundContainers, result);
            return result;
        }
        iteratorObjects.forEach(iterator -> iteratorToContainers.get(iterator).forEach(container -> {
            result.addAll(loadCollectionValues(container));
            result.addAll(loadListValues(container));
        }));
        return result;
    }

    private void collectContainerValues(Collection<CSObj> containers, PointsToSet result) {
        containers.forEach(container -> {
            result.addAll(loadCollectionValues(container));
            result.addAll(loadListValues(container));
        });
    }

    private void mergeInto(Map<CSObj, PointsToSet> store, CSObj container, PointsToSet values) {
        Objects.requireNonNull(container);
        Objects.requireNonNull(values);
        if (values.isEmpty()) {
            return;
        }
        store.computeIfAbsent(container, __ -> pointsToSetFactory.get())
                .addAll(values);
    }

    private void mergeInto(Map<KeySelector, PointsToSet> store, KeySelector key, PointsToSet values) {
        Objects.requireNonNull(key);
        Objects.requireNonNull(values);
        if (values.isEmpty()) {
            return;
        }
        store.computeIfAbsent(key, __ -> pointsToSetFactory.get())
                .addAll(values);
    }

    private PointsToSet snapshotOf(Map<CSObj, PointsToSet> store, CSObj container) {
        Objects.requireNonNull(container);
        PointsToSet current = store.get(container);
        return current == null ? pointsToSetFactory.get() : current.copy();
    }
}
