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

import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.Map;
import java.util.Objects;
import java.util.function.Supplier;

/**
 * Summary-side state store for MBG-style Example/Criteria builder objects.
 */
public final class CriteriaSummaryStore {

    private final Supplier<PointsToSet> pointsToSetFactory;

    private final MultiMap<CSObj, CSObj> exampleToCriteria = Maps.newMultiMap();

    private final MultiMap<CSObj, CSObj> criteriaToExample = Maps.newMultiMap();

    private final Map<CSObj, PointsToSet> criteriaValues = Maps.newMap();

    public CriteriaSummaryStore(PointsToSetFactory pointsToSetFactory) {
        this(Objects.requireNonNull(pointsToSetFactory)::make);
    }

    public CriteriaSummaryStore(Supplier<PointsToSet> pointsToSetFactory) {
        this.pointsToSetFactory = Objects.requireNonNull(pointsToSetFactory);
    }

    public void linkExampleToCriteria(CSObj example, PointsToSet criteriaPts) {
        Objects.requireNonNull(example);
        Objects.requireNonNull(criteriaPts);
        criteriaPts.forEach(criteria -> {
            exampleToCriteria.put(example, criteria);
            criteriaToExample.put(criteria, example);
        });
    }

    public void addCriteriaValues(CSObj criteria, PointsToSet values) {
        Objects.requireNonNull(criteria);
        Objects.requireNonNull(values);
        if (values.isEmpty()) {
            return;
        }
        criteriaValues.computeIfAbsent(criteria, __ -> pointsToSetFactory.get())
                .addAll(values);
    }

    public PointsToSet loadCriteriaValues(CSObj criteria) {
        return snapshotOf(criteriaValues.get(criteria));
    }

    public PointsToSet loadExampleValues(CSObj example) {
        Objects.requireNonNull(example);
        PointsToSet result = pointsToSetFactory.get();
        exampleToCriteria.get(example).forEach(criteria ->
                result.addAll(loadCriteriaValues(criteria)));
        return result;
    }

    public java.util.Set<CSObj> linkedExamples(CSObj criteria) {
        return criteriaToExample.get(criteria);
    }

    private PointsToSet snapshotOf(PointsToSet current) {
        return current == null ? pointsToSetFactory.get() : current.copy();
    }
}
