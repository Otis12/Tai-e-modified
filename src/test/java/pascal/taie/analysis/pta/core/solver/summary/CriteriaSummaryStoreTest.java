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

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.TrieContext;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.language.type.Type;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.Maps;

import java.lang.reflect.Constructor;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

class CriteriaSummaryStoreTest {

    private final Context emptyContext = new TrieContext.Factory<>().getEmptyContext();

    private final TestIndexer indexer = new TestIndexer();

    private final PointsToSetFactory ptsFactory =
            new PointsToSetFactory(indexer);

    private int nextIndex;

    private CriteriaSummaryStore store;

    @BeforeEach
    void setUp() {
        store = new CriteriaSummaryStore(ptsFactory);
        nextIndex = 0;
    }

    @Test
    void exampleValuesAreSeparatedByExampleObject() {
        CSObj example1 = csObj("example-1", "Example");
        CSObj example2 = csObj("example-2", "Example");
        CSObj criteria1 = csObj("criteria-1", "Criteria");
        CSObj criteria2 = csObj("criteria-2", "Criteria");
        CSObj value1 = csObj("value-1", "java.lang.String");
        CSObj value2 = csObj("value-2", "java.lang.String");

        store.linkExampleToCriteria(example1, pointsToSet(criteria1));
        store.linkExampleToCriteria(example2, pointsToSet(criteria2));
        store.addCriteriaValues(criteria1, pointsToSet(value1));
        store.addCriteriaValues(criteria2, pointsToSet(value2));

        assertEquals(Set.of(value1), store.loadExampleValues(example1).getObjects());
        assertEquals(Set.of(value2), store.loadExampleValues(example2).getObjects());
    }

    @Test
    void exampleAggregatesAllLinkedCriteriaBuckets() {
        CSObj example = csObj("example-1", "Example");
        CSObj criteria1 = csObj("criteria-1", "Criteria");
        CSObj criteria2 = csObj("criteria-2", "Criteria");
        CSObj value1 = csObj("value-1", "java.lang.String");
        CSObj value2 = csObj("value-2", "java.lang.String");

        store.linkExampleToCriteria(example, pointsToSet(criteria1, criteria2));
        store.addCriteriaValues(criteria1, pointsToSet(value1));
        store.addCriteriaValues(criteria2, pointsToSet(value2));

        assertEquals(Set.of(value1, value2), store.loadExampleValues(example).getObjects());
    }

    @Test
    void valuesAddedAfterLinkRemainVisibleThroughExample() {
        CSObj example = csObj("example-1", "Example");
        CSObj criteria = csObj("criteria-1", "Criteria");
        CSObj oldValue = csObj("value-1", "java.lang.String");
        CSObj newValue = csObj("value-2", "java.lang.String");

        store.linkExampleToCriteria(example, pointsToSet(criteria));
        store.addCriteriaValues(criteria, pointsToSet(oldValue));
        store.addCriteriaValues(criteria, pointsToSet(newValue));

        assertEquals(Set.of(oldValue, newValue), store.loadExampleValues(example).getObjects());
    }

    private CSObj csObj(String allocation, String typeName) {
        Type type = () -> typeName;
        Obj obj = new MockObj(Descriptor.ENTRY_DESC, allocation, type, null, true);
        CSObj csObj = newCSObj(obj, emptyContext, nextIndex++);
        indexer.register(csObj);
        return csObj;
    }

    private PointsToSet pointsToSet(CSObj... objects) {
        PointsToSet pts = ptsFactory.make();
        for (CSObj object : objects) {
            pts.addObject(object);
        }
        return pts;
    }

    private static CSObj newCSObj(Obj obj, Context context, int index) {
        try {
            Constructor<CSObj> constructor = CSObj.class.getDeclaredConstructor(
                    Obj.class, Context.class, int.class);
            constructor.setAccessible(true);
            return constructor.newInstance(obj, context, index);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("failed to create CSObj test fixture", e);
        }
    }

    private static final class TestIndexer implements Indexer<CSObj> {

        private final Map<Integer, CSObj> objects = Maps.newMap();

        private void register(CSObj csObj) {
            objects.put(csObj.getIndex(), csObj);
        }

        @Override
        public int getIndex(CSObj o) {
            return o.getIndex();
        }

        @Override
        public CSObj getObject(int index) {
            return objects.get(index);
        }
    }
}
