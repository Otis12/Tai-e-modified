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

class ContainerSummaryStoreTest {

    private final Context emptyContext = new TrieContext.Factory<>().getEmptyContext();

    private final TestIndexer indexer = new TestIndexer();

    private final PointsToSetFactory ptsFactory =
            new PointsToSetFactory(indexer);

    private int nextIndex;

    private ContainerSummaryStore store;

    @BeforeEach
    void setUp() {
        store = new ContainerSummaryStore(ptsFactory);
        nextIndex = 0;
    }

    @Test
    void mapValuesAreSeparatedByContainerObject() {
        CSObj map1 = csObj("map-1", "java.util.HashMap");
        CSObj map2 = csObj("map-2", "java.util.HashMap");
        CSObj value1 = csObj("value-1", "java.lang.String");
        CSObj value2 = csObj("value-2", "java.lang.String");

        store.putMapValues(map1, pointsToSet(value1));
        store.putMapValues(map2, pointsToSet(value2));

        assertEquals(Set.of(value1), store.loadMapValues(map1).getObjects());
        assertEquals(Set.of(value2), store.loadMapValues(map2).getObjects());
    }

    @Test
    void mapPutReturnsPreviousValuesOfSameContainer() {
        CSObj map1 = csObj("map-1", "java.util.HashMap");
        CSObj map2 = csObj("map-2", "java.util.HashMap");
        CSObj oldValue = csObj("old-value", "java.lang.String");
        CSObj otherValue = csObj("other-value", "java.lang.String");
        CSObj newValue = csObj("new-value", "java.lang.String");

        store.putMapValues(map1, pointsToSet(oldValue));
        store.putMapValues(map2, pointsToSet(otherValue));

        PointsToSet previous = store.putMapValues(map1, pointsToSet(newValue));

        assertEquals(Set.of(oldValue), previous.getObjects());
        assertEquals(Set.of(oldValue, newValue), store.loadMapValues(map1).getObjects());
        assertEquals(Set.of(otherValue), store.loadMapValues(map2).getObjects());
    }

    @Test
    void mapValuesAreSeparatedByConstantKeyWithinSameContainer() {
        CSObj map = csObj("map-1", "java.util.HashMap");
        CSObj userValue = csObj("user-value", "java.lang.String");
        CSObj captchaValue = csObj("captcha-value", "java.lang.String");

        store.putMapValues(map, KeySelector.constant("user"), pointsToSet(userValue));
        store.putMapValues(map, KeySelector.constant("captcha"), pointsToSet(captchaValue));

        assertEquals(Set.of(userValue),
                store.loadMapValues(map, KeySelector.constant("user")).getObjects());
        assertEquals(Set.of(captchaValue),
                store.loadMapValues(map, KeySelector.constant("captcha")).getObjects());
        assertEquals(Set.of(userValue, captchaValue),
                store.loadAllMapValues(map).getObjects());
    }

    @Test
    void wildcardMapValuesConservativelyFlowIntoConcreteLookups() {
        CSObj map = csObj("map-1", "java.util.HashMap");
        CSObj wildcardValue = csObj("wildcard-value", "java.lang.String");
        CSObj userValue = csObj("user-value", "java.lang.String");

        store.putMapValues(map, KeySelector.wildcard(), pointsToSet(wildcardValue));
        store.putMapValues(map, KeySelector.constant("user"), pointsToSet(userValue));

        assertEquals(Set.of(wildcardValue, userValue),
                store.loadMapValues(map, KeySelector.constant("user")).getObjects());
        assertEquals(Set.of(wildcardValue),
                store.loadMapValues(map, KeySelector.constant("captcha")).getObjects());
        assertEquals(Set.of(wildcardValue, userValue),
                store.loadMapValues(map, KeySelector.wildcard()).getObjects());
    }

    @Test
    void collectionValuesAreSeparatedByContainerObject() {
        CSObj collection1 = csObj("collection-1", "java.util.ArrayList");
        CSObj collection2 = csObj("collection-2", "java.util.ArrayList");
        CSObj value1 = csObj("value-1", "java.lang.String");
        CSObj value2 = csObj("value-2", "java.lang.String");

        store.addCollectionValues(collection1, pointsToSet(value1));
        store.addCollectionValues(collection2, pointsToSet(value2));

        assertEquals(Set.of(value1), store.loadCollectionValues(collection1).getObjects());
        assertEquals(Set.of(value2), store.loadCollectionValues(collection2).getObjects());
    }

    @Test
    void listSetReturnsPreviousValuesOfSameContainer() {
        CSObj list1 = csObj("list-1", "java.util.ArrayList");
        CSObj list2 = csObj("list-2", "java.util.ArrayList");
        CSObj oldValue = csObj("old-value", "java.lang.String");
        CSObj otherValue = csObj("other-value", "java.lang.String");
        CSObj newValue = csObj("new-value", "java.lang.String");

        store.setListValues(list1, pointsToSet(oldValue));
        store.setListValues(list2, pointsToSet(otherValue));

        PointsToSet previous = store.setListValues(list1, pointsToSet(newValue));

        assertEquals(Set.of(oldValue), previous.getObjects());
        assertEquals(Set.of(oldValue, newValue), store.loadListValues(list1).getObjects());
        assertEquals(Set.of(otherValue), store.loadListValues(list2).getObjects());
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
