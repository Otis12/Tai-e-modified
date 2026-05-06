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

package pascal.taie.analysis.pta.core.solver;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.flowgraph.ObjectFlowGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.HostPointer;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.container.Host;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.Indexer;

import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ObjectFlowGraphHostPointerCompatibilityTest {

    @Test
    void ignoresHostPointersThatCannotBeMappedToProgramLocations() {
        Type type = () -> "java.util.HashMap";
        Obj obj = new MockObj(Descriptor.ENTRY_DESC, "host-alloc", type, null, true);
        HostPointer hostPointer = new HostPointer(
                new Host(obj, 0, Host.Classification.MAP),
                "Map-Value",
                0);
        PointerFlowGraph pfg = new PointerFlowGraph(new SinglePointerCSManager(hostPointer));

        ObjectFlowGraph ofg = assertDoesNotThrow(
                () -> new ObjectFlowGraph(pfg, new DefaultCallGraph()));

        assertTrue(ofg.getNodes().isEmpty(),
                "HostPointer is an internal container-model pointer and should not appear as an OFG node");
    }

    private record SinglePointerCSManager(HostPointer hostPointer) implements CSManager {

        @Override
        public Stream<Pointer> pointers() {
            return Stream.of(hostPointer);
        }

        @Override
        public Collection<HostPointer> getHostPointers() {
            return List.of(hostPointer);
        }

        @Override
        public CSVar getCSVar(Context context, pascal.taie.ir.exp.Var var) {
            throw unsupported();
        }

        @Override
        public CSObj getCSObj(Context heapContext, Obj obj) {
            throw unsupported();
        }

        @Override
        public CSCallSite getCSCallSite(Context context, pascal.taie.ir.stmt.Invoke callSite) {
            throw unsupported();
        }

        @Override
        public CSMethod getCSMethod(Context context, JMethod method) {
            throw unsupported();
        }

        @Override
        public StaticField getStaticField(JField field) {
            throw unsupported();
        }

        @Override
        public InstanceField getInstanceField(CSObj base, JField field) {
            throw unsupported();
        }

        @Override
        public ArrayIndex getArrayIndex(CSObj array) {
            throw unsupported();
        }

        @Override
        public HostPointer getHostPointer(Host host, String category) {
            throw unsupported();
        }

        @Override
        public Collection<pascal.taie.ir.exp.Var> getVars() {
            return List.of();
        }

        @Override
        public Collection<CSVar> getCSVarsOf(pascal.taie.ir.exp.Var var) {
            return List.of();
        }

        @Override
        public Collection<CSVar> getCSVars() {
            return List.of();
        }

        @Override
        public Collection<CSObj> getObjects() {
            return List.of();
        }

        @Override
        public Collection<CSObj> getCSObjsOf(Obj obj) {
            return List.of();
        }

        @Override
        public Collection<StaticField> getStaticFields() {
            return List.of();
        }

        @Override
        public Collection<InstanceField> getInstanceFields() {
            return List.of();
        }

        @Override
        public Collection<ArrayIndex> getArrayIndexes() {
            return List.of();
        }

        @Override
        public Indexer<CSObj> getObjectIndexer() {
            throw unsupported();
        }

        @Override
        public Collection<CSCallSite> getCSCallSites() {
            return List.of();
        }

        private UnsupportedOperationException unsupported() {
            return new UnsupportedOperationException("not needed in this compatibility test");
        }
    }
}
