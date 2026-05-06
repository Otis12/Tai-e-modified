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

import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.util.Hashes;
import pascal.taie.util.collection.Sets;
import pascal.taie.util.graph.Edge;

import java.util.Set;

public class PointerFlowEdge implements Edge<Pointer> {

    public enum Kind {
        LOCAL_ASSIGN(FlowKind.LOCAL_ASSIGN),
        CAST(FlowKind.CAST),
        INSTANCE_LOAD(FlowKind.INSTANCE_LOAD),
        INSTANCE_STORE(FlowKind.INSTANCE_STORE),
        ARRAY_LOAD(FlowKind.ARRAY_LOAD),
        ARRAY_STORE(FlowKind.ARRAY_STORE),
        STATIC_LOAD(FlowKind.STATIC_LOAD),
        STATIC_STORE(FlowKind.STATIC_STORE),
        PARAMETER_PASSING(FlowKind.PARAMETER_PASSING),
        RETURN(FlowKind.RETURN),
        ARG_TO_HOST(FlowKind.ARG_TO_HOST),
        HOST_TO_RESULT(FlowKind.HOST_TO_RESULT),
        SUBSET(FlowKind.SUBSET),
        CORRELATION(FlowKind.CORRELATION),
        ARRAYCOPY(FlowKind.ARRAYCOPY),
        ID(FlowKind.ID),
        VIRTUAL_ARRAY(FlowKind.VIRTUAL_ARRAY),
        VIRTUAL_ARG(FlowKind.VIRTUAL_ARG),
        SET(FlowKind.SET),
        GET(FlowKind.GET),
        NON_RELAY_GET(FlowKind.NON_RELAY_GET);

        private final FlowKind flowKind;

        Kind(FlowKind flowKind) {
            this.flowKind = flowKind;
        }

        public FlowKind asFlowKind() {
            return flowKind;
        }

        public static Kind fromFlowKind(FlowKind flowKind) {
            for (Kind kind : values()) {
                if (kind.flowKind == flowKind) {
                    return kind;
                }
            }
            return null;
        }
    }

    private final FlowKind kind;

    private final Pointer source;

    private final Pointer target;

    private final Set<Transfer> transfers = Sets.newHybridSet();

    public PointerFlowEdge(FlowKind kind, Pointer source, Pointer target) {
        this.kind = kind;
        this.source = source;
        this.target = target;
    }

    public PointerFlowEdge(FlowKind kind, Pointer source, Pointer target,
                           Transfer transfer) {
        this(kind, source, target);
        addTransfer(transfer);
    }

    public PointerFlowEdge(Kind kind, Pointer source, Pointer target) {
        this(kind.asFlowKind(), source, target);
    }

    public PointerFlowEdge(Kind kind, Pointer source, Pointer target,
                           Transfer transfer) {
        this(kind.asFlowKind(), source, target, transfer);
    }

    public FlowKind kind() {
        return kind;
    }

    public Kind getKind() {
        return Kind.fromFlowKind(kind);
    }

    public Pointer source() {
        return source;
    }

    public Pointer getSource() {
        return source;
    }

    public Pointer target() {
        return target;
    }

    public Pointer getTarget() {
        return target;
    }

    /**
     * @return String representation of information for this edge.
     * By default, the information represents the {@link FlowKind},
     * and other subclasses of {@link PointerFlowEdge} may contain
     * additional content.
     */
    public String getInfo() {
        return kind.name();
    }

    public boolean addTransfer(Transfer transfer) {
        return transfers.add(transfer);
    }

    public Set<Transfer> getTransfers() {
        return transfers;
    }

    public Transfer getTransfer() {
        return transfers.isEmpty() ? Identity.get() : transfers.iterator().next();
    }

    @Override
    public int hashCode() {
        return Hashes.hash(kind, source, target);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        PointerFlowEdge that = (PointerFlowEdge) o;
        return kind == that.kind &&
                source.equals(that.source) &&
                target.equals(that.target);
    }

    @Override
    public String toString() {
        return "[" + getInfo() + "]" + source + " -> " + target;
    }
}
