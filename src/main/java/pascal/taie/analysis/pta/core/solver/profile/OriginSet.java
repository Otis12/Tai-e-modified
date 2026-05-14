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

package pascal.taie.analysis.pta.core.solver.profile;

import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Set;

/**
 * Bounded set of app origins. The cap keeps profiling memory predictable while
 * preserving enough distinct callsite/frontier evidence for hub attribution.
 */
public class OriginSet {

    private final int cap;

    private final Set<AppOrigin> origins = Sets.newLinkedSet();

    private boolean capped;

    public OriginSet(int cap) {
        this.cap = Math.max(1, cap);
    }

    public boolean add(AppOrigin origin) {
        if (origin == null || origins.contains(origin)) {
            return false;
        }
        if (origins.size() >= cap) {
            capped = true;
            return false;
        }
        return origins.add(origin);
    }

    public boolean addAll(OriginSet other) {
        if (other == null) {
            return false;
        }
        boolean changed = false;
        for (AppOrigin origin : other.origins) {
            changed |= add(origin);
        }
        capped |= other.capped;
        return changed;
    }

    public int size() {
        return origins.size();
    }

    public boolean isEmpty() {
        return origins.isEmpty();
    }

    public boolean isCapped() {
        return capped;
    }

    public Collection<AppOrigin> origins() {
        return Collections.unmodifiableSet(origins);
    }

    public int appCallsiteCount() {
        return appCallsites().size();
    }

    public Set<String> appCallsites() {
        Set<String> callsites = Sets.newLinkedSet();
        for (AppOrigin origin : origins) {
            if (origin.originAppCallsite() != null) {
                callsites.add(origin.originAppCallsite());
            }
        }
        return callsites;
    }

    public int appMethodCount() {
        Set<String> methods = Sets.newLinkedSet();
        for (AppOrigin origin : origins) {
            if (origin.originAppMethod() != null) {
                methods.add(origin.originAppMethod());
            }
        }
        return methods.size();
    }

    public Map<String, Integer> boundaryMethodCounts() {
        Map<String, Integer> counts = Maps.newLinkedHashMap();
        for (AppOrigin origin : origins) {
            String boundary = origin.originBoundaryMethod();
            if (boundary != null && !boundary.isBlank()) {
                counts.merge(boundary, 1, Integer::sum);
            }
        }
        return counts;
    }

    public Set<String> allocationSites() {
        Set<String> allocations = Sets.newLinkedSet();
        for (AppOrigin origin : origins) {
            if (origin.originAppAlloc() != null
                    && !origin.originAppAlloc().isBlank()) {
                allocations.add(origin.originAppAlloc());
            }
        }
        return allocations;
    }
}
