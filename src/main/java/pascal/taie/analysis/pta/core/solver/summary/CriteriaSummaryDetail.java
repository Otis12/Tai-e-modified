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

import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Summary descriptor for MBG-style Example/Criteria builder state.
 *
 * <p>These summaries observe fluent builder calls and maintain detached state
 * that is re-materialized at terminal {@code *ByExample*} consumers.
 */
public record CriteriaSummaryDetail(
        JMethod method,
        Kind kind,
        List<Integer> argIndexes) {

    public CriteriaSummaryDetail {
        argIndexes = List.copyOf(argIndexes);
    }

    public static CriteriaSummaryDetail of(JMethod method, Kind kind, int... argIndexes) {
        java.util.List<Integer> indexes = new java.util.ArrayList<>(argIndexes.length);
        for (int argIndex : argIndexes) {
            indexes.add(argIndex);
        }
        return new CriteriaSummaryDetail(method, kind, indexes);
    }

    public enum Kind {
        EXAMPLE_LINK_RESULT,
        EXAMPLE_LINK_ARGUMENT,
        CRITERIA_ADD_VALUES,
        BY_EXAMPLE_LOAD
    }
}
