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

import java.util.Objects;

/**
 * First-phase selector abstraction for summary-side keyed carriers.
 */
public final class KeySelector {

    private static final KeySelector WILDCARD = new KeySelector(true, null);

    private final boolean wildcard;

    private final String constantValue;

    private KeySelector(boolean wildcard, String constantValue) {
        this.wildcard = wildcard;
        this.constantValue = constantValue;
    }

    public static KeySelector constant(String value) {
        return new KeySelector(false, Objects.requireNonNull(value));
    }

    public static KeySelector wildcard() {
        return WILDCARD;
    }

    public boolean isWildcard() {
        return wildcard;
    }

    public String constantValue() {
        if (wildcard) {
            throw new IllegalStateException("wildcard selector does not carry a constant value");
        }
        return constantValue;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof KeySelector that)) {
            return false;
        }
        return wildcard == that.wildcard
                && Objects.equals(constantValue, that.constantValue);
    }

    @Override
    public int hashCode() {
        return Objects.hash(wildcard, constantValue);
    }

    @Override
    public String toString() {
        return wildcard ? "*" : constantValue;
    }
}
