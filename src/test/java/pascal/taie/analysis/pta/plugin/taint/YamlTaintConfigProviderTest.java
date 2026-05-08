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

package pascal.taie.analysis.pta.plugin.taint;

import static org.junit.jupiter.api.Assertions.assertFalse;

import java.nio.file.Files;
import java.nio.file.Path;
import org.junit.jupiter.api.Test;

class YamlTaintConfigProviderTest {

    @Test
    void phantomSinkDeserializationDoesNotMutateSharedResultFromParallelStream()
            throws Exception {
        String source = Files.readString(Path.of(
                "src/main/java/pascal/taie/analysis/pta/plugin/taint/"
                        + "YamlTaintConfigProvider.java"));
        String method = source.substring(
                source.indexOf("private List<PhantomSink> deserializePhantomSinks"),
                source.indexOf("private List<TaintTransfer> deserializeTransfers"));

        assertFalse(method.contains("parallelStream()"),
                "deserializePhantomSinks must not collect into a shared list from a parallel stream");
        assertFalse(method.contains("for(PhantomSink phantomSinka: result)"),
                "deserializePhantomSinks must not iterate result while also adding to it");
    }
}
