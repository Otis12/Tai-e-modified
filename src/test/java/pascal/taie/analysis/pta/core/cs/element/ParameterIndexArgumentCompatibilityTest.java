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
package pascal.taie.analysis.pta.core.cs.element;

import org.junit.jupiter.api.Test;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.plugin.field.ParameterIndex;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JClassLoader;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.Type;

import java.util.Collection;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

class ParameterIndexArgumentCompatibilityTest {

    @Test
    void returnsNullWhenCallEdgeHasFewerArgumentsThanParameterIndex() {
        Edge<CSCallSite, CSMethod> edge = makeStaticEdge(1);

        Var arg = assertDoesNotThrow(
                () -> ParameterIndex.getCorrespondingArgument(
                        edge, ParameterIndex.getRealParameterIndex(1)));

        assertNull(arg,
                "cutshortcut summary replay should skip mismatched call edges instead of crashing");
    }

    @Test
    void returnsMatchingArgumentWhenIndexIsInRange() {
        Edge<CSCallSite, CSMethod> edge = makeStaticEdge(1);
        Var expected = edge.getCallSite().getCallSite().getInvokeExp().getArg(0);

        Var arg = ParameterIndex.getCorrespondingArgument(
                edge, ParameterIndex.getRealParameterIndex(0));

        assertSame(expected, arg);
    }

    private static Edge<CSCallSite, CSMethod> makeStaticEdge(int argCount) {
        DummyContext context = new DummyContext();
        JMethod caller = newMethod("Caller", "caller");
        JMethod callee = newMethod("Callee", "callee");
        List<Var> args = java.util.stream.IntStream.range(0, argCount)
                .mapToObj(i -> new Var(caller, "arg" + i, SIMPLE_TYPE, i))
                .toList();
        MethodRef methodRef = MethodRef.get(
                callee.getDeclaringClass(),
                callee.getName(),
                List.of(SIMPLE_TYPE),
                SIMPLE_TYPE,
                true);
        Invoke invoke = new Invoke(caller, new InvokeStatic(methodRef, args));
        CSMethod csCaller = new CSMethod(caller, context);
        CSMethod csCallee = new CSMethod(callee, context);
        CSCallSite csCallSite = new CSCallSite(invoke, context, csCaller);
        return new Edge<>(CallKind.STATIC, csCallSite, csCallee);
    }

    private static JMethod newMethod(String className, String methodName) {
        JClass owner = new JClass(DUMMY_LOADER, className);
        return new JMethod(
                owner,
                methodName,
                Set.of(Modifier.PUBLIC, Modifier.STATIC),
                List.of(SIMPLE_TYPE),
                SIMPLE_TYPE,
                List.of(),
                null,
                AnnotationHolder.emptyHolder(),
                null,
                null,
                methodName);
    }

    private static final Type SIMPLE_TYPE = () -> "java.lang.Object";

    private static final JClassLoader DUMMY_LOADER = new JClassLoader() {
        @Override
        public JClass loadClass(String name) {
            return new JClass(this, name);
        }

        @Override
        public Collection<JClass> getLoadedClasses() {
            return List.of();
        }
    };

    private static final class DummyContext implements Context {
        @Override
        public int getLength() {
            return 0;
        }

        @Override
        public Object getElementAt(int i) {
            throw new IndexOutOfBoundsException(i);
        }

        @Override
        public String toString() {
            return "[]";
        }
    }
}


