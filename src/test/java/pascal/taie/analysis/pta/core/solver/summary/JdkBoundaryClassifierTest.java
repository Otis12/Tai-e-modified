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

import org.junit.jupiter.api.Test;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.config.Configs;
import pascal.taie.language.annotation.AnnotationHolder;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JClassLoader;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.VoidType;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class JdkBoundaryClassifierTest {

    private static final JdkBoundaryClassifier CLASSIFIER =
            new JdkBoundaryClassifier();

    @Test
    void includesJdkPlatformClassesByDefault() {
        assertPlatformClass("java.lang.String");
        assertPlatformClass("java.util.HashMap");
        assertPlatformClass("sun.font.TrueTypeFont");
        assertPlatformClass("jdk.internal.misc.Unsafe");
        assertPlatformClass("com.sun.crypto.provider.AESCipher");
        assertPlatformClass("javax.crypto.Cipher");
        assertPlatformClass("javax.xml.parsers.DocumentBuilder");
        assertPlatformClass("org.w3c.dom.Document");
        assertPlatformClass("org.xml.sax.XMLReader");
    }

    @Test
    void excludesNonJdkAndThirdPartyClassesByDefault() {
        assertNotPlatformClass("javax.servlet.http.HttpServletRequest");
        assertNotPlatformClass("javax.websocket.Session");
        assertNotPlatformClass("javax.validation.Validator");
        assertNotPlatformClass("javax.persistence.EntityManager");
        assertNotPlatformClass("javax.transaction.UserTransaction");
        assertNotPlatformClass("org.springframework.web.bind.annotation.RequestMapping");
        assertNotPlatformClass("org.mybatis.spring.SqlSessionTemplate");
        assertNotPlatformClass("com.baomidou.mybatisplus.core.mapper.BaseMapper");
        assertNotPlatformClass("com.alibaba.fastjson.JSON");
        assertNotPlatformClass("com.fasterxml.jackson.databind.ObjectMapper");
        assertNotPlatformClass("org.apache.commons.lang3.StringUtils");
    }

    @Test
    void classifiesMethodsByDeclaringClass() {
        assertTrue(CLASSIFIER.isJdkPlatformMethod(method("java.lang.String")));
        assertTrue(CLASSIFIER.isJdkPlatformMethod(method("javax.crypto.Cipher")));
        assertTrue(CLASSIFIER.isJdkInternalMethod(method("sun.font.TrueTypeFont")));
        assertTrue(CLASSIFIER.isJdkInternalMethod(method("jdk.internal.misc.Unsafe")));
        assertTrue(CLASSIFIER.isJdkInternalMethod(method("com.sun.crypto.provider.AESCipher")));

        assertFalse(CLASSIFIER.isJdkPlatformMethod(
                method("org.springframework.web.bind.annotation.RequestMapping")));
        assertFalse(CLASSIFIER.isJdkPlatformMethod(
                method("org.apache.commons.lang3.StringUtils")));
        assertFalse(CLASSIFIER.isJdkInternalMethod(method("java.lang.String")));
    }

    @Test
    void supportsExtraIncludeAndExcludeOverrides() {
        JdkBoundaryClassifier classifier = new JdkBoundaryClassifier(
                List.of("javax.servlet."),
                List.of("java.util."));

        assertTrue(classifier.isJdkPlatformClass(
                "javax.servlet.http.HttpServletRequest"));
        assertFalse(classifier.isJdkPlatformClass("java.util.HashMap"));
        assertTrue(classifier.isJdkPlatformClass("java.lang.String"));
    }

    @Test
    void extraIncludesMatchClassesExactlyUnlessTheyArePackagePrefixes() {
        JdkBoundaryClassifier classifier = new JdkBoundaryClassifier(
                List.of("java.lang.String", "java.util.regex.Pattern"),
                List.of("java."));

        assertTrue(classifier.isJdkPlatformClass("java.lang.String"));
        assertTrue(classifier.isJdkPlatformClass("java.util.regex.Pattern$Curly"));
        assertFalse(classifier.isJdkPlatformClass(
                "java.lang.StringIndexOutOfBoundsException"));
        assertFalse(classifier.isJdkPlatformClass("java.lang.Class"));
    }

    @Test
    void classifiesSelectedStringBoundaryFamiliesSeparatelyFromAllJdk() {
        assertTrue(CLASSIFIER.isStringFamilyClass("java.lang.String"));
        assertTrue(CLASSIFIER.isStringFamilyClass("java.lang.StringBuilder"));
        assertTrue(CLASSIFIER.isStringFamilyClass("java.lang.StringBuilder$Appendable"));
        assertTrue(CLASSIFIER.isStringFamilyClass("java.util.regex.Pattern"));

        assertFalse(CLASSIFIER.isStringFamilyClass("java.util.HashMap"));
        assertFalse(CLASSIFIER.isStringFamilyClass("javax.servlet.http.HttpServletRequest"));

        assertTrue(CLASSIFIER.isJdkContainerClass("java.util.HashMap"));
        assertFalse(CLASSIFIER.isJdkContainerClass("org.apache.commons.lang3.StringUtils"));
    }

    @Test
    void jdkSummaryOnlyOptionsAreKnownAndDefaultToNormalMode() {
        AnalysisOptions ptaOptions = AnalysisConfig
                .parseConfigs(Configs.getAnalysisConfig())
                .stream()
                .filter(config -> "pta".equals(config.getId()))
                .findFirst()
                .orElseThrow()
                .getOptions();

        assertEquals("normal", ptaOptions.getString("jdk-analysis-mode"));
        assertDoesNotThrow(() -> ptaOptions.update(new AnalysisOptions(Map.of(
                "jdk-analysis-mode", "summary-only",
                "jdk-summary-profile", "jdk17",
                "jdk-summary-configs", List.of("config/summary/jdk/jdk17.yml"),
                "jdk-summary-missing-signature", "error",
                "jdk-summary-report-unsummarized", false,
                "jdk-boundary-extra-includes", List.of("javax.servlet."),
                "jdk-boundary-extra-excludes", List.of("java.util.")))));
    }

    private static void assertPlatformClass(String className) {
        assertTrue(CLASSIFIER.isJdkPlatformClass(className),
                () -> className + " should be in the JDK boundary");
    }

    private static void assertNotPlatformClass(String className) {
        assertFalse(CLASSIFIER.isJdkPlatformClass(className),
                () -> className + " should not be in the JDK boundary");
    }

    private static JMethod method(String declaringClassName) {
        return new JMethod(
                new JClass(DUMMY_LOADER, declaringClassName),
                "m",
                Set.of(Modifier.PUBLIC),
                List.of(),
                VoidType.VOID,
                List.of(),
                null,
                AnnotationHolder.emptyHolder(),
                null,
                null,
                "test");
    }

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
}
