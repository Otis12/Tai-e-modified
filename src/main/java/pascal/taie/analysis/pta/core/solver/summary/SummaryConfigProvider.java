/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 */

package pascal.taie.analysis.pta.core.solver.summary;

import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.SignatureMatcher;
import pascal.taie.language.type.TypeSystem;

import java.util.List;

import static java.util.Collections.unmodifiableList;

/**
 * Provides a configuration for method summaries.
 *
 * <p>Similar to {@link pascal.taie.analysis.pta.plugin.taint.TaintConfigProvider},
 * subclasses should implement the constructor
 * {@link #SummaryConfigProvider(ClassHierarchy, TypeSystem)}
 * and override the necessary methods to provide specific configurations.
 *
 * <p>This class can be extended to provide summary configurations programmatically
 * (e.g., from plugins) instead of loading from YAML files.
 *
 * <p>Example usage:
 * <pre>
 * public class MyLibrarySummaryProvider extends SummaryConfigProvider {
 *     public MyLibrarySummaryProvider(ClassHierarchy h, TypeSystem t) {
 *         super(h, t);
 *     }
 *
 *     &#64;Override
 *     protected List&lt;SummaryDetail&gt; summaries() {
 *         List&lt;SummaryDetail&gt; result = new ArrayList&lt;&gt;();
 *         // Add summary rules for my library
 *         for (JMethod m : matcher.getMethods("&lt;MyClass: * get*()&gt;")) {
 *             AccessPath source = AccessPath.ofField(InvokeUtils.BASE, ...);
 *             AccessPath target = AccessPath.ofVar(InvokeUtils.RESULT);
 *             result.add(SummaryDetail.of(m, "base.field", "result", source, target));
 *         }
 *         return result;
 *     }
 * }
 * </pre>
 */
public abstract class SummaryConfigProvider {

    protected final ClassHierarchy hierarchy;

    protected final TypeSystem typeSystem;

    protected final SignatureMatcher matcher;

    protected final AccessPathParser accessPathParser;

    protected SummaryConfigProvider(ClassHierarchy hierarchy, TypeSystem typeSystem) {
        this.hierarchy = hierarchy;
        this.typeSystem = typeSystem;
        this.matcher = new SignatureMatcher(hierarchy);
        this.accessPathParser = new AccessPathParser(hierarchy);
    }

    /**
     * Override this method to provide summary rules.
     *
     * @return list of summary details
     */
    protected List<SummaryDetail> summaries() {
        return List.of();
    }

    /**
     * Builds and returns the summary configuration.
     *
     * @return the summary configuration
     */
    public SummaryConfig get() {
        return new SummaryConfig(unmodifiableList(summaries()));
    }
}
