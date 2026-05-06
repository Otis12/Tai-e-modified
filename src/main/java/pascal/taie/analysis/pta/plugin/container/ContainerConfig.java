package pascal.taie.analysis.pta.plugin.container;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.container.HostMap.HostList;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Pair;
import pascal.taie.util.collection.Sets;
import pascal.taie.util.collection.TwoKeyMap;

import java.util.Collections;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Stream;

import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.ClassificationOf;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.COL_0;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.COL_ITR;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_0;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_ENTRY;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_ENTRY_ITR;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_ENTRY_SET;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_KEY_ITR;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_KEY_SET;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_VALUES;
import static pascal.taie.analysis.pta.plugin.container.HostMap.HostList.Kind.MAP_VALUE_ITR;

public class ContainerConfig {

    public static ContainerConfig config = new ContainerConfig();
    private static final Logger logger = LogManager.getLogger(ContainerConfig.class);
    private final TwoKeyMap<JMethod, Integer, Parameter> parameters = Maps.newTwoKeyMap();
    private final Map<Parameter, ClassType> ParameterOfColValue = Maps.newMap();

    private final Map<Parameter, ClassType> ParameterOfMapValue = Maps.newMap();
    private final Map<Parameter, ClassType> ParameterOfMapKey = Maps.newMap();

    private final Set<String> excludedContainers = Sets.newSet();
    private final Set<String> keySet = Sets.newSet();
    private final Set<String> valueSet = Sets.newSet();

    private final Set<String> unrelatedInInvokes = Sets.newSet();

    private final Set<JMethod> OutMethodsOfMapKey = Sets.newSet();
    private final Set<JMethod> OutMethodsOfMapValue = Sets.newSet();
    private final Set<JMethod> OutMethodsOfColValue = Sets.newSet();

    private final Set<JClass> iteratorClasses = Sets.newSet();

    private final HostManager hostManager = new HostManager();

    /**
     * Map correlation-extending JMethods to their parameters
     */
    private final MultiMap<JMethod, Pair<Integer, Integer>> corExtenders = Maps.newMultiMap(); // parameters in methods which are similar to "putAll"/"addAll"

    private final Map<JMethod, Pair<Integer, Integer>> arrayInitializer = Maps.newMap();

    private static final ClassHierarchy hierarchy = World.get().getClassHierarchy();

    private static final TwoKeyMap<HostList.Kind, String, HostList.Kind> hostGenerators = Maps.newTwoKeyMap();

    private final Set<JClass> hostClasses = Sets.newSet();

    // r = x.foo(...)
    // TwoKeyMap pair <kind, str, type> (type in [Map-Key, Map-Value, Col-Value]
    // if x has containerKind kind and foo has a substring (specified in the map), then r will be added to the result set
    // (of type) of x
    private static final TwoKeyMap<HostList.Kind, String, String> NonContainerExits = Maps.newTwoKeyMap();

    private final MultiMap<JClass, JClass> allocSiteOfEntrySet = Maps.newMultiMap();

    private final Set<JClass> taintClasses = Sets.newSet();

    private final Set<JClass> taintAbstractListClasses = Sets.newSet();

    static { // initialize hostGenerators (host-passer means pass a host to lhs at an invoke when the base-variable has a required kind)
        hostGenerators.put(COL_0, "iterator", COL_ITR);
        hostGenerators.put(COL_0, "Iterator", COL_ITR);
        hostGenerators.put(MAP_0, "entrySet", MAP_ENTRY_SET);
        hostGenerators.put(MAP_0, "keySet", MAP_KEY_SET);
        hostGenerators.put(MAP_0, "KeySet", MAP_KEY_SET);
        hostGenerators.put(MAP_0, "values", MAP_VALUES);
        hostGenerators.put(MAP_0, "Entry", MAP_ENTRY);
        hostGenerators.put(MAP_0, "keys", MAP_KEY_ITR);
        hostGenerators.put(MAP_ENTRY_SET, "iterator", MAP_ENTRY_ITR);
        hostGenerators.put(MAP_VALUES, "iterator", MAP_VALUE_ITR);
        hostGenerators.put(MAP_KEY_SET, "iterator", MAP_KEY_ITR);
        hostGenerators.put(MAP_ENTRY_ITR, "next", MAP_ENTRY);

        NonContainerExits.put(MAP_ENTRY, "getValue", "Map-Value");
        NonContainerExits.put(MAP_ENTRY, "getKey", "Map-Key");
        NonContainerExits.put(MAP_KEY_ITR, "next", "Map-Key");
        NonContainerExits.put(MAP_KEY_ITR, "nextElement", "Map-Key");
        NonContainerExits.put(MAP_VALUE_ITR, "next", "Map-Value");
        NonContainerExits.put(MAP_VALUE_ITR, "nextElement", "Map-Value");
        NonContainerExits.put(COL_ITR, "next", "Col-Value");
        NonContainerExits.put(COL_ITR, "nextElement", "Col-Value");
        NonContainerExits.put(COL_ITR, "previous", "Col-Value");
    }

    public boolean isTaintType(Type type) {
        if (type instanceof ClassType classType) {
//            return ClassificationOf(type) != ClassAndTypeClassifier.containerType.OTHER && classType.getJClass().isApplication();
            return taintClasses.contains(classType.getJClass());
        }
        return false;
    }

    public boolean isRealHostClass(JClass clz) {
        return hostClasses.contains(clz);
    }

    public boolean isTaintAbstractListType(Type type) {
        if (type instanceof ClassType classType) {
            return taintAbstractListClasses.contains(classType.getJClass());
        }
        return false;
    }

    public Stream<JClass> taintAbstractListClasses() {
        return taintAbstractListClasses.stream();
    }

    public void addHostClass(String clz) {
        JClass c = hierarchy.getClass(clz);
        if (c != null && !c.isAbstract())
            hostClasses.add(c);
    }

    public void computeTaintClass() {
        JClass c = hierarchy.getClass("java.util.Collection"), ca = hierarchy.getClass("java.util.AbstractList");
        hierarchy.getAllSubclassesOf(c).forEach(clz -> {
            if (!clz.isAbstract() && !hostClasses.contains(clz) && !excludedContainers.contains(clz.getName())) {
                if (hierarchy.isSubclass(ca, clz))
                    taintAbstractListClasses.add(clz);
                else
                    taintClasses.add(clz);
            }
        });
        c = hierarchy.getClass("java.util.Map");
        hierarchy.getAllSubclassesOf(c).forEach(clz -> {
            if (!clz.isAbstract() && !hostClasses.contains(clz) && !excludedContainers.contains(clz.getName())) {
                taintClasses.add(clz);
            }
        });
//        taintClasses.forEach(System.out::println);
    }

    public static void setConfig(ContainerConfig config) {
        ContainerConfig.config = config;
    }

    public JMethod getMethod(String signature) {
        return hierarchy.getMethod(signature);
    }

    public Parameter getParameter(JMethod method, int index) {
        if (parameters.get(method, index) == null) {
            parameters.put(method, index, new Parameter(method, index));
        }
        return parameters.get(method, index);
    }

    public void addParameterWithType(Parameter parameter, ClassType classType, String type) {
        if (classType == null)
            return;
        switch (type) {
            case "Map-Key" -> {
                if (ParameterOfMapKey.get(parameter) != null)
                    throw new AnalysisException("Multiple classType for parameter: " + parameter);
                ParameterOfMapKey.put(parameter, classType);
            }
            case "Map-Value" -> {
                if (ParameterOfMapValue.get(parameter) != null) {
                    throw new AnalysisException("Multiple classType for parameter: " + parameter);
                }
                ParameterOfMapValue.put(parameter, classType);
            }
            case "Col-Value" -> {
                if (ParameterOfColValue.get(parameter) != null)
                    throw new AnalysisException("Multiple classType for parameter: " + parameter);
                ParameterOfColValue.put(parameter, classType);
            }
        }
    }

    public void addInParameter(String SMethod, int index, String type) {
        JMethod method = hierarchy.getMethod(SMethod);
        if (method == null) {
            return;
        }
        Parameter parameter = getParameter(method, index);
        ClassType classType = method.getDeclaringClass().getType();
        addInParameter(parameter, classType, type);
    }

    public void addInParameter(String SMethod, int index, String type, String jClass) {
        JMethod method = hierarchy.getMethod(SMethod);
        if (method == null) {
            logger.warn("Skipping unresolved constrained input method {} (type={}, constraint={})",
                    SMethod, type, jClass);
            return;
        }
        Parameter parameter = getParameter(method, index);
        JClass constrainedClass = hierarchy.getClass(jClass);
        if (constrainedClass == null) {
            logger.warn("Skipping constrained input method {} because constraint class {} is unresolved",
                    SMethod, jClass);
            return;
        }
        ClassType classType = constrainedClass.getType();
        addInParameter(parameter, classType, type);
    }

    public void excludeClass(String clz) {
        excludedContainers.add(clz);
    }

    public void addKeySetClass(String clz) {
        keySet.add(clz);
    }

    public void addValueSetClass(String clz) {
        valueSet.add(clz);
    }

    public boolean isKeySetClass(String clz) {
        return keySet.contains(clz);
    }

    public boolean isValueSetClass(String clz) {
        return valueSet.contains(clz);
    }

    private void addInParameter(Parameter parameter, ClassType classType, String type) {
        switch(type) {
            case "Map-Key", "Map-Value", "Col-Value" -> addParameterWithType(parameter, classType, type);
            default -> throw new AnalysisException("No such parameters!");
        }
    }

    public ClassType getTypeConstraintOf(JMethod method, int index, String type) {
        Parameter parameter = getParameter(method, index);
        switch (type) {
            case "Map-Key" -> {
                return ParameterOfMapKey.get(parameter);
            }
            case "Map-Value" -> {
                return ParameterOfMapValue.get(parameter);
            }
            case "Col-Value" -> {
                return ParameterOfColValue.get(parameter);
            }
            default -> {
                return null;
            }
        }
    }

    public void addMapKeyExit(String... methods) {
        for (String method: methods)
            OutMethodsOfMapKey.add(getMethod(method));
    }

    public String CategoryOfExit(JMethod method) {
        if (OutMethodsOfMapKey.contains(method))
            return "Map-Key";
        if (OutMethodsOfMapValue.contains(method))
            return "Map-Value";
        if (OutMethodsOfColValue.contains(method))
            return "Col-Value";
        return "Other";
    }

    public void addMapValueOutMethod(String... methods)  {
        for (String method: methods)
            OutMethodsOfMapValue.add(getMethod(method));
    }

    public void addCollectionValueOutMethod(String... methods) {
        for (String method: methods)
            OutMethodsOfColValue.add(getMethod(method));
    }

    public void addCorrelationExtender(String inMethod, int index0, int index1) {
        addCorrelationExtender(getMethod(inMethod), index0, index1);
    }

    public void addCorrelationExtender(JMethod inMethod, int index0, int index1) {
        if (inMethod != null)
            corExtenders.put(inMethod, new Pair<>(index0, index1));
    }

    public void addArrayInitializer(String smethod, int index0, int index1) {
        // index0: index of array variable, index1: index of Collection variable
        JMethod method = getMethod(smethod);
        assert method != null;
        arrayInitializer.put(method, new Pair<>(index0, index1));
    }

    public boolean isCorrelationExtender(JMethod inMethod) {
        return corExtenders.get(inMethod).size() > 0;
    }

    public boolean isHostType(Type type) {
        return ClassificationOf(type) != ClassAndTypeClassifier.containerType.OTHER && !excludedContainers.contains(type.getName());
    }

    public Host getObjectHost(Obj obj, Host.Classification classification) {
        if (!isHostType(obj.getType())) {
            logger.warn("{} is not an outer class!", obj.getType());
            return null;
        }
        else {
            return hostManager.getHost(obj, classification);
        }

    }

    public int getHostCount() {
        return hostManager.getHostCount();
    }

    public void addUnrelatedInvoke(String invoke) {
        unrelatedInInvokes.add(invoke);
    }

    public boolean isUnrelatedInInvoke(Invoke invoke) {
        return unrelatedInInvokes.contains(invoke.getContainer() + "/" + invoke.getIndex());
    }

    public Set<Pair<Integer, Integer>> getCorrelationExtender(JMethod method) {
        return corExtenders.get(method);
    }

    public Pair<Integer, Integer> getArrayInitializer(JMethod method) {
        return arrayInitializer.get(method);
    }

    public static TwoKeyMap<HostList.Kind, String, HostList.Kind> getHostGenerators() {
        return hostGenerators;
    }

    public static TwoKeyMap<HostList.Kind, String, String> getNonContainerExits() {
        return NonContainerExits;
    }

    public void addIteratorClass(String clz) {
        JClass iclz = hierarchy.getClass(clz);
        if (clz != null)
            iteratorClasses.add(iclz);
    }

    public boolean isIteratorClass(JClass clz) {
        return iteratorClasses.contains(clz);
    }

    public void addAllocationSiteOfEntrySet(String entrySet, String allocClass) {
        JClass c1 = hierarchy.getClass(entrySet), c2 = hierarchy.getClass(allocClass);
        if (c1 == null || c2 == null) {
//            logger.warn("Invalid info about EntrySet: {} and {}", entrySet, allocClass);
        }
        else
            addAllocationSiteOfEntrySet(c1, c2);
    }

    private void addAllocationSiteOfEntrySet(JClass entrySet, JClass allocClass) {
        // An EntrySet Class may have several allocation Sites which allocate its elements
        // We only specified the declaring class of the container of allocation Sites.
        allocSiteOfEntrySet.put(allocClass, entrySet);
        entrySetClasses.add(entrySet);
    }

    public Set<JClass> getRelatedEntrySetClassesOf(JClass allocClass) {
        return allocSiteOfEntrySet.get(allocClass);
    }

    private final Set<JClass> entrySetClasses = Sets.newSet();

    public Set<JClass> getAllEntrySetClasses() {
        return Collections.unmodifiableSet(entrySetClasses);
    }

    public boolean isEntrySetClass(JClass clz) {
        return entrySetClasses.contains(clz);
    }

    public Indexer<Host> getHostIndexer() {
        return hostManager;
    }

    private static class HostManager implements Indexer<Host> {

        private final Map<Obj, Host> objHostMap = Maps.newMap();

        private Host[] hosts = new Host[8092];

        private int counter = 0;

        Host getHost(Obj obj, Host.Classification classification) {
            return objHostMap.computeIfAbsent(obj, o -> {
                int index = counter ++;
                Host host = new Host(o, index, classification);
                storeHost(host, index);
                return host;
            });
        }

        private void storeHost(Host host, int index) {
            if (index >= hosts.length) {
                int newLength = Math.max(index + 1, (int) (hosts.length * 1.5));
                Host[] oldArray = hosts;
                hosts = new Host[newLength];
                System.arraycopy(oldArray, 0, hosts, 0, oldArray.length);
            }
            hosts[index] = host;
        }

        @Override
        public int getIndex(Host o) {
            return o.getIndex();
        }

        @Override
        public Host getObject(int index) {
            return hosts[index];
        }

        public int getHostCount() {
            return counter;
        }
    }
}
