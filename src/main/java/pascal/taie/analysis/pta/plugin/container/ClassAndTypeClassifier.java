package pascal.taie.analysis.pta.plugin.container;

import pascal.taie.World;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;

import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.containerType.COLLECTION;
import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.containerType.MAP;
import static pascal.taie.analysis.pta.plugin.container.ClassAndTypeClassifier.containerType.OTHER;

public class ClassAndTypeClassifier {
    private static final ClassHierarchy hierarchy = World.get().getClassHierarchy();

    private static final TypeSystem typeSystem = World.get().getTypeSystem();

    private static final JClass mapClass = hierarchy.getClass("java.util.Map");
    private static final JClass collectionClass = hierarchy.getClass("java.util.Collection");
    private static final JClass mapEntryClass = hierarchy.getClass("java.util.Map$Entry");

    private static final JClass iteratorClass = hierarchy.getClass("java.util.Iterator");

    private static final JClass enumerationClass = hierarchy.getClass("java.util.Enumeration");

    private static final JClass hashtableClass = hierarchy.getClass("java.util.Hashtable");
    private static final Type hashtableType = typeSystem.getType("java.util.Hashtable");

    private static final JClass vectorClass = hierarchy.getClass("java.util.Vector");
    private static final Type vectorType = typeSystem.getType("java.util.Vector");

    private static final JClass abstractList = hierarchy.getClass("java.util.AbstractList");

    public enum containerType {
        MAP, COLLECTION, OTHER
    }

    public static containerType ClassificationOf(Type type) {
        JClass clz = hierarchy.getClass(type.getName());
        if (clz == null)
            return OTHER;
        if (hierarchy.isSubclass(mapClass, clz))
            return MAP;
        if (hierarchy.isSubclass(collectionClass, clz))
            return COLLECTION;
        return OTHER;
    }

    public static boolean isIteratorClass(JClass iterator) {
        return hierarchy.isSubclass(iteratorClass, iterator);
    }

    public static boolean isEnumerationClass(JClass enumeration) {
        return hierarchy.isSubclass(enumerationClass, enumeration) && !enumeration.isApplication();
    }

    public static boolean isAbstractListClass(JClass clz) {
        return hierarchy.isSubclass(abstractList, clz);
    }

    public static boolean isMapEntryClass(JClass entry) {
        return hierarchy.isSubclass(mapEntryClass, entry) && !entry.isApplication();
    }

    public static boolean isHashtableClass(JClass hashtable) {
        return hierarchy.isSubclass(hashtableClass, hashtable) && !hashtable.isApplication();
    }

    public static boolean isVectorClass(JClass vector) {
        return hierarchy.isSubclass(vectorClass, vector) && !vector.isApplication();
    }

    public static boolean isVectorType(Type vector) {
        return typeSystem.isSubtype(vectorType, vector);
    }

    public static boolean isHashtableType(Type hashtable) {
        return typeSystem.isSubtype(hashtableType, hashtable);
    }
}
