package pascal.taie.analysis.pta.plugin.container;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.util.AnalysisException;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

public class MakeDefaultContainerConfig {
    private static final Logger logger = LogManager.getLogger(MakeDefaultContainerConfig.class);

    private static void readFile(String fileName, String id, ContainerConfig config) {
        BufferedReader reader = null;
        try {
            reader = new BufferedReader(new FileReader("DefaultContainerConfig/" + fileName));
            String lineStr;
            while ((lineStr = reader.readLine()) != null) {
                if (lineStr.length() == 0)
                    continue;
                switch (id) {
                    case "host" -> {
                        config.addHostClass(lineStr);
                    }
                    case "exclusion" -> {
                        int ind = lineStr.indexOf(' ');
                        if (ind != -1) {
                            String ks = lineStr.substring(0, ind), vs = lineStr.substring(ind + 1);
                            config.addKeySetClass(ks);
                            config.excludeClass(ks);
                            config.addValueSetClass(vs);
                            config.excludeClass(vs);
                        }
                        else config.excludeClass(lineStr);
                    }
                    case "extender0" -> config.addCorrelationExtender(lineStr, -1, 0);
                    case "extender1" -> config.addCorrelationExtender(lineStr, -1, 1); // can be merged with the previous case
                    case "unrelatedInvoke" -> config.addUnrelatedInvoke(lineStr);
                    case "col-out" -> config.addCollectionValueOutMethod(lineStr);
                    case "map-val-out" -> config.addMapValueOutMethod(lineStr);
                    case "parameter" -> {
                        int space1 = lineStr.indexOf(' '), space2 = lineStr.lastIndexOf(' ');
                        String type   = lineStr.substring(0, space1),
                               method = lineStr.substring(space1 + 1, space2),
                               sIndex = lineStr.substring(space2 + 1);
                        int index = Integer.parseInt(sIndex);
                        config.addInParameter(method, index, type);
                    }
                    case "paraWithConstraint" -> {
                        int space1 = lineStr.indexOf(' '), space3 = lineStr.lastIndexOf(' '),
                            space2 = lineStr.lastIndexOf('>') + 1;
                        String type   = lineStr.substring(0, space1),
                               method = lineStr.substring(space1 + 1, space2),
                               sIndex = lineStr.substring(space2 + 1, space3),
                               cons   = lineStr.substring(space3 + 1);
                        int index = Integer.parseInt(sIndex);
                        try {
                            config.addInParameter(method, index, type, cons);
                        } catch (AnalysisException e) {
                            throw new AnalysisException(
                                    "Failed to load DefaultContainerConfig/" + fileName +
                                            " line: " + lineStr, e);
                        }
                    }
                    case "array-init" -> {
                        String[] info = lineStr.split("#");
                        int index0 = Integer.parseInt(info[1]), index1 = Integer.parseInt(info[2]);
                        config.addArrayInitializer(info[0], index0, index1);
                    }
                    case "iter" -> {
                        config.addIteratorClass(lineStr);
                    }
                    case "entrySet" -> {
                        String[] info = lineStr.split("#");
                        config.addAllocationSiteOfEntrySet(info[0], info[1]);
                    }
                    default -> throw new AnalysisException("No such id for assigned correlation!");
                }
            }
            reader.close();
        } catch (FileNotFoundException f) {
            logger.error(f);
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            if (reader != null) {
                try {
                    reader.close();
                } catch (IOException e1) {
                    e1.printStackTrace();
                }
            }
        }
    }

    public static ContainerConfig make() {
        ContainerConfig config = ContainerConfig.config;
        // In a more expressive way, a table?
        // For every object of an outer class type, a new determinant will be generated at its allocation Site.
        readFile("hostClasses.txt", "host", config);
        readFile("exclusion.txt", "exclusion", config);
        readFile("CorrelationExtenders.txt", "extender0", config);
        readFile("CorrelationExtenders1.txt", "extender1", config);
        readFile("unrelatedInvokes.txt", "unrelatedInvoke", config);

        config.addCorrelationExtender("<javax.security.auth.Subject$SecureSet: void <init>(javax.security.auth.Subject,int,java.util.Set)>", -1, 2);
        // destination is the larger one, which means source is a subset of it.

        readFile("InMethod.txt", "parameter", config);
        readFile("InWithCons.txt", "paraWithConstraint", config);
        readFile("CollectionOut.txt", "col-out", config);
        readFile("MapValueOut.txt", "map-val-out", config);

        readFile("iteratorClass.txt", "iter", config);
        readFile("ArrayInitializer.txt", "array-init", config);

        readFile("EntrySet.txt", "entrySet", config);

        // TODO: some set methods are also get methods
        config.addMapKeyExit(
                "<java.util.TreeMap: java.lang.Object firstKey()>",
                "<java.util.TreeMap: java.lang.Object lastKey()>",
                "<java.util.TreeMap: java.lang.Object lowerKey(java.lang.Object)>",
                "<java.util.TreeMap: java.lang.Object floorKey(java.lang.Object)>",
                "<java.util.TreeMap: java.lang.Object ceilingKey(java.lang.Object)>",
                "<java.util.TreeMap: java.lang.Object higherKey(java.lang.Object)>",
                "<java.util.Collections$UnmodifiableSortedMap: java.lang.Object firstKey()>",
                "<java.util.Collections$UnmodifiableSortedMap: java.lang.Object lastKey()>",
                "<java.util.Collections$CheckedSortedMap: java.lang.Object firstKey()>",
                "<java.util.Collections$CheckedSortedMap: java.lang.Object lastKey()>",
                "<java.util.TreeMap$NavigableSubMap: java.lang.Object ceilingKey(java.lang.Object)>",
                "<java.util.TreeMap$NavigableSubMap: java.lang.Object higherKey(java.lang.Object)>",
                "<java.util.TreeMap$NavigableSubMap: java.lang.Object floorKey(java.lang.Object)>",
                "<java.util.TreeMap$NavigableSubMap: java.lang.Object lowerKey(java.lang.Object)>",
                "<java.util.TreeMap$NavigableSubMap: java.lang.Object firstKey()>",
                "<java.util.TreeMap$NavigableSubMap: java.lang.Object lastKey()>",
                "<java.util.TreeMap$SubMap: java.lang.Object firstKey()>",
                "<java.util.TreeMap$SubMap: java.lang.Object lastKey()>",
                "<java.util.concurrent.ConcurrentSkipListMap$SubMap: java.lang.Object ceilingKey(java.lang.Object)>",
                "<java.util.concurrent.ConcurrentSkipListMap$SubMap: java.lang.Object lowerKey(java.lang.Object)>",
                "<java.util.concurrent.ConcurrentSkipListMap$SubMap: java.lang.Object higherKey(java.lang.Object)>",
                "<java.util.concurrent.ConcurrentSkipListMap$SubMap: java.lang.Object floorKey(java.lang.Object)>",
                "<java.util.concurrent.ConcurrentSkipListMap$SubMap: java.lang.Object firstKey()>",
                "<java.util.concurrent.ConcurrentSkipListMap$SubMap: java.lang.Object lastKey()>",
                "<java.util.concurrent.ConcurrentSkipListMap$SubMap: java.lang.Object ceilingKey(java.lang.Object)>",
                "<java.util.concurrent.ConcurrentSkipListMap: java.lang.Object lowerKey(java.lang.Object)>",
                "<java.util.concurrent.ConcurrentSkipListMap: java.lang.Object higherKey(java.lang.Object)>",
                "<java.util.concurrent.ConcurrentSkipListMap: java.lang.Object floorKey(java.lang.Object)>",
                "<java.util.concurrent.ConcurrentSkipListMap: java.lang.Object firstKey()>",
                "<java.util.concurrent.ConcurrentSkipListMap: java.lang.Object lastKey()>"
                );
        config.computeTaintClass();
        return config;
    }
}
