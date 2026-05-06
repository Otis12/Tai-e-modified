package pascal.taie.analysis.pta.plugin.dumper;

import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.util.collection.Sets;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class ResultComparator {
    private final PointerAnalysisResult result1;

    private final PointerAnalysisResult result2;

    private final Collection<Var> keyVariables;

    public enum ComparePattern {
        DIFF, UNSOUND, IMPRECISE
    }

    ComparePattern pattern;

    private final PrintStream out;
    public ResultComparator(PointerAnalysisResult result1, PointerAnalysisResult result2, Collection<Var> keyVariables, String dumpFile,
                            ComparePattern pattern) {
        this.result1 = result1;
        this.result2 = result2;
        this.keyVariables = keyVariables;
        this.pattern = pattern;
        if (dumpFile != null) {  // if output file is given, then dump to the file
            File outFile = new File(dumpFile);
            try {
                out = new PrintStream(new FileOutputStream(outFile));
            } catch (FileNotFoundException e) {
                throw new RuntimeException("Failed to open output file", e);
            }
        } else {  // otherwise, dump to System.out
            out = System.out;
        }
    }

    public void compare() {
        final Set<Var> diffVars = Sets.newSet();
        final List<Integer> diffSize = new LinkedList<>();
        keyVariables.stream()
                .sorted(Comparator.comparing(v -> v.getMethod() + "/" + v.getName()))
                .forEach(v -> {
//                    if (v.getMethod().getDeclaringClass().isApplication()) {
                        Set<Obj> pts1 = result1.getPointsToSet(v), pts2 = result2.getPointsToSet(v);
                        if (this.pattern == ComparePattern.UNSOUND) {
                            Set<Obj> diff = Sets.newSet();
                            for (Obj obj: pts1) {
                                if (!pts2.contains(obj)) {
                                    diff.add(obj);
                                }
                            }
                            if (diff.size() != 0) {
                                diffVars.add(v);
                                diffSize.add(diff.size());
                                out.println("For " + v.getMethod() + "/" + v.getName() + ": (origin: " + pts1.size() + ", cbPTA: " + pts2.size() + ")");
                                out.println("Result of PTA which not included in result of cbPTA  : ( totally " + diff.size() + ") ");
                                out.println(diff);
                                out.println("\n\n\n");
                            }
                        }
                        else if (pattern == ComparePattern.DIFF) {
                            if ((pts1.size() != pts2.size()) || !(pts1.containsAll(pts2))) {
                                diffVars.add(v);
                                out.println("For " + v.getMethod() + "/" + v.getName() + ": (origin: " + pts1.size() + ", cbPTA: " + pts2.size() + ")");
                                out.println();
                                out.println("Result of PTA: ");
                                out.println(pts1);
                                out.println();
                                out.println("Result of cbPTA: ");
                                out.println(pts2);
                                out.println("\n\n\n");
                            }
                        }
                        else if (pattern == ComparePattern.IMPRECISE) {
                            Set<Obj> diff = Sets.newSet();
                            for (Obj obj: pts2) {
                                if (!pts1.contains(obj)) {
                                    diff.add(obj);
                                }
                            }
                            if (diff.size() > 0) {
                                diffVars.add(v);
                                diffSize.add(diff.size());
                                out.println("For " + v.getMethod() + "/" + v.getName() + ": (origin: " + pts1.size() + ", cbPTA: " + pts2.size() + ")");
                                out.println("Result of cbPTA which not included in result of PTA  : ( totally " + diff.size() + ") ");
                                out.println(diff);
                                out.println("\n\n\n");
                            }
                        }
//            }
        });
        System.out.println("Total key variables: " + keyVariables.size());
        System.out.println("Total diff variables: " + diffVars.size());
        System.out.println("Total diff varpts: " + diffSize.stream().reduce(0, Integer::sum));
    }
}
