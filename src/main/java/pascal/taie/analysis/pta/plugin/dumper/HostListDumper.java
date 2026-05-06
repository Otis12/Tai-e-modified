package pascal.taie.analysis.pta.plugin.dumper;

import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.HostPointer;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.plugin.container.Host;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Comparator;

public class HostListDumper {
    static public void dumpHostLists(PointerAnalysisResult result) {
        File outFile = new File("pta-output/tainted-hosts.txt"), outFile2 = new File("pta-output/var-hosts");
        PrintStream out, out1;
        try {
            out = new PrintStream(new FileOutputStream(outFile));
            out1 = new PrintStream(new FileOutputStream(outFile2));
            result.getHostPointers().stream().map(HostPointer::getHost).distinct().filter(Host::getTaint).forEach(out::println);
        } catch (FileNotFoundException e) {
            throw new RuntimeException("Failed to open output file", e);
        }
        dumpHostLists(result.getCSVars(), out1);
//        dumpHostLists(result.getInstanceFields(), out);
//        dumpHostLists(result.getArrayIndexes(), out);
    }

    static public void dumpHostLists(Collection<? extends Pointer> pointers, PrintStream out) {

        pointers.stream()
//                .filter(p -> ! p.getHostMap().isEmpty())
                .sorted(Comparator.comparing(Object::toString))
                .forEach(p -> {
                    out.println("For " + p + ": ");
                    p.getHostList().forEach((k, set) -> out.println("[" + k + "]: " + set));
                    out.println("\n\n");
                });
    }
}
