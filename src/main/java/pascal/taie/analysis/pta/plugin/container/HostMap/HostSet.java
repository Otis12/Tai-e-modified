package pascal.taie.analysis.pta.plugin.container.HostMap;

import pascal.taie.analysis.pta.plugin.container.Host;
import pascal.taie.util.Copyable;

import java.util.Iterator;
import java.util.Set;
import java.util.stream.Stream;

public interface HostSet extends Iterable<Host>, Copyable<HostSet> {

    boolean addHost(Host host);

    boolean addAll(HostSet hostSet);

    HostSet addAllDiff(HostSet hostSet);

    boolean contains(Host host);

    boolean isEmpty();

    int size();

    Set<Host> getHosts();

    Stream<Host> hosts();

    default Iterator<Host> iterator() {
        return getHosts().iterator();
    }

    void clear();
}
