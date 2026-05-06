package pascal.taie.analysis.pta.plugin.container.HostMap;

import pascal.taie.analysis.pta.plugin.container.Host;
import pascal.taie.util.collection.SetEx;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Stream;

abstract class DelegateHostSet implements HostSet {

    protected final SetEx<Host> set;

    DelegateHostSet(SetEx<Host> set) {
        this.set = set;
    }

    @Override
    public boolean addHost(Host host) {
        return set.add(host);
    }

    @Override
    public boolean addAll(HostSet hostSet) {
        if (hostSet instanceof DelegateHostSet other) {
            return set.addAll(other.set);
        } else {
            boolean changed = false;
            for (Host h : hostSet) {
                changed |= addHost(h);
            }
            return changed;
        }
    }

    @Override
    public boolean contains(Host host) {
        return set.contains(host);
    }

    @Override
    public boolean isEmpty() {
        return set.isEmpty();
    }

    @Override
    public int size() {
        return set.size();
    }

    @Override
    public Set<Host> getHosts() {
        return Collections.unmodifiableSet(set);
    }

    @Override
    public Stream<Host> hosts() {
        return set.stream();
    }

    @Override
    public void clear() {
        this.set.clear();
    }

    @Override
    public String toString() {
        return set.toString();
    }

    @Override
    public HostSet addAllDiff(HostSet hostSet) {
        Set<Host> otherSet = hostSet instanceof DelegateHostSet other ?
                other.set : hostSet.getHosts();
        return newSet(set.addAllDiff(otherSet));
    }

    @Override
    public HostSet copy() {
        return newSet(set.copy());
    }

    protected abstract HostSet newSet(SetEx<Host> set);
}
