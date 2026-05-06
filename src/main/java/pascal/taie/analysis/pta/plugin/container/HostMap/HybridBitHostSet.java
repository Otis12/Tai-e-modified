package pascal.taie.analysis.pta.plugin.container.HostMap;

import pascal.taie.analysis.pta.plugin.container.Host;
import pascal.taie.util.Indexer;
import pascal.taie.util.collection.HybridBitSet;
import pascal.taie.util.collection.SetEx;

class HybridBitHostSet extends DelegateHostSet {

    public HybridBitHostSet(Indexer<Host> indexer) {
        this(new HybridBitSet<>(indexer, true));
    }

    public HybridBitHostSet(SetEx<Host> set) {
        super(set);
    }

    @Override
    protected HostSet newSet(SetEx<Host> set) {
        return new HybridBitHostSet(set);
    }
}
