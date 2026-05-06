package pascal.taie.analysis.pta.plugin.container.HostMap;

import pascal.taie.util.collection.Maps;

import javax.annotation.Nullable;
import java.util.Map;
import java.util.function.BiConsumer;

public class HostList {
    private final Map<Kind, HostSet> map = Maps.newMap();

    public HostList() {}

    public HostList(Kind kind, HostSet hostSet) {
        map.put(kind, hostSet);
    }

    public boolean addHostSet(Kind kind, HostSet hostSet) {
        if (map.get(kind) == null) {
            map.put(kind, hostSet);
            return true;
        }
        else {
            return map.get(kind).addAll(hostSet);
        }
    }

    public HostSet addAllDiff(Kind kind, HostSet hostSet) {
        if (map.get(kind) == null) {
            HostSet set = hostSet.copy();
            map.put(kind, set);
            return set;
        }
        return map.get(kind).addAllDiff(hostSet);
    }

    public boolean hasKind(Kind kind) {
        return map.containsKey(kind);
    }

    @Nullable
    public HostSet getHostSetOf(Kind kind) {
        return map.get(kind);
    }

    public boolean isEmpty() {
        return map.isEmpty();
    }

    public void forEach(BiConsumer<Kind, HostSet> action) {
        map.forEach(action);
    }

    public enum Kind {
        MAP_0,
        MAP_ENTRY_SET, MAP_ENTRY_ITR, MAP_ENTRY,
        MAP_KEY_SET, MAP_KEY_ITR,
        MAP_VALUES, MAP_VALUE_ITR,

        COL_0,
        COL_ITR,
        ALL
    }
}
