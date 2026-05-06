package pascal.taie.analysis.pta.core.cs.element;

import pascal.taie.analysis.pta.plugin.container.Host;
import pascal.taie.language.type.Type;

public class HostPointer extends AbstractPointer {

    private final Host host;

    private final String category;

    public HostPointer(Host host, String category, int index) {
        super(index);
        this.host = host;
        this.category = category;
    }

    public Host getHost() {
        return host;
    }

    @Override
    public Type getType() {
        return host.getType();
    }

    @Override
    public String toString() {
        return host.toString();
    }
}
