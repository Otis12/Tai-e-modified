package pascal.taie.analysis.pta.plugin.container;

import pascal.taie.language.classes.JMethod;

public record Parameter(JMethod method, int index) {

    @Override
    public String toString() {
        return "Parameter[" + index + "@" + method + "]";
    }

}
