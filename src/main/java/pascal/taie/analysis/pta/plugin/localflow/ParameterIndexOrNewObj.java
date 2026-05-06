package pascal.taie.analysis.pta.plugin.localflow;

import pascal.taie.analysis.pta.plugin.field.ParameterIndex;
import pascal.taie.analysis.pta.core.heap.Obj;

import static pascal.taie.analysis.pta.plugin.field.ParameterIndex.THISINDEX;

public record ParameterIndexOrNewObj(boolean isObj, ParameterIndex index, Obj obj) {

    public static ParameterIndexOrNewObj INDEX_THIS = new ParameterIndexOrNewObj(false, THISINDEX, null);
    @Override
    public String toString() {
        return isObj ? obj.toString() : index.toString();
    }
}
