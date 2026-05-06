package pascal.taie.analysis.pta.plugin.field;

import pascal.taie.ir.proginfo.FieldRef;

public record GetStatement(int lhsIndex, ParameterIndex baseIndex, FieldRef fieldRef) {

    @Override
    public String toString() {
        return "[GetStmt]" + lhsIndex + "=" + baseIndex().toString() + "." + fieldRef.getName();
    }

}
