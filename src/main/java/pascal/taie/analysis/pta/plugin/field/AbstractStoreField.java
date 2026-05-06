package pascal.taie.analysis.pta.plugin.field;

import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.FieldStmt;
import pascal.taie.ir.stmt.StmtVisitor;

public class AbstractStoreField extends FieldStmt<FieldAccess, Var> {

    public AbstractStoreField(FieldAccess lvalue, Var rvalue) {
        super(lvalue, rvalue);
        if (lvalue instanceof InstanceFieldAccess) {
            Var base = ((InstanceFieldAccess) lvalue).getBase();
            base.addAbstractStoreField(this);
        }
    }

    @Override
    public FieldAccess getFieldAccess() {
        return getLValue();
    }

    @Override
    public <T> T accept(StmtVisitor<T> visitor) {
        return null;
    }
}
