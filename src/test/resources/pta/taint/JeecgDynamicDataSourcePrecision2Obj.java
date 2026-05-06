import org.jeecg.common.system.vo.DynamicDataSourceModel;
import org.jeecg.modules.system.entity.SysDataSource;
import org.jeecg.modules.system.service.impl.SysBaseApiImplSlice;

public class JeecgDynamicDataSourcePrecision2Obj {

    public static void main(String[] args) {
        SysBaseApiImplSlice api = new SysBaseApiImplSlice();

        SysDataSource safe = new SysDataSource();
        safe.setDbPassword("safe-password");
        DynamicDataSourceModel safeModel = api.getDynamicDbSourceById(safe);
        SourceSink.sink(safeModel.getDbPassword());

        SysDataSource tainted = new SysDataSource();
        tainted.setDbPassword(SourceSink.source());
        DynamicDataSourceModel taintedModel = api.getDynamicDbSourceByCode(tainted);
        SourceSink.sink(taintedModel.getDbPassword());
    }
}
