package org.jeecg.modules.system.service.impl;

import org.jeecg.common.system.vo.DynamicDataSourceModel;
import org.jeecg.common.util.SecurityUtil;
import org.jeecg.modules.system.entity.SysDataSource;

public class SysBaseApiImplSlice {

    public DynamicDataSourceModel getDynamicDbSourceById(SysDataSource dbSource) {
        if (dbSource != null && dbSource.getDbPassword() != null) {
            dbSource.setDbPassword(SecurityUtil.jiemi(dbSource.getDbPassword()));
        }
        return new DynamicDataSourceModel(dbSource);
    }

    public DynamicDataSourceModel getDynamicDbSourceByCode(SysDataSource dbSource) {
        if (dbSource != null && dbSource.getDbPassword() != null) {
            dbSource.setDbPassword(SecurityUtil.jiemi(dbSource.getDbPassword()));
        }
        return new DynamicDataSourceModel(dbSource);
    }
}
