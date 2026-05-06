package org.springframework.beans;

import org.jeecg.common.system.vo.DynamicDataSourceModel;
import org.jeecg.modules.system.entity.SysDataSource;

public class BeanUtils {

    public static void copyProperties(Object source, Object target) {
        if (source instanceof SysDataSource src &&
                target instanceof DynamicDataSourceModel dst) {
            dst.setDbPassword(src.getDbPassword());
            dst.setDbUrl(src.getDbUrl());
        }
    }
}
