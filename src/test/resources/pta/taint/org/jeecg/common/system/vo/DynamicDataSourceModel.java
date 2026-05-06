package org.jeecg.common.system.vo;

import org.jeecg.modules.system.entity.SysDataSource;

public class DynamicDataSourceModel {

    private String dbPassword;
    private String dbUrl;

    public DynamicDataSourceModel() {
    }

    public DynamicDataSourceModel(Object dbSource) {
        if (dbSource instanceof SysDataSource source) {
            copyFrom(source);
        }
    }

    private void copyFrom(SysDataSource source) {
        setDbPassword(source.getDbPassword());
        setDbUrl(source.getDbUrl());
    }

    public String getDbPassword() {
        return dbPassword;
    }

    public void setDbPassword(String dbPassword) {
        this.dbPassword = dbPassword;
    }

    public String getDbUrl() {
        return dbUrl;
    }

    public void setDbUrl(String dbUrl) {
        this.dbUrl = dbUrl;
    }
}
