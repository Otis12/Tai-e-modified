package io.dataease.datasource.provider;

import io.dataease.extensions.datasource.vo.DatasourceConfiguration;
import io.dataease.utils.JsonUtil;

public class CalciteProviderSlice {

    private final DatasourceProfile profile = new DatasourceProfile();

    public void loadConfiguration(String configuration) {
        profile.copyFrom(JsonUtil.parseObject(
                configuration, DatasourceConfiguration.class));
    }

    public String getSchema() {
        return profile.getSchema();
    }

    static class DatasourceProfile {

        private String schema;

        void copyFrom(DatasourceConfiguration configuration) {
            schema = configuration.getSchema();
        }

        String getSchema() {
            return schema;
        }
    }
}
