package io.dataease.datasource.server;

import io.dataease.extensions.datasource.vo.DatasourceConfiguration;
import io.dataease.utils.JsonUtil;

public class DatasourceServerSlice {

    private final DatasourceProfile profile = new DatasourceProfile();

    public void loadConfiguration(String configurationStr) {
        profile.copyFrom(JsonUtil.parseObject(
                configurationStr, DatasourceConfiguration.class));
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
