package com.fasterxml.jackson.databind;

import io.dataease.extensions.datasource.vo.DatasourceConfiguration;

import java.util.HashMap;
import java.util.Map;

public class ObjectMapper {

    @SuppressWarnings("unchecked")
    public <T> T readValue(String json, Class<T> clazz) {
        if (clazz == Map.class || clazz == HashMap.class) {
            Map<String, String> map = new HashMap<>();
            map.put("dynamic", json);
            map.put("schema", json);
            return (T) map;
        }
        if (clazz == DatasourceConfiguration.class) {
            DatasourceConfiguration configuration = new DatasourceConfiguration();
            configuration.setHost(json);
            configuration.setSchema(json);
            return (T) configuration;
        }
        throw new IllegalArgumentException("Unsupported class: " + clazz);
    }
}
