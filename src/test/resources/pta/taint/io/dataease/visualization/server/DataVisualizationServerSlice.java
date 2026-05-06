package io.dataease.visualization.server;

import io.dataease.utils.JsonUtil;

import java.util.Map;

public class DataVisualizationServerSlice {

    private Map<String, String> dynamicDataMap;

    @SuppressWarnings("unchecked")
    public void parseDynamicData(String dynamicData) {
        dynamicDataMap = JsonUtil.parseObject(dynamicData, Map.class);
    }

    public String getDynamicValue() {
        return dynamicDataMap.get("dynamic");
    }
}
