package io.dataease.utils;

import com.fasterxml.jackson.databind.ObjectMapper;

public class JsonUtil {

    private static final ObjectMapper objectMapper = new ObjectMapper();

    public static <T> T parseObject(String json, Class<T> classOfT) {
        if (json == null) {
            return null;
        }
        return objectMapper.readValue(json, classOfT);
    }
}
