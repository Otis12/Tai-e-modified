package com.baomidou.mybatisplus.core.conditions.query;

import java.util.Collection;

public class QueryWrapper<T> {

    public QueryWrapper<T> eq(String column, Object value) {
        return this;
    }

    public QueryWrapper<T> ne(String column, Object value) {
        return this;
    }

    public QueryWrapper<T> in(String column, Collection<?> values) {
        return this;
    }

    public QueryWrapper<T> orderByDesc(String column) {
        return this;
    }

    public QueryWrapper<T> last(String sql) {
        return this;
    }

    public void clear() {
    }
}
