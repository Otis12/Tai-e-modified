package com.baomidou.mybatisplus.core.conditions.query;

import com.baomidou.mybatisplus.core.toolkit.support.SFunction;

public class LambdaQueryWrapper<T> {

    public LambdaQueryWrapper<T> eq(SFunction<T, ?> column, Object value) {
        return this;
    }

    public LambdaQueryWrapper<T> like(SFunction<T, ?> column, Object value) {
        return this;
    }

    public LambdaQueryWrapper<T> orderByAsc(SFunction<T, ?> column) {
        return this;
    }

    public LambdaQueryWrapper<T> last(String sql) {
        return this;
    }

    public void clear() {
    }
}
