package com.baomidou.mybatisplus.core.toolkit;

import com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper;

public final class Wrappers {

    private Wrappers() {
    }

    public static <T> LambdaQueryWrapper<T> lambdaQuery() {
        return new LambdaQueryWrapper<>();
    }
}
