package com.baomidou.mybatisplus.core.toolkit.support;

public interface SFunction<T, R> {

    R apply(T value);
}
