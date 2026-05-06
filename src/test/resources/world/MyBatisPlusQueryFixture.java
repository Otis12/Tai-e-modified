import com.baomidou.mybatisplus.core.conditions.query.LambdaQueryWrapper;
import com.baomidou.mybatisplus.core.conditions.query.QueryWrapper;
import com.baomidou.mybatisplus.core.toolkit.Wrappers;
import com.baomidou.mybatisplus.core.toolkit.support.SFunction;

import java.util.List;

public class MyBatisPlusQueryFixture {
}

class MbpEntity {

    private Object id;

    public Object getId() {
        return id;
    }
}

class MbpMapper {

    public Object selectOne(QueryWrapper<MbpEntity> wrapper) {
        return wrapper;
    }

    public Long selectCount(QueryWrapper<MbpEntity> wrapper) {
        return 0L;
    }

    public List<Object> selectList(QueryWrapper<MbpEntity> wrapper) {
        return List.of();
    }

    public Object selectOne(LambdaQueryWrapper<MbpEntity> wrapper) {
        return wrapper;
    }
}

class MbpService {

    public Object queryById(Object id, MbpMapper mapper) {
        QueryWrapper<MbpEntity> wrapper = new QueryWrapper<>();
        wrapper.eq("id", id).last("limit 1");
        return mapper.selectOne(wrapper);
    }

    public Object queryByLambda(
            SFunction<MbpEntity, Object> getter, Object id, MbpMapper mapper) {
        LambdaQueryWrapper<MbpEntity> wrapper = Wrappers.lambdaQuery();
        wrapper.eq(getter, id);
        return mapper.selectOne(wrapper);
    }
}
