import com.baomidou.mybatisplus.core.conditions.query.QueryWrapper;

import java.util.List;

public class GridBinderQueryFixture {
}

class GridBinder<T> {

    public void setWrapper(QueryWrapper<T> wrapper) {
    }

    public List<T> queryObjs() {
        return List.of();
    }

    public Object queryPage() {
        return null;
    }
}

class GridBinderCaller {

    public Object queryById(Object id, GridBinder<MbpEntity> binder) {
        QueryWrapper<MbpEntity> wrapper = new QueryWrapper<>();
        wrapper.eq("id", id);
        binder.setWrapper(wrapper);
        return binder.queryPage();
    }
}
