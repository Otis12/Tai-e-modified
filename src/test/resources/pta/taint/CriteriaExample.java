import java.util.ArrayList;
import java.util.List;

public class CriteriaExample {

    public CriteriaExample() {
    }

    protected List<Criteria> oredCriteria = new ArrayList<>();

    public Criteria createCriteria() {
        Criteria criteria = createCriteriaInternal();
        if (oredCriteria.isEmpty()) {
            oredCriteria.add(criteria);
        }
        return criteria;
    }

    protected Criteria createCriteriaInternal() {
        return new Criteria();
    }
}
