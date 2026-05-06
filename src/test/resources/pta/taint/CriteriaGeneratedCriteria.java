import java.util.ArrayList;
import java.util.List;

public abstract class CriteriaGeneratedCriteria {

    protected CriteriaGeneratedCriteria() {
    }

    protected List<CriteriaCriterion> criteria = new ArrayList<>();

    protected void addCriterion(String condition, Object value, String property) {
        criteria.add(new CriteriaCriterion(condition, value));
    }

    public Criteria andIdEqualTo(Long value) {
        addCriterion("id =", value, "id");
        return (Criteria) this;
    }

    public Criteria andDeleteStatusEqualTo(Integer value) {
        addCriterion("delete_status =", value, "deleteStatus");
        return (Criteria) this;
    }

    public Criteria andStatusEqualTo(Integer value) {
        addCriterion("status =", value, "status");
        return (Criteria) this;
    }

    public Criteria andTitleEqualTo(String value) {
        addCriterion("title =", value, "title");
        return (Criteria) this;
    }
}
