public class CriteriaCriterion {

    private final String condition;

    private final Object value;

    public CriteriaCriterion(String condition, Object value) {
        this.condition = condition;
        this.value = value;
    }

    public String getCondition() {
        return condition;
    }

    public Object getValue() {
        return value;
    }
}
