import java.util.ArrayList;
import java.util.List;

public class MbgCriteriaFixture {
}

class MbgExample {

    protected List<MbgCriteria> oredCriteria = new ArrayList<>();

    public void or(MbgCriteria criteria) {
        oredCriteria.add(criteria);
    }

    public MbgCriteria or() {
        MbgCriteria criteria = createCriteriaInternal();
        oredCriteria.add(criteria);
        return criteria;
    }

    public MbgCriteria createCriteria() {
        MbgCriteria criteria = createCriteriaInternal();
        if (oredCriteria.isEmpty()) {
            oredCriteria.add(criteria);
        }
        return criteria;
    }

    protected MbgCriteria createCriteriaInternal() {
        return new MbgCriteria();
    }
}

abstract class MbgGeneratedCriteria {

    protected List<MbgCriterion> criteria = new ArrayList<>();

    protected void addCriterion(String condition) {
        criteria.add(new MbgCriterion(condition));
    }

    protected void addCriterion(String condition, Object value, String property) {
        criteria.add(new MbgCriterion(condition, value));
    }

    protected void addCriterion(
            String condition, Object value1, Object value2, String property) {
        criteria.add(new MbgCriterion(condition, value1, value2));
    }

    public MbgCriteria andIdEqualTo(Object value) {
        addCriterion("id =", value, "id");
        return (MbgCriteria) this;
    }
}

class MbgCriteria extends MbgGeneratedCriteria {

    public MbgCriteria andIdEqualTo(Object value) {
        return super.andIdEqualTo(value);
    }
}

class MbgCriterion {

    private final String condition;

    private final Object value;

    private final Object secondValue;

    protected MbgCriterion(String condition) {
        this.condition = condition;
        this.value = null;
        this.secondValue = null;
    }

    protected MbgCriterion(String condition, Object value) {
        this.condition = condition;
        this.value = value;
        this.secondValue = null;
    }

    protected MbgCriterion(String condition, Object value, Object secondValue) {
        this.condition = condition;
        this.value = value;
        this.secondValue = secondValue;
    }

    public String getCondition() {
        return condition;
    }

    public Object getValue() {
        return value;
    }

    public Object getSecondValue() {
        return secondValue;
    }
}

class MbgMapper {

    public void updateByExampleSelective(Object record, MbgExample example) {
    }

    public Object selectByExample(MbgExample example) {
        return example;
    }
}

class MbgRecord {

    private Object id;

    public Object getId() {
        return id;
    }

    public void setId(Object id) {
        this.id = id;
    }
}

class MbgCaller {

    public void drive(MbgExample example, MbgRecord record, Object orderId, MbgMapper mapper) {
        record.setId(orderId);
        Object extractedId = record.getId();
        MbgCriteria criteria = example.createCriteria();
        criteria.andIdEqualTo(extractedId);
        mapper.updateByExampleSelective(record, example);
    }
}

class MbgInheritedExample {

    protected List<MbgInheritedCriteria> oredCriteria = new ArrayList<>();

    public void or(MbgInheritedCriteria criteria) {
        oredCriteria.add(criteria);
    }

    public MbgInheritedCriteria or() {
        MbgInheritedCriteria criteria = createCriteriaInternal();
        oredCriteria.add(criteria);
        return criteria;
    }

    public MbgInheritedCriteria createCriteria() {
        MbgInheritedCriteria criteria = createCriteriaInternal();
        if (oredCriteria.isEmpty()) {
            oredCriteria.add(criteria);
        }
        return criteria;
    }

    protected MbgInheritedCriteria createCriteriaInternal() {
        return new MbgInheritedCriteria();
    }
}

abstract class MbgInheritedGeneratedCriteria {

    protected List<MbgCriterion> criteria = new ArrayList<>();

    protected void addCriterion(String condition) {
        criteria.add(new MbgCriterion(condition));
    }

    protected void addCriterion(String condition, Object value, String property) {
        criteria.add(new MbgCriterion(condition, value));
    }

    protected void addCriterion(
            String condition, Object value1, Object value2, String property) {
        criteria.add(new MbgCriterion(condition, value1, value2));
    }

    public MbgInheritedCriteria andIdEqualTo(Object value) {
        addCriterion("id =", value, "id");
        return (MbgInheritedCriteria) this;
    }
}

class MbgInheritedCriteria extends MbgInheritedGeneratedCriteria {
}

class MbgInheritedMapper {

    public void updateByExampleSelective(Object record, MbgInheritedExample example) {
    }
}

class MbgInheritedCaller {

    public void drive(MbgInheritedExample example, MbgRecord record,
                      Object orderId, MbgInheritedMapper mapper) {
        record.setId(orderId);
        Object extractedId = record.getId();
        MbgInheritedCriteria criteria = example.createCriteria();
        criteria.andIdEqualTo(extractedId);
        mapper.updateByExampleSelective(record, example);
    }
}
