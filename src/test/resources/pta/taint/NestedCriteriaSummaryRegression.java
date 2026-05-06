import java.util.ArrayList;
import java.util.List;

class NestedCriteriaSummaryRegression {

    public static void main(String[] args) {
        CriteriaController controller = new CriteriaController();
        controller.paySuccess(CriteriaSource.source(), Integer.valueOf(1));
    }

    static class CriteriaController {

        private final CriteriaService service = new CriteriaService(new CriteriaMapper());

        void paySuccess(Long orderId, Integer payType) {
            service.paySuccess(orderId, payType);
        }
    }

    static class CriteriaService {

        private final CriteriaMapper mapper;

        CriteriaService(CriteriaMapper mapper) {
            this.mapper = mapper;
        }

        int paySuccess(Long orderId, Integer payType) {
            CriteriaOrder order = new CriteriaOrder();
            order.setId(orderId);
            order.setStatus(Integer.valueOf(1));
            order.setPayType(payType);

            CriteriaExample example = new CriteriaExample();
            Criteria criteria = example.createCriteria();
            criteria.andIdEqualTo(order.getId());
            criteria.andDeleteStatusEqualTo(Integer.valueOf(0));
            criteria.andStatusEqualTo(Integer.valueOf(0));

            return mapper.updateByExampleSelective(order, example);
        }
    }

    static class CriteriaOrder {

        private Long id;

        private Integer status;

        private Integer payType;

        public void setId(Long id) {
            this.id = id;
        }

        public Long getId() {
            return id;
        }

        public void setStatus(Integer status) {
            this.status = status;
        }

        public Integer getStatus() {
            return status;
        }

        public void setPayType(Integer payType) {
            this.payType = payType;
        }

        public Integer getPayType() {
            return payType;
        }
    }

    static class CriteriaMapper {

        public int updateByExampleSelective(CriteriaOrder order, CriteriaExample example) {
            return 1;
        }
    }

    static class CriteriaExample {

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

    abstract static class CriteriaGeneratedCriteria {

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
    }

    static class Criteria extends CriteriaGeneratedCriteria {
    }

    static class CriteriaCriterion {

        private final String condition;

        private final Object value;

        CriteriaCriterion(String condition, Object value) {
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

    static class CriteriaSource {

        static Long source() {
            return Long.valueOf(42L);
        }
    }
}
