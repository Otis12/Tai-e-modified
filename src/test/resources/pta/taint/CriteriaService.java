public class CriteriaService {

    private final CriteriaMapper mapper;

    public CriteriaService(CriteriaMapper mapper) {
        this.mapper = mapper;
    }

    public int paySuccess(Long orderId, Integer payType) {
        CriteriaOrder order = new CriteriaOrder();
        order.setId(orderId);
        order.setStatus(Integer.valueOf(1));
        order.setPayType(payType);

        CriteriaExample example = new CriteriaExample();
        example.createCriteria()
                .andIdEqualTo(order.getId())
                .andDeleteStatusEqualTo(Integer.valueOf(0))
                .andStatusEqualTo(Integer.valueOf(0));

        return mapper.updateByExampleSelective(order, example);
    }
}
