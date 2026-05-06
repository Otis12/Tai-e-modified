public class CriteriaController {

    private final CriteriaService service = new CriteriaService(new CriteriaMapper());

    public CriteriaController() {
    }

    public void paySuccess(Long orderId, Integer payType) {
        service.paySuccess(orderId, payType);
    }
}
