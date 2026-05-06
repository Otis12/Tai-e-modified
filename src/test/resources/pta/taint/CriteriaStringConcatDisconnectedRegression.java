public class CriteriaStringConcatDisconnectedRegression {

    public static void main(String[] args) {
        unrelatedRendering();
        safeQuery();
    }

    private static void unrelatedRendering() {
        Long tainted = CriteriaSource.source();
        String rendered = "id=" + tainted;
        if (rendered.length() == -1) {
            throw new AssertionError(rendered);
        }
    }

    private static void safeQuery() {
        String keyword = "safe";
        CriteriaExample example = new CriteriaExample();
        example.createCriteria().andTitleEqualTo("%" + keyword + "%");
        new CriteriaMapper().updateByExampleSelective(new CriteriaOrder(), example);
    }
}
