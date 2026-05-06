public class CriteriaStringConcatCrossMethodRegression {

    public static void main(String[] args) {
        unrelatedRendering();
        queryWithLegitimateSource();
    }

    private static void unrelatedRendering() {
        String tainted = CriteriaStringSource.source();
        StringBuilder builder = new StringBuilder();
        builder.append("id=");
        builder.append(tainted);
        String rendered = builder.toString();
        if (rendered.length() == -1) {
            throw new AssertionError(rendered);
        }
    }

    private static void queryWithLegitimateSource() {
        String keyword = CriteriaStringSource.source();
        StringBuilder builder = new StringBuilder();
        builder.append("%");
        builder.append(keyword);
        builder.append("%");
        String likeValue = builder.toString();
        CriteriaExample example = new CriteriaExample();
        example.createCriteria().andTitleEqualTo(likeValue);
        new CriteriaMapper().updateByExampleSelective(new CriteriaOrder(), example);
    }
}
