import java.util.ArrayList;

public class CriteriaUnsafeBridgeNegativeRegression {

    public static void main(String[] args) {
        ArrayList<Object> values = new ArrayList<>();
        values.add(CriteriaSource.source());

        StringBuilder builder = new StringBuilder();
        builder.append(values.stream());
        String rendered = builder.toString();

        CriteriaExample example = new CriteriaExample();
        example.createCriteria().andTitleEqualTo(rendered);

        new CriteriaMapper().updateByExampleSelective(new CriteriaOrder(), example);
    }
}
