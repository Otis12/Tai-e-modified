import java.util.ArrayList;

class IteratorSummaryRegression {

    public static void main(String[] args) {
        ArrayList<String> values = new ArrayList<>();
        values.add(SourceSink.source());
        String first = values.iterator().next();
        SourceSink.sink(first);
    }
}
