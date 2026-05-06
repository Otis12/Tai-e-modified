import java.util.ArrayList;

class IteratorSummaryPrecisionRegression {

    public static void main(String[] args) {
        ArrayList<String> positive = new ArrayList<>();
        positive.add(SourceSink.source());
        String tainted = positive.iterator().next();
        SourceSink.sink(tainted);

        ArrayList<String> negative = new ArrayList<>();
        negative.add("safe");
        String safe = negative.iterator().next();
        SourceSink.sink(safe);
    }
}
