class ObjectToStringSummaryRegression {

    private final String value;

    ObjectToStringSummaryRegression(String value) {
        this.value = value;
    }

    @Override
    public String toString() {
        return value;
    }

    public static void main(String[] args) {
        SourceSink.sink(new Object().toString());
        SourceSink.sink(new ObjectToStringSummaryRegression(SourceSink.source()).toString());
    }
}
