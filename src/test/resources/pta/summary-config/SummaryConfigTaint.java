class SummaryConfigTaint {
    public static void main(String[] args) {
        String value = SourceSink.source();
        String copied = passthrough(value);
        SourceSink.sink(copied);
    }

    static String passthrough(String value) {
        return new String();
    }
}
