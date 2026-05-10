class JdkStringSummaryPropagation {

    public static void main(String[] args) {
        concatSink();
        builderSink();
        builderDetachedSink();
        bufferSink();
        bufferDetachedSink();
    }

    static void concatSink() {
        String taint = SourceSink.source();
        String result = new String("prefix").concat(taint);
        SourceSink.sink(result);
    }

    static void builderSink() {
        String taint = SourceSink.source();
        StringBuilder builder = new StringBuilder();
        String result = builder.append(taint).toString();
        SourceSink.sink(result);
    }

    static void builderDetachedSink() {
        String taint = SourceSink.source();
        StringBuilder builder = new StringBuilder();
        builder.append(taint);
        String result = builder.toString();
        SourceSink.sink(result);
    }

    static void bufferSink() {
        String taint = SourceSink.source();
        StringBuffer buffer = new StringBuffer();
        String result = buffer.append(taint).toString();
        SourceSink.sink(result);
    }

    static void bufferDetachedSink() {
        String taint = SourceSink.source();
        StringBuffer buffer = new StringBuffer();
        buffer.append(taint);
        String result = buffer.toString();
        SourceSink.sink(result);
    }
}
