import io.dataease.datasource.provider.CalciteProviderSlice;

public class DataEaseJsonPrecision2Obj {

    public static void main(String[] args) {
        CalciteProviderSlice safe = new CalciteProviderSlice();
        safe.loadConfiguration("safe-schema");
        SourceSink.sink(safe.getSchema());

        CalciteProviderSlice tainted = new CalciteProviderSlice();
        tainted.loadConfiguration(SourceSink.source());
        SourceSink.sink(tainted.getSchema());
    }
}
