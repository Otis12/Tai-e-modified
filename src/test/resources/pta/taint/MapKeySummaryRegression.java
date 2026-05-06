import java.util.HashMap;

class MapKeySummaryRegression {

    public static void main(String[] args) {
        HashMap<String, String> values = new HashMap<>();
        values.put("user", SourceSink.source());
        values.put("captcha", "safe");

        String user = values.get("user");
        SourceSink.sink(user);

        String captcha = values.get("captcha");
        SourceSink.sink(captcha);
    }
}
