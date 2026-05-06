class AttributeSummaryRegression {

    public static void main(String[] args) {
        javax.servlet.ServletRequest request = new MockServletRequest();
        request.setAttribute("user", SourceSink.source());
        String positive = (String) request.getAttribute("user");
        SourceSink.sink(positive);

        request.setAttribute("captcha", "safe");
        String negative = (String) request.getAttribute("captcha");
        SourceSink.sink(negative);
    }
}
