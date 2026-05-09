class JdkSummaryOnlyBoundaryMain {

    public static void main(String[] args) {
        String jdkValue = new String("value");
        String jdkResult = jdkValue.toString();

        Object helperInput = new Object();
        Object helperResult = apple.laf.thirdparty.BoundaryHelper.forward(helperInput);

        Object servletInput = new Object();
        javax.servlet.http.HttpServletRequest request =
                new javax.servlet.http.HttpServletRequest();
        Object servletResult = request.forward(servletInput);

        consume(jdkResult, helperResult, servletResult);
    }

    static void consume(Object first, Object second, Object third) {
    }
}
