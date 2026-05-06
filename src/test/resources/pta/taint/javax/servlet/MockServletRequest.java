package javax.servlet;

public class MockServletRequest implements ServletRequest {

    @Override
    public void setAttribute(String name, Object value) {
    }

    @Override
    public Object getAttribute(String name) {
        return null;
    }
}
