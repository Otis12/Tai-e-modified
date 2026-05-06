class MockServletRequest implements javax.servlet.ServletRequest {

    @Override
    public void setAttribute(String name, Object value) {
    }

    @Override
    public Object getAttribute(String name) {
        return null;
    }
}
