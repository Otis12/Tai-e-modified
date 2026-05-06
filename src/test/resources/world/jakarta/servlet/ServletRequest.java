package jakarta.servlet;

public interface ServletRequest {

    void setAttribute(String name, Object value);

    Object getAttribute(String name);
}
