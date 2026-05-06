package jakarta.servlet.http;

public interface HttpSession {

    void setAttribute(String name, Object value);

    Object getAttribute(String name);
}
