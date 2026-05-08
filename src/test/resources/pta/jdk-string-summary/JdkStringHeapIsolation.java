class JdkStringHeapIsolation {

    public static void main(String[] args) {
        String string1 = new String("left");
        String string2 = new String("right");

        StringBuilder builder1 = new StringBuilder();
        StringBuilder builder2 = new StringBuilder();

        StringBuffer buffer1 = new StringBuffer();
        StringBuffer buffer2 = new StringBuffer();
    }
}
