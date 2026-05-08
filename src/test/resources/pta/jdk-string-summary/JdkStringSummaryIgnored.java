class JdkStringSummaryIgnored {

    public static void main(String[] args) {
        String base = new String("prefix");
        String suffix = new String("suffix");
        String concat = base.concat(suffix);

        StringBuilder builder = new StringBuilder();
        builder.append(concat);
        builder.toString();

        StringBuffer buffer = new StringBuffer();
        buffer.append(concat);
        buffer.toString();
    }
}
