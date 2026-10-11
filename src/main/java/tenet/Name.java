package tenet;

import java.util.Objects;

/** Hierarchical name: anonymous, a string component, or a numeric component. */
public final class Name {
    public static final Name ANON = new Name(null, null, 0);

    public final Name pre;
    public final String str; // null for numeric components and anonymous
    public final long num;
    private final int hash;

    private Name(Name pre, String str, long num) {
        this.pre = pre;
        this.str = str;
        this.num = num;
        this.hash = pre == null ? 17 : Objects.hash(pre.hash, str, num);
    }

    public static Name str(Name pre, String s) { return new Name(pre, s, 0); }
    public static Name num(Name pre, long n) { return new Name(pre, null, n); }

    /** Parses a dotted name such as "Nat.add" (string components only). */
    public static Name of(String dotted) {
        Name n = ANON;
        for (String part : dotted.split("\\.")) n = str(n, part);
        return n;
    }

    public boolean isAnon() { return pre == null; }

    @Override public int hashCode() { return hash; }

    @Override public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Name)) return false;
        Name a = this, b = (Name) o;
        while (a != b) {
            if (a == null || b == null) return false;
            if (a.hash != b.hash) return false;
            if (a.pre == null || b.pre == null) return a.pre == b.pre;
            if (a.num != b.num || !Objects.equals(a.str, b.str)) return false;
            a = a.pre;
            b = b.pre;
        }
        return true;
    }

    /** Total order used to sort levels into normal form. */
    public int compareTo(Name o) {
        if (this == o) return 0;
        String a = toString(), b = o.toString();
        return a.compareTo(b);
    }

    @Override public String toString() {
        if (pre == null) return "[anonymous]";
        StringBuilder sb = new StringBuilder();
        build(sb);
        return sb.toString();
    }

    private void build(StringBuilder sb) {
        if (pre.pre != null) {
            pre.build(sb);
            sb.append('.');
        }
        if (str != null) sb.append(str); else sb.append(num);
    }
}
