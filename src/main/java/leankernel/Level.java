package leankernel;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/** Universe levels, with normalisation and the equivalence / ordering tests the kernel needs. */
public abstract class Level {
    public enum Kind { ZERO, SUCC, MAX, IMAX, PARAM }

    public final Kind kind;
    private final int hash;
    public final boolean hasParam;

    private Level(Kind kind, int hash, boolean hasParam) {
        this.kind = kind;
        this.hash = hash;
        this.hasParam = hasParam;
    }

    public static final Level ZERO = new Level(Kind.ZERO, 1, false) { };
    public static final Level ONE = succ(ZERO);

    public static final class Succ extends Level {
        public final Level of;
        Succ(Level of) { super(Kind.SUCC, 31 * of.hash + 2, of.hasParam); this.of = of; }
    }

    public static final class Max extends Level {
        public final Level lhs, rhs;
        Max(Level l, Level r) { super(Kind.MAX, Objects.hash(l.hash, r.hash, 3), l.hasParam || r.hasParam); lhs = l; rhs = r; }
    }

    public static final class IMax extends Level {
        public final Level lhs, rhs;
        IMax(Level l, Level r) { super(Kind.IMAX, Objects.hash(l.hash, r.hash, 4), l.hasParam || r.hasParam); lhs = l; rhs = r; }
    }

    public static final class Param extends Level {
        public final Name name;
        Param(Name n) { super(Kind.PARAM, n.hashCode() * 31 + 5, true); name = n; }
    }

    public static Level succ(Level l) { return new Succ(l); }
    public static Level max(Level a, Level b) { return new Max(a, b); }
    public static Level imax(Level a, Level b) { return new IMax(a, b); }
    public static Level param(Name n) { return new Param(n); }

    @Override public int hashCode() { return hash; }

    @Override public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Level)) return false;
        Level b = (Level) o;
        if (hash != b.hash || kind != b.kind) return false;
        switch (kind) {
            case ZERO: return true;
            case SUCC: return ((Succ) this).of.equals(((Succ) b).of);
            case MAX: return ((Max) this).lhs.equals(((Max) b).lhs) && ((Max) this).rhs.equals(((Max) b).rhs);
            case IMAX: return ((IMax) this).lhs.equals(((IMax) b).lhs) && ((IMax) this).rhs.equals(((IMax) b).rhs);
            default: return ((Param) this).name.equals(((Param) b).name);
        }
    }

    // ---- structure helpers -------------------------------------------------

    public boolean isZero() { return kind == Kind.ZERO; }

    /** True if the level can never be zero under any assignment. */
    public boolean isNeverZero() {
        switch (kind) {
            case ZERO: case PARAM: return false;
            case SUCC: return true;
            case MAX: return ((Max) this).lhs.isNeverZero() || ((Max) this).rhs.isNeverZero();
            default: return ((IMax) this).rhs.isNeverZero();
        }
    }

    /** succ^k(zero) for some k? */
    private boolean isExplicit() {
        Level l = this;
        while (l.kind == Kind.SUCC) l = ((Succ) l).of;
        return l.kind == Kind.ZERO;
    }

    private Level base() {
        Level l = this;
        while (l.kind == Kind.SUCC) l = ((Succ) l).of;
        return l;
    }

    private int offset() {
        int k = 0;
        Level l = this;
        while (l.kind == Kind.SUCC) { l = ((Succ) l).of; k++; }
        return k;
    }

    private static Level addOffset(Level l, int k) {
        for (int i = 0; i < k; i++) l = succ(l);
        return l;
    }

    /** Smart imax: keeps the result semantically equal but simplifies trivial cases. */
    public static Level mkIMax(Level a, Level b) {
        if (b.isNeverZero()) return mkMax(a, b);
        if (b.isZero()) return ZERO;
        if (a.isZero()) return b;
        if (a.equals(b)) return a;
        return imax(a, b);
    }

    public static Level mkMax(Level a, Level b) {
        if (a.isZero()) return b;
        if (b.isZero()) return a;
        if (a.equals(b)) return a;
        return max(a, b);
    }

    // ---- instantiation -----------------------------------------------------

    public Level instantiate(List<Name> params, List<Level> args) {
        if (!hasParam) return this;
        switch (kind) {
            case SUCC: return succ(((Succ) this).of.instantiate(params, args));
            case MAX: return mkMax(((Max) this).lhs.instantiate(params, args), ((Max) this).rhs.instantiate(params, args));
            case IMAX: return mkIMax(((IMax) this).lhs.instantiate(params, args), ((IMax) this).rhs.instantiate(params, args));
            case PARAM: {
                Name n = ((Param) this).name;
                for (int i = 0; i < params.size(); i++) if (params.get(i).equals(n)) return args.get(i);
                return this;
            }
            default: return this;
        }
    }

    // ---- normalisation -----------------------------------------------------

    private static void pushMaxArgs(Level l, List<Level> out) {
        if (l.kind == Kind.MAX) {
            pushMaxArgs(((Max) l).lhs, out);
            pushMaxArgs(((Max) l).rhs, out);
        } else out.add(l);
    }

    private static boolean normLt(Level a, Level b) {
        if (a.equals(b)) return false;
        Level l1 = a.base(), l2 = b.base();
        int k1 = a.offset(), k2 = b.offset();
        if (!l1.equals(l2)) {
            if (l1.kind != l2.kind) return l1.kind.ordinal() < l2.kind.ordinal();
            switch (l1.kind) {
                case PARAM: return ((Param) l1).name.compareTo(((Param) l2).name) < 0;
                case MAX: {
                    Max x = (Max) l1, y = (Max) l2;
                    return !x.lhs.equals(y.lhs) ? normLt(x.lhs, y.lhs) : normLt(x.rhs, y.rhs);
                }
                case IMAX: {
                    IMax x = (IMax) l1, y = (IMax) l2;
                    return !x.lhs.equals(y.lhs) ? normLt(x.lhs, y.lhs) : normLt(x.rhs, y.rhs);
                }
                default: return false;
            }
        }
        return k1 < k2;
    }

    public Level normalize() {
        Level r = base();
        int k = offset();
        switch (r.kind) {
            case ZERO: case PARAM: return this;
            case IMAX: {
                Level l1 = ((IMax) r).lhs.normalize(), l2 = ((IMax) r).rhs.normalize();
                return addOffset(mkIMax(l1, l2), k);
            }
            default: break;
        }
        List<Level> todo = new ArrayList<>(), args = new ArrayList<>();
        pushMaxArgs(r, todo);
        for (Level a : todo) pushMaxArgs(a.normalize(), args);
        args.sort((x, y) -> normLt(x, y) ? -1 : normLt(y, x) ? 1 : 0);
        List<Level> rargs = new ArrayList<>();
        int i = 0;
        if (args.get(i).isExplicit()) {
            while (i + 1 < args.size() && args.get(i + 1).isExplicit()) i++;
            int kmax = args.get(i).offset();
            int j = i + 1;
            for (; j < args.size(); j++) if (args.get(j).offset() >= kmax) break;
            if (j < args.size()) i++; // explicit universe is subsumed by succ^k(l)
        }
        rargs.add(args.get(i));
        Level prev = args.get(i);
        i++;
        for (; i < args.size(); i++) {
            Level curr = args.get(i);
            if (prev.base().equals(curr.base())) {
                if (prev.offset() < curr.offset()) {
                    prev = curr;
                    rargs.remove(rargs.size() - 1);
                    rargs.add(curr);
                }
            } else {
                prev = curr;
                rargs.add(curr);
            }
        }
        Level res = addOffset(rargs.get(rargs.size() - 1), k);
        for (int m = rargs.size() - 2; m >= 0; m--) res = max(addOffset(rargs.get(m), k), res);
        return res;
    }

    /** Some parameter occurring in the right-hand side of an imax that does not simplify away, or null. */
    private static Name unresolvedImaxParam(Level l) {
        switch (l.kind) {
            case SUCC: return unresolvedImaxParam(((Succ) l).of);
            case MAX: {
                Name n = unresolvedImaxParam(((Max) l).lhs);
                return n != null ? n : unresolvedImaxParam(((Max) l).rhs);
            }
            case IMAX: {
                IMax m = (IMax) l;
                if (!m.rhs.isNeverZero() && !m.rhs.isZero()) {
                    Name p = anyParam(m.rhs);
                    if (p != null) return p;
                }
                Name n = unresolvedImaxParam(m.lhs);
                return n != null ? n : unresolvedImaxParam(m.rhs);
            }
            default: return null;
        }
    }

    /** A parameter whose value decides whether the level is zero (null if zero-ness is already settled). */
    private static Name anyParam(Level l) {
        switch (l.kind) {
            case MAX: {
                Max m = (Max) l;
                if (m.lhs.isNeverZero() || m.rhs.isNeverZero()) return null;
                Name n = anyParam(m.lhs);
                return n != null ? n : anyParam(m.rhs);
            }
            case IMAX: return anyParam(((IMax) l).rhs);
            case PARAM: return ((Param) l).name;
            default: return null;
        }
    }

    private interface Test { boolean ok(Level a, Level b); }

    /**
     * Decides the test for all assignments. imax only depends on whether its right argument is zero, so
     * we split each such parameter into the cases "zero" and "successor", which removes the imax, and
     * then compare the imax-free normal forms.
     */
    private static boolean forAllCases(Level a, Level b, Test t) {
        Level na = a.normalize(), nb = b.normalize();
        Name p = unresolvedImaxParam(na);
        if (p == null) p = unresolvedImaxParam(nb);
        if (p == null) return t.ok(na, nb);
        List<Name> ps = List.of(p);
        Level zero = Level.ZERO, succP = succ(param(p));
        return forAllCases(na.instantiate(ps, List.of(zero)), nb.instantiate(ps, List.of(zero)), t)
                && forAllCases(na.instantiate(ps, List.of(succP)), nb.instantiate(ps, List.of(succP)), t);
    }

    public boolean isEquiv(Level o) {
        if (this == o || equals(o)) return true;
        return forAllCases(this, o, (x, y) -> x.equals(y));
    }

    /** this >= o for every assignment of the parameters. */
    public boolean isGeq(Level o) {
        return forAllCases(this, o, Level::geqCore);
    }

    private static boolean geqCore(Level l1, Level l2) {
        if (l1.equals(l2) || l2.isZero()) return true;
        if (l2.kind == Kind.MAX) return geqCore(l1, ((Max) l2).lhs) && geqCore(l1, ((Max) l2).rhs);
        if (l1.kind == Kind.MAX && (geqCore(((Max) l1).lhs, l2) || geqCore(((Max) l1).rhs, l2))) return true;
        Level b1 = l1.base(), b2 = l2.base();
        int k1 = l1.offset(), k2 = l2.offset();
        if (b1.equals(b2) || b1.isZero()) return k1 >= k2;
        if (k1 == k2 && k1 > 0) return geqCore(b1, b2);
        return false;
    }

    /** All parameters mentioned are in the given list. */
    public boolean paramsIn(List<Name> declared, Name[] missing) {
        switch (kind) {
            case SUCC: return ((Succ) this).of.paramsIn(declared, missing);
            case MAX: return ((Max) this).lhs.paramsIn(declared, missing) && ((Max) this).rhs.paramsIn(declared, missing);
            case IMAX: return ((IMax) this).lhs.paramsIn(declared, missing) && ((IMax) this).rhs.paramsIn(declared, missing);
            case PARAM:
                if (declared.contains(((Param) this).name)) return true;
                missing[0] = ((Param) this).name;
                return false;
            default: return true;
        }
    }

    @Override public String toString() {
        switch (kind) {
            case ZERO: return "0";
            case SUCC: {
                int k = offset();
                Level b = base();
                return b.isZero() ? Integer.toString(k) : b + "+" + k;
            }
            case MAX: return "max(" + ((Max) this).lhs + "," + ((Max) this).rhs + ")";
            case IMAX: return "imax(" + ((IMax) this).lhs + "," + ((IMax) this).rhs + ")";
            default: return ((Param) this).name.toString();
        }
    }
}
