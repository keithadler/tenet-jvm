package leankernel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Kernel expressions. Binder names and binder infos are carried for display only and are ignored by
 * equality, so structural equality is alpha-equivalence. Metadata is stripped at parse time.
 */
public abstract class Expr {
    public enum Kind { BVAR, FVAR, SORT, CONST, APP, LAM, PI, LET, NAT, STR, PROJ }

    public final Kind kind;
    public final int hash;
    /** One more than the largest loose bound variable index (0 if closed). */
    public final int looseBVarRange;
    public final boolean hasFVar;
    public final boolean hasLevelParam;

    private Expr(Kind kind, int hash, int range, boolean hasFVar, boolean hasLevelParam) {
        this.kind = kind;
        this.hash = hash;
        this.looseBVarRange = range;
        this.hasFVar = hasFVar;
        this.hasLevelParam = hasLevelParam;
    }

    // ---- node types --------------------------------------------------------

    public static final class BVar extends Expr {
        public final int idx;
        BVar(int idx) { super(Kind.BVAR, 1000003 * idx + 7, idx + 1, false, false); this.idx = idx; }
    }

    public static final class FVar extends Expr {
        public final long id;
        FVar(long id) { super(Kind.FVAR, Long.hashCode(id) * 31 + 11, 0, true, false); this.id = id; }
    }

    public static final class Sort extends Expr {
        public final Level level;
        Sort(Level l) { super(Kind.SORT, l.hashCode() * 31 + 13, 0, false, l.hasParam); level = l; }
    }

    public static final class Const extends Expr {
        public final Name name;
        public final List<Level> levels;
        Const(Name n, List<Level> ls) {
            super(Kind.CONST, Objects.hash(n.hashCode(), ls) * 31 + 17, 0, false, ls.stream().anyMatch(x -> x.hasParam));
            name = n;
            levels = ls;
        }
    }

    public static final class App extends Expr {
        public final Expr fn, arg;
        App(Expr f, Expr a) {
            super(Kind.APP, (f.hash * 31 + a.hash) * 31 + 19, Math.max(f.looseBVarRange, a.looseBVarRange),
                    f.hasFVar || a.hasFVar, f.hasLevelParam || a.hasLevelParam);
            fn = f;
            arg = a;
        }
    }

    public static final class Binder extends Expr {
        public final Name name;
        public final Expr type, body;
        public final String info;
        Binder(Kind k, Name n, Expr t, Expr b, String info) {
            super(k, (t.hash * 31 + b.hash) * 31 + (k == Kind.LAM ? 23 : 29), Math.max(t.looseBVarRange, Math.max(0, b.looseBVarRange - 1)),
                    t.hasFVar || b.hasFVar, t.hasLevelParam || b.hasLevelParam);
            name = n;
            type = t;
            body = b;
            this.info = info;
        }
    }

    public static final class Let extends Expr {
        public final Name name;
        public final Expr type, value, body;
        Let(Name n, Expr t, Expr v, Expr b) {
            super(Kind.LET, ((t.hash * 31 + v.hash) * 31 + b.hash) * 31 + 37,
                    Math.max(Math.max(t.looseBVarRange, v.looseBVarRange), Math.max(0, b.looseBVarRange - 1)),
                    t.hasFVar || v.hasFVar || b.hasFVar, t.hasLevelParam || v.hasLevelParam || b.hasLevelParam);
            name = n;
            type = t;
            value = v;
            body = b;
        }
    }

    public static final class NatLit extends Expr {
        public final BigInteger val;
        NatLit(BigInteger v) { super(Kind.NAT, v.hashCode() * 31 + 41, 0, false, false); val = v; }
    }

    public static final class StrLit extends Expr {
        public final String val;
        StrLit(String v) { super(Kind.STR, v.hashCode() * 31 + 43, 0, false, false); val = v; }
    }

    public static final class Proj extends Expr {
        public final Name typeName;
        public final int idx;
        public final Expr struct;
        Proj(Name t, int i, Expr s) {
            super(Kind.PROJ, (Objects.hash(t.hashCode(), i) * 31 + s.hash) * 31 + 47, s.looseBVarRange, s.hasFVar, s.hasLevelParam);
            typeName = t;
            idx = i;
            struct = s;
        }
    }

    // ---- constructors ------------------------------------------------------

    private static final BVar[] SMALL_BVARS = new BVar[64];
    static { for (int i = 0; i < SMALL_BVARS.length; i++) SMALL_BVARS[i] = new BVar(i); }

    public static Expr bvar(int i) { return i < SMALL_BVARS.length ? SMALL_BVARS[i] : new BVar(i); }
    public static Expr fvar(long id) { return new FVar(id); }
    public static Expr sort(Level l) { return new Sort(l); }
    public static Expr cnst(Name n, List<Level> ls) { return new Const(n, ls); }
    public static Expr app(Expr f, Expr a) { return new App(f, a); }
    public static Expr lam(Name n, Expr t, Expr b, String info) { return new Binder(Kind.LAM, n, t, b, info); }
    public static Expr pi(Name n, Expr t, Expr b, String info) { return new Binder(Kind.PI, n, t, b, info); }
    public static Expr let(Name n, Expr t, Expr v, Expr b) { return new Let(n, t, v, b); }
    public static Expr nat(BigInteger v) { return new NatLit(v); }
    public static Expr nat(long v) { return new NatLit(BigInteger.valueOf(v)); }
    public static Expr str(String s) { return new StrLit(s); }
    public static Expr proj(Name t, int i, Expr s) { return new Proj(t, i, s); }

    public static Expr apps(Expr f, List<Expr> args) {
        for (Expr a : args) f = app(f, a);
        return f;
    }

    public static Expr apps(Expr f, Expr... args) {
        for (Expr a : args) f = app(f, a);
        return f;
    }

    // ---- equality ----------------------------------------------------------

    @Override public int hashCode() { return hash; }

    @Override public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Expr)) return false;
        return eq(this, (Expr) o);
    }

    /** Structural equality up to binder names; iterative along the spine to avoid deep recursion. */
    private static boolean eq(Expr a, Expr b) {
        while (true) {
            if (a == b) return true;
            if (a.hash != b.hash || a.kind != b.kind) return false;
            switch (a.kind) {
                case BVAR: return ((BVar) a).idx == ((BVar) b).idx;
                case FVAR: return ((FVar) a).id == ((FVar) b).id;
                case SORT: return ((Sort) a).level.equals(((Sort) b).level);
                case CONST: return ((Const) a).name.equals(((Const) b).name) && ((Const) a).levels.equals(((Const) b).levels);
                case NAT: return ((NatLit) a).val.equals(((NatLit) b).val);
                case STR: return ((StrLit) a).val.equals(((StrLit) b).val);
                case APP: {
                    App x = (App) a, y = (App) b;
                    if (!eq(x.arg, y.arg)) return false;
                    a = x.fn;
                    b = y.fn;
                    break;
                }
                case LAM: case PI: {
                    Binder x = (Binder) a, y = (Binder) b;
                    if (!eq(x.type, y.type)) return false;
                    a = x.body;
                    b = y.body;
                    break;
                }
                case LET: {
                    Let x = (Let) a, y = (Let) b;
                    if (!eq(x.type, y.type) || !eq(x.value, y.value)) return false;
                    a = x.body;
                    b = y.body;
                    break;
                }
                default: {
                    Proj x = (Proj) a, y = (Proj) b;
                    if (x.idx != y.idx || !x.typeName.equals(y.typeName)) return false;
                    a = x.struct;
                    b = y.struct;
                }
            }
        }
    }

    // ---- application spine helpers ----------------------------------------

    public Expr getAppFn() {
        Expr e = this;
        while (e.kind == Kind.APP) e = ((App) e).fn;
        return e;
    }

    public int getAppNumArgs() {
        int n = 0;
        Expr e = this;
        while (e.kind == Kind.APP) { e = ((App) e).fn; n++; }
        return n;
    }

    public List<Expr> getAppArgs() {
        int n = getAppNumArgs();
        Expr[] arr = new Expr[n];
        Expr e = this;
        for (int i = n - 1; i >= 0; i--) { arr[i] = ((App) e).arg; e = ((App) e).fn; }
        List<Expr> out = new ArrayList<>(n);
        for (Expr x : arr) out.add(x);
        return out;
    }

    public boolean isConstOf(Name n) { return kind == Kind.CONST && ((Const) this).name.equals(n); }

    // ---- generic traversal with offset ------------------------------------

    /** Replaces sub-expressions; fn returns null to recurse. Offset counts the binders crossed. */
    public interface Replacer { Expr apply(Expr e, int offset); }

    private static final class Key {
        final Expr e;
        final int off;
        Key(Expr e, int off) { this.e = e; this.off = off; }
        @Override public int hashCode() { return System.identityHashCode(e) * 31 + off; }
        @Override public boolean equals(Object o) { return o instanceof Key && ((Key) o).e == e && ((Key) o).off == off; }
    }

    public static Expr replace(Expr e, Replacer f) { return replace(e, 0, f, new HashMap<>()); }

    private static Expr replace(Expr e, int off, Replacer f, Map<Key, Expr> cache) {
        Expr r = f.apply(e, off);
        if (r != null) return r;
        boolean shared = e.kind == Kind.APP || e.kind == Kind.LAM || e.kind == Kind.PI || e.kind == Kind.LET || e.kind == Kind.PROJ;
        Key k = null;
        if (shared) {
            k = new Key(e, off);
            Expr c = cache.get(k);
            if (c != null) return c;
        }
        Expr res;
        switch (e.kind) {
            case APP: {
                App a = (App) e;
                Expr nf = replace(a.fn, off, f, cache), na = replace(a.arg, off, f, cache);
                res = nf == a.fn && na == a.arg ? e : app(nf, na);
                break;
            }
            case LAM: case PI: {
                Binder b = (Binder) e;
                Expr nt = replace(b.type, off, f, cache), nb = replace(b.body, off + 1, f, cache);
                res = nt == b.type && nb == b.body ? e : new Binder(b.kind, b.name, nt, nb, b.info);
                break;
            }
            case LET: {
                Let l = (Let) e;
                Expr nt = replace(l.type, off, f, cache), nv = replace(l.value, off, f, cache), nb = replace(l.body, off + 1, f, cache);
                res = nt == l.type && nv == l.value && nb == l.body ? e : new Let(l.name, nt, nv, nb);
                break;
            }
            case PROJ: {
                Proj p = (Proj) e;
                Expr ns = replace(p.struct, off, f, cache);
                res = ns == p.struct ? e : new Proj(p.typeName, p.idx, ns);
                break;
            }
            default: res = e;
        }
        if (shared) cache.put(k, res);
        return res;
    }

    // ---- bound-variable operations ----------------------------------------

    /** Replaces loose bvar i (i < subst.length) by subst[subst.length-1-i]; shifts the rest down. */
    public static Expr instantiateRev(Expr e, Expr[] subst) {
        if (e.looseBVarRange == 0 || subst.length == 0) return e;
        final int n = subst.length;
        return replace(e, (x, off) -> {
            if (x.looseBVarRange <= off) return x;
            if (x.kind == Kind.BVAR) {
                int i = ((BVar) x).idx;
                if (i < off) return x;
                if (i < off + n) return liftLooseBVars(subst[n - 1 - (i - off)], 0, off);
                return bvar(i - n);
            }
            return null;
        });
    }

    /** Replaces loose bvar i by subst[i]. */
    public static Expr instantiate(Expr e, Expr[] subst) {
        if (e.looseBVarRange == 0 || subst.length == 0) return e;
        final int n = subst.length;
        return replace(e, (x, off) -> {
            if (x.looseBVarRange <= off) return x;
            if (x.kind == Kind.BVAR) {
                int i = ((BVar) x).idx;
                if (i < off) return x;
                if (i < off + n) return liftLooseBVars(subst[i - off], 0, off);
                return bvar(i - n);
            }
            return null;
        });
    }

    public static Expr instantiate1(Expr e, Expr v) { return instantiate(e, new Expr[] {v}); }

    /** Adds d to every loose bvar index >= s. */
    public static Expr liftLooseBVars(Expr e, int s, int d) {
        if (d == 0 || e.looseBVarRange <= s) return e;
        return replace(e, (x, off) -> {
            if (x.looseBVarRange <= s + off) return x;
            if (x.kind == Kind.BVAR) return bvar(((BVar) x).idx + d);
            return null;
        });
    }

    /** Subtracts d from every loose bvar index >= s (caller guarantees no capture). */
    public static Expr lowerLooseBVars(Expr e, int s, int d) {
        if (d == 0 || e.looseBVarRange <= s) return e;
        return replace(e, (x, off) -> {
            if (x.looseBVarRange <= s + off) return x;
            if (x.kind == Kind.BVAR) return bvar(((BVar) x).idx - d);
            return null;
        });
    }

    public static boolean hasLooseBVar(Expr e, int i) {
        if (e.looseBVarRange <= i) return false;
        switch (e.kind) {
            case BVAR: return ((BVar) e).idx == i;
            case APP: return hasLooseBVar(((App) e).fn, i) || hasLooseBVar(((App) e).arg, i);
            case LAM: case PI: return hasLooseBVar(((Binder) e).type, i) || hasLooseBVar(((Binder) e).body, i + 1);
            case LET: return hasLooseBVar(((Let) e).type, i) || hasLooseBVar(((Let) e).value, i) || hasLooseBVar(((Let) e).body, i + 1);
            case PROJ: return hasLooseBVar(((Proj) e).struct, i);
            default: return false;
        }
    }

    /** Replaces fvars[i] by bvar (n-1-i) (plus binder offset); inverse of instantiateRev on fvars. */
    public static Expr abstractFVars(Expr e, long[] ids) {
        if (!e.hasFVar || ids.length == 0) return e;
        final int n = ids.length;
        return replace(e, (x, off) -> {
            if (!x.hasFVar) return x;
            if (x.kind == Kind.FVAR) {
                long id = ((FVar) x).id;
                for (int i = n - 1; i >= 0; i--) if (ids[i] == id) return bvar(off + n - 1 - i);
                return x;
            }
            return null;
        });
    }

    public static Expr instantiateLevelParams(Expr e, List<Name> params, List<Level> args) {
        if (!e.hasLevelParam || params.isEmpty()) return e;
        return replace(e, (x, off) -> {
            if (!x.hasLevelParam) return x;
            if (x.kind == Kind.SORT) return sort(((Sort) x).level.instantiate(params, args));
            if (x.kind == Kind.CONST) {
                Const c = (Const) x;
                List<Level> ls = new ArrayList<>(c.levels.size());
                for (Level l : c.levels) ls.add(l.instantiate(params, args));
                return cnst(c.name, ls);
            }
            return null;
        });
    }

    /** Beta-reduces head application f a1..an where f is a lambda (as many steps as there are lambdas). */
    public static Expr betaRev(Expr f, List<Expr> argsRev) {
        // argsRev is in application order (first argument first)
        int n = argsRev.size();
        int i = 0;
        Expr body = f;
        while (body.kind == Kind.LAM && i < n) { body = ((Binder) body).body; i++; }
        if (i == 0) return apps(f, argsRev);
        Expr[] sub = new Expr[i];
        for (int j = 0; j < i; j++) sub[j] = argsRev.get(j);
        Expr r = instantiateRev(body, sub);
        for (int j = i; j < n; j++) r = app(r, argsRev.get(j));
        return r;
    }

    @Override public String toString() { return Printer.show(this); }
}
