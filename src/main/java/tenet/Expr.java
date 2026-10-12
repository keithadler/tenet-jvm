package tenet;

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

    static int mix(int a, int b) {
        int h = a * 0x9E3779B1 + b;
        h ^= h >>> 15;
        h *= 0x85EBCA6B;
        h ^= h >>> 13;
        return h;
    }

    // ---- node types --------------------------------------------------------

    public static final class BVar extends Expr {
        public final int idx;
        BVar(int idx) { super(Kind.BVAR, mix(idx, 7), idx + 1, false, false); this.idx = idx; }
    }

    public static final class FVar extends Expr {
        public final long id;
        FVar(long id) { super(Kind.FVAR, mix(Long.hashCode(id), 11), 0, true, false); this.id = id; }
    }

    public static final class Sort extends Expr {
        public final Level level;
        Sort(Level l) { super(Kind.SORT, mix(l.hashCode(), 13), 0, false, l.hasParam); level = l; }
    }

    public static final class Const extends Expr {
        public final Name name;
        public final List<Level> levels;
        Const(Name n, List<Level> ls) {
            super(Kind.CONST, mix(mix(n.hashCode(), ls.hashCode()), 17), 0, false, ls.stream().anyMatch(x -> x.hasParam));
            name = n;
            levels = ls;
        }
    }

    public static final class App extends Expr {
        public final Expr fn, arg;
        App(Expr f, Expr a) {
            super(Kind.APP, mix(mix(f.hash, a.hash), 19), Math.max(f.looseBVarRange, a.looseBVarRange),
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
            super(k, mix(mix(t.hash, b.hash), k == Kind.LAM ? 23 : 29), Math.max(t.looseBVarRange, Math.max(0, b.looseBVarRange - 1)),
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
            super(Kind.LET, mix(mix(mix(t.hash, v.hash), b.hash), 37),
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
        NatLit(BigInteger v) { super(Kind.NAT, mix(v.hashCode(), 41), 0, false, false); val = v; }
    }

    public static final class StrLit extends Expr {
        public final String val;
        StrLit(String v) { super(Kind.STR, mix(v.hashCode(), 43), 0, false, false); val = v; }
    }

    public static final class Proj extends Expr {
        public final Name typeName;
        public final int idx;
        public final Expr struct;
        Proj(Name t, int i, Expr s) {
            super(Kind.PROJ, mix(mix(mix(t.hashCode(), i), s.hash), 47), s.looseBVarRange, s.hasFVar, s.hasLevelParam);
            typeName = t;
            idx = i;
            struct = s;
        }
    }

    // ---- constructors ------------------------------------------------------

    private static final BVar[] SMALL_BVARS = new BVar[64];
    static { for (int i = 0; i < SMALL_BVARS.length; i++) SMALL_BVARS[i] = new BVar(i); }

    public static Expr bvar(int i) { return i < SMALL_BVARS.length ? SMALL_BVARS[i] : share(new BVar(i)); }
    public static Expr fvar(long id) { return share(new FVar(id)); }
    public static Expr sort(Level l) { return share(new Sort(l)); }
    public static Expr cnst(Name n, List<Level> ls) { return share(new Const(n, ls)); }
    public static Expr app(Expr f, Expr a) { return share(new App(f, a)); }
    public static Expr lam(Name n, Expr t, Expr b, String info) { return share(new Binder(Kind.LAM, n, t, b, info)); }
    public static Expr pi(Name n, Expr t, Expr b, String info) { return share(new Binder(Kind.PI, n, t, b, info)); }
    public static Expr let(Name n, Expr t, Expr v, Expr b) { return share(new Let(n, t, v, b)); }
    public static Expr nat(BigInteger v) { return share(new NatLit(v)); }
    public static Expr nat(long v) { return nat(BigInteger.valueOf(v)); }
    public static Expr str(String s) { return share(new StrLit(s)); }
    public static Expr proj(Name t, int i, Expr s) { return share(new Proj(t, i, s)); }

    public static Expr apps(Expr f, List<Expr> args) {
        for (Expr a : args) f = app(f, a);
        return f;
    }

    public static Expr apps(Expr f, Expr... args) {
        for (Expr a : args) f = app(f, a);
        return f;
    }

    // ---- sharing -----------------------------------------------------------
    //
    // A fixed, direct-mapped table makes most structurally equal terms the same object, so that cache
    // lookups usually succeed on a pointer comparison. It is lossy by design (a colliding entry is simply
    // overwritten), costs one array access per node built, and never grows. Terms that miss the table
    // are still compared structurally, so this affects speed only, never results.

    private static final int SHARE_BITS = Integer.getInteger("tenet.share.bits", 18);
    private static final Expr[] SHARE = new Expr[SHARE_BITS == 0 ? 1 : 1 << SHARE_BITS];

    private static boolean shallowEq(Expr a, Expr b) {
        if (a.kind != b.kind || a.hash != b.hash) return false;
        switch (a.kind) {
            case BVAR: return ((BVar) a).idx == ((BVar) b).idx;
            case FVAR: return ((FVar) a).id == ((FVar) b).id;
            case SORT: return ((Sort) a).level.equals(((Sort) b).level);
            case CONST: return ((Const) a).name.equals(((Const) b).name) && ((Const) a).levels.equals(((Const) b).levels);
            case NAT: return ((NatLit) a).val.equals(((NatLit) b).val);
            case STR: return ((StrLit) a).val.equals(((StrLit) b).val);
            case APP: return ((App) a).fn == ((App) b).fn && ((App) a).arg == ((App) b).arg;
            case LAM: case PI: return ((Binder) a).type == ((Binder) b).type && ((Binder) a).body == ((Binder) b).body;
            case LET: return ((Let) a).type == ((Let) b).type && ((Let) a).value == ((Let) b).value && ((Let) a).body == ((Let) b).body;
            default: return ((Proj) a).idx == ((Proj) b).idx && ((Proj) a).typeName.equals(((Proj) b).typeName) && ((Proj) a).struct == ((Proj) b).struct;
        }
    }

    private static Expr share(Expr c) {
        if (SHARE_BITS == 0) return c;
        int i = (c.hash * 0x9E3779B9) >>> (32 - SHARE_BITS);
        Expr e = SHARE[i];
        if (e != null && shallowEq(e, c)) return e;
        SHARE[i] = c;
        return c;
    }

    // ---- equality ----------------------------------------------------------

    @Override public int hashCode() { return hash; }

    @Override public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Expr)) return false;
        Expr b = (Expr) o;
        if (hash != b.hash || kind != b.kind) return false;
        return eq(this, b);
    }

    private static final class Pair {
        final Expr a, b;
        Pair(Expr a, Expr b) { this.a = a; this.b = b; }
        @Override public int hashCode() { return System.identityHashCode(a) * 31 + System.identityHashCode(b); }
        @Override public boolean equals(Object o) { return o instanceof Pair && ((Pair) o).a == a && ((Pair) o).b == b; }
    }

    private static final int EQ_BUDGET = 256;

    /**
     * Structural equality up to binder names. Terms are DAGs, so a naive walk of two isomorphic but
     * unshared copies is exponential; after a small budget of steps we switch to a walk that remembers
     * the pairs of nodes it has already proved equal.
     */
    private static boolean eq(Expr a, Expr b) {
        int[] budget = {EQ_BUDGET};
        int r = eqBounded(a, b, budget);
        if (r != 2) return r == 1;
        java.util.Set<Pair> done = new java.util.HashSet<>();
        boolean res = eqMemo(a, b, done);
        if (res) rememberEqual(done);
        return res;
    }

    /**
     * Pairs of nodes (by identity) already proved structurally equal. Terms are immutable, so such a fact never
     * becomes false; remembering it spares the next comparison of two big, unshared but equal copies from
     * walking them again. Bounded: when full it is simply emptied.
     */
    private static java.util.Set<Pair> KNOWN_EQUAL = new java.util.HashSet<>();

    /** Forgets the persistent equal-pairs memo; called between declarations so it cannot grow without bound. */
    static void forgetKnownEqual() {
        if (KNOWN_EQUAL.size() > 1000) KNOWN_EQUAL = new java.util.HashSet<>(); else KNOWN_EQUAL.clear();
    }
    private static final int KNOWN_EQUAL_CAP = 4_000_000;

    private static void rememberEqual(java.util.Set<Pair> done) {
        if (KNOWN_EQUAL.size() + done.size() > KNOWN_EQUAL_CAP) KNOWN_EQUAL.clear();
        KNOWN_EQUAL.addAll(done);
    }

    /** 1 equal, 0 different, 2 budget exhausted. */
    private static int eqBounded(Expr a, Expr b, int[] budget) {
        while (true) {
            if (a == b) return 1;
            if (a.hash != b.hash || a.kind != b.kind) return 0;
            if (--budget[0] < 0) return 2;
            switch (a.kind) {
                case BVAR: return ((BVar) a).idx == ((BVar) b).idx ? 1 : 0;
                case FVAR: return ((FVar) a).id == ((FVar) b).id ? 1 : 0;
                case SORT: return ((Sort) a).level.equals(((Sort) b).level) ? 1 : 0;
                case CONST: return ((Const) a).name.equals(((Const) b).name) && ((Const) a).levels.equals(((Const) b).levels) ? 1 : 0;
                case NAT: return ((NatLit) a).val.equals(((NatLit) b).val) ? 1 : 0;
                case STR: return ((StrLit) a).val.equals(((StrLit) b).val) ? 1 : 0;
                case APP: {
                    App x = (App) a, y = (App) b;
                    int r = eqBounded(x.arg, y.arg, budget);
                    if (r != 1) return r;
                    a = x.fn;
                    b = y.fn;
                    break;
                }
                case LAM: case PI: {
                    Binder x = (Binder) a, y = (Binder) b;
                    int r = eqBounded(x.type, y.type, budget);
                    if (r != 1) return r;
                    a = x.body;
                    b = y.body;
                    break;
                }
                case LET: {
                    Let x = (Let) a, y = (Let) b;
                    int r = eqBounded(x.type, y.type, budget);
                    if (r != 1) return r;
                    r = eqBounded(x.value, y.value, budget);
                    if (r != 1) return r;
                    a = x.body;
                    b = y.body;
                    break;
                }
                default: {
                    Proj x = (Proj) a, y = (Proj) b;
                    if (x.idx != y.idx || !x.typeName.equals(y.typeName)) return 0;
                    a = x.struct;
                    b = y.struct;
                }
            }
        }
    }

    private static boolean eqMemo(Expr a, Expr b, java.util.Set<Pair> done) {
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
                default: break;
            }
            Pair pr = new Pair(a, b);
            if (KNOWN_EQUAL.contains(pr)) return true;
            if (!done.add(pr)) return true; // being proved higher up in this walk: cannot differ on a DAG
            switch (a.kind) {
                case APP: {
                    App x = (App) a, y = (App) b;
                    if (!eqMemo(x.arg, y.arg, done)) return false;
                    a = x.fn;
                    b = y.fn;
                    break;
                }
                case LAM: case PI: {
                    Binder x = (Binder) a, y = (Binder) b;
                    if (!eqMemo(x.type, y.type, done)) return false;
                    a = x.body;
                    b = y.body;
                    break;
                }
                case LET: {
                    Let x = (Let) a, y = (Let) b;
                    if (!eqMemo(x.type, y.type, done) || !eqMemo(x.value, y.value, done)) return false;
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

    private static final class BudgetExceeded extends RuntimeException {
        private static final long serialVersionUID = 1L;
        BudgetExceeded() { super(null, null, false, false); }
    }

    private static final BudgetExceeded BUDGET_EXCEEDED = new BudgetExceeded();
    private static final int REPLACE_UNCACHED_BUDGET = 4096;

    /**
     * Rebuilds e, letting f replace sub-terms. Small terms are walked without any bookkeeping; if the walk
     * turns out to be large (where shared sub-terms could otherwise be revisited exponentially often) it is
     * restarted with a cache keyed on node identity and binder depth.
     */
    public static Expr replace(Expr e, Replacer f) {
        try {
            return replaceFast(e, 0, f, new int[] {REPLACE_UNCACHED_BUDGET});
        } catch (BudgetExceeded x) {
            return replace(e, 0, f, new HashMap<>());
        }
    }

    private static Expr replaceFast(Expr e, int off, Replacer f, int[] budget) {
        Expr r = f.apply(e, off);
        if (r != null) return r;
        switch (e.kind) {
            case APP: {
                if (--budget[0] < 0) throw BUDGET_EXCEEDED;
                App a = (App) e;
                Expr nf = replaceFast(a.fn, off, f, budget), na = replaceFast(a.arg, off, f, budget);
                return nf == a.fn && na == a.arg ? e : app(nf, na);
            }
            case LAM: case PI: {
                if (--budget[0] < 0) throw BUDGET_EXCEEDED;
                Binder b = (Binder) e;
                Expr nt = replaceFast(b.type, off, f, budget), nb = replaceFast(b.body, off + 1, f, budget);
                return nt == b.type && nb == b.body ? e : (b.kind == Kind.LAM ? lam(b.name, nt, nb, b.info) : pi(b.name, nt, nb, b.info));
            }
            case LET: {
                if (--budget[0] < 0) throw BUDGET_EXCEEDED;
                Let l = (Let) e;
                Expr nt = replaceFast(l.type, off, f, budget), nv = replaceFast(l.value, off, f, budget), nb = replaceFast(l.body, off + 1, f, budget);
                return nt == l.type && nv == l.value && nb == l.body ? e : let(l.name, nt, nv, nb);
            }
            case PROJ: {
                if (--budget[0] < 0) throw BUDGET_EXCEEDED;
                Proj p = (Proj) e;
                Expr ns = replaceFast(p.struct, off, f, budget);
                return ns == p.struct ? e : proj(p.typeName, p.idx, ns);
            }
            default: return e;
        }
    }

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
                res = nt == b.type && nb == b.body ? e : (b.kind == Kind.LAM ? lam(b.name, nt, nb, b.info) : pi(b.name, nt, nb, b.info));
                break;
            }
            case LET: {
                Let l = (Let) e;
                Expr nt = replace(l.type, off, f, cache), nv = replace(l.value, off, f, cache), nb = replace(l.body, off + 1, f, cache);
                res = nt == l.type && nv == l.value && nb == l.body ? e : let(l.name, nt, nv, nb);
                break;
            }
            case PROJ: {
                Proj p = (Proj) e;
                Expr ns = replace(p.struct, off, f, cache);
                res = ns == p.struct ? e : proj(p.typeName, p.idx, ns);
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
