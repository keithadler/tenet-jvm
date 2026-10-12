package tenet;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The expressions of an export, kept as flat arrays instead of objects: about 17 bytes per node, against
 * roughly 45 for an {@link Expr}. An export refers back to earlier expressions by id for as long as it
 * likes, so a reader has to remember all of them; as objects that is the whole export held in memory
 * (over 12 GB for Mathlib). Here an expression becomes an object only while a declaration that uses it is
 * being read and checked.
 */
final class ExprStore {
    static final byte BVAR = 1, SORT = 2, CONST = 3, APP = 4, LAM = 5, PI = 6, LET = 7, NAT = 8, STR = 9, PROJ = 10, ALIAS = 11;

    private static final String[] BINDER_INFO = {"default", "implicit", "strictImplicit", "instImplicit"};

    private byte[] kind = new byte[1 << 16];
    private int[] a = new int[1 << 16], b = new int[1 << 16], c = new int[1 << 16], d = new int[1 << 16];
    private int size = 0;
    private final List<int[]> levelLists = new ArrayList<>();
    private final List<Object> literals = new ArrayList<>();
    private final ExportReader reader;

    ExprStore(ExportReader reader) {
        this.reader = reader;
        levelLists.add(new int[0]);
    }

    private void ensure(int id) {
        if (id < kind.length) return;
        int n = kind.length;
        while (n <= id) n *= 2;
        kind = Arrays.copyOf(kind, n);
        a = Arrays.copyOf(a, n);
        b = Arrays.copyOf(b, n);
        c = Arrays.copyOf(c, n);
        d = Arrays.copyOf(d, n);
    }

    private void put(int id, byte k, int x, int y, int z, int w) {
        ensure(id);
        kind[id] = k;
        a[id] = x;
        b[id] = y;
        c[id] = z;
        d[id] = w;
        if (id >= size) size = id + 1;
    }

    boolean defined(int id) { return id >= 0 && id < size && kind[id] != 0; }

    static int infoCode(String info) {
        for (int i = 0; i < BINDER_INFO.length; i++) if (BINDER_INFO[i].equals(info)) return i;
        return 0;
    }

    void bvar(int id, int idx) { put(id, BVAR, idx, 0, 0, 0); }
    void sort(int id, int level) { put(id, SORT, level, 0, 0, 0); }
    void cnst(int id, int name, int[] levels) {
        int ll = 0;
        if (levels.length > 0) { ll = levelLists.size(); levelLists.add(levels); }
        put(id, CONST, name, ll, 0, 0);
    }
    void app(int id, int fn, int arg) { put(id, APP, fn, arg, 0, 0); }
    void binder(int id, boolean pi, int name, int type, int body, String info) { put(id, pi ? PI : LAM, name, type, body, infoCode(info)); }
    void let(int id, int name, int type, int value, int body) {
        // four references: keep them in a, b, c and the body in d
        put(id, LET, name, type, value, body);
    }
    void nat(int id, BigInteger v) { literals.add(v); put(id, NAT, literals.size() - 1, 0, 0, 0); }
    void str(int id, String v) { literals.add(v); put(id, STR, literals.size() - 1, 0, 0, 0); }
    void proj(int id, int typeName, int idx, int struct) { put(id, PROJ, typeName, idx, struct, 0); }
    void alias(int id, int target) { put(id, ALIAS, target, 0, 0, 0); }

    // ---- materialisation ---------------------------------------------------

    /** A small open-addressing map from node id to the object built for it, for one declaration. */
    static final class Memo {
        private int[] keys = new int[256];
        private Expr[] vals = new Expr[256];
        private int count = 0;
        Memo() { Arrays.fill(keys, -1); }
        Expr get(int k) {
            int mask = keys.length - 1;
            for (int i = (k * 0x9E3779B1) >>> 7 & mask; keys[i] != -1; i = (i + 1) & mask) if (keys[i] == k) return vals[i];
            return null;
        }
        void put(int k, Expr v) {
            if (count * 2 >= keys.length) grow();
            int mask = keys.length - 1;
            int i = (k * 0x9E3779B1) >>> 7 & mask;
            while (keys[i] != -1 && keys[i] != k) i = (i + 1) & mask;
            if (keys[i] == -1) count++;
            keys[i] = k;
            vals[i] = v;
        }
        private void grow() {
            int[] ok = keys;
            Expr[] ov = vals;
            keys = new int[ok.length * 2];
            vals = new Expr[ok.length * 2];
            Arrays.fill(keys, -1);
            count = 0;
            for (int i = 0; i < ok.length; i++) if (ok[i] != -1) put(ok[i], ov[i]);
        }
    }

    /**
     * The expression with this id as an object. `kept` holds the nodes the environment keeps (types and
     * definition bodies), shared by every declaration; `temp` is a scratch table for one proof term. Nodes
     * found in `kept` are reused either way. Nodes built for a proof (temp != null) go into `temp` only, so
     * they can be collected as soon as the declaration has been checked; all others go into `kept`.
     */
    Expr get(int id, Memo kept, Memo temp) {
        if (!defined(id)) throw new KernelException("undefined expr id " + id);
        Expr hit = kept.get(id);
        if (hit == null && temp != null) hit = temp.get(id);
        if (hit != null) return hit;
        Expr r;
        switch (kind[id]) {
            case ALIAS: r = get(a[id], kept, temp); break;
            case BVAR: r = Expr.bvar(a[id]); break;
            case SORT: r = Expr.sort(reader.levelAt(a[id])); break;
            case CONST: {
                int[] ls = levelLists.get(b[id]);
                List<Level> levels;
                if (ls.length == 0) levels = List.of();
                else {
                    List<Level> l = new ArrayList<>(ls.length);
                    for (int x : ls) l.add(reader.levelAt(x));
                    levels = l;
                }
                r = Expr.cnst(reader.nameAt(a[id]), levels);
                break;
            }
            case APP: r = Expr.app(get(a[id], kept, temp), get(b[id], kept, temp)); break;
            case LAM: r = Expr.lam(reader.nameAt(a[id]), get(b[id], kept, temp), get(c[id], kept, temp), BINDER_INFO[d[id]]); break;
            case PI: r = Expr.pi(reader.nameAt(a[id]), get(b[id], kept, temp), get(c[id], kept, temp), BINDER_INFO[d[id]]); break;
            case LET: r = Expr.let(reader.nameAt(a[id]), get(b[id], kept, temp), get(c[id], kept, temp), get(d[id], kept, temp)); break;
            case NAT: r = Expr.nat((BigInteger) literals.get(a[id])); break;
            case STR: r = Expr.str((String) literals.get(a[id])); break;
            case PROJ: r = Expr.proj(reader.nameAt(a[id]), b[id], get(c[id], kept, temp)); break;
            default: throw new KernelException("corrupt expression store at id " + id);
        }
        (temp != null ? temp : kept).put(id, r);
        return r;
    }

    /** A kept node (type, definition body, ...). */
    Expr get(int id) { return get(id, keptMemo, null); }

    /** A proof term: built into scratch space, reusing kept nodes. */
    Expr getTemp(int id) { return get(id, keptMemo, new Memo()); }

    private final Memo keptMemo = new Memo();

    Expr materialize(int id) { return getTemp(id); }
}
