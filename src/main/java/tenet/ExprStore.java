package tenet;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The expressions of an export, kept as flat primitive arrays indexed by the export's own ids instead of as
 * objects. An export refers back to earlier expressions by id for as long as it likes, so a reader has to
 * remember all of them; as objects that is the whole export held in memory. Here a node costs about 10.6
 * bytes on average (a kind byte and two ints, plus two or three more ints in a side table for the binders,
 * lets, projections and constants that need them), and an expression becomes an object only while a
 * declaration that uses it is being checked.
 *
 * <p>The arrays are kept in chunks of 2^20 entries, so the store grows by allocating one more chunk, never by
 * copying everything into an array twice as big, and is not limited to the 2^30 ids a doubling int array
 * would reach.
 *
 * <p>Objects built from the store for declaration types and bodies are memoised by id in {@link #kept} so that
 * a declaration sees one shared object per node. That memo is a cache, not the store: once it holds more than
 * {@link #KEEP_LIMIT} nodes it is dropped between two declarations and refilled on demand. Nothing in the
 * environment holds on to these objects (a declaration holds ids, see {@link Term}), so dropping it frees them.
 */
final class ExprStore {
    static final byte BVAR = 1, SORT = 2, CONST = 3, APP = 4, LET = 5, NAT = 6, STR = 7, PROJ = 8, ALIAS = 9;
    /** LAM + binder info code (0..3) and PI + binder info code. */
    static final byte LAM = 16, PI = 24;

    private static final String[] BINDER_INFO = {"default", "implicit", "strictImplicit", "instImplicit"};

    private static final int BITS = 20, CHUNK = 1 << BITS, MASK = CHUNK - 1;

    /** Kept-memo size (in nodes) above which it is dropped between declarations. */
    static final int KEEP_LIMIT = Integer.getInteger("tenet.keep", 1 << 21);

    private byte[][] kind = new byte[16][];
    private int[][] a = new int[16][], b = new int[16][];
    private int size = 0;
    /** Extra fields: [type, body] for binders, [type, value, body] for let, [idx, struct] for proj, [n, l1..ln] for const. */
    private final IntList extra = new IntList();
    private final List<Object> literals = new ArrayList<>();
    private final ExportReader reader;

    ExprStore(ExportReader reader) {
        this.reader = reader;
    }

    private void put(int id, byte k, int x, int y) {
        int c = id >>> BITS;
        if (c >= kind.length) {
            int n = Math.max(kind.length * 2, c + 1);
            kind = Arrays.copyOf(kind, n);
            a = Arrays.copyOf(a, n);
            b = Arrays.copyOf(b, n);
        }
        if (kind[c] == null) {
            kind[c] = new byte[CHUNK];
            a[c] = new int[CHUNK];
            b[c] = new int[CHUNK];
        }
        int o = id & MASK;
        kind[c][o] = k;
        a[c][o] = x;
        b[c][o] = y;
        if (id >= size) size = id + 1;
    }

    private byte kindAt(int id) { return kind[id >>> BITS][id & MASK]; }
    private int aAt(int id) { return a[id >>> BITS][id & MASK]; }
    private int bAt(int id) { return b[id >>> BITS][id & MASK]; }

    boolean defined(int id) {
        if (id < 0 || id >= size) return false;
        byte[] k = kind[id >>> BITS];
        return k != null && k[id & MASK] != 0;
    }

    static int infoCode(String info) {
        for (int i = 0; i < BINDER_INFO.length; i++) if (BINDER_INFO[i].equals(info)) return i;
        return 0;
    }

    void bvar(int id, int idx) { put(id, BVAR, idx, 0); }
    void sort(int id, int level) { put(id, SORT, level, 0); }
    void cnst(int id, int name, int[] levels) {
        int off = -1;
        if (levels.length > 0) {
            off = extra.add(levels.length);
            for (int l : levels) extra.add(l);
        }
        put(id, CONST, name, off);
    }
    void app(int id, int fn, int arg) { put(id, APP, fn, arg); }
    void binder(int id, boolean pi, int name, int type, int body, String info) {
        int off = extra.add(type);
        extra.add(body);
        put(id, (byte) ((pi ? PI : LAM) + infoCode(info)), name, off);
    }
    void let(int id, int name, int type, int value, int body) {
        int off = extra.add(type);
        extra.add(value);
        extra.add(body);
        put(id, LET, name, off);
    }
    void nat(int id, BigInteger v) { literals.add(v); put(id, NAT, literals.size() - 1, 0); }
    void str(int id, String v) { literals.add(v); put(id, STR, literals.size() - 1, 0); }
    void proj(int id, int typeName, int idx, int struct) {
        int off = extra.add(idx);
        extra.add(struct);
        put(id, PROJ, typeName, off);
    }
    void alias(int id, int target) { put(id, ALIAS, target, 0); }

    /** Number of expression ids in use (one more than the largest). */
    int size() { return size; }

    /** Bytes held by the primitive arrays, for diagnostics. */
    long footprint() {
        long n = 0;
        for (byte[] k : kind) if (k != null) n += CHUNK * 9L;
        return n + extra.footprint();
    }

    // ---- materialisation ---------------------------------------------------

    /** A small open-addressing map from node id to the object built for it. */
    static final class Memo {
        private int[] keys = new int[256];
        private Expr[] vals = new Expr[256];
        private int count = 0;
        Memo() { Arrays.fill(keys, -1); }
        int size() { return count; }
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
            if (keys.length >= 1 << 30) throw new KernelException("a single declaration has more than 2^29 distinct expression nodes");
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
     * The expression with this id as an object. `kept` holds the nodes of declaration types and bodies, shared
     * by every declaration until it is dropped; `temp` is a scratch table for one proof term. Nodes found in
     * `kept` are reused either way. Nodes built for a proof (temp != null) go into `temp` only, so they can be
     * collected as soon as the declaration has been checked; all others go into `kept`.
     */
    Expr get(int id, Memo kept, Memo temp) {
        if (!defined(id)) throw new KernelException("undefined expr id " + id);
        Expr hit = kept.get(id);
        if (hit == null && temp != null) hit = temp.get(id);
        if (hit != null) return hit;
        Expr r;
        byte k = kindAt(id);
        int x = aAt(id), y = bAt(id);
        switch (k) {
            case ALIAS: r = get(x, kept, temp); break;
            case BVAR: r = Expr.bvar(x); break;
            case SORT: r = Expr.sort(reader.levelAt(x)); break;
            case CONST: {
                List<Level> levels;
                if (y < 0) levels = List.of();
                else {
                    int n = extra.get(y);
                    List<Level> l = new ArrayList<>(n);
                    for (int j = 1; j <= n; j++) l.add(reader.levelAt(extra.get(y + j)));
                    levels = l;
                }
                r = Expr.cnst(reader.nameAt(x), levels);
                break;
            }
            case APP: r = Expr.app(get(x, kept, temp), get(y, kept, temp)); break;
            case LET: r = Expr.let(reader.nameAt(x), get(extra.get(y), kept, temp), get(extra.get(y + 1), kept, temp), get(extra.get(y + 2), kept, temp)); break;
            case NAT: r = Expr.nat((BigInteger) literals.get(x)); break;
            case STR: r = Expr.str((String) literals.get(x)); break;
            case PROJ: r = Expr.proj(reader.nameAt(x), extra.get(y), get(extra.get(y + 1), kept, temp)); break;
            default: {
                if (k >= LAM && k < LAM + 4) r = Expr.lam(reader.nameAt(x), get(extra.get(y), kept, temp), get(extra.get(y + 1), kept, temp), BINDER_INFO[k - LAM]);
                else if (k >= PI && k < PI + 4) r = Expr.pi(reader.nameAt(x), get(extra.get(y), kept, temp), get(extra.get(y + 1), kept, temp), BINDER_INFO[k - PI]);
                else throw new KernelException("corrupt expression store at id " + id);
            }
        }
        (temp != null ? temp : kept).put(id, r);
        return r;
    }

    private Memo kept = new Memo();

    /** A kept node (type, definition body, ...). */
    Expr get(int id) { return get(id, kept, null); }

    /** A proof term being checked: built into scratch space, reusing kept nodes. */
    Expr getTemp(int id) { return get(id, kept, new Memo()); }

    /** Called between declarations: drops the memo of built objects once it has grown past {@link #KEEP_LIMIT}. */
    void endDeclaration() {
        if (kept.size() > KEEP_LIMIT) kept = new Memo();
    }

    /** A growable int sequence kept in chunks; indices are ints, so it holds at most 2^31 - 1 values. */
    static final class IntList {
        private int[][] chunks = new int[16][];
        private int size = 0;

        int add(int v) {
            if (size == Integer.MAX_VALUE) throw new KernelException("export too large: more than 2^31 auxiliary expression fields");
            int c = size >>> BITS;
            if (c >= chunks.length) chunks = Arrays.copyOf(chunks, chunks.length * 2);
            if (chunks[c] == null) chunks[c] = new int[CHUNK];
            chunks[c][size & MASK] = v;
            return size++;
        }

        int get(int i) { return chunks[i >>> BITS][i & MASK]; }

        long footprint() {
            long n = 0;
            for (int[] c : chunks) if (c != null) n += CHUNK * 4L;
            return n;
        }
    }
}
