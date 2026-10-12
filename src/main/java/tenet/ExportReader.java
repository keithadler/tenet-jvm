package tenet;

import java.io.BufferedReader;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

/** Streams a lean4export NDJSON file (format 3.x), delivering Decl / InductiveBlock items in order. */
public final class ExportReader {
    private Name[] names = new Name[1 << 12];
    private Level[] levels = new Level[1 << 12];
    private Expr[] exprs = new Expr[1 << 14];
    public String formatVersion = "?", leanVersion = "?";
    public long lines;

    public ExportReader() {
        names[0] = Name.ANON;
        levels[0] = Level.ZERO;
    }

    private static <T> T[] grow(T[] a, int idx) {
        if (idx < a.length) return a;
        int n = a.length;
        while (n <= idx) n *= 2;
        return Arrays.copyOf(a, n);
    }

    private Name name(Object id) {
        Name n = names[(int) (long) (Long) id];
        if (n == null) throw new KernelException("undefined name id " + id);
        return n;
    }

    private Level level(Object id) {
        Level l = levels[(int) (long) (Long) id];
        if (l == null) throw new KernelException("undefined level id " + id);
        return l;
    }

    private Expr expr(Object id) {
        Expr e = exprs[(int) (long) (Long) id];
        if (e == null) throw new KernelException("undefined expr id " + id);
        return e;
    }

    private List<Name> nameList(Object o) {
        List<Name> out = new ArrayList<>();
        for (Object x : (List<?>) o) out.add(name(x));
        return out;
    }

    private static int i(Object o) { return (int) (long) (Long) o; }
    private static boolean b(Object o) { return o != null && (Boolean) o; }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> m(Object o) { return (Map<String, Object>) o; }

    public void read(BufferedReader in, Consumer<Object> sink) throws IOException {
        String line;
        while ((line = in.readLine()) != null) {
            if (line.isEmpty()) continue;
            lines++;
            Map<String, Object> o;
            try {
                o = m(Json.parse(line));
            } catch (KernelException e) {
                throw e;
            } catch (RuntimeException e) {
                // A line cut off mid-record (an exporter that died, a short download) or not JSON at all.
                throw new KernelException("malformed export: line " + (lines) + " is not a complete JSON object");
            }
            if (lines == 1 && !o.containsKey("meta")) throw new KernelException("not a lean4export file: the first line is not the metadata record");
            handle(o, sink);
        }
        if (lines == 0) throw new KernelException("empty input: not a lean4export file");
    }

    private void handle(Map<String, Object> o, Consumer<Object> sink) {
        if (o.containsKey("meta")) {
            Map<String, Object> meta = m(o.get("meta"));
            formatVersion = String.valueOf(m(meta.get("format")).get("version"));
            leanVersion = String.valueOf(m(meta.get("lean")).get("version"));
            if (!formatVersion.startsWith("3.")) throw new KernelException("unsupported export format version " + formatVersion + " (this checker reads 3.x)");
        } else if (o.containsKey("in")) {
            int id = i(o.get("in"));
            names = grow(names, id);
            if (o.containsKey("str")) {
                Map<String, Object> s = m(o.get("str"));
                names[id] = Name.str(name(s.get("pre")), (String) s.get("str"));
            } else {
                Map<String, Object> s = m(o.get("num"));
                names[id] = Name.num(name(s.get("pre")), (Long) s.get("i"));
            }
        } else if (o.containsKey("il")) {
            int id = i(o.get("il"));
            levels = grow(levels, id);
            if (o.containsKey("succ")) levels[id] = Level.succ(level(o.get("succ")));
            else if (o.containsKey("max")) {
                List<?> a = (List<?>) o.get("max");
                levels[id] = Level.max(level(a.get(0)), level(a.get(1)));
            } else if (o.containsKey("imax")) {
                List<?> a = (List<?>) o.get("imax");
                levels[id] = Level.imax(level(a.get(0)), level(a.get(1)));
            } else levels[id] = Level.param(name(o.get("param")));
        } else if (o.containsKey("ie")) {
            int id = i(o.get("ie"));
            exprs = grow(exprs, id);
            exprs[id] = parseExpr(o);
        } else {
            decl(o, sink);
        }
    }

    private Expr parseExpr(Map<String, Object> o) {
        if (o.containsKey("bvar")) return Expr.bvar(i(o.get("bvar")));
        if (o.containsKey("sort")) return Expr.sort(level(o.get("sort")));
        if (o.containsKey("const")) {
            Map<String, Object> c = m(o.get("const"));
            List<Level> ls = new ArrayList<>();
            for (Object x : (List<?>) c.get("us")) ls.add(level(x));
            return Expr.cnst(name(c.get("name")), ls);
        }
        if (o.containsKey("app")) {
            Map<String, Object> a = m(o.get("app"));
            return Expr.app(expr(a.get("fn")), expr(a.get("arg")));
        }
        if (o.containsKey("lam")) {
            Map<String, Object> a = m(o.get("lam"));
            return Expr.lam(name(a.get("name")), expr(a.get("type")), expr(a.get("body")), (String) a.get("binderInfo"));
        }
        if (o.containsKey("forallE")) {
            Map<String, Object> a = m(o.get("forallE"));
            return Expr.pi(name(a.get("name")), expr(a.get("type")), expr(a.get("body")), (String) a.get("binderInfo"));
        }
        if (o.containsKey("letE")) {
            Map<String, Object> a = m(o.get("letE"));
            return Expr.let(name(a.get("name")), expr(a.get("type")), expr(a.get("value")), expr(a.get("body")));
        }
        if (o.containsKey("proj")) {
            Map<String, Object> a = m(o.get("proj"));
            return Expr.proj(name(a.get("typeName")), i(a.get("idx")), expr(a.get("struct")));
        }
        if (o.containsKey("natVal")) return Expr.nat(new BigInteger((String) o.get("natVal")));
        if (o.containsKey("strVal")) return Expr.str((String) o.get("strVal"));
        if (o.containsKey("mdata")) return expr(m(o.get("mdata")).get("expr"));
        throw new KernelException("unknown expression node: " + o.keySet());
    }

    private void decl(Map<String, Object> o, Consumer<Object> sink) {
        if (o.containsKey("axiom")) {
            Map<String, Object> d = m(o.get("axiom"));
            sink.accept(new Decl.Axiom(name(d.get("name")), nameList(d.get("levelParams")), expr(d.get("type")), b(d.get("isUnsafe"))));
        } else if (o.containsKey("def")) {
            Map<String, Object> d = m(o.get("def"));
            Object h = d.get("hints");
            String hints;
            long height = 0;
            if (h instanceof Map) { hints = "regular"; height = (Long) m(h).get("regular"); } else hints = (String) h;
            sink.accept(new Decl.Def(name(d.get("name")), nameList(d.get("levelParams")), expr(d.get("type")), expr(d.get("value")),
                    hints, height, (String) d.get("safety")));
        } else if (o.containsKey("thm")) {
            Map<String, Object> d = m(o.get("thm"));
            sink.accept(new Decl.Thm(name(d.get("name")), nameList(d.get("levelParams")), expr(d.get("type")), expr(d.get("value"))));
        } else if (o.containsKey("opaque")) {
            Map<String, Object> d = m(o.get("opaque"));
            sink.accept(new Decl.Opaque(name(d.get("name")), nameList(d.get("levelParams")), expr(d.get("type")), expr(d.get("value")),
                    b(d.get("isUnsafe"))));
        } else if (o.containsKey("quot")) {
            Map<String, Object> d = m(o.get("quot"));
            sink.accept(new Decl.Quot(name(d.get("name")), nameList(d.get("levelParams")), expr(d.get("type")), (String) d.get("kind")));
        } else if (o.containsKey("inductive")) {
            Map<String, Object> d = m(o.get("inductive"));
            List<Decl.Inductive> ts = new ArrayList<>();
            for (Object x : (List<?>) d.get("types")) {
                Map<String, Object> t = m(x);
                ts.add(new Decl.Inductive(name(t.get("name")), nameList(t.get("levelParams")), expr(t.get("type")), i(t.get("numParams")),
                        i(t.get("numIndices")), nameList(t.get("all")), nameList(t.get("ctors")), i(t.get("numNested")), b(t.get("isRec")),
                        b(t.get("isUnsafe")), b(t.get("isReflexive"))));
            }
            List<Decl.Ctor> cs = new ArrayList<>();
            for (Object x : (List<?>) d.get("ctors")) {
                Map<String, Object> c = m(x);
                cs.add(new Decl.Ctor(name(c.get("name")), nameList(c.get("levelParams")), expr(c.get("type")), name(c.get("induct")),
                        i(c.get("cidx")), i(c.get("numParams")), i(c.get("numFields")), b(c.get("isUnsafe"))));
            }
            List<Decl.Recursor> rs = new ArrayList<>();
            for (Object x : (List<?>) d.get("recs")) {
                Map<String, Object> r = m(x);
                List<Decl.RecRule> rules = new ArrayList<>();
                for (Object y : (List<?>) r.get("rules")) {
                    Map<String, Object> ru = m(y);
                    rules.add(new Decl.RecRule(name(ru.get("ctor")), i(ru.get("nfields")), expr(ru.get("rhs"))));
                }
                rs.add(new Decl.Recursor(name(r.get("name")), nameList(r.get("levelParams")), expr(r.get("type")), nameList(r.get("all")),
                        i(r.get("numParams")), i(r.get("numIndices")), i(r.get("numMotives")), i(r.get("numMinors")), rules, b(r.get("k")),
                        b(r.get("isUnsafe"))));
            }
            sink.accept(new InductiveBlock(ts, cs, rs));
        } else {
            throw new KernelException("unknown export record: " + o.keySet());
        }
    }
}
