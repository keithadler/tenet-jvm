package tenet;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BinaryOperator;

/**
 * The Lean 4 kernel type checker: inference, weak head normalisation and definitional equality.
 * Works over locally-nameless terms; free variables live in the local context of this checker.
 */
public final class TypeChecker {
    static final class Local {
        final Name name;
        final Expr type;
        final Expr value; // null unless a let-variable
        final String info;
        Local(Name n, Expr t, Expr v, String info) { name = n; type = t; value = v; this.info = info; }
    }

    private static long fvarCounter = 0;
    private static final boolean DEBUG_NAT = System.getenv("LEANKERNEL_DEBUG_NAT") != null;

    public final Env env;
    private List<Name> lparams = List.of();
    private int safetyRank = 0; // 0 safe, 1 partial, 2 unsafe
    private final Map<Long, Local> lctx = new HashMap<>();

    private Map<Expr, Expr> inferOnlyCache = new HashMap<>();
    private Map<Expr, Expr> inferCheckedCache = new HashMap<>();
    private Map<Expr, Expr> whnfCoreCache = new HashMap<>();
    private Map<Expr, Expr> whnfCoreCheapCache = new HashMap<>();
    private Map<Expr, Expr> whnfCache = new HashMap<>();
    private Map<Expr, Expr> unfoldCache = new HashMap<>();
    private Set<List<Expr>> eqCache = new HashSet<>();
    private Set<List<Expr>> failCache = new HashSet<>();

    static TypeChecker CURRENT;
    public TypeChecker(Env env) { this.env = env; CURRENT = this; }

    private static Map<Expr, Expr> fresh(Map<Expr, Expr> m) {
        if (m.size() > 256) return new HashMap<>();
        m.clear();
        return m;
    }

    /** Prepare to check a declaration with the given universe parameters. */
    public void begin(List<Name> lparams, int safetyRank) {
        this.lparams = lparams;
        this.safetyRank = safetyRank;
        lctx.clear();
        // clear() costs time proportional to the table's capacity, which stays large after a big declaration
        inferOnlyCache = fresh(inferOnlyCache);
        inferCheckedCache = fresh(inferCheckedCache);
        whnfCoreCache = fresh(whnfCoreCache);
        whnfCoreCheapCache = fresh(whnfCoreCheapCache);
        whnfCache = fresh(whnfCache);
        unfoldCache = fresh(unfoldCache);
        if (eqCache.size() > 256) eqCache = new HashSet<>(); else eqCache.clear();
        if (failCache.size() > 256) failCache = new HashSet<>(); else failCache.clear();
    }

    // ---- local context -----------------------------------------------------

    Expr mkLocal(Name n, Expr type, String info) { return mkLocal(n, type, null, info); }

    Expr mkLocal(Name n, Expr type, Expr value, String info) {
        long id = ++fvarCounter;
        lctx.put(id, new Local(n, type, value, info));
        return Expr.fvar(id);
    }

    Local local(Expr fv) {
        Local l = lctx.get(((Expr.FVar) fv).id);
        if (l == null) throw new KernelException("unknown free variable " + fv);
        return l;
    }

    /** Pi (or lambda) over the given locals, in order. */
    Expr mkBinding(boolean isPi, List<Expr> fvars, Expr body) {
        int n = fvars.size();
        long[] ids = new long[n];
        for (int i = 0; i < n; i++) ids[i] = ((Expr.FVar) fvars.get(i)).id;
        Expr r = Expr.abstractFVars(body, ids);
        for (int i = n - 1; i >= 0; i--) {
            Local l = lctx.get(ids[i]);
            Expr ty = Expr.abstractFVars(l.type, Arrays.copyOf(ids, i));
            r = isPi ? Expr.pi(l.name, ty, r, l.info) : Expr.lam(l.name, ty, r, l.info);
        }
        return r;
    }

    Expr mkPi(List<Expr> fvars, Expr body) { return mkBinding(true, fvars, body); }
    Expr mkLambda(List<Expr> fvars, Expr body) { return mkBinding(false, fvars, body); }

    // ---- inference ---------------------------------------------------------

    public Expr infer(Expr e) { return infer(e, true); }
    public Expr check(Expr e) { return infer(e, false); }

    public Expr infer(Expr e, boolean inferOnly) {
        if (e.kind == Expr.Kind.BVAR) throw new KernelException("type checker does not support loose bound variables");
        Expr cached = inferOnly ? inferOnlyCache.get(e) : null;
        if (cached == null) cached = inferCheckedCache.get(e);
        if (cached != null) return cached;
        Expr r;
        switch (e.kind) {
            case FVAR: r = local(e).type; break;
            case SORT: {
                Level l = ((Expr.Sort) e).level;
                if (!inferOnly) checkLevel(l);
                r = Expr.sort(Level.succ(l));
                break;
            }
            case CONST: r = inferConst((Expr.Const) e, inferOnly); break;
            case APP: r = inferApp(e, inferOnly); break;
            case LAM: r = inferLambda(e, inferOnly); break;
            case PI: r = inferPi(e, inferOnly); break;
            case LET: r = inferLet((Expr.Let) e, inferOnly); break;
            case NAT: r = Expr.cnst(Names.NAT, List.of()); break;
            case STR: r = Expr.cnst(Names.STRING, List.of()); break;
            default: r = inferProj((Expr.Proj) e, inferOnly);
        }
        (inferOnly ? inferOnlyCache : inferCheckedCache).put(e, r);
        return r;
    }

    private void checkLevel(Level l) {
        Name[] missing = new Name[1];
        if (!l.paramsIn(lparams, missing)) throw new KernelException("undeclared universe parameter " + missing[0]);
    }

    private Expr inferConst(Expr.Const c, boolean inferOnly) {
        Decl d = env.get(c.name);
        if (d == null) throw new KernelException("unknown constant " + c.name);
        if (d.levelParams.size() != c.levels.size())
            throw new KernelException("incorrect number of universe levels for " + c.name + ": expected " + d.levelParams.size() + ", got " + c.levels.size());
        if (!inferOnly) {
            for (Level l : c.levels) checkLevel(l);
            if (rank(d) > safetyRank) throw new KernelException("invalid declaration, it uses " + (rank(d) == 2 ? "unsafe" : "partial") + " declaration " + c.name);
        }
        return Expr.instantiateLevelParams(d.type, d.levelParams, c.levels);
    }

    static int rank(Decl d) {
        switch (d.kind) {
            case AXIOM: return ((Decl.Axiom) d).isUnsafe ? 2 : 0;
            case DEF: {
                String s = ((Decl.Def) d).safety;
                return s.equals("unsafe") ? 2 : s.equals("partial") ? 1 : 0;
            }
            case OPAQUE: return ((Decl.Opaque) d).isUnsafe ? 2 : 0;
            case INDUCTIVE: return ((Decl.Inductive) d).isUnsafe ? 2 : 0;
            case CTOR: return ((Decl.Ctor) d).isUnsafe ? 2 : 0;
            case RECURSOR: return ((Decl.Recursor) d).isUnsafe ? 2 : 0;
            default: return 0;
        }
    }

    private Expr inferApp(Expr e, boolean inferOnly) {
        if (!inferOnly) {
            Expr.App a = (Expr.App) e;
            Expr fType = ensurePi(infer(a.fn, false), a.fn);
            Expr aType = infer(a.arg, false);
            Expr dom = ((Expr.Binder) fType).type;
            if (!isDefEq(aType, dom))
                throw new KernelException("application type mismatch\n  function head: " + a.fn.getAppFn() + "\n  argument: " + a.arg + "\n  has type: " + aType + "\n  but is expected to have type: " + dom);
            return Expr.instantiate1(((Expr.Binder) fType).body, a.arg);
        }
        List<Expr> args = e.getAppArgs();
        Expr fType = infer(e.getAppFn(), true);
        int j = 0, n = args.size();
        for (int i = 0; i < n; i++) {
            if (fType.kind == Expr.Kind.PI) {
                fType = ((Expr.Binder) fType).body;
            } else {
                fType = Expr.instantiateRev(fType, args.subList(j, i).toArray(new Expr[0]));
                fType = ensurePi(fType, e);
                fType = ((Expr.Binder) fType).body;
                j = i;
            }
        }
        return Expr.instantiateRev(fType, args.subList(j, n).toArray(new Expr[0]));
    }

    private Expr inferLambda(Expr e, boolean inferOnly) {
        List<Expr> fvars = new ArrayList<>();
        Expr cur = e;
        while (cur.kind == Expr.Kind.LAM) {
            Expr.Binder b = (Expr.Binder) cur;
            Expr dom = Expr.instantiateRev(b.type, fvars.toArray(new Expr[0]));
            if (!inferOnly) ensureSort(infer(dom, false), dom);
            fvars.add(mkLocal(b.name, dom, b.info));
            cur = b.body;
        }
        Expr r = infer(Expr.instantiateRev(cur, fvars.toArray(new Expr[0])), inferOnly);
        return mkPi(fvars, r);
    }

    private Expr inferPi(Expr e, boolean inferOnly) {
        List<Expr> fvars = new ArrayList<>();
        List<Level> us = new ArrayList<>();
        Expr cur = e;
        while (cur.kind == Expr.Kind.PI) {
            Expr.Binder b = (Expr.Binder) cur;
            Expr dom = Expr.instantiateRev(b.type, fvars.toArray(new Expr[0]));
            us.add(ensureSort(infer(dom, inferOnly), dom));
            fvars.add(mkLocal(b.name, dom, b.info));
            cur = b.body;
        }
        Expr body = Expr.instantiateRev(cur, fvars.toArray(new Expr[0]));
        Level r = ensureSort(infer(body, inferOnly), body);
        for (int i = us.size() - 1; i >= 0; i--) r = Level.mkIMax(us.get(i), r);
        return Expr.sort(r);
    }

    private Expr inferLet(Expr.Let l, boolean inferOnly) {
        if (!inferOnly) {
            ensureSort(infer(l.type, false), l.type);
            Expr vt = infer(l.value, false);
            if (!isDefEq(vt, l.type))
                throw new KernelException("let-value type mismatch for " + l.name + "\n  value has type: " + vt + "\n  expected: " + l.type);
        }
        return infer(Expr.instantiate1(l.body, l.value), inferOnly);
    }

    private Expr inferProj(Expr.Proj p, boolean inferOnly) {
        Expr structType = whnf(infer(p.struct, inferOnly));
        Expr fn = structType.getAppFn();
        if (fn.kind != Expr.Kind.CONST) throw new KernelException("invalid projection, structure expected: " + p);
        Expr.Const ic = (Expr.Const) fn;
        if (!ic.name.equals(p.typeName)) throw new KernelException("invalid projection, type name mismatch: " + p);
        Decl d = env.get(ic.name);
        if (!(d instanceof Decl.Inductive)) throw new KernelException("invalid projection, not an inductive type: " + ic.name);
        Decl.Inductive ind = (Decl.Inductive) d;
        if (ind.ctors.size() != 1 || ind.numIndices != 0) throw new KernelException("invalid projection, not a structure: " + ic.name);
        List<Expr> args = structType.getAppArgs();
        if (args.size() != ind.numParams) throw new KernelException("invalid projection, wrong number of parameters: " + p);
        Decl cd = env.get(ind.ctors.get(0));
        if (!(cd instanceof Decl.Ctor)) throw new KernelException("invalid projection, unknown constructor " + ind.ctors.get(0));
        Decl.Ctor ctor = (Decl.Ctor) cd;
        Expr ct = Expr.instantiateLevelParams(ctor.type, ctor.levelParams, ic.levels);
        for (Expr a : args) {
            ct = whnf(ct);
            if (ct.kind != Expr.Kind.PI) throw new KernelException("invalid projection, ill-formed constructor type");
            ct = Expr.instantiate1(((Expr.Binder) ct).body, a);
        }
        boolean isPropType = isPropType(structType);
        for (int i = 0; i < p.idx; i++) {
            ct = whnf(ct);
            if (ct.kind != Expr.Kind.PI) throw new KernelException("invalid projection, index out of range: " + p);
            Expr.Binder b = (Expr.Binder) ct;
            if (isPropType && !isPropType(b.type) && Expr.hasLooseBVar(b.body, 0))
                throw new KernelException("invalid projection, structure is a proposition and a later field depends on a data field: " + p);
            ct = Expr.instantiate1(b.body, Expr.proj(p.typeName, i, p.struct));
        }
        ct = whnf(ct);
        if (ct.kind != Expr.Kind.PI) throw new KernelException("invalid projection, index out of range: " + p);
        Expr fieldType = ((Expr.Binder) ct).type;
        if (isPropType && !isPropType(fieldType))
            throw new KernelException("invalid projection, structure is a proposition but field is not: " + p);
        return fieldType;
    }

    // ---- ensure helpers ----------------------------------------------------

    public Expr ensurePi(Expr t, Expr src) {
        if (t.kind == Expr.Kind.PI) return t;
        Expr w = whnf(t);
        if (w.kind == Expr.Kind.PI) return w;
        throw new KernelException("function expected\n  term: " + src + "\n  has type: " + t);
    }

    public Level ensureSort(Expr t, Expr src) {
        if (t.kind == Expr.Kind.SORT) return ((Expr.Sort) t).level;
        Expr w = whnf(t);
        if (w.kind == Expr.Kind.SORT) return ((Expr.Sort) w).level;
        throw new KernelException("type expected\n  term: " + src + "\n  has type: " + t);
    }

    /** Is the given type a proposition, i.e. does it have type Prop? */
    public boolean isPropType(Expr type) {
        Expr w = whnf(infer(type, true));
        // A sort that does not reduce to a Sort is an error, not an answer: "not a proposition" would be
        // a claim about a type whose universe we could not even determine (cf. lean4#14807).
        if (w.kind != Expr.Kind.SORT) throw new KernelException("type expected: " + type + " has type " + w);
        return ((Expr.Sort) w).level.isEquivZero();
    }

    // ---- weak head normal form --------------------------------------------

    public Expr whnfCore(Expr e) { return whnfCore(e, false, false); }

    public Expr whnfCore(Expr e, boolean cheapRec, boolean cheapProj) {
        switch (e.kind) {
            case BVAR: case SORT: case CONST: case LAM: case PI: case NAT: case STR: return e;
            default: break;
        }
        // Separate caches: a fully reduced result must not leak into "cheap" calls, which are meant to
        // leave projections of unreduced structures stuck so that both sides of a comparison unfold in step.
        boolean cheap = cheapRec || cheapProj;
        Map<Expr, Expr> cache = cheap ? whnfCoreCheapCache : whnfCoreCache;
        Expr cached = cache.get(e);
        if (cached != null) return cached;
        Expr r;
        switch (e.kind) {
            case FVAR: {
                Local l = local(e);
                if (l.value == null) return e;
                r = whnfCore(l.value, cheapRec, cheapProj);
                break;
            }
            case LET: r = whnfCore(Expr.instantiate1(((Expr.Let) e).body, ((Expr.Let) e).value), cheapRec, cheapProj); break;
            case PROJ: {
                Expr red = reduceProj((Expr.Proj) e, cheapRec, cheapProj);
                r = red == null ? e : whnfCore(red, cheapRec, cheapProj);
                break;
            }
            default: { // APP
                Expr f0 = e.getAppFn();
                Expr f = whnfCore(f0, cheapRec, cheapProj);
                if (f.kind == Expr.Kind.LAM) {
                    r = whnfCore(Expr.betaRev(f, e.getAppArgs()), cheapRec, cheapProj);
                } else if (f == f0) {
                    Expr red = reduceRecursor(e, cheapRec, cheapProj);
                    r = red == null ? e : whnfCore(red, cheapRec, cheapProj);
                } else {
                    r = whnfCore(Expr.apps(f, e.getAppArgs()), cheapRec, cheapProj);
                }
            }
        }
        cache.put(e, r);
        return r;
    }

    private Expr reduceProj(Expr.Proj p, boolean cheapRec, boolean cheapProj) {
        Expr c = cheapProj ? whnfCore(p.struct, cheapRec, cheapProj) : whnf(p.struct);
        if (c.kind == Expr.Kind.STR) c = whnf(strLitToCtor(((Expr.StrLit) c).val));
        Expr fn = c.getAppFn();
        if (fn.kind != Expr.Kind.CONST) return null;
        Decl d = env.get(((Expr.Const) fn).name);
        if (!(d instanceof Decl.Ctor)) return null;
        Decl.Ctor ctor = (Decl.Ctor) d;
        List<Expr> args = c.getAppArgs();
        int i = ctor.numParams + p.idx;
        return i < args.size() ? args.get(i) : null;
    }

    private Expr reduceRecursor(Expr e, boolean cheapRec, boolean cheapProj) {
        Expr fn = e.getAppFn();
        if (fn.kind != Expr.Kind.CONST) return null;
        Name n = ((Expr.Const) fn).name;
        Decl d = env.get(n);
        if (d instanceof Decl.Recursor) return reduceInductiveRec(e, (Expr.Const) fn, (Decl.Recursor) d, cheapRec, cheapProj);
        if (env.quotInitialized && (n.equals(Names.QUOT_LIFT) || n.equals(Names.QUOT_IND))) return reduceQuot(e, n, cheapRec, cheapProj);
        return null;
    }

    private Expr reduceQuot(Expr e, Name n, boolean cheapRec, boolean cheapProj) {
        int mkPos = n.equals(Names.QUOT_LIFT) ? 5 : 4;
        int argPos = 3;
        List<Expr> args = e.getAppArgs();
        if (args.size() <= mkPos) return null;
        Expr mk = cheapRec ? whnfCore(args.get(mkPos), cheapRec, cheapProj) : whnf(args.get(mkPos));
        Expr mkFn = mk.getAppFn();
        if (!mkFn.isConstOf(Names.QUOT_MK) || mk.getAppNumArgs() != 3) return null;
        Expr r = Expr.app(args.get(argPos), mk.getAppArgs().get(2));
        for (int i = mkPos + 1; i < args.size(); i++) r = Expr.app(r, args.get(i));
        return r;
    }

    /** Name of the inductive type the recursor eliminates (the head of the major premise's type). */
    static Name majorInduct(Decl.Recursor rec) {
        Expr t = rec.type;
        int n = rec.majorIdx();
        for (int i = 0; i < n; i++) t = ((Expr.Binder) t).body;
        t = ((Expr.Binder) t).type;
        return ((Expr.Const) t.getAppFn()).name;
    }

    private Expr reduceInductiveRec(Expr e, Expr.Const rc, Decl.Recursor rec, boolean cheapRec, boolean cheapProj) {
        List<Expr> args = e.getAppArgs();
        int majorIdx = rec.majorIdx();
        if (majorIdx >= args.size()) return null;
        Expr major = args.get(majorIdx);
        if (rec.k) {
            Expr m2 = toCtorWhenK(rec, major);
            if (m2 != null) major = m2;
        }
        major = cheapRec ? whnfCore(major, cheapRec, cheapProj) : whnf(major);
        if (major.kind == Expr.Kind.NAT) major = natLitToCtor(((Expr.NatLit) major).val);
        else if (major.kind == Expr.Kind.STR) major = whnf(strLitToCtor(((Expr.StrLit) major).val));
        else major = toCtorWhenStructure(majorInduct(rec), major);
        Expr mfn = major.getAppFn();
        if (mfn.kind != Expr.Kind.CONST) return null;
        Decl.RecRule rule = null;
        for (Decl.RecRule r : rec.rules) if (r.ctor.equals(((Expr.Const) mfn).name)) { rule = r; break; }
        if (rule == null) return null;
        List<Expr> margs = major.getAppArgs();
        if (rule.nfields > margs.size()) return null;
        if (rc.levels.size() != rec.levelParams.size()) return null;
        Expr rhs = Expr.instantiateLevelParams(rule.rhs, rec.levelParams, rc.levels);
        rhs = Expr.apps(rhs, args.subList(0, rec.numParams + rec.numMotives + rec.numMinors));
        rhs = Expr.apps(rhs, margs.subList(margs.size() - rule.nfields, margs.size()));
        if (args.size() > majorIdx + 1) rhs = Expr.apps(rhs, args.subList(majorIdx + 1, args.size()));
        return rhs;
    }

    private Expr toCtorWhenK(Decl.Recursor rec, Expr e) {
        Expr appType = whnf(infer(e, true));
        Expr I = appType.getAppFn();
        if (I.kind != Expr.Kind.CONST || !((Expr.Const) I).name.equals(majorInduct(rec))) return e;
        Decl d = env.get(((Expr.Const) I).name);
        if (!(d instanceof Decl.Inductive) || ((Decl.Inductive) d).ctors.isEmpty()) return e;
        Decl.Inductive ind = (Decl.Inductive) d;
        List<Expr> targs = appType.getAppArgs();
        if (targs.size() < ind.numParams) return e;
        Expr ctorApp = Expr.apps(Expr.cnst(ind.ctors.get(0), ((Expr.Const) I).levels), targs.subList(0, ind.numParams));
        Expr newType = infer(ctorApp, true);
        if (!isDefEq(appType, newType)) return e;
        return ctorApp;
    }

    boolean isStructureLike(Name n) {
        Decl d = env.get(n);
        if (!(d instanceof Decl.Inductive)) return false;
        Decl.Inductive ind = (Decl.Inductive) d;
        return ind.ctors.size() == 1 && ind.numIndices == 0 && !ind.isRec;
    }

    private Expr toCtorWhenStructure(Name induct, Expr e) {
        if (!isStructureLike(induct)) return e;
        Expr f = e.getAppFn();
        if (f.kind == Expr.Kind.CONST && env.get(((Expr.Const) f).name) instanceof Decl.Ctor) return e;
        Expr eType = whnf(infer(e, true));
        Expr I = eType.getAppFn();
        if (!I.isConstOf(induct)) return e;
        if (isPropType(eType)) return e;
        return expandEtaStruct(eType, e);
    }

    private Expr expandEtaStruct(Expr eType, Expr e) {
        Expr I = eType.getAppFn();
        Decl.Inductive ind = (Decl.Inductive) env.get(((Expr.Const) I).name);
        Decl.Ctor ctor = (Decl.Ctor) env.get(ind.ctors.get(0));
        List<Expr> targs = eType.getAppArgs();
        Expr r = Expr.apps(Expr.cnst(ctor.name, ((Expr.Const) I).levels), targs.subList(0, Math.min(ind.numParams, targs.size())));
        for (int i = 0; i < ctor.numFields; i++) r = Expr.app(r, Expr.proj(ind.name, i, e));
        return r;
    }

    static Expr natLitToCtor(BigInteger v) {
        if (DEBUG_NAT && v.compareTo(BigInteger.valueOf(100000)) > 0 && v.bitLength() < 64 && (v.longValue() & 0xFFFFF) == 0)
            { System.err.println("natLitToCtor " + v); CURRENT.dumpDbgStack(); System.exit(3); }
        if (v.signum() == 0) return Expr.cnst(Names.NAT_ZERO, List.of());
        return Expr.app(Expr.cnst(Names.NAT_SUCC, List.of()), Expr.nat(v.subtract(BigInteger.ONE)));
    }

    Expr strLitToCtor(String s) {
        Expr charT = Expr.cnst(Names.CHAR, List.of());
        List<Level> l0 = List.of(Level.ZERO);
        Expr list = Expr.app(Expr.cnst(Names.LIST_NIL, l0), charT);
        int[] cps = s.codePoints().toArray();
        for (int i = cps.length - 1; i >= 0; i--) {
            Expr ch = Expr.app(Expr.cnst(Names.CHAR_OF_NAT, List.of()), Expr.nat(cps[i]));
            list = Expr.apps(Expr.cnst(Names.LIST_CONS, l0), charT, ch, list);
        }
        return Expr.app(Expr.cnst(stringBuilderName(), List.of()), list);
    }

    /** Recent Lean versions build strings with String.ofList (String.mk became an ordinary definition). */
    private Name stringBuilderName() {
        return env.contains(Names.STRING_OF_LIST) ? Names.STRING_OF_LIST : Names.STRING_MK;
    }

    public Expr whnf(Expr e) {
        switch (e.kind) {
            case BVAR: case SORT: case PI: case LAM: case NAT: case STR: return e;
            default: break;
        }
        Expr cached = whnfCache.get(e);
        if (cached != null) return cached;
        Expr t = e;
        while (true) {
            Expr t1 = whnfCore(t);
            Expr v = reduceNat(t1);
            if (v != null) { whnfCache.put(e, v); return v; }
            Expr next = unfoldDefinition(t1);
            if (next != null) { t = next; continue; }
            whnfCache.put(e, t1);
            return t1;
        }
    }

    // ---- delta -------------------------------------------------------------

    Decl deltaInfo(Expr e) {
        Expr f = e.getAppFn();
        if (f.kind != Expr.Kind.CONST) return null;
        Decl d = env.get(((Expr.Const) f).name);
        return d != null && d.value() != null ? d : null;
    }

    private Expr unfoldConst(Expr.Const c, Decl d) {
        if (d.levelParams.size() != c.levels.size()) return null;
        Expr cached = unfoldCache.get(c);
        if (cached != null) return cached;
        Expr v = Expr.instantiateLevelParams(d.value(), d.levelParams, c.levels);
        unfoldCache.put(c, v);
        return v;
    }

    Expr unfoldDefinition(Expr e) {
        Decl d = deltaInfo(e);
        if (d == null) return null;
        Expr f = e.getAppFn();
        Expr v = unfoldConst((Expr.Const) f, d);
        if (v == null) return null;
        if (e.kind == Expr.Kind.APP) return Expr.betaRev(v, e.getAppArgs());
        return v;
    }

    // ---- Nat acceleration --------------------------------------------------

    private static final Map<Name, BinaryOperator<BigInteger>> NAT_BIN = new HashMap<>();
    private static final Map<Name, java.util.function.BiPredicate<BigInteger, BigInteger>> NAT_PRED = new HashMap<>();
    private static final int MAX_SHIFT = 1 << 24;

    static {
        NAT_BIN.put(Name.of("Nat.add"), BigInteger::add);
        NAT_BIN.put(Name.of("Nat.sub"), (a, b) -> a.compareTo(b) <= 0 ? BigInteger.ZERO : a.subtract(b));
        NAT_BIN.put(Name.of("Nat.mul"), BigInteger::multiply);
        NAT_BIN.put(Name.of("Nat.div"), (a, b) -> b.signum() == 0 ? BigInteger.ZERO : a.divide(b));
        NAT_BIN.put(Name.of("Nat.mod"), (a, b) -> b.signum() == 0 ? a : a.mod(b));
        NAT_BIN.put(Name.of("Nat.gcd"), BigInteger::gcd);
        NAT_BIN.put(Name.of("Nat.land"), BigInteger::and);
        NAT_BIN.put(Name.of("Nat.lor"), BigInteger::or);
        NAT_BIN.put(Name.of("Nat.xor"), BigInteger::xor);
        NAT_BIN.put(Name.of("Nat.shiftLeft"), (a, b) -> {
            if (b.compareTo(BigInteger.valueOf(MAX_SHIFT)) > 0) return null;
            return a.shiftLeft(b.intValue());
        });
        NAT_BIN.put(Name.of("Nat.shiftRight"), (a, b) -> b.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0 ? BigInteger.ZERO : a.shiftRight(b.intValue()));
        NAT_BIN.put(Name.of("Nat.pow"), (a, b) -> {
            if (b.compareTo(BigInteger.valueOf(MAX_SHIFT)) > 0) return null;
            return a.pow(b.intValue());
        });
        NAT_PRED.put(Name.of("Nat.beq"), (a, b) -> a.equals(b));
        NAT_PRED.put(Name.of("Nat.ble"), (a, b) -> a.compareTo(b) <= 0);
    }

    private static boolean isNatZero(Expr e) {
        return (e.kind == Expr.Kind.NAT && ((Expr.NatLit) e).val.signum() == 0) || e.isConstOf(Names.NAT_ZERO);
    }

    private BigInteger natValue(Expr e) {
        Expr w = whnf(e);
        if (w.kind == Expr.Kind.NAT) return ((Expr.NatLit) w).val;
        if (w.isConstOf(Names.NAT_ZERO)) return BigInteger.ZERO;
        return null;
    }

    private Expr reduceNat(Expr e) {
        if (e.hasFVar || e.kind != Expr.Kind.APP) return null;
        Expr f = e.getAppFn();
        if (f.kind != Expr.Kind.CONST) return null;
        Name n = ((Expr.Const) f).name;
        int nargs = e.getAppNumArgs();
        if (nargs == 1) {
            Expr arg = ((Expr.App) e).arg;
            if (n.equals(Names.NAT_SUCC)) {
                BigInteger v = natValue(arg);
                return v == null ? null : Expr.nat(v.add(BigInteger.ONE));
            }
            if (n.equals(Name.of("Nat.log2"))) {
                BigInteger v = natValue(arg);
                if (v == null) return null;
                return Expr.nat(v.signum() == 0 ? 0 : v.bitLength() - 1);
            }
            return null;
        }
        if (nargs != 2) return null;
        BinaryOperator<BigInteger> op = NAT_BIN.get(n);
        java.util.function.BiPredicate<BigInteger, BigInteger> pred = op == null ? NAT_PRED.get(n) : null;
        if (op == null && pred == null) return null;
        List<Expr> args = e.getAppArgs();
        BigInteger a = natValue(args.get(0));
        if (a == null) return null;
        BigInteger b = natValue(args.get(1));
        if (b == null) return null;
        if (op != null) {
            BigInteger r = op.apply(a, b);
            return r == null ? null : Expr.nat(r);
        }
        return Expr.cnst(pred.test(a, b) ? Names.BOOL_TRUE : Names.BOOL_FALSE, List.of());
    }

    // ---- definitional equality --------------------------------------------

    private final java.util.ArrayDeque<Expr[]> dbgStack = new java.util.ArrayDeque<>();

    public boolean isDefEq(Expr t, Expr s) {
        if (DEBUG_NAT) dbgStack.push(new Expr[] {t, s});
        boolean r = isDefEqCore(t, s);
        if (DEBUG_NAT) dbgStack.pop();
        if (r) eqCache.add(List.of(t, s));
        return r;
    }

    private final java.util.ArrayDeque<String> ring = new java.util.ArrayDeque<>();

    void dumpDbgStack() {
        for (String r : ring) System.err.println(r);
        int n = 0;
        for (Expr[] p : dbgStack) {
            String a = p[0].toString(), b = p[1].toString();
            System.err.println("  [" + n + "] " + a.substring(0, Math.min(400, a.length())) + "\n      =?= " + b.substring(0, Math.min(400, b.length())));
            if (n == 0) { try { java.nio.file.Files.writeString(java.nio.file.Path.of("/tmp/pair0.txt"), a + "\n=?=\n" + b); } catch (Exception ex) { } }
            if (++n >= 6) break;
        }
    }

    private static final int UNDEF = -1, FALSE = 0, TRUE = 1;

    private int quickIsDefEq(Expr t, Expr s) {
        if (t == s || t.equals(s) || eqCache.contains(List.of(t, s))) return TRUE;
        if (t.kind == s.kind) {
            switch (t.kind) {
                case LAM: case PI: return isDefEqBinding(t, s) ? TRUE : FALSE;
                case SORT: return ((Expr.Sort) t).level.isEquiv(((Expr.Sort) s).level) ? TRUE : FALSE;
                case NAT: case STR: return FALSE; // equal literals were caught above
                default: break;
            }
        }
        return UNDEF;
    }

    private boolean isDefEqBinding(Expr t, Expr s) {
        Expr.Kind k = t.kind;
        List<Expr> subst = new ArrayList<>();
        do {
            Expr.Binder bt = (Expr.Binder) t, bs = (Expr.Binder) s;
            Expr sType = null;
            if (!bt.type.equals(bs.type)) {
                sType = Expr.instantiateRev(bs.type, subst.toArray(new Expr[0]));
                Expr tType = Expr.instantiateRev(bt.type, subst.toArray(new Expr[0]));
                if (!isDefEq(tType, sType)) return false;
            }
            if (bt.body.looseBVarRange > 0 || bs.body.looseBVarRange > 0) {
                if (sType == null) sType = Expr.instantiateRev(bs.type, subst.toArray(new Expr[0]));
                subst.add(mkLocal(bs.name, sType, bs.info));
            } else {
                subst.add(Expr.sort(Level.ZERO));
            }
            t = bt.body;
            s = bs.body;
        } while (t.kind == k && s.kind == k);
        Expr[] sub = subst.toArray(new Expr[0]);
        return isDefEq(Expr.instantiateRev(t, sub), Expr.instantiateRev(s, sub));
    }

    private int proofIrrel(Expr t, Expr s) {
        Expr tType = infer(t, true);
        if (!isPropType(tType)) return UNDEF;
        Expr sType = infer(s, true);
        return isDefEq(tType, sType) ? TRUE : FALSE;
    }

    private boolean isDefEqCore(Expr t, Expr s) {
        int r = quickIsDefEq(t, s);
        if (r != UNDEF) return r == TRUE;

        if (!t.hasFVar && s.isConstOf(Names.BOOL_TRUE) && whnf(t).isConstOf(Names.BOOL_TRUE)) return true;

        Expr tn = whnfCore(t, false, true);
        Expr sn = whnfCore(s, false, true);
        if (!tn.equals(t) || !sn.equals(s)) {
            r = quickIsDefEq(tn, sn);
            if (r != UNDEF) return r == TRUE;
        }

        r = proofIrrel(tn, sn);
        if (r != UNDEF) return r == TRUE;

        Expr[] ts = {tn, sn};
        r = lazyDeltaReduction(ts);
        tn = ts[0];
        sn = ts[1];
        if (r != UNDEF) return r == TRUE;

        if (tn.kind == Expr.Kind.CONST && sn.kind == Expr.Kind.CONST && ((Expr.Const) tn).name.equals(((Expr.Const) sn).name)
                && levelsEquiv(((Expr.Const) tn).levels, ((Expr.Const) sn).levels)) return true;
        if (tn.kind == Expr.Kind.FVAR && sn.kind == Expr.Kind.FVAR && ((Expr.FVar) tn).id == ((Expr.FVar) sn).id) return true;
        if (tn.kind == Expr.Kind.PROJ && sn.kind == Expr.Kind.PROJ && ((Expr.Proj) tn).idx == ((Expr.Proj) sn).idx) {
            Expr[] pst = {((Expr.Proj) tn).struct, ((Expr.Proj) sn).struct};
            if (lazyDeltaProjReduction(pst, ((Expr.Proj) tn).idx)) return true;
        }

        Expr tnn = whnfCore(tn);
        Expr snn = whnfCore(sn);
        if (!tnn.equals(tn) || !snn.equals(sn)) return isDefEqCore(tnn, snn);

        if (isDefEqApp(tn, sn)) return true;
        if (tryEtaExpansion(tn, sn)) return true;
        if (tryEtaStruct(tn, sn)) return true;
        r = tryStringLitExpansion(tn, sn);
        if (r != UNDEF) return r == TRUE;
        return isDefEqUnitLike(tn, sn);
    }

    private static boolean levelsEquiv(List<Level> a, List<Level> b) {
        if (a.size() != b.size()) return false;
        for (int i = 0; i < a.size(); i++) if (!a.get(i).isEquiv(b.get(i))) return false;
        return true;
    }

    private boolean isDefEqApp(Expr t, Expr s) {
        if (t.kind != Expr.Kind.APP || s.kind != Expr.Kind.APP) return false;
        if (t.getAppNumArgs() != s.getAppNumArgs()) return false;
        if (!isDefEq(t.getAppFn(), s.getAppFn())) return false;
        return isDefEqArgs(t, s);
    }

    private boolean isDefEqArgs(Expr t, Expr s) {
        while (t.kind == Expr.Kind.APP && s.kind == Expr.Kind.APP) {
            if (!isDefEq(((Expr.App) t).arg, ((Expr.App) s).arg)) {
                if (DEBUG_NAT) {
                    String a = ((Expr.App) t).arg.toString(), b = ((Expr.App) s).arg.toString();
                    ring.addLast("ARGFAIL head=" + t.getAppFn() + "\n   " + a.substring(0, Math.min(900, a.length())) + "\n   =?= " + b.substring(0, Math.min(900, b.length())));
                    if (ring.size() > 4) ring.removeFirst();
                }
                return false;
            }
            t = ((Expr.App) t).fn;
            s = ((Expr.App) s).fn;
        }
        return t.kind != Expr.Kind.APP && s.kind != Expr.Kind.APP;
    }

    private boolean tryEtaExpansion(Expr t, Expr s) { return etaCore(t, s) || etaCore(s, t); }

    private boolean etaCore(Expr t, Expr s) {
        if (t.kind != Expr.Kind.LAM || s.kind == Expr.Kind.LAM) return false;
        Expr sType = whnf(infer(s, true));
        if (sType.kind != Expr.Kind.PI) return false;
        Expr.Binder pi = (Expr.Binder) sType;
        Expr newS = Expr.lam(pi.name, pi.type, Expr.app(s, Expr.bvar(0)), pi.info);
        return isDefEq(t, newS);
    }

    private boolean tryEtaStruct(Expr t, Expr s) { return etaStructCore(t, s) || etaStructCore(s, t); }

    private boolean etaStructCore(Expr t, Expr s) {
        Expr f = s.getAppFn();
        if (f.kind != Expr.Kind.CONST) return false;
        Decl d = env.get(((Expr.Const) f).name);
        if (!(d instanceof Decl.Ctor)) return false;
        Decl.Ctor ctor = (Decl.Ctor) d;
        List<Expr> args = s.getAppArgs();
        if (args.size() != ctor.numParams + ctor.numFields) return false;
        if (!isStructureLike(ctor.induct)) return false;
        if (!isDefEq(infer(t, true), infer(s, true))) return false;
        for (int i = ctor.numParams; i < args.size(); i++) {
            Expr proj = Expr.proj(ctor.induct, i - ctor.numParams, t);
            if (!isDefEq(proj, args.get(i))) return false;
        }
        return true;
    }

    private int tryStringLitExpansion(Expr t, Expr s) {
        if (t.kind == Expr.Kind.STR && s.kind == Expr.Kind.APP && s.getAppFn().isConstOf(stringBuilderName()))
            return isDefEqCore(strLitToCtor(((Expr.StrLit) t).val), s) ? TRUE : FALSE;
        if (s.kind == Expr.Kind.STR && t.kind == Expr.Kind.APP && t.getAppFn().isConstOf(stringBuilderName()))
            return isDefEqCore(t, strLitToCtor(((Expr.StrLit) s).val)) ? TRUE : FALSE;
        return UNDEF;
    }

    private boolean isDefEqUnitLike(Expr t, Expr s) {
        Expr tType = whnf(infer(t, true));
        Expr I = tType.getAppFn();
        if (I.kind != Expr.Kind.CONST || !isStructureLike(((Expr.Const) I).name)) return false;
        Decl.Inductive ind = (Decl.Inductive) env.get(((Expr.Const) I).name);
        Decl.Ctor ctor = (Decl.Ctor) env.get(ind.ctors.get(0));
        if (ctor.numFields != 0) return false;
        return isDefEqCore(tType, infer(s, true));
    }

    // ---- lazy delta reduction ---------------------------------------------

    private static Expr natPred(Expr e) {
        if (e.kind == Expr.Kind.NAT) {
            BigInteger v = ((Expr.NatLit) e).val;
            return v.signum() > 0 ? Expr.nat(v.subtract(BigInteger.ONE)) : null;
        }
        if (e.kind == Expr.Kind.APP && ((Expr.App) e).fn.isConstOf(Names.NAT_SUCC)) return ((Expr.App) e).arg;
        return null;
    }

    private int isDefEqOffsetNat(Expr t, Expr s) {
        if (isNatZero(t) && isNatZero(s)) return TRUE;
        Expr pt = natPred(t), ps = natPred(s);
        if (pt != null && ps != null) return isDefEqCore(pt, ps) ? TRUE : FALSE;
        return UNDEF;
    }

    private static int compareHints(Decl a, Decl b) {
        int ka = hintKind(a), kb = hintKind(b); // 0 opaque, 1 abbrev, 2 regular
        if (ka == kb) {
            if (ka != 2) return 0;
            long ha = ((Decl.Def) a).height, hb = ((Decl.Def) b).height;
            return ha == hb ? 0 : ha > hb ? -1 : 1;
        }
        if (ka == 0) return 1;
        if (kb == 0) return -1;
        if (ka == 1) return -1;
        return 1;
    }

    private static int hintKind(Decl d) {
        if (!(d instanceof Decl.Def)) return 0; // theorems behave as opaque
        String h = ((Decl.Def) d).hints;
        return h.equals("opaque") ? 0 : h.equals("abbrev") ? 1 : 2;
    }

    private static final int CONTINUE = 0, DEF_EQ = 1, DEF_DIFF = 2, DEF_UNKNOWN = 3;

    /** One delta step on the pair; updates st in place. */
    private int lazyDeltaStep(Expr[] st) {
        Expr t = st[0], s = st[1];
        Decl dt = deltaInfo(t), ds = deltaInfo(s);
        if (DEBUG_NAT) {
            String a = t.getAppFn() instanceof Expr.Const ? ((Expr.Const) t.getAppFn()).name.toString() : t.getAppFn().kind.toString();
            String b = s.getAppFn() instanceof Expr.Const ? ((Expr.Const) s.getAppFn()).name.toString() : s.getAppFn().kind.toString();
            String cmp = dt != null && ds != null ? " cmp=" + compareHints(dt, ds) + " ht=" + (dt instanceof Decl.Def ? ((Decl.Def) dt).hints + ((Decl.Def) dt).height : "thm") + " hs=" + (ds instanceof Decl.Def ? ((Decl.Def) ds).hints + ((Decl.Def) ds).height : "thm") : "";
            System.err.println("STEP depth=" + dbgStack.size() + " " + a + " | " + b + cmp);
            if (a.equals("Sub.sub") || a.equals("Nat.sub")) { if (s.getAppFn() instanceof Expr.Proj) { Expr pstruct = ((Expr.Proj) s.getAppFn()).struct; Expr w = whnf(pstruct); String ws = w.toString(); System.err.println("   WHNF(struct)=" + ws.substring(0, Math.min(300, ws.length())) + "  headkind=" + w.getAppFn().kind + " tc=" + (w.getAppFn() instanceof Expr.Const ? env.get(((Expr.Const) w.getAppFn()).name) : null)); } String ts = t.toString(), ss = s.toString(); System.err.println("   T=" + ts.substring(0, Math.min(500, ts.length())) + "\n   S=" + ss.substring(0, Math.min(700, ss.length()))); }
        }
        if (dt == null && ds == null) return DEF_UNKNOWN;
        if (dt != null && ds == null) {
            // The other side may only be stuck on a projection that a full whnfCore can reduce; do that
            // before unfolding a definition, which could otherwise start a huge unrelated computation.
            if (s.getAppFn().kind == Expr.Kind.PROJ) {
                Expr s2 = whnfCore(s);
                if (!s2.equals(s)) { st[1] = s2; return afterStep(st); }
            }
            Expr u = unfoldDefinition(t);
            if (u == null) return DEF_UNKNOWN;
            st[0] = whnfCore(u, false, true);
        } else if (dt == null) {
            if (t.getAppFn().kind == Expr.Kind.PROJ) {
                Expr t2 = whnfCore(t);
                if (!t2.equals(t)) { st[0] = t2; return afterStep(st); }
            }
            Expr u = unfoldDefinition(s);
            if (u == null) return DEF_UNKNOWN;
            st[1] = whnfCore(u, false, true);
        } else {
            int c = compareHints(dt, ds);
            if (c < 0) {
                Expr u = unfoldDefinition(t);
                if (u == null) return DEF_UNKNOWN;
                st[0] = whnfCore(u, false, true);
            } else if (c > 0) {
                Expr u = unfoldDefinition(s);
                if (u == null) return DEF_UNKNOWN;
                st[1] = whnfCore(u, false, true);
            } else {
                if (t.kind == Expr.Kind.APP && s.kind == Expr.Kind.APP && dt == ds && hintKind(dt) == 2) {
                    List<Expr> key = List.of(t, s);
                    if (!failCache.contains(key)) {
                        if (levelsEquiv(((Expr.Const) t.getAppFn()).levels, ((Expr.Const) s.getAppFn()).levels) && isDefEqArgs(t, s)) return DEF_EQ;
                        failCache.add(key);
                    }
                }
                Expr ut = unfoldDefinition(t), us = unfoldDefinition(s);
                if (ut == null || us == null) return DEF_UNKNOWN;
                st[0] = whnfCore(ut, false, true);
                st[1] = whnfCore(us, false, true);
            }
        }
        if (DEBUG_NAT) System.err.println("   after: " + st[0].getAppFn().kind + (st[0].getAppFn() instanceof Expr.Const ? ":" + ((Expr.Const) st[0].getAppFn()).name : "") + " | " + st[1].getAppFn().kind + (st[1].getAppFn() instanceof Expr.Const ? ":" + ((Expr.Const) st[1].getAppFn()).name : ""));
        return afterStep(st);
    }

    private int afterStep(Expr[] st) {
        int r = quickIsDefEq(st[0], st[1]);
        if (r == TRUE) return DEF_EQ;
        if (r == FALSE) return DEF_DIFF;
        return CONTINUE;
    }

    /** Returns TRUE/FALSE when decided, UNDEF when the (updated) terms need the remaining rules. */
    private int lazyDeltaReduction(Expr[] st) {
        while (true) {
            Expr t = st[0], s = st[1];
            int r = isDefEqOffsetNat(t, s);
            if (r != UNDEF) return r;
            if (!t.hasFVar && !s.hasFVar) {
                Expr tv = reduceNat(t);
                if (tv != null) return isDefEqCore(tv, s) ? TRUE : FALSE;
                Expr sv = reduceNat(s);
                if (sv != null) return isDefEqCore(t, sv) ? TRUE : FALSE;
            }
            switch (lazyDeltaStep(st)) {
                case CONTINUE: break;
                case DEF_EQ: return TRUE;
                case DEF_DIFF: return FALSE;
                default: return UNDEF;
            }
        }
    }

    /** Same as lazyDeltaReduction but for the structure arguments of two projections with the same index. */
    private boolean lazyDeltaProjReduction(Expr[] st, int idx) {
        while (true) {
            switch (lazyDeltaStep(st)) {
                case CONTINUE: break;
                case DEF_EQ: return true;
                default: {
                    Expr tc = reduceProjCore(st[0], idx);
                    if (tc != null) {
                        Expr sc = reduceProjCore(st[1], idx);
                        if (sc != null) return isDefEqCore(tc, sc);
                    }
                    return isDefEqCore(st[0], st[1]);
                }
            }
        }
    }

    private Expr reduceProjCore(Expr c, int idx) {
        if (c.kind == Expr.Kind.STR) c = whnf(strLitToCtor(((Expr.StrLit) c).val));
        Expr fn = c.getAppFn();
        if (fn.kind != Expr.Kind.CONST) return null;
        Decl d = env.get(((Expr.Const) fn).name);
        if (!(d instanceof Decl.Ctor)) return null;
        List<Expr> args = c.getAppArgs();
        int i = ((Decl.Ctor) d).numParams + idx;
        return i < args.size() ? args.get(i) : null;
    }
}
