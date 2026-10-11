package tenet;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Validates a (mutual, non-nested) inductive declaration and generates its constructors' bookkeeping and
 * its recursors. This follows the construction in Lean 4's kernel (add_inductive_fn). The input is only
 * the declaration proper (types and constructor types); everything else is derived here, never trusted.
 */
final class InductiveChecker {
    /** What the checker derives from a declaration. */
    static final class Result {
        final List<Decl.Inductive> types = new ArrayList<>();
        final List<Decl.Ctor> ctors = new ArrayList<>();
        final List<Decl.Recursor> recs = new ArrayList<>();
    }

    private final Env env;
    private final TypeChecker tc;
    private final IndSpec spec;

    private final List<Name> lparams;
    private final List<Level> levels = new ArrayList<>();
    private final int nparams;
    private final boolean isUnsafe;
    private final List<IndSpec.Type> types;
    private final List<Expr> indConsts = new ArrayList<>();
    private final Set<Name> indNames = new HashSet<>();
    private final List<Expr> params = new ArrayList<>();
    private final int[] nindices;
    private Level resultLevel;
    private boolean isNotZero;
    private Level elimLevel;
    private boolean kTarget;
    private final Result result = new Result();

    InductiveChecker(Env env, TypeChecker tc, IndSpec spec) {
        this.env = env;
        this.tc = tc;
        this.spec = spec;
        this.types = spec.types;
        this.lparams = spec.lparams;
        for (Name n : lparams) levels.add(Level.param(n));
        this.nparams = spec.nparams;
        this.isUnsafe = spec.isUnsafe;
        this.nindices = new int[types.size()];
        for (IndSpec.Type t : types) {
            indConsts.add(Expr.cnst(t.name, levels));
            indNames.add(t.name);
        }
    }

    private static KernelException err(String m) { return new KernelException(m); }

    private static final Name OPT_PARAM = Name.of("optParam"), OUT_PARAM = Name.of("outParam"), AUTO_PARAM = Name.of("autoParam"),
            SEMI_OUT_PARAM = Name.of("semiOutParam");

    /** Lean's consume_type_annotations: strips optParam / outParam / autoParam wrappers from a binder type. */
    static Expr consumeTypeAnnotations(Expr e) {
        while (true) {
            Expr f = e.getAppFn();
            if (f.kind != Expr.Kind.CONST) return e;
            Name n = ((Expr.Const) f).name;
            int na = e.getAppNumArgs();
            if (na == 2 && (n.equals(OPT_PARAM) || n.equals(AUTO_PARAM))) e = e.getAppArgs().get(0);
            else if (na == 1 && (n.equals(OUT_PARAM) || n.equals(SEMI_OUT_PARAM))) e = e.getAppArgs().get(0);
            else return e;
        }
    }

    private Expr localFor(Expr.Binder b) {
        return tc.mkLocal(b.name, consumeTypeAnnotations(b.type), b.info);
    }

    // ---- helpers -----------------------------------------------------------

    private boolean hasIndOcc(Expr e) { return hasIndOcc(e, new IdentityHashMap<>()); }

    private boolean hasIndOcc(Expr e, Map<Expr, Boolean> seen) {
        switch (e.kind) {
            case CONST: return indNames.contains(((Expr.Const) e).name);
            case APP: case LAM: case PI: case LET: case PROJ: break;
            default: return false;
        }
        Boolean c = seen.get(e);
        if (c != null) return c;
        boolean r;
        switch (e.kind) {
            case APP: r = hasIndOcc(((Expr.App) e).fn, seen) || hasIndOcc(((Expr.App) e).arg, seen); break;
            case LAM: case PI: r = hasIndOcc(((Expr.Binder) e).type, seen) || hasIndOcc(((Expr.Binder) e).body, seen); break;
            case LET: r = hasIndOcc(((Expr.Let) e).type, seen) || hasIndOcc(((Expr.Let) e).value, seen) || hasIndOcc(((Expr.Let) e).body, seen); break;
            default: r = hasIndOcc(((Expr.Proj) e).struct, seen);
        }
        seen.put(e, r);
        return r;
    }

    /** Is t of the form I_idx params indices, with exactly our parameters? */
    private boolean isValidIndApp(Expr t, int idx) {
        Expr f = t.getAppFn();
        if (!f.equals(indConsts.get(idx))) return false;
        List<Expr> args = t.getAppArgs();
        if (args.size() != nparams + nindices[idx]) return false;
        for (int i = 0; i < nparams; i++) if (!params.get(i).equals(args.get(i))) return false;
        return true;
    }

    private int validIndAppIdx(Expr t) {
        for (int i = 0; i < types.size(); i++) if (isValidIndApp(t, i)) return i;
        return -1;
    }

    private boolean isRecArgument(Expr t) {
        t = tc.whnf(t);
        while (t.kind == Expr.Kind.PI) {
            Expr.Binder b = (Expr.Binder) t;
            Expr l = localFor(b);
            t = tc.whnf(Expr.instantiate1(b.body, l));
        }
        return validIndAppIdx(t) >= 0;
    }

    /** A binder telescope may hide behind a definition (`Presieve X` unfolds to a Pi); expose it. */
    private Expr piView(Expr t) {
        if (t.kind == Expr.Kind.PI) return t;
        Expr w = tc.whnf(t);
        return w.kind == Expr.Kind.PI ? w : t;
    }

    // ---- main entry --------------------------------------------------------

    Result run() {
        checkInductiveTypes();
        declareInductiveTypes();
        checkConstructors();
        declareConstructors();
        initElimLevel();
        initKTarget();
        generateRecursors();
        return result;
    }

    // ---- types -------------------------------------------------------------

    private void checkInductiveTypes() {
        boolean first = true;
        for (int idx = 0; idx < types.size(); idx++) {
            IndSpec.Type ind = types.get(idx);
            if (env.contains(ind.name)) throw err("already declared: " + ind.name);
            Expr type = ind.type;
            if (type.hasFVar || type.looseBVarRange > 0) throw err("inductive type has free variables: " + ind.name);
            tc.ensureSort(tc.check(type), type);
            int i = 0, nidx = 0;
            while ((type = piView(type)).kind == Expr.Kind.PI) {
                Expr.Binder b = (Expr.Binder) type;
                if (i < nparams) {
                    if (first) {
                        Expr p = localFor(b);
                        params.add(p);
                        type = Expr.instantiate1(b.body, p);
                    } else {
                        if (!tc.isDefEq(b.type, tc.local(params.get(i)).type))
                            throw err("parameters of all inductive datatypes must match");
                        type = Expr.instantiate1(b.body, params.get(i));
                    }
                    i++;
                } else {
                    type = Expr.instantiate1(b.body, localFor(b));
                    nidx++;
                }
            }
            if (i != nparams) throw err("number of parameters mismatch in inductive datatype declaration");
            Level lvl = tc.ensureSort(type, type);
            if (first) {
                resultLevel = lvl;
                isNotZero = lvl.isNeverZero();
                first = false;
            } else if (!lvl.isEquiv(resultLevel)) {
                throw err("mutually inductive types must live in the same universe");
            }
            nindices[idx] = nidx;
        }
    }

    /** Syntactic: does any constructor binder mention one of the types being declared? */
    private boolean computeIsRec() {
        for (IndSpec.Type ind : types)
            for (IndSpec.Ctor c : ind.ctors) {
                Expr t = c.type;
                while (t.kind == Expr.Kind.PI) {
                    if (hasIndOcc(((Expr.Binder) t).type)) return true;
                    t = ((Expr.Binder) t).body;
                }
            }
        return false;
    }

    private boolean computeIsReflexive() {
        for (IndSpec.Type ind : types)
            for (IndSpec.Ctor c : ind.ctors) {
                Expr t = c.type;
                while (t.kind == Expr.Kind.PI) {
                    Expr.Binder b = (Expr.Binder) t;
                    if (b.type.kind == Expr.Kind.PI && hasIndOcc(b.type)) return true;
                    t = b.body;
                }
            }
        return false;
    }

    private void declareInductiveTypes() {
        boolean isRec = computeIsRec(), isReflexive = computeIsReflexive();
        List<Name> all = spec.typeNames();
        for (int idx = 0; idx < types.size(); idx++) {
            IndSpec.Type t = types.get(idx);
            List<Name> cnames = new ArrayList<>();
            for (IndSpec.Ctor c : t.ctors) cnames.add(c.name);
            Decl.Inductive d = new Decl.Inductive(t.name, lparams, t.type, nparams, nindices[idx], all, cnames, 0, isRec, isUnsafe, isReflexive);
            result.types.add(d);
            env.add(d);
        }
    }

    // ---- constructors ------------------------------------------------------

    private void checkConstructors() {
        for (int idx = 0; idx < types.size(); idx++) {
            IndSpec.Type ind = types.get(idx);
            for (IndSpec.Ctor c : ind.ctors) {
                Name cn = c.name;
                if (env.contains(cn)) throw err("already declared: " + cn);
                Expr t = c.type;
                if (t.hasFVar || t.looseBVarRange > 0) throw err("constructor type has free variables: " + cn);
                tc.ensureSort(tc.check(t), t);
                int i = 0;
                while (t.kind == Expr.Kind.PI) {
                    Expr.Binder b = (Expr.Binder) t;
                    if (i < nparams) {
                        if (!tc.isDefEq(b.type, tc.local(params.get(i)).type))
                            throw err("arg #" + (i + 1) + " of '" + cn + "' does not match inductive datatype parameters");
                        t = Expr.instantiate1(b.body, params.get(i));
                    } else {
                        Level s = tc.ensureSort(tc.infer(b.type), b.type);
                        if (!(resultLevel.isGeq(s) || resultLevel.isEquivZero()))
                            throw err("universe level of type_of(arg #" + (i + 1) + ") of '" + cn + "' is too big for the corresponding inductive datatype");
                        if (!isUnsafe) checkPositivity(b.type, cn, i);
                        Expr l = localFor(b);
                        t = Expr.instantiate1(b.body, l);
                    }
                    i++;
                }
                if (i < nparams) throw err("constructor " + cn + " has too few parameters");
                if (!isValidIndApp(t, idx)) throw err("invalid return type for '" + cn + "'");
                for (Expr ia : t.getAppArgs().subList(nparams, t.getAppNumArgs()))
                    if (hasIndOcc(ia)) throw err("inductive occurrence in an index of the result type of '" + cn + "'");
            }
        }
    }

    private void checkPositivity(Expr t, Name cn, int argIdx) {
        t = tc.whnf(t);
        if (!hasIndOcc(t)) return;
        if (t.kind == Expr.Kind.PI) {
            Expr.Binder b = (Expr.Binder) t;
            if (hasIndOcc(b.type)) throw err("arg #" + (argIdx + 1) + " of '" + cn + "' has a non positive occurrence of the datatypes being declared");
            Expr l = localFor(b);
            checkPositivity(Expr.instantiate1(b.body, l), cn, argIdx);
        } else if (validIndAppIdx(t) < 0) {
            throw err("arg #" + (argIdx + 1) + " of '" + cn + "' has a non valid occurrence of the datatypes being declared");
        }
    }

    private void declareConstructors() {
        for (int idx = 0; idx < types.size(); idx++) {
            IndSpec.Type ind = types.get(idx);
            int cidx = 0;
            for (IndSpec.Ctor c : ind.ctors) {
                int nfields = 0, i = 0;
                for (Expr t = c.type; t.kind == Expr.Kind.PI; t = ((Expr.Binder) t).body) {
                    if (i >= nparams) nfields++;
                    i++;
                }
                Decl.Ctor d = new Decl.Ctor(c.name, lparams, c.type, ind.name, cidx++, nparams, nfields, isUnsafe);
                result.ctors.add(d);
                env.add(d);
            }
        }
    }

    // ---- eliminator universe -----------------------------------------------

    private boolean elimOnlyAtUniverseZero() {
        if (isNotZero) return false;
        if (types.size() > 1) return true;
        IndSpec.Type ind = types.get(0);
        int n = ind.ctors.size();
        if (n > 1) return true;
        if (n == 0) return false;
        Expr t = ind.ctors.get(0).type;
        int i = 0;
        List<Expr> toCheck = new ArrayList<>();
        while (t.kind == Expr.Kind.PI) {
            Expr.Binder b = (Expr.Binder) t;
            if (i < nparams) {
                t = Expr.instantiate1(b.body, params.get(i));
            } else {
                Expr l = localFor(b);
                Level s = tc.ensureSort(tc.infer(b.type), b.type);
                if (!s.isEquivZero()) toCheck.add(l);
                t = Expr.instantiate1(b.body, l);
            }
            i++;
        }
        List<Expr> resArgs = t.getAppArgs();
        for (Expr f : toCheck) if (!resArgs.contains(f)) return true;
        return false;
    }

    private void initElimLevel() {
        if (elimOnlyAtUniverseZero()) {
            elimLevel = Level.ZERO;
        } else {
            Name u = Name.of("u");
            int i = 1;
            while (lparams.contains(u)) u = Name.str(Name.ANON, "u_" + i++);
            elimLevel = Level.param(u);
        }
    }

    private void initKTarget() {
        kTarget = types.size() == 1 && resultLevel.isEquivZero() && types.get(0).ctors.size() == 1;
        if (!kTarget) return;
        Expr it = types.get(0).ctors.get(0).type;
        int i = 0;
        while (it.kind == Expr.Kind.PI) {
            if (i < nparams) it = ((Expr.Binder) it).body;
            else { kTarget = false; break; }
            i++;
        }
    }

    // ---- recursors ---------------------------------------------------------

    private static final class RecInfo {
        Expr motive;
        List<Expr> indices = new ArrayList<>();
        Expr major;
    }

    private Name recName(int idx) { return Name.str(types.get(idx).name, "rec"); }

    /** Fields (all non-parameter binders) of a constructor, with the recursive ones also listed in u. */
    private Expr ctorTelescope(IndSpec.Ctor c, List<Expr> bu, List<Expr> u) {
        Expr t = c.type;
        int i = 0;
        while (t.kind == Expr.Kind.PI) {
            Expr.Binder b = (Expr.Binder) t;
            if (i < nparams) {
                t = Expr.instantiate1(b.body, params.get(i));
            } else {
                Expr l = localFor(b);
                bu.add(l);
                if (isRecArgument(b.type)) u.add(l);
                t = Expr.instantiate1(b.body, l);
            }
            i++;
        }
        return t;
    }

    /** For a recursive field u_i: its telescope xs, the index k of the type it recurses on, and that type's indices. */
    private int recFieldInfo(Expr ui, List<Expr> xs, List<Expr> kIndices) {
        Expr uiTy = tc.whnf(tc.local(ui).type);
        while (uiTy.kind == Expr.Kind.PI) {
            Expr.Binder b = (Expr.Binder) uiTy;
            Expr x = localFor(b);
            xs.add(x);
            uiTy = tc.whnf(Expr.instantiate1(b.body, x));
        }
        int k = validIndAppIdx(uiTy);
        kIndices.addAll(uiTy.getAppArgs().subList(nparams, uiTy.getAppNumArgs()));
        return k;
    }

    private void generateRecursors() {
        int n = types.size();
        RecInfo[] infos = new RecInfo[n];
        for (int d = 0; d < n; d++) {
            RecInfo info = new RecInfo();
            Expr t = types.get(d).type;
            int i = 0;
            while ((t = piView(t)).kind == Expr.Kind.PI) {
                Expr.Binder b = (Expr.Binder) t;
                if (i < nparams) {
                    t = Expr.instantiate1(b.body, params.get(i));
                } else {
                    Expr idx = localFor(b);
                    info.indices.add(idx);
                    t = Expr.instantiate1(b.body, idx);
                }
                i++;
            }
            Expr majorTy = Expr.apps(Expr.apps(indConsts.get(d), params), info.indices);
            info.major = tc.mkLocal(Name.of("t"), majorTy, "default");
            Expr cTy = Expr.sort(elimLevel);
            List<Expr> mi = new ArrayList<>(info.indices);
            mi.add(info.major);
            cTy = tc.mkPi(mi, cTy);
            Name cName = n > 1 ? Name.of("motive_" + (d + 1)) : Name.of("motive");
            info.motive = tc.mkLocal(cName, cTy, "implicit");
            infos[d] = info;
        }
        List<Expr> allMinors = new ArrayList<>();
        List<Expr> allMotives = new ArrayList<>();
        for (RecInfo info : infos) allMotives.add(info.motive);
        for (int d = 0; d < n; d++) {
            for (IndSpec.Ctor c : types.get(d).ctors) {
                List<Expr> bu = new ArrayList<>(), u = new ArrayList<>(), v = new ArrayList<>();
                Expr t = ctorTelescope(c, bu, u);
                int itIdx = validIndAppIdx(t);
                List<Expr> itIndices = t.getAppArgs().subList(nparams, t.getAppNumArgs());
                Expr introApp = Expr.apps(Expr.apps(Expr.cnst(c.name, levels), params), bu);
                Expr cApp = Expr.app(Expr.apps(infos[itIdx].motive, itIndices), introApp);
                for (Expr ui : u) {
                    List<Expr> xs = new ArrayList<>(), kIndices = new ArrayList<>();
                    int k = recFieldInfo(ui, xs, kIndices);
                    Expr ihApp = Expr.app(Expr.apps(infos[k].motive, kIndices), Expr.apps(ui, xs));
                    v.add(tc.mkLocal(Name.str(tc.local(ui).name, "ih"), tc.mkPi(xs, ihApp), "default"));
                }
                List<Expr> bv = new ArrayList<>(bu);
                bv.addAll(v);
                allMinors.add(tc.mkLocal(Name.of("minor"), tc.mkPi(bv, cApp), "default"));
            }
        }
        int nMinors = allMinors.size();
        List<Name> all = spec.typeNames();
        List<Name> recLps = new ArrayList<>();
        if (elimLevel.kind == Level.Kind.PARAM) recLps.add(((Level.Param) elimLevel).name);
        recLps.addAll(lparams);
        List<Level> recLevels = new ArrayList<>();
        for (Name ln : recLps) recLevels.add(Level.param(ln));
        int minorIdx = 0;
        for (int d = 0; d < n; d++) {
            RecInfo info = infos[d];
            Expr majorApp = Expr.app(Expr.apps(info.motive, info.indices), info.major);
            List<Expr> binders = new ArrayList<>(params);
            binders.addAll(allMotives);
            binders.addAll(allMinors);
            binders.addAll(info.indices);
            binders.add(info.major);
            Expr recTy = tc.mkPi(binders, majorApp);
            List<Decl.RecRule> rules = new ArrayList<>();
            for (IndSpec.Ctor c : types.get(d).ctors) {
                List<Expr> bu = new ArrayList<>(), u = new ArrayList<>(), v = new ArrayList<>();
                ctorTelescope(c, bu, u);
                for (Expr ui : u) {
                    List<Expr> xs = new ArrayList<>(), kIndices = new ArrayList<>();
                    int k = recFieldInfo(ui, xs, kIndices);
                    Expr recApp = Expr.apps(Expr.cnst(recName(k), recLevels), params);
                    recApp = Expr.apps(recApp, allMotives);
                    recApp = Expr.apps(recApp, allMinors);
                    recApp = Expr.apps(recApp, kIndices);
                    recApp = Expr.app(recApp, Expr.apps(ui, xs));
                    v.add(tc.mkLambda(xs, recApp));
                }
                Expr eApp = Expr.apps(Expr.apps(allMinors.get(minorIdx++), bu), v);
                List<Expr> lamBinders = new ArrayList<>(params);
                lamBinders.addAll(allMotives);
                lamBinders.addAll(allMinors);
                lamBinders.addAll(bu);
                rules.add(new Decl.RecRule(c.name, bu.size(), tc.mkLambda(lamBinders, eApp)));
            }
            Decl.Recursor rec = new Decl.Recursor(recName(d), recLps, recTy, all, nparams, nindices[d], n, nMinors, rules, kTarget, isUnsafe);
            result.recs.add(rec);
            env.add(rec);
        }
    }
}
