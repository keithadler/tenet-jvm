package leankernel;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Validates a (mutual, non-nested) inductive declaration group and regenerates its recursors, which are
 * then compared with the exported ones. This follows the construction in Lean 4's kernel
 * (add_inductive_fn): the exported recursors and rules are never trusted, only compared.
 */
final class InductiveChecker {
    private final Env env;
    private final TypeChecker tc;
    private final InductiveBlock block;

    private final List<Name> lparams;
    private final List<Level> levels = new ArrayList<>();
    private final int nparams;
    private final boolean isUnsafe;
    private final List<Decl.Inductive> types;
    private final List<Expr> indConsts = new ArrayList<>();
    private final Set<Name> indNames = new HashSet<>();
    private final List<Expr> params = new ArrayList<>();
    private final int[] nindices;
    private Level resultLevel;
    private boolean isNotZero;
    private Level elimLevel;
    private boolean kTarget;

    InductiveChecker(Env env, TypeChecker tc, InductiveBlock block) {
        this.env = env;
        this.tc = tc;
        this.block = block;
        this.types = block.types;
        this.lparams = types.get(0).levelParams;
        for (Name n : lparams) levels.add(Level.param(n));
        this.nparams = types.get(0).numParams;
        this.isUnsafe = types.get(0).isUnsafe;
        this.nindices = new int[types.size()];
        for (Decl.Inductive t : types) {
            indConsts.add(Expr.cnst(t.name, levels));
            indNames.add(t.name);
        }
    }

    private static KernelException err(String m) { return new KernelException(m); }

    private static final Name OPT_PARAM = Name.of("optParam"), OUT_PARAM = Name.of("outParam"), AUTO_PARAM = Name.of("autoParam"), SEMI_OUT_PARAM = Name.of("semiOutParam");

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

    private boolean hasIndOcc(Expr e) {
        return hasIndOcc(e, new IdentityHashMap<>());
    }

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

    // ---- main entry --------------------------------------------------------

    void run() {
        checkInductiveTypes();
        declareInductiveTypes();
        checkConstructors();
        declareConstructors();
        initElimLevel();
        initKTarget();
        checkAndDeclareRecursors();
    }

    // ---- types -------------------------------------------------------------

    private void checkInductiveTypes() {
        boolean first = true;
        for (int idx = 0; idx < types.size(); idx++) {
            Decl.Inductive ind = types.get(idx);
            if (!ind.levelParams.equals(lparams)) throw err("mutual inductive types must have the same universe parameters");
            if (ind.numParams != nparams) throw err("mutual inductive types must have the same number of parameters");
            if (ind.isUnsafe != isUnsafe) throw err("mutual inductive types must agree on unsafe");
            if (env.contains(ind.name)) throw err("already declared: " + ind.name);
            Expr type = ind.type;
            tc.ensureSort(tc.check(type), type);
            int i = 0, nidx = 0;
            while (type.kind == Expr.Kind.PI) {
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
                    type = b.body;
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
            if (ind.numIndices != nidx) throw err("exported number of indices of " + ind.name + " is wrong");
        }
    }

    private void declareInductiveTypes() {
        // isRec / isReflexive are recomputed after constructors are known; the exported values are compared later
        for (Decl.Inductive t : types) env.add(t);
    }

    // ---- constructors ------------------------------------------------------

    private void checkConstructors() {
        List<Name> seenCtors = new ArrayList<>();
        for (int idx = 0; idx < types.size(); idx++) {
            Decl.Inductive ind = types.get(idx);
            int cidx = 0;
            for (Name cn : ind.ctors) {
                Decl.Ctor c = findCtor(cn);
                if (c == null) throw err("constructor " + cn + " listed by " + ind.name + " is missing from the export");
                seenCtors.add(cn);
                if (env.contains(cn)) throw err("already declared: " + cn);
                if (!c.induct.equals(ind.name)) throw err("constructor " + cn + " belongs to the wrong inductive type");
                if (c.cidx != cidx) throw err("constructor " + cn + " has the wrong index");
                if (!c.levelParams.equals(lparams)) throw err("constructor " + cn + " has different universe parameters");
                if (c.numParams != nparams) throw err("constructor " + cn + " has the wrong number of parameters");
                if (c.isUnsafe != isUnsafe) throw err("constructor " + cn + " has the wrong unsafe flag");
                cidx++;
                Expr t = c.type;
                if (t.hasFVar || t.looseBVarRange > 0) throw err("constructor type has free variables: " + cn);
                tc.ensureSort(tc.check(t), t);
                int i = 0, nfields = 0;
                while (t.kind == Expr.Kind.PI) {
                    Expr.Binder b = (Expr.Binder) t;
                    if (i < nparams) {
                        if (!tc.isDefEq(b.type, tc.local(params.get(i)).type))
                            throw err("arg #" + (i + 1) + " of '" + cn + "' does not match inductive datatype parameters");
                        t = Expr.instantiate1(b.body, params.get(i));
                    } else {
                        Level s = tc.ensureSort(tc.infer(b.type), b.type);
                        if (!(resultLevel.isGeq(s) || resultLevel.isZero()))
                            throw err("universe level of type_of(arg #" + (i + 1) + ") of '" + cn + "' is too big for the corresponding inductive datatype");
                        if (!isUnsafe) checkPositivity(b.type, cn, i);
                        Expr l = localFor(b);
                        t = Expr.instantiate1(b.body, l);
                        nfields++;
                    }
                    i++;
                }
                if (i < nparams) throw err("constructor " + cn + " has too few parameters");
                if (!isValidIndApp(t, idx)) throw err("invalid return type for '" + cn + "'");
                for (Expr ia : t.getAppArgs().subList(nparams, t.getAppNumArgs()))
                    if (hasIndOcc(ia)) throw err("inductive occurrence in an index of the result type of '" + cn + "'");
                if (c.numFields != nfields) throw err("constructor " + cn + " has the wrong number of fields");
            }
        }
        if (seenCtors.size() != block.ctors.size()) throw err("export contains constructors that no inductive type lists");
    }

    private Decl.Ctor findCtor(Name n) {
        for (Decl.Ctor c : block.ctors) if (c.name.equals(n)) return c;
        return null;
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
        for (Decl.Ctor c : block.ctors) env.add(c);
        // compare the informational flags on the inductive types with what the constructors imply
        boolean anyRec = false, anyReflexive = false;
        for (Decl.Inductive ind : types) {
            boolean isRec = false, isReflexive = false;
            for (Name cn : ind.ctors) {
                Decl.Ctor c = findCtor(cn);
                Expr t = c.type;
                int i = 0;
                while (t.kind == Expr.Kind.PI) {
                    Expr.Binder b = (Expr.Binder) t;
                    if (i < nparams) {
                        t = Expr.instantiate1(b.body, params.get(i));
                    } else {
                        if (isRecArgument(b.type)) {
                            isRec = true;
                            if (tc.whnf(b.type).kind == Expr.Kind.PI) isReflexive = true;
                        }
                        Expr l = localFor(b);
                        t = Expr.instantiate1(b.body, l);
                    }
                    i++;
                }
            }
            anyRec |= isRec;
            anyReflexive |= isReflexive;
        }
        for (Decl.Inductive ind : types) {
            if (ind.isRec != anyRec) throw err("exported isRec flag of " + ind.name + " is wrong");
            if (ind.isReflexive != anyReflexive) throw err("exported isReflexive flag of " + ind.name + " is wrong");
            if (ind.numNested != 0) throw err("unexpected nested count for " + ind.name);
            if (!ind.all.equals(names(types))) throw err("exported 'all' of " + ind.name + " is wrong");
        }
    }

    private static List<Name> names(List<Decl.Inductive> ts) {
        List<Name> r = new ArrayList<>();
        for (Decl.Inductive t : ts) r.add(t.name);
        return r;
    }

    // ---- eliminator universe -----------------------------------------------

    private boolean elimOnlyAtUniverseZero() {
        if (isNotZero) return false;
        if (types.size() > 1) return true;
        Decl.Inductive ind = types.get(0);
        int n = ind.ctors.size();
        if (n > 1) return true;
        if (n == 0) return false;
        Decl.Ctor c = findCtor(ind.ctors.get(0));
        Expr t = c.type;
        int i = 0;
        List<Expr> toCheck = new ArrayList<>();
        while (t.kind == Expr.Kind.PI) {
            Expr.Binder b = (Expr.Binder) t;
            if (i < nparams) {
                t = Expr.instantiate1(b.body, params.get(i));
            } else {
                Expr l = localFor(b);
                Level s = tc.ensureSort(tc.infer(b.type), b.type);
                if (!s.isZero()) toCheck.add(l);
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
        kTarget = types.size() == 1 && resultLevel.isZero() && types.get(0).ctors.size() == 1;
        if (!kTarget) return;
        Expr it = findCtor(types.get(0).ctors.get(0)).type;
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
        List<Expr> minors = new ArrayList<>();
    }

    private Name recName(int idx) { return Name.str(types.get(idx).name, "rec"); }

    private void checkAndDeclareRecursors() {
        int n = types.size();
        RecInfo[] infos = new RecInfo[n];
        // motives and majors
        for (int d = 0; d < n; d++) {
            RecInfo info = new RecInfo();
            Expr t = types.get(d).type;
            int i = 0;
            while (t.kind == Expr.Kind.PI) {
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
        // minor premises
        List<Expr> allMinors = new ArrayList<>();
        List<Expr> allMotives = new ArrayList<>();
        for (RecInfo info : infos) allMotives.add(info.motive);
        for (int d = 0; d < n; d++) {
            for (Name cn : types.get(d).ctors) {
                Decl.Ctor c = findCtor(cn);
                List<Expr> bu = new ArrayList<>(), u = new ArrayList<>(), v = new ArrayList<>();
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
                int itIdx = validIndAppIdx(t);
                List<Expr> itIndices = t.getAppArgs().subList(nparams, t.getAppNumArgs());
                Expr introApp = Expr.apps(Expr.apps(Expr.cnst(cn, levels), params), bu);
                Expr cApp = Expr.app(Expr.apps(infos[itIdx].motive, itIndices), introApp);
                for (Expr ui : u) {
                    Expr uiTy = tc.whnf(tc.local(ui).type);
                    List<Expr> xs = new ArrayList<>();
                    while (uiTy.kind == Expr.Kind.PI) {
                        Expr.Binder b = (Expr.Binder) uiTy;
                        Expr x = localFor(b);
                        xs.add(x);
                        uiTy = tc.whnf(Expr.instantiate1(b.body, x));
                    }
                    int k = validIndAppIdx(uiTy);
                    List<Expr> kIndices = uiTy.getAppArgs().subList(nparams, uiTy.getAppNumArgs());
                    Expr ihApp = Expr.app(Expr.apps(infos[k].motive, kIndices), Expr.apps(ui, xs));
                    Expr vTy = tc.mkPi(xs, ihApp);
                    v.add(tc.mkLocal(Name.str(tc.local(ui).name, "ih"), vTy, "default"));
                }
                List<Expr> bv = new ArrayList<>(bu);
                bv.addAll(v);
                Expr minorTy = tc.mkPi(bv, cApp);
                Expr minor = tc.mkLocal(Name.of("minor"), minorTy, "default");
                infos[d].minors.add(minor);
                allMinors.add(minor);
            }
        }
        // build and compare each recursor
        int nMinorsTotal = allMinors.size();
        if (block.recs.size() != n) throw err("export has " + block.recs.size() + " recursors but the block has " + n + " inductive types");
        for (int d = 0; d < n; d++) {
            Decl.Recursor rec = recByName(recName(d));
            if (rec == null) throw err("missing recursor " + recName(d));
            RecInfo info = infos[d];
            List<Name> expectLps = new ArrayList<>();
            if (elimLevel.kind == Level.Kind.PARAM) expectLps.add(((Level.Param) elimLevel).name);
            expectLps.addAll(lparams);
            if (!rec.levelParams.equals(expectLps)) throw err("recursor " + rec.name + " has wrong universe parameters: " + rec.levelParams + " vs " + expectLps);
            Expr majorApp = Expr.app(Expr.apps(info.motive, info.indices), info.major);
            List<Expr> binders = new ArrayList<>(params);
            binders.addAll(allMotives);
            binders.addAll(allMinors);
            binders.addAll(info.indices);
            binders.add(info.major);
            Expr recTy = tc.mkPi(binders, majorApp);
            if (!recTy.equals(rec.type))
                throw err("recursor " + rec.name + " has the wrong type\n  expected: " + recTy + "\n  exported: " + rec.type);
            if (rec.numParams != nparams || rec.numIndices != nindices[d] || rec.numMotives != n || rec.numMinors != nMinorsTotal)
                throw err("recursor " + rec.name + " has wrong counts");
            if (rec.k != kTarget) throw err("recursor " + rec.name + " has the wrong K flag");
            if (rec.isUnsafe != isUnsafe) throw err("recursor " + rec.name + " has the wrong unsafe flag");
            if (!rec.all.equals(names(types))) throw err("recursor " + rec.name + " has the wrong 'all'");
            // rules
            List<Level> recLevels = new ArrayList<>();
            for (Name ln : rec.levelParams) recLevels.add(Level.param(ln));
            Decl.Inductive ind = types.get(d);
            if (rec.rules.size() != ind.ctors.size()) throw err("recursor " + rec.name + " has the wrong number of rules");
            int minorIdx = 0;
            for (int dd = 0; dd < d; dd++) minorIdx += types.get(dd).ctors.size();
            for (int ci = 0; ci < ind.ctors.size(); ci++) {
                Name cn = ind.ctors.get(ci);
                Decl.Ctor c = findCtor(cn);
                List<Expr> bu = new ArrayList<>(), u = new ArrayList<>();
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
                List<Expr> v = new ArrayList<>();
                for (Expr ui : u) {
                    Expr uiTy = tc.whnf(tc.local(ui).type);
                    List<Expr> xs = new ArrayList<>();
                    while (uiTy.kind == Expr.Kind.PI) {
                        Expr.Binder b = (Expr.Binder) uiTy;
                        Expr x = localFor(b);
                        xs.add(x);
                        uiTy = tc.whnf(Expr.instantiate1(b.body, x));
                    }
                    int k = validIndAppIdx(uiTy);
                    List<Expr> kIndices = uiTy.getAppArgs().subList(nparams, uiTy.getAppNumArgs());
                    Expr recApp = Expr.apps(Expr.cnst(recName(k), recLevels), params);
                    recApp = Expr.apps(recApp, allMotives);
                    recApp = Expr.apps(recApp, allMinors);
                    recApp = Expr.apps(recApp, kIndices);
                    recApp = Expr.app(recApp, Expr.apps(ui, xs));
                    v.add(tc.mkLambda(xs, recApp));
                }
                Expr eApp = Expr.apps(Expr.apps(allMinors.get(minorIdx + ci), bu), v);
                List<Expr> lamBinders = new ArrayList<>(params);
                lamBinders.addAll(allMotives);
                lamBinders.addAll(allMinors);
                lamBinders.addAll(bu);
                Expr rhs = tc.mkLambda(lamBinders, eApp);
                Decl.RecRule rule = rec.rules.get(ci);
                if (!rule.ctor.equals(cn) || rule.nfields != bu.size())
                    throw err("recursor rule for " + cn + " has the wrong constructor or field count");
                if (!rhs.equals(rule.rhs))
                    throw err("recursor rule for " + cn + " has the wrong right-hand side\n  expected: " + rhs + "\n  exported: " + rule.rhs);
            }
        }
        for (Decl.Recursor r : block.recs) env.add(r);
    }

    private Decl.Recursor recByName(Name n) {
        for (Decl.Recursor r : block.recs) if (r.name.equals(n)) return r;
        return null;
    }
}
