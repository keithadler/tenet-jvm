package tenet;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Elimination of nested inductive occurrences (Lean 4's elim_nested_inductive). Occurrences such as
 * {@code Array Syntax} inside the declaration of {@code Syntax} are replaced by auxiliary inductive types
 * that are declared together with the originals; after the recursors have been generated for the whole
 * mutual group, the auxiliary types are translated back into the nested applications.
 */
final class NestedInductive {
    private final Env env;       // the environment without the declaration being added
    private final TypeChecker tc;
    private final IndSpec in;
    private final List<Level> lvls = new ArrayList<>();
    private final List<Expr> mParams = new ArrayList<>();
    private final List<Map.Entry<Expr, Name>> nestedAux = new ArrayList<>();
    /** auxiliary type name -> the nested application it stands for, over mParams */
    final Map<Name, Expr> aux2nested = new LinkedHashMap<>();
    private final List<TypeBuilder> newTypes = new ArrayList<>();
    private int nextIdx = 1;

    private static final class TypeBuilder {
        final Name name;
        final Expr type;
        List<IndSpec.Ctor> ctors;
        TypeBuilder(Name n, Expr t, List<IndSpec.Ctor> c) { name = n; type = t; ctors = c; }
    }

    NestedInductive(Env env, TypeChecker tc, IndSpec in) {
        this.env = env;
        this.tc = tc;
        this.in = in;
        for (Name n : in.lparams) lvls.add(Level.param(n));
    }

    private static KernelException err(String m) { return new KernelException(m); }

    private boolean containsNewType(Expr e) {
        switch (e.kind) {
            case CONST: {
                Name n = ((Expr.Const) e).name;
                for (TypeBuilder t : newTypes) if (t.name.equals(n)) return true;
                return false;
            }
            case APP: return containsNewType(((Expr.App) e).fn) || containsNewType(((Expr.App) e).arg);
            case LAM: case PI: return containsNewType(((Expr.Binder) e).type) || containsNewType(((Expr.Binder) e).body);
            case LET: return containsNewType(((Expr.Let) e).type) || containsNewType(((Expr.Let) e).value) || containsNewType(((Expr.Let) e).body);
            case PROJ: return containsNewType(((Expr.Proj) e).struct);
            default: return false;
        }
    }

    private static long[] ids(List<Expr> fvars) {
        long[] r = new long[fvars.size()];
        for (int i = 0; i < r.length; i++) r[i] = ((Expr.FVar) fvars.get(i)).id;
        return r;
    }

    private static Expr instantiatePiParams(Expr e, int n, List<Expr> args) {
        for (int i = 0; i < n; i++) {
            if (e.kind != Expr.Kind.PI) throw err("ill-formed nested inductive type");
            e = ((Expr.Binder) e).body;
        }
        return Expr.instantiateRev(e, args.subList(0, n).toArray(new Expr[0]));
    }

    static Name replacePrefix(Name n, Name prefix, Name newPrefix) {
        if (n.equals(prefix)) return newPrefix;
        if (n.pre == null) return n;
        Name p = replacePrefix(n.pre, prefix, newPrefix);
        if (p == n.pre) return n;
        return n.str != null ? Name.str(p, n.str) : Name.num(p, n.num);
    }

    // ---- elimination -------------------------------------------------------

    IndSpec run() {
        for (IndSpec.Type t : in.types) newTypes.add(new TypeBuilder(t.name, t.type, t.ctors));
        Expr type = in.types.get(0).type;
        for (int i = 0; i < in.nparams; i++) {
            if (type.kind != Expr.Kind.PI) throw err("number of parameters mismatch in inductive datatype declaration");
            Expr.Binder b = (Expr.Binder) type;
            Expr p = tc.mkLocal(b.name, b.type, b.info);
            mParams.add(p);
            type = Expr.instantiate1(b.body, p);
        }
        for (int i = 0; i < newTypes.size(); i++) {
            TypeBuilder t = newTypes.get(i);
            List<IndSpec.Ctor> nc = new ArrayList<>();
            for (IndSpec.Ctor c : t.ctors) {
                Expr ct = c.type;
                List<Expr> As = new ArrayList<>();
                for (int k = 0; k < in.nparams; k++) {
                    if (ct.kind != Expr.Kind.PI) throw err("constructor " + c.name + " has too few parameters");
                    Expr.Binder b = (Expr.Binder) ct;
                    Expr a = tc.mkLocal(b.name, b.type, b.info);
                    As.add(a);
                    ct = Expr.instantiate1(b.body, a);
                }
                Expr replaced = Expr.replace(ct, (e, off) -> replaceIfNested(As, e));
                nc.add(new IndSpec.Ctor(c.name, tc.mkPi(As, replaced)));
            }
            t.ctors = nc;
        }
        List<IndSpec.Type> out = new ArrayList<>();
        for (TypeBuilder t : newTypes) out.add(new IndSpec.Type(t.name, t.type, t.ctors));
        return new IndSpec(in.lparams, in.nparams, in.isUnsafe, out);
    }

    private Expr replaceIfNested(List<Expr> As, Expr e) {
        Expr fn = e.getAppFn();
        if (fn.kind != Expr.Kind.CONST) return null;
        Expr.Const fc = (Expr.Const) fn;
        Decl d = env.get(fc.name);
        if (!(d instanceof Decl.Inductive)) return null;
        Decl.Inductive I = (Decl.Inductive) d;
        List<Expr> args = e.getAppArgs();
        int inp = I.numParams;
        if (inp > args.size()) return null;
        boolean isNested = false, loose = false;
        for (int i = 0; i < inp; i++) {
            if (args.get(i).looseBVarRange > 0) loose = true;
            if (containsNewType(args.get(i))) isNested = true;
        }
        if (!isNested) return null;
        if (loose)
            throw err("invalid nested inductive datatype '" + fc.name + "', nested inductive datatypes parameters cannot contain local variables.");
        Expr IAs = Expr.apps(fn, args.subList(0, inp));
        Expr key = Expr.instantiateRev(Expr.abstractFVars(IAs, ids(As)), mParams.toArray(new Expr[0]));
        Name auxName = null;
        for (Map.Entry<Expr, Name> p : nestedAux) if (p.getKey().equals(key)) { auxName = p.getValue(); break; }
        if (auxName != null) {
            Expr r = Expr.apps(Expr.cnst(auxName, lvls), As);
            return Expr.apps(r, args.subList(inp, args.size()));
        }
        Expr result = null;
        for (Name jName : I.all) {
            Decl jd = env.get(jName);
            if (!(jd instanceof Decl.Inductive)) throw err("unknown inductive type " + jName);
            Decl.Inductive J = (Decl.Inductive) jd;
            Expr JAs = Expr.apps(Expr.cnst(jName, fc.levels), args.subList(0, inp));
            Name auxJName = Name.str(Name.of("_nested"), jName + "_" + nextIdx++);
            Expr auxJType = Expr.instantiateLevelParams(J.type, J.levelParams, fc.levels);
            auxJType = instantiatePiParams(auxJType, inp, args);
            auxJType = tc.mkPi(As, auxJType);
            Expr jKey = Expr.instantiateRev(Expr.abstractFVars(JAs, ids(As)), mParams.toArray(new Expr[0]));
            nestedAux.add(Map.entry(jKey, auxJName));
            aux2nested.put(auxJName, jKey);
            if (jName.equals(fc.name)) {
                result = Expr.apps(Expr.apps(Expr.cnst(auxJName, lvls), As), args.subList(inp, args.size()));
            }
            List<IndSpec.Ctor> auxCtors = new ArrayList<>();
            for (Name jc : J.ctors) {
                Decl cd = env.get(jc);
                if (!(cd instanceof Decl.Ctor)) throw err("unknown constructor " + jc);
                Expr ct = Expr.instantiateLevelParams(cd.type, cd.levelParams, fc.levels);
                ct = instantiatePiParams(ct, inp, args);
                ct = tc.mkPi(As, ct);
                auxCtors.add(new IndSpec.Ctor(replacePrefix(jc, jName, auxJName), ct));
            }
            newTypes.add(new TypeBuilder(auxJName, auxJType, auxCtors));
        }
        return result;
    }

    // ---- restoration -------------------------------------------------------

    /**
     * Translates auxiliary types, constructors and recursors in a generated term back to the nested
     * applications. The first nparams binders (Pi if pi, otherwise lambda) are the declaration parameters.
     */
    Expr restore(Expr e, boolean pi, Env auxEnv, Map<Name, Name> recRename) {
        List<Expr> As = new ArrayList<>();
        for (int i = 0; i < in.nparams; i++) {
            Expr.Binder b = (Expr.Binder) e;
            if (b.kind != (pi ? Expr.Kind.PI : Expr.Kind.LAM)) throw err("ill-formed generated recursor");
            Expr a = tc.mkLocal(b.name, b.type, b.info);
            As.add(a);
            e = Expr.instantiate1(b.body, a);
        }
        Expr res = go(e, As, auxEnv, recRename);
        return pi ? tc.mkPi(As, res) : tc.mkLambda(As, res);
    }

    private Expr instNested(Expr nested, List<Expr> As) {
        return Expr.instantiateRev(Expr.abstractFVars(nested, ids(mParams)), As.toArray(new Expr[0]));
    }

    private Expr go(Expr e, List<Expr> As, Env auxEnv, Map<Name, Name> recRename) {
        return Expr.replace(e, (t, off) -> {
            if (t.kind == Expr.Kind.CONST) {
                Expr.Const c = (Expr.Const) t;
                Name rn = recRename.get(c.name);
                if (rn != null) return Expr.cnst(rn, c.levels);
            }
            Expr fn = t.getAppFn();
            if (fn.kind != Expr.Kind.CONST) return null;
            Expr.Const fc = (Expr.Const) fn;
            Expr nested = aux2nested.get(fc.name);
            if (nested != null) {
                List<Expr> args = t.getAppArgs();
                if (args.size() < in.nparams) throw err("ill-formed auxiliary type application");
                Expr r = instNested(nested, As);
                for (Expr a : args.subList(in.nparams, args.size())) r = Expr.app(r, go(a, As, auxEnv, recRename));
                return r;
            }
            Decl d = auxEnv.get(fc.name);
            if (d instanceof Decl.Ctor && aux2nested.containsKey(((Decl.Ctor) d).induct)) {
                Name auxI = ((Decl.Ctor) d).induct;
                List<Expr> args = t.getAppArgs();
                if (args.size() < in.nparams) throw err("ill-formed auxiliary constructor application");
                Expr newNested = instNested(aux2nested.get(auxI), As);
                Expr I = newNested.getAppFn();
                List<Expr> iArgs = newNested.getAppArgs();
                Name newFn = replacePrefix(fc.name, auxI, ((Expr.Const) I).name);
                Expr r = Expr.apps(Expr.cnst(newFn, ((Expr.Const) I).levels), iArgs);
                for (Expr a : args.subList(in.nparams, args.size())) r = Expr.app(r, go(a, As, auxEnv, recRename));
                return r;
            }
            return null;
        });
    }

    /** For a constructor name in a generated rule: the real constructor name. */
    Name restoreCtorName(Name ctor, Env auxEnv) {
        Decl d = auxEnv.get(ctor);
        if (d instanceof Decl.Ctor && aux2nested.containsKey(((Decl.Ctor) d).induct)) {
            Name auxI = ((Decl.Ctor) d).induct;
            return replacePrefix(ctor, auxI, ((Expr.Const) aux2nested.get(auxI).getAppFn()).name);
        }
        return ctor;
    }
}
