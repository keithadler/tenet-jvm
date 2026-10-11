package tenet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Adds declarations to an environment, checking each one. */
public final class Kernel {
    public final Env env = new Env();
    private final TypeChecker tc = new TypeChecker(env);
    /** Declarations accepted on trust rather than fully verified (to be driven to zero). */
    public final List<String> trusted = new java.util.ArrayList<>();
    /** Axioms the export declares. A kernel cannot judge an axiom, only report it. */
    public final List<Name> axioms = new java.util.ArrayList<>();

    private void checkLParams(List<Name> lps) {
        Set<Name> seen = new HashSet<>();
        for (Name n : lps) if (!seen.add(n)) throw new KernelException("duplicate universe parameter " + n);
    }

    private void checkType(Decl d) {
        checkLParams(d.levelParams);
        if (env.contains(d.name)) throw new KernelException("already declared: " + d.name);
        Expr t = d.type;
        if (t.hasFVar || t.looseBVarRange > 0) throw new KernelException("declaration type has free variables: " + d.name);
        tc.ensureSort(tc.check(t), t);
    }

    private void checkValue(Decl d, Expr value) {
        if (value.hasFVar || value.looseBVarRange > 0) throw new KernelException("declaration value has free variables: " + d.name);
        Expr vt = tc.check(value);
        if (!tc.isDefEq(vt, d.type))
            throw new KernelException("declaration type mismatch, " + d.name + "\n  value has type: " + vt + "\n  but is expected to have type: " + d.type);
    }

    public void add(Object item) {
        if (item instanceof InductiveBlock) { addInductive((InductiveBlock) item); return; }
        Decl d = (Decl) item;
        tc.begin(d.levelParams, TypeChecker.rank(d));
        switch (d.kind) {
            case AXIOM: checkType(d); env.add(d); axioms.add(d.name); break;
            case DEF: {
                Decl.Def def = (Decl.Def) d;
                checkType(d);
                if (def.isUnsafe()) {
                    env.add(d);
                    checkValue(d, def.value);
                } else {
                    checkValue(d, def.value);
                    env.add(d);
                }
                break;
            }
            case THM: {
                checkType(d);
                if (!tc.isPropType(d.type)) throw new KernelException("theorem type is not a proposition: " + d.name);
                checkValue(d, ((Decl.Thm) d).value);
                env.add(d);
                break;
            }
            case OPAQUE: {
                checkType(d);
                checkValue(d, ((Decl.Opaque) d).value);
                env.add(d);
                break;
            }
            case QUOT: addQuot((Decl.Quot) d); break;
            default: throw new KernelException("unexpected top-level declaration kind " + d.kind);
        }
    }

    private void addQuot(Decl.Quot q) {
        checkType(q);
        Expr expected = expectedQuotType(q);
        if (!q.type.equals(expected))
            throw new KernelException("quotient declaration " + q.name + " does not have the canonical type\n  expected: " + expected + "\n  exported: " + q.type);
        env.add(q);
        if (q.quotKind.equals("ind")) {
            for (Name n : new Name[] {Names.QUOT, Names.QUOT_MK, Names.QUOT_LIFT})
                if (!(env.get(n) instanceof Decl.Quot)) throw new KernelException("quotient package is incomplete: missing " + n);
            env.quotInitialized = true;
        }
    }

    private void checkEq() {
        Decl eq = env.get(Names.EQ);
        if (!(eq instanceof Decl.Inductive) || eq.levelParams.size() != 1)
            throw new KernelException("quotient types need the inductive type Eq with one universe parameter");
        Name u = eq.levelParams.get(0);
        Level lu = Level.param(u);
        tc.begin(eq.levelParams, 0);
        Expr sortU = Expr.sort(lu);
        Expr alpha = tc.mkLocal(Name.of("α"), sortU, "implicit");
        Expr a = tc.mkLocal(Name.of("a"), alpha, "default");
        Expr b = tc.mkLocal(Name.of("b"), alpha, "default");
        Expr expectedEq = tc.mkPi(List.of(alpha, a, b), Expr.sort(Level.ZERO));
        Decl.Inductive ind = (Decl.Inductive) eq;
        if (!eq.type.equals(expectedEq) || ind.numParams != 2 || ind.numIndices != 1 || ind.ctors.size() != 1)
            throw new KernelException("the inductive type Eq does not have the expected shape");
        Decl refl = env.get(ind.ctors.get(0));
        Expr eqApp = Expr.apps(Expr.cnst(Names.EQ, List.of(lu)), alpha, a, a);
        Expr expectedRefl = tc.mkPi(List.of(alpha, a), eqApp);
        if (!(refl instanceof Decl.Ctor) || !refl.name.equals(Names.EQ_REFL) || !refl.type.equals(expectedRefl))
            throw new KernelException("the constructor Eq.refl does not have the expected type");
    }

    /** The types Lean's kernel assigns to the four quotient constants. */
    private Expr expectedQuotType(Decl.Quot q) {
        checkEq();
        int need = q.quotKind.equals("lift") ? 2 : 1;
        if (q.levelParams.size() != need) throw new KernelException("quotient declaration " + q.name + " has the wrong number of universe parameters");
        tc.begin(q.levelParams, 0);
        Level lu = Level.param(q.levelParams.get(0));
        Expr sortU = Expr.sort(lu);
        Expr prop = Expr.sort(Level.ZERO);
        Expr alpha = tc.mkLocal(Name.of("α"), sortU, "implicit");
        Expr a = tc.mkLocal(Name.of("a"), alpha, "default");
        Expr b = tc.mkLocal(Name.of("b"), alpha, "default");
        Expr rTy = tc.mkPi(List.of(a, b), prop);
        Expr quotC = Expr.cnst(Names.QUOT, List.of(lu));
        switch (q.quotKind) {
            case "type": {
                Expr r = tc.mkLocal(Name.of("r"), rTy, "default");
                return tc.mkPi(List.of(alpha, r), sortU);
            }
            case "ctor": {
                Expr r = tc.mkLocal(Name.of("r"), rTy, "default");
                return tc.mkPi(List.of(alpha, r, a), Expr.apps(quotC, alpha, r));
            }
            case "lift": {
                Level lv = Level.param(q.levelParams.get(1));
                Expr r = tc.mkLocal(Name.of("r"), rTy, "implicit");
                Expr beta = tc.mkLocal(Name.of("β"), Expr.sort(lv), "implicit");
                Expr f = tc.mkLocal(Name.of("f"), tc.mkPi(List.of(a), beta), "default");
                Expr hr = tc.mkLocal(Name.of("h"), Expr.apps(r, a, b), "default");
                Expr eq = Expr.apps(Expr.cnst(Names.EQ, List.of(lv)), beta, Expr.app(f, a), Expr.app(f, b));
                Expr h = tc.mkLocal(Name.of("a"), tc.mkPi(List.of(a, b, hr), eq), "default");
                Expr qq = tc.mkLocal(Name.of("q"), Expr.apps(quotC, alpha, r), "default");
                return tc.mkPi(List.of(alpha, r, beta, f, h, qq), beta);
            }
            case "ind": {
                Expr r = tc.mkLocal(Name.of("r"), rTy, "implicit");
                Expr quotAR = Expr.apps(quotC, alpha, r);
                Expr q0 = tc.mkLocal(Name.of("q"), quotAR, "default");
                Expr beta = tc.mkLocal(Name.of("β"), tc.mkPi(List.of(q0), prop), "implicit");
                Expr mkApp = Expr.apps(Expr.cnst(Names.QUOT_MK, List.of(lu)), alpha, r, a);
                Expr mk = tc.mkLocal(Name.of("mk"), tc.mkPi(List.of(a), Expr.app(beta, mkApp)), "default");
                Expr q1 = tc.mkLocal(Name.of("q"), quotAR, "default");
                return tc.mkPi(List.of(alpha, r, beta, mk, q1), Expr.app(beta, q1));
            }
            default: throw new KernelException("unknown quotient kind " + q.quotKind);
        }
    }

    private void addInductive(InductiveBlock b) {
        // 1. the declaration proper, as the kernel would receive it
        Decl.Inductive first = b.types.get(0);
        List<IndSpec.Type> stypes = new ArrayList<>();
        for (Decl.Inductive t : b.types) {
            if (!t.levelParams.equals(first.levelParams)) throw new KernelException("mutual inductive types must have the same universe parameters");
            if (t.numParams != first.numParams) throw new KernelException("mutual inductive types must have the same number of parameters");
            if (t.isUnsafe != first.isUnsafe) throw new KernelException("mutual inductive types must agree on unsafe");
            List<IndSpec.Ctor> cs = new ArrayList<>();
            for (Name cn : t.ctors) {
                Decl.Ctor c = null;
                for (Decl.Ctor x : b.ctors) if (x.name.equals(cn)) c = x;
                if (c == null) throw new KernelException("constructor " + cn + " listed by " + t.name + " is missing from the export");
                cs.add(new IndSpec.Ctor(cn, c.type));
            }
            stypes.add(new IndSpec.Type(t.name, t.type, cs));
        }
        int nctors = 0;
        for (IndSpec.Type t : stypes) nctors += t.ctors.size();
        if (nctors != b.ctors.size()) throw new KernelException("export contains constructors that no inductive type lists");
        IndSpec spec = new IndSpec(first.levelParams, first.numParams, first.isUnsafe, stypes);

        // 2. eliminate nested occurrences, 3. check and generate in a scratch environment
        tc.begin(first.levelParams, TypeChecker.rank(first));
        NestedInductive nested = new NestedInductive(env, tc, spec);
        IndSpec auxSpec = nested.run();
        Env auxEnv = env.fork();
        TypeChecker auxTc = new TypeChecker(auxEnv);
        auxTc.begin(first.levelParams, TypeChecker.rank(first));
        InductiveChecker.Result gen = new InductiveChecker(auxEnv, auxTc, auxSpec).run();

        // 4. translate back and compare everything with what was exported
        tc.begin(first.levelParams, TypeChecker.rank(first));
        int k = b.types.size();
        int nAux = auxSpec.types.size() - k;
        Map<Name, Name> recRename = new HashMap<>();
        for (int j = 0; j < nAux; j++)
            recRename.put(Name.str(auxSpec.types.get(k + j).name, "rec"), Name.str(b.types.get(0).name, "rec_" + (j + 1)));
        List<Name> all = spec.typeNames();
        for (int i = 0; i < k; i++) {
            Decl.Inductive t = b.types.get(i), g = gen.types.get(i);
            if (t.numIndices != g.numIndices || t.isRec != g.isRec || t.isReflexive != g.isReflexive || t.numNested != nAux || !t.all.equals(all))
                throw new KernelException("inductive type " + t.name + " has wrong bookkeeping: numIndices " + t.numIndices + "/" + g.numIndices
                        + ", isRec " + t.isRec + "/" + g.isRec + ", isReflexive " + t.isReflexive + "/" + g.isReflexive + ", numNested " + t.numNested + "/" + nAux);
        }
        int ci = 0;
        for (int i = 0; i < k; i++)
            for (Name cn : b.types.get(i).ctors) {
                Decl.Ctor c = null;
                for (Decl.Ctor x : b.ctors) if (x.name.equals(cn)) c = x;
                Decl.Ctor g = gen.ctors.get(ci++);
                if (!g.name.equals(c.name) || c.cidx != g.cidx || c.numParams != g.numParams || c.numFields != g.numFields || c.isUnsafe != g.isUnsafe
                        || !c.induct.equals(g.induct) || !c.levelParams.equals(g.levelParams))
                    throw new KernelException("constructor " + c.name + " has wrong bookkeeping");
            }
        if (b.recs.size() != gen.recs.size())
            throw new KernelException("export has " + b.recs.size() + " recursors but " + gen.recs.size() + " are expected");
        for (int i = 0; i < gen.recs.size(); i++) {
            Decl.Recursor g = gen.recs.get(i);
            Name expectName = i < k ? g.name : Name.str(b.types.get(0).name, "rec_" + (i - k + 1));
            Decl.Recursor r = null;
            for (Decl.Recursor x : b.recs) if (x.name.equals(expectName)) r = x;
            if (r == null) throw new KernelException("missing recursor " + expectName);
            Expr type = nested.restore(g.type, true, auxEnv, recRename);
            if (!type.equals(r.type))
                throw new KernelException("recursor " + r.name + " has the wrong type\n  expected: " + type + "\n  exported: " + r.type);
            if (!r.levelParams.equals(g.levelParams) || r.numParams != g.numParams || r.numIndices != g.numIndices || r.numMotives != g.numMotives
                    || r.numMinors != g.numMinors || r.k != g.k || r.isUnsafe != g.isUnsafe || !r.all.equals(all))
                throw new KernelException("recursor " + r.name + " has wrong bookkeeping");
            if (r.rules.size() != g.rules.size()) throw new KernelException("recursor " + r.name + " has the wrong number of rules");
            for (int j = 0; j < g.rules.size(); j++) {
                Decl.RecRule gr = g.rules.get(j), rr = r.rules.get(j);
                Name cname = nested.restoreCtorName(gr.ctor, auxEnv);
                Expr rhs = nested.restore(gr.rhs, false, auxEnv, recRename);
                if (!rr.ctor.equals(cname) || rr.nfields != gr.nfields)
                    throw new KernelException("recursor rule for " + cname + " has the wrong constructor or field count");
                if (!rhs.equals(rr.rhs))
                    throw new KernelException("recursor rule for " + cname + " has the wrong right-hand side\n  expected: " + rhs + "\n  exported: " + rr.rhs);
            }
        }

        // 5. everything matched: the exported declarations are now known to be exactly what the kernel derives
        for (Decl.Inductive t : b.types) env.add(t);
        for (Decl.Ctor c : b.ctors) env.add(c);
        for (Decl.Recursor r : b.recs) env.add(r);
    }
}
