package leankernel;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/** Adds declarations to an environment, checking each one. */
public final class Kernel {
    public final Env env = new Env();
    private final TypeChecker tc = new TypeChecker(env);
    /** Declarations accepted on trust rather than fully verified (to be driven to zero). */
    public final List<String> trusted = new java.util.ArrayList<>();

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
            case AXIOM: checkType(d); env.add(d); break;
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
        trusted.add("quot " + q.name + " (shape not yet compared with the canonical quotient types)");
        env.add(q);
        if (q.quotKind.equals("ind")) env.quotInitialized = true;
    }

    private void addInductive(InductiveBlock b) {
        for (Decl.Inductive t : b.types) {
            tc.begin(t.levelParams, TypeChecker.rank(t));
            checkType(t);
            env.add(t);
        }
        for (Decl.Ctor c : b.ctors) {
            tc.begin(c.levelParams, TypeChecker.rank(c));
            checkType(c);
            env.add(c);
        }
        for (Decl.Recursor r : b.recs) {
            tc.begin(r.levelParams, TypeChecker.rank(r));
            checkType(r);
            env.add(r);
        }
        trusted.add("inductive " + b.types.get(0).name + " (positivity, universes and recursors not yet verified)");
    }
}
