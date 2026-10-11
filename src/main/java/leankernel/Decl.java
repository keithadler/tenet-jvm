package leankernel;

import java.util.List;

/** Kernel constants as they sit in the environment. */
public abstract class Decl {
    public enum Kind { AXIOM, DEF, THM, OPAQUE, QUOT, INDUCTIVE, CTOR, RECURSOR }

    public final Kind kind;
    public final Name name;
    public final List<Name> levelParams;
    public final Expr type;

    Decl(Kind kind, Name name, List<Name> levelParams, Expr type) {
        this.kind = kind;
        this.name = name;
        this.levelParams = levelParams;
        this.type = type;
    }

    public static final class Axiom extends Decl {
        public final boolean isUnsafe;
        public Axiom(Name n, List<Name> lps, Expr t, boolean u) { super(Kind.AXIOM, n, lps, t); isUnsafe = u; }
    }

    public static final class Def extends Decl {
        public final Expr value;
        /** "opaque", "abbrev" or "regular"; height only meaningful for regular. */
        public final String hints;
        public final long height;
        public final String safety;
        public Def(Name n, List<Name> lps, Expr t, Expr v, String hints, long height, String safety) {
            super(Kind.DEF, n, lps, t);
            value = v;
            this.hints = hints;
            this.height = height;
            this.safety = safety;
        }
        public boolean isUnsafe() { return safety.equals("unsafe"); }
    }

    public static final class Thm extends Decl {
        public final Expr value;
        public Thm(Name n, List<Name> lps, Expr t, Expr v) { super(Kind.THM, n, lps, t); value = v; }
    }

    public static final class Opaque extends Decl {
        public final Expr value;
        public final boolean isUnsafe;
        public Opaque(Name n, List<Name> lps, Expr t, Expr v, boolean u) { super(Kind.OPAQUE, n, lps, t); value = v; isUnsafe = u; }
    }

    public static final class Quot extends Decl {
        public final String quotKind; // type | ctor | lift | ind
        public Quot(Name n, List<Name> lps, Expr t, String k) { super(Kind.QUOT, n, lps, t); quotKind = k; }
    }

    public static final class Inductive extends Decl {
        public final int numParams, numIndices, numNested;
        public final List<Name> all, ctors;
        public final boolean isRec, isUnsafe, isReflexive;
        public Inductive(Name n, List<Name> lps, Expr t, int np, int ni, List<Name> all, List<Name> ctors, int nn,
                         boolean isRec, boolean isUnsafe, boolean isReflexive) {
            super(Kind.INDUCTIVE, n, lps, t);
            numParams = np;
            numIndices = ni;
            this.all = all;
            this.ctors = ctors;
            numNested = nn;
            this.isRec = isRec;
            this.isUnsafe = isUnsafe;
            this.isReflexive = isReflexive;
        }
    }

    public static final class Ctor extends Decl {
        public final Name induct;
        public final int cidx, numParams, numFields;
        public final boolean isUnsafe;
        public Ctor(Name n, List<Name> lps, Expr t, Name induct, int cidx, int np, int nf, boolean u) {
            super(Kind.CTOR, n, lps, t);
            this.induct = induct;
            this.cidx = cidx;
            numParams = np;
            numFields = nf;
            isUnsafe = u;
        }
    }

    public static final class RecRule {
        public final Name ctor;
        public final int nfields;
        public final Expr rhs;
        public RecRule(Name ctor, int nfields, Expr rhs) { this.ctor = ctor; this.nfields = nfields; this.rhs = rhs; }
    }

    public static final class Recursor extends Decl {
        public final List<Name> all;
        public final int numParams, numIndices, numMotives, numMinors;
        public final List<RecRule> rules;
        public final boolean k, isUnsafe;
        public Recursor(Name n, List<Name> lps, Expr t, List<Name> all, int np, int ni, int nmot, int nmin,
                        List<RecRule> rules, boolean k, boolean u) {
            super(Kind.RECURSOR, n, lps, t);
            this.all = all;
            numParams = np;
            numIndices = ni;
            numMotives = nmot;
            numMinors = nmin;
            this.rules = rules;
            this.k = k;
            isUnsafe = u;
        }
        public int majorIdx() { return numParams + numMotives + numMinors + numIndices; }
    }

    /** The definition body, if this constant is unfoldable by delta. */
    public Expr value() {
        if (this instanceof Def) return ((Def) this).value;
        if (this instanceof Thm) return ((Thm) this).value;
        return null;
    }
}
