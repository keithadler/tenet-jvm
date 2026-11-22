package tenet;

import java.util.List;

/** Kernel constants as they sit in the environment. */
public abstract class Decl {
    public enum Kind { AXIOM, DEF, THM, OPAQUE, QUOT, INDUCTIVE, CTOR, RECURSOR }

    public final Kind kind;
    public final Name name;
    public final List<Name> levelParams;
    private final Term type;

    Decl(Kind kind, Name name, List<Name> levelParams, Term type) {
        this.kind = kind;
        this.name = name;
        this.levelParams = levelParams;
        this.type = type;
    }

    /** The declared type (built from the export's expression store on demand). */
    public final Expr type() { return type.get(); }

    public static final class Axiom extends Decl {
        public final boolean isUnsafe;
        Axiom(Name n, List<Name> lps, Term t, boolean u) { super(Kind.AXIOM, n, lps, t); isUnsafe = u; }
    }

    public static final class Def extends Decl {
        private final Term value;
        /** "opaque", "abbrev" or "regular"; height only meaningful for regular. */
        public final String hints;
        public final long height;
        public final String safety;
        Def(Name n, List<Name> lps, Term t, Term v, String hints, long height, String safety) {
            super(Kind.DEF, n, lps, t);
            value = v;
            this.hints = hints;
            this.height = height;
            this.safety = safety;
        }
        public boolean isUnsafe() { return safety.equals("unsafe"); }
    }

    public static final class Thm extends Decl {
        private final Term value;

        Thm(Name n, List<Name> lps, Term t, Term v) {
            super(Kind.THM, n, lps, t);
            this.value = v;
        }

        /**
         * The proof term for checking this theorem: nodes not already kept are built into scratch space, so the
         * proof (usually the largest term of all) can be collected once it has been checked.
         */
        Expr proof() { return value.getTemp(); }
    }

    public static final class Opaque extends Decl {
        private final Term value;
        public final boolean isUnsafe;
        Opaque(Name n, List<Name> lps, Term t, Term v, boolean u) { super(Kind.OPAQUE, n, lps, t); value = v; isUnsafe = u; }
        /** The body; an opaque constant is never unfolded, so this is only for checking it. */
        public Expr opaqueValue() { return value.get(); }
    }

    public static final class Quot extends Decl {
        public final String quotKind; // type | ctor | lift | ind
        Quot(Name n, List<Name> lps, Term t, String k) { super(Kind.QUOT, n, lps, t); quotKind = k; }
    }

    public static final class Inductive extends Decl {
        public final int numParams, numIndices, numNested;
        public final List<Name> all, ctors;
        public final boolean isRec, isUnsafe, isReflexive;
        public Inductive(Name n, List<Name> lps, Expr t, int np, int ni, List<Name> all, List<Name> ctors, int nn,
                         boolean isRec, boolean isUnsafe, boolean isReflexive) {
            this(n, lps, Term.of(t), np, ni, all, ctors, nn, isRec, isUnsafe, isReflexive);
        }
        Inductive(Name n, List<Name> lps, Term t, int np, int ni, List<Name> all, List<Name> ctors, int nn,
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
            this(n, lps, Term.of(t), induct, cidx, np, nf, u);
        }
        Ctor(Name n, List<Name> lps, Term t, Name induct, int cidx, int np, int nf, boolean u) {
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
        private final Term rhs;
        public RecRule(Name ctor, int nfields, Expr rhs) { this(ctor, nfields, Term.of(rhs)); }
        RecRule(Name ctor, int nfields, Term rhs) { this.ctor = ctor; this.nfields = nfields; this.rhs = rhs; }
        public Expr rhs() { return rhs.get(); }
    }

    public static final class Recursor extends Decl {
        public final List<Name> all;
        public final int numParams, numIndices, numMotives, numMinors;
        public final List<RecRule> rules;
        public final boolean k, isUnsafe;
        public Recursor(Name n, List<Name> lps, Expr t, List<Name> all, int np, int ni, int nmot, int nmin,
                        List<RecRule> rules, boolean k, boolean u) {
            this(n, lps, Term.of(t), all, np, ni, nmot, nmin, rules, k, u);
        }
        Recursor(Name n, List<Name> lps, Term t, List<Name> all, int np, int ni, int nmot, int nmin,
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
    public final Expr value() {
        if (this instanceof Def) return ((Def) this).value.get();
        if (this instanceof Thm) return ((Thm) this).value.get();
        return null;
    }

    /** Can this constant be unfolded? (Cheaper than {@link #value()}, which may rebuild a proof term.) */
    public boolean hasValue() { return this instanceof Def || this instanceof Thm; }
}
