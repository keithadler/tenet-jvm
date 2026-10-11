package tenet;

import java.util.ArrayList;
import java.util.List;

/** The input of an inductive declaration, as the kernel receives it: types and constructor types only. */
final class IndSpec {
    static final class Ctor {
        final Name name;
        final Expr type;
        Ctor(Name name, Expr type) { this.name = name; this.type = type; }
    }

    static final class Type {
        final Name name;
        final Expr type;
        final List<Ctor> ctors;
        Type(Name name, Expr type, List<Ctor> ctors) { this.name = name; this.type = type; this.ctors = ctors; }
    }

    final List<Name> lparams;
    final int nparams;
    final boolean isUnsafe;
    final List<Type> types;

    IndSpec(List<Name> lparams, int nparams, boolean isUnsafe, List<Type> types) {
        this.lparams = lparams;
        this.nparams = nparams;
        this.isUnsafe = isUnsafe;
        this.types = types;
    }

    List<Name> typeNames() {
        List<Name> r = new ArrayList<>();
        for (Type t : types) r.add(t.name);
        return r;
    }
}
