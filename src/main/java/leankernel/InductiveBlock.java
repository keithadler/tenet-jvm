package leankernel;

import java.util.List;

/** A (mutual) inductive declaration group as exported: types, constructors and recursors. */
public final class InductiveBlock {
    public final List<Decl.Inductive> types;
    public final List<Decl.Ctor> ctors;
    public final List<Decl.Recursor> recs;

    public InductiveBlock(List<Decl.Inductive> types, List<Decl.Ctor> ctors, List<Decl.Recursor> recs) {
        this.types = types;
        this.ctors = ctors;
        this.recs = recs;
    }
}
