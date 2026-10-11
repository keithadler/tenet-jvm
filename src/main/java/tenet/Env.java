package tenet;

import java.util.HashMap;
import java.util.Map;

/** The environment of already-checked constants. */
public final class Env {
    private final Map<Name, Decl> decls = new HashMap<>();
    public boolean quotInitialized = false;
    private final Env parent;

    public Env() { this.parent = null; }

    private Env(Env parent) {
        this.parent = parent;
        this.quotInitialized = parent.quotInitialized;
    }

    /** A scratch environment layered over this one; additions to it do not touch this environment. */
    public Env fork() { return new Env(this); }

    public Decl get(Name n) {
        Decl d = decls.get(n);
        return d != null || parent == null ? d : parent.get(n);
    }

    public boolean contains(Name n) { return get(n) != null; }
    public int size() { return decls.size() + (parent == null ? 0 : parent.size()); }

    public void add(Decl d) {
        if (contains(d.name)) throw new KernelException("already declared: " + d.name);
        decls.put(d.name, d);
    }
}
