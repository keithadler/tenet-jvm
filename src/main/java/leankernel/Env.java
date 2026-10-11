package leankernel;

import java.util.HashMap;
import java.util.Map;

/** The environment of already-checked constants. */
public final class Env {
    private final Map<Name, Decl> decls = new HashMap<>();
    public boolean quotInitialized = false;

    public Decl get(Name n) { return decls.get(n); }
    public boolean contains(Name n) { return decls.containsKey(n); }
    public int size() { return decls.size(); }

    public void add(Decl d) {
        if (decls.putIfAbsent(d.name, d) != null) throw new KernelException("already declared: " + d.name);
    }
}
