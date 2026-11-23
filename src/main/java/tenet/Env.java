package tenet;

import java.util.HashMap;
import java.util.Map;

/** The environment of already-checked constants. */
public final class Env {
    private final Map<Name, Decl> decls = new HashMap<>();
    public boolean quotInitialized = false;
    /**
     * The Lean that wrote these declarations has the 4.37 definitional-equality rules (see {@link LeanVersion#kernelHasEta437}):
     * proof irrelevance before weak head normalization, no reduction of a proof standing as a recursor's major premise,
     * eta for the major of a subsingleton structure's recursor, and structure eta against a partially applied constructor.
     */
    public boolean eta437 = false;
    private final Env parent;

    public Env() { this.parent = null; }

    private Env(Env parent) {
        this.parent = parent;
        this.quotInitialized = parent.quotInitialized;
        this.eta437 = parent.eta437;
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
        if (journal != null) journal.add(d.name);
    }

    /** Names added since {@link #startJournal}, so that a declaration that is re-checked can be taken back out. */
    private java.util.List<Name> journal = null;

    void startJournal() { journal = new java.util.ArrayList<>(); }

    void stopJournal() { journal = null; }

    /** Removes everything added since {@link #startJournal}. */
    void rollBack() {
        if (journal == null) return;
        for (Name n : journal) decls.remove(n);
        journal.clear();
    }
}
