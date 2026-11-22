package tenet;

/**
 * A declaration's type or body: either an expression object (for declarations the kernel builds itself) or an
 * id in the export's {@link ExprStore}, built into an object only when asked for. Exported declarations hold
 * ids, so the environment does not keep every type and body of the export alive as objects.
 */
final class Term {
    private final Expr expr;
    private final ExprStore store;
    private final int id;

    private Term(Expr expr, ExprStore store, int id) {
        this.expr = expr;
        this.store = store;
        this.id = id;
    }

    static Term of(Expr e) { return new Term(e, null, -1); }
    static Term stored(ExprStore s, int id) { return new Term(null, s, id); }

    /** The expression, shared through the store's kept memo. */
    Expr get() { return expr != null ? expr : store.get(id); }

    /** The expression, with nodes not already kept built into scratch space (for a proof being checked). */
    Expr getTemp() { return expr != null ? expr : store.getTemp(id); }
}
