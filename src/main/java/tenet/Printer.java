package tenet;

/** Debug printer for expressions. */
public final class Printer {
    private Printer() { }

    /**
     * Characters printed for one term. Terms are DAGs and the printer writes them out as trees, so a term of a
     * few thousand shared nodes can print as gigabytes; the message of a rejection must not be what exhausts
     * the heap. The longest message any local test export produces is under 9,000 characters.
     */
    private static final int LIMIT = 100_000;

    public static String show(Expr e) {
        StringBuilder sb = new StringBuilder();
        go(e, sb, 0);
        if (sb.length() > LIMIT) { sb.setLength(LIMIT); sb.append(" …(truncated)"); }
        return sb.toString();
    }

    private static void go(Expr e, StringBuilder sb, int depth) {
        if (sb.length() > LIMIT) return;
        if (depth > 40) { sb.append("…"); return; }
        switch (e.kind) {
            case BVAR: sb.append('#').append(((Expr.BVar) e).idx); break;
            case FVAR: sb.append("_f").append(((Expr.FVar) e).id); break;
            case SORT: sb.append("Sort(").append(((Expr.Sort) e).level).append(')'); break;
            case CONST: {
                Expr.Const c = (Expr.Const) e;
                sb.append(c.name);
                if (!c.levels.isEmpty()) sb.append(".{").append(c.levels).append('}');
                break;
            }
            case APP: {
                sb.append('(');
                go(e.getAppFn(), sb, depth + 1);
                for (Expr a : e.getAppArgs()) { sb.append(' '); go(a, sb, depth + 1); }
                sb.append(')');
                break;
            }
            case LAM: case PI: {
                Expr.Binder b = (Expr.Binder) e;
                sb.append(e.kind == Expr.Kind.LAM ? "(fun " : "(Π ").append(b.name).append(" : ");
                go(b.type, sb, depth + 1);
                sb.append(e.kind == Expr.Kind.LAM ? " => " : ", ");
                go(b.body, sb, depth + 1);
                sb.append(')');
                break;
            }
            case LET: {
                Expr.Let l = (Expr.Let) e;
                sb.append("(let ").append(l.name).append(" : ");
                go(l.type, sb, depth + 1);
                sb.append(" := ");
                go(l.value, sb, depth + 1);
                sb.append("; ");
                go(l.body, sb, depth + 1);
                sb.append(')');
                break;
            }
            case NAT: sb.append(((Expr.NatLit) e).val); break;
            case STR: sb.append('"').append(((Expr.StrLit) e).val).append('"'); break;
            default: {
                Expr.Proj p = (Expr.Proj) e;
                go(p.struct, sb, depth + 1);
                sb.append('.').append(p.idx + 1);
            }
        }
    }
}
