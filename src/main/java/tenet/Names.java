package tenet;

/** Names of constants the kernel treats specially. */
public final class Names {
    private Names() { }

    public static final Name NAT = Name.of("Nat");
    public static final Name NAT_ZERO = Name.of("Nat.zero");
    public static final Name NAT_SUCC = Name.of("Nat.succ");
    public static final Name STRING = Name.of("String");
    public static final Name STRING_MK = Name.of("String.mk");
    public static final Name STRING_OF_LIST = Name.of("String.ofList");
    public static final Name CHAR = Name.of("Char");
    public static final Name CHAR_OF_NAT = Name.of("Char.ofNat");
    public static final Name LIST_CONS = Name.of("List.cons");
    public static final Name LIST_NIL = Name.of("List.nil");
    public static final Name BOOL_TRUE = Name.of("Bool.true");
    public static final Name BOOL_FALSE = Name.of("Bool.false");
    public static final Name EQ = Name.of("Eq");
    public static final Name EQ_REFL = Name.of("Eq.refl");
    public static final Name QUOT = Name.of("Quot");
    public static final Name QUOT_MK = Name.of("Quot.mk");
    public static final Name QUOT_LIFT = Name.of("Quot.lift");
    public static final Name QUOT_IND = Name.of("Quot.ind");
}
