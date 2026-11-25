package tenet;

/** Raised when the checker will not give a verdict: the file is in a format it does not know. */
@SuppressWarnings("serial")
public class DeclinedException extends RuntimeException {
    public DeclinedException(String msg) { super(msg); }
}
