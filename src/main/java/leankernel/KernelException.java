package leankernel;

/** Raised when a declaration is rejected. */
@SuppressWarnings("serial")
public class KernelException extends RuntimeException {
    public KernelException(String msg) { super(msg); }
}
