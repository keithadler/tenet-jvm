package tenet;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** What the kernel of a given Lean version does, as far as this checker's verdicts depend on it. */
public final class LeanVersion {
    private LeanVersion() {}

    private static final Pattern SHAPE = Pattern.compile("^v?(\\d+)\\.(\\d+)\\.(\\d+)(?:-(.+))?$");
    private static final Pattern NIGHTLY = Pattern.compile("^nightly-(\\d{4})-(\\d{2})-(\\d{2}).*$", Pattern.CASE_INSENSITIVE);

    /**
     * True when Lean's own kernel of this version has the definitional-equality changes that first shipped in
     * 4.37.0-rc1 (lean4#15103, #15371, #15373): proof irrelevance is tried before the first weak head
     * normalization, a recursor's major premise is not reduced when it is a proof and is eta-expanded for a
     * subsingleton structure such as And, and structure eta applies to a partially applied constructor. They
     * landed on master on 2026-10-20, so a 4.37 nightly counts from 2026-10-21 on. A version that cannot be
     * parsed answers false, which keeps the rules every earlier release has.
     */
    public static boolean kernelHasEta437(String version) {
        if (version == null) return false;
        Matcher m = SHAPE.matcher(version.trim());
        if (!m.matches()) return false;
        int major, minor;
        try {
            major = Integer.parseInt(m.group(1));
            minor = Integer.parseInt(m.group(2));
        } catch (NumberFormatException e) {
            return false;
        }
        if (major != 4 || minor != 37) return major > 4 || (major == 4 && minor > 37);
        String suffix = m.group(4) == null ? "" : m.group(4);
        Matcher n = NIGHTLY.matcher(suffix);
        if (!n.matches()) return !suffix.regionMatches(true, 0, "nightly", 0, 7);
        return (n.group(1) + n.group(2) + n.group(3)).compareTo("20261021") >= 0;
    }

    /** For the test suite: prints true or false for each version given. */
    public static void main(String[] args) {
        for (String a : args) System.out.println(kernelHasEta437(a.equals("null") ? null : a));
    }
}
