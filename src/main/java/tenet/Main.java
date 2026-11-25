package tenet;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.EnumMap;
import java.util.Map;

/** Command line: java -jar tenet-jvm.jar [--keep-going] export.ndjson  (or - for stdin). */
public final class Main {
    static final String VERSION = "0.1.6";
    private static final boolean TRACE = System.getenv("TENET_TRACE") != null;
    /** --verbose: name each declaration on stderr before checking it, and its time and heap after. */
    private static boolean verbose = false;
    /** The item being checked and when it started, for the --verbose heartbeat. */
    private static volatile String current = null;
    private static volatile long currentStart = 0;

    public static void main(String[] args) throws Exception {
        boolean keepGoing = false;
        String file = null;
        for (String a : args) {
            if (a.equals("--keep-going")) keepGoing = true;
            else if (a.equals("--verbose")) verbose = true;
            else if (a.equals("-h") || a.equals("--help")) { usage(); return; }
            else if (a.equals("--version")) { System.out.println("tenet-jvm " + VERSION); return; }
            else file = a;
        }
        if (file == null) { usage(); System.exit(64); }
        final boolean kg = keepGoing;
        final String f = file;
        // Fail closed: unless run() returns normally the verdict is "error", never "accepted".
        int[] code = {3};
        Thread t = new Thread(null, () -> {
            try {
                code[0] = run(f, kg);
            } catch (DeclinedException e) {
                System.out.println("DECLINED " + e.getMessage());
                code[0] = 2;
            } catch (KernelException e) {
                System.out.println("REJECTED malformed export: " + e.getMessage());
                code[0] = 1;
            } catch (Throwable e) {
                System.out.println("ERROR " + e);
                code[0] = 3;
            }
        }, "checker", 4L << 30);
        t.start();
        t.join();
        System.exit(code[0]);
    }

    private static void usage() {
        System.err.println("tenet-jvm " + VERSION + "\nusage: tenet-jvm [--keep-going] [--verbose] [--version] <export.ndjson | ->");
    }

    private static int run(String file, boolean keepGoing) {
        long start = System.nanoTime();
        Kernel kernel = new Kernel();
        ExportReader reader = new ExportReader();
        // Which rules apply depends on the Lean that wrote the export; see LeanVersion.
        reader.onMeta = () -> kernel.env.eta437 = LeanVersion.kernelHasEta437(reader.leanVersion);
        Map<Decl.Kind, Integer> counts = new EnumMap<>(Decl.Kind.class);
        int[] failures = {0};
        int[] blocks = {0};
        int[] done = {0};
        if (verbose) {
            Thread beat = new Thread(() -> {
                while (true) {
                    try { Thread.sleep(30_000); } catch (InterruptedException e) { return; }
                    String c = current;
                    if (c == null) continue;
                    long s = (System.nanoTime() - currentStart) / 1_000_000_000L;
                    if (s < 30) continue;
                    Runtime rt = Runtime.getRuntime();
                    System.err.println("  still checking " + c + " after " + s + " s, heap " + ((rt.totalMemory() - rt.freeMemory()) >> 20) + " MB");
                }
            }, "heartbeat");
            beat.setDaemon(true);
            beat.start();
        }
        try (BufferedReader in = file.equals("-")
                ? new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8))
                : Files.newBufferedReader(Path.of(file), StandardCharsets.UTF_8)) {
            reader.read(in, item -> {
                if (failures[0] > 0 && !keepGoing) return;
                String label = item instanceof InductiveBlock ? "inductive " + ((InductiveBlock) item).types.get(0).name : ((Decl) item).kind + " " + ((Decl) item).name;
                if (TRACE || verbose) { System.err.println("> " + label); System.err.flush(); }
                try {
                    long t0 = System.nanoTime();
                    currentStart = t0;
                    current = label;
                    kernel.add(item);
                    current = null;
                    long ms = (System.nanoTime() - t0) / 1_000_000;
                    if (verbose) {
                        Runtime rt = Runtime.getRuntime();
                        System.err.println("< " + ms + " ms, heap " + ((rt.totalMemory() - rt.freeMemory()) >> 20) + " MB: " + label);
                    }
                    if (ms > 2000) System.err.println("slow (" + ms + " ms): " + label);
                    if ((++done[0] & 1023) == 0) System.err.println("... " + done[0] + " items, at " + label);
                    if (item instanceof InductiveBlock) blocks[0]++; else counts.merge(((Decl) item).kind, 1, Integer::sum);
                } catch (OutOfMemoryError e) {
                    // Unwinding has made the declaration's working set garbage, so there is room to say which one it was.
                    throw new OutOfMemoryError(e.getMessage() + " while checking " + label);
                } catch (KernelException | StackOverflowError e) {
                    failures[0]++;
                    if (TRACE && e instanceof StackOverflowError) {
                        StackTraceElement[] st = e.getStackTrace();
                        for (int i = 0; i < Math.min(40, st.length); i++) System.err.println("    " + st[i]);
                    }
                    System.out.println("REJECTED " + label + ": " + (e instanceof KernelException ? e.getMessage() : "stack overflow"));
                }
            });
        } catch (IOException e) {
            System.err.println("cannot read " + file + ": " + e.getMessage());
            return 3;
        }
        double secs = (System.nanoTime() - start) / 1e9;
        System.out.printf("lean %s, export format %s, %d lines%n", reader.leanVersion, reader.formatVersion, reader.lines);
        System.out.printf("checked %d constants (%s) and %d inductive blocks in %.2fs%n", kernel.env.size(), counts, blocks[0], secs);
        System.out.println("axioms declared: " + (kernel.axioms.isEmpty() ? "none" : kernel.axioms.toString().replaceAll("^\\[|\\]$", "")));
        if (!kernel.trusted.isEmpty()) {
            System.out.println("NOT FULLY VERIFIED (" + kernel.trusted.size() + " items accepted on trust):");
            for (String s : kernel.trusted.subList(0, Math.min(10, kernel.trusted.size()))) System.out.println("  " + s);
        }
        if (failures[0] > 0) { System.out.println(failures[0] + " declaration(s) rejected"); return 1; }
        System.out.println(kernel.trusted.isEmpty() ? "all declarations verified" : "no declaration rejected");
        return 0;
    }
}
