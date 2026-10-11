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
    private static final boolean TRACE = System.getenv("TENET_TRACE") != null;

    public static void main(String[] args) throws Exception {
        boolean keepGoing = false;
        String file = null;
        for (String a : args) {
            if (a.equals("--keep-going")) keepGoing = true;
            else if (a.equals("-h") || a.equals("--help")) { usage(); return; }
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
        System.err.println("usage: tenet-jvm [--keep-going] <export.ndjson | ->");
    }

    private static int run(String file, boolean keepGoing) {
        long start = System.nanoTime();
        Kernel kernel = new Kernel();
        ExportReader reader = new ExportReader();
        Map<Decl.Kind, Integer> counts = new EnumMap<>(Decl.Kind.class);
        int[] failures = {0};
        int[] blocks = {0};
        int[] done = {0};
        try (BufferedReader in = file.equals("-")
                ? new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8))
                : Files.newBufferedReader(Path.of(file), StandardCharsets.UTF_8)) {
            reader.read(in, item -> {
                if (failures[0] > 0 && !keepGoing) return;
                String label = item instanceof InductiveBlock ? "inductive " + ((InductiveBlock) item).types.get(0).name : ((Decl) item).kind + " " + ((Decl) item).name;
                if (TRACE) System.err.println("> " + label);
                try {
                    long t0 = System.nanoTime();
                    kernel.add(item);
                    long ms = (System.nanoTime() - t0) / 1_000_000;
                    if (ms > 2000) System.err.println("slow (" + ms + " ms): " + label);
                    if ((++done[0] & 1023) == 0) System.err.println("... " + done[0] + " items, at " + label);
                    if (item instanceof InductiveBlock) blocks[0]++; else counts.merge(((Decl) item).kind, 1, Integer::sum);
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
        if (!kernel.trusted.isEmpty()) {
            System.out.println("NOT FULLY VERIFIED (" + kernel.trusted.size() + " items accepted on trust):");
            for (String s : kernel.trusted.subList(0, Math.min(10, kernel.trusted.size()))) System.out.println("  " + s);
        }
        if (failures[0] > 0) { System.out.println(failures[0] + " declaration(s) rejected"); return 1; }
        System.out.println(kernel.trusted.isEmpty() ? "all declarations verified" : "no declaration rejected");
        return 0;
    }
}
