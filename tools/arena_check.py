#!/usr/bin/env python3
"""Run tenet-jvm over a locally built copy of the Lean Kernel Arena tests and score it the way the arena does.

    uv run --with pyyaml tools/arena_check.py ~/lean-ext/lean-kernel-arena [group ...]

Build the tests first with `uv run lka.py build-test '<group>/*'` inside the arena checkout.
Exit codes of tenet-jvm: 0 accepted, 1 rejected, 2 declined, anything else is a checker error.
"""
import os, subprocess, sys, time
import yaml

def main():
    arena = os.path.abspath(sys.argv[1])
    groups = sys.argv[2:] or ["tutorial", "bugs", "corner-cases", "other", "perf"]
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    cp = os.path.join(here, "out")
    java = os.environ.get("JAVA", "java")
    opts = os.environ.get("JAVA_OPTS", "-Xss512m -Xmx6g").split()
    wrong_accept, wrong_reject, declined, ok, either = [], [], [], 0, 0
    for g in groups:
        base = os.path.join(arena, "_build", "tests", g)
        cases = []  # (label, path, expected)
        if g == "tutorial":
            for sub, exp in (("good", "accept"), ("bad", "reject")):
                d = os.path.join(base, sub)
                for f in sorted(os.listdir(d)):
                    if f.endswith(".ndjson"):
                        cases.append((f"{g}/{sub}/{f[:-7]}", os.path.join(d, f), exp, 60))
        else:
            for f in sorted(os.listdir(base)):
                if not f.endswith(".ndjson"):
                    continue
                name = f[:-7]
                ypath = os.path.join(arena, "tests", g, name + ".yaml")
                exp, tmo = "accept", 300
                if os.path.exists(ypath):
                    y = yaml.safe_load(open(ypath)) or {}
                    exp, tmo = y.get("outcome", "accept"), y.get("timeout", 300)
                cases.append((f"{g}/{name}", os.path.join(base, f), exp, tmo))
        for label, path, exp, tmo in cases:
            t0 = time.time()
            try:
                r = subprocess.run([java, *opts, "-cp", cp, "tenet.Main", path], capture_output=True, timeout=tmo)
                code = r.returncode
            except subprocess.TimeoutExpired:
                code = 124
            dt = time.time() - t0
            if exp == "either":
                either += 1; status = "either"
            elif code == 2 or code not in (0, 1):
                declined.append((label, code)); status = f"DECLINED({code})"
            elif (code == 0) == (exp == "accept"):
                ok += 1; status = "ok"
            elif exp == "reject":
                wrong_accept.append(label); status = "WRONGLY ACCEPTED"
            else:
                wrong_reject.append(label); status = "WRONGLY REJECTED"
            if status not in ("ok", "either") or os.environ.get("VERBOSE"):
                print(f"{status:18} {label} ({dt:.1f}s)")
    print(f"\ncorrect: {ok}   either: {either}   wrongly accepted: {len(wrong_accept)}   wrongly rejected: {len(wrong_reject)}   declined/crashed: {len(declined)}")
    sys.exit(1 if wrong_accept or wrong_reject else 0)

main()
