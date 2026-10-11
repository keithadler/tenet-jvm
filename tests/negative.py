#!/usr/bin/env python3
"""Mutation tests: take a valid export, damage it in one targeted way, and require that tenet-jvm rejects it.

    python3 tests/negative.py

The unmodified export must be accepted; every mutant must be rejected (exit code 1). A mutant that is
accepted is a soundness hole, a mutant that crashes (exit code other than 0 or 1) is a bug.
"""
import copy, json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LAUNCHER = os.path.join(ROOT, "bin", "tenet-jvm")
SOURCE = os.path.join(HERE, "exports", "nat_add_comm.ndjson")


def load():
    return [json.loads(l) for l in open(SOURCE)]


def key(rec):
    return next(k for k in rec if k not in ("in", "il", "ie"))


def find(recs, kind):
    return [r for r in recs if key(r) == kind]


def inductive(recs, i):
    return find(recs, "inductive")[i]["inductive"]


def by_name(recs, which):
    """The inductive block containing a type whose first rec is the n-th recursor."""
    return find(recs, "inductive")[which]["inductive"]


# Each mutator edits the record list in place.
def thm_wrong_value(recs):
    # give a later theorem the proof of an earlier one (so the id is already defined)
    a, b = find(recs, "thm")[0]["thm"], find(recs, "thm")[1]["thm"]
    b["value"] = a["value"]

def thm_undeclared_universe(recs):
    for r in find(recs, "thm"):
        if r["thm"]["levelParams"]:
            r["thm"]["levelParams"] = []
            return
    raise SystemExit("no theorem with universe parameters in the source export")

def def_wrong_type(recs):
    ds = find(recs, "def")
    ds[1]["def"]["type"] = ds[0]["def"]["type"]

def rec_rules_swapped(recs):
    rules = inductive(recs, 0)["recs"][0]["rules"]
    rules[0]["rhs"], rules[1]["rhs"] = rules[1]["rhs"], rules[0]["rhs"]

def rec_rule_field_count(recs):
    inductive(recs, 0)["recs"][0]["rules"][1]["nfields"] = 2

def rec_wrong_type(recs):
    a, b = inductive(recs, 0)["recs"][0], inductive(recs, 1)["recs"][0]
    b["type"] = a["type"]

def rec_k_flag_flipped(recs):
    for r in find(recs, "inductive"):
        rec = r["inductive"]["recs"][0]
        rec["k"] = not rec["k"]
        return

def rec_k_flag_on_nat(recs):
    inductive(recs, 0)["recs"][0]["k"] = True

def ind_isrec_flipped(recs):
    t = inductive(recs, 0)["types"][0]
    t["isRec"] = not t["isRec"]

def ind_num_params(recs):
    t = inductive(recs, 1)["types"][0]
    t["numParams"] += 1

def ind_num_indices(recs):
    t = inductive(recs, 1)["types"][0]
    t["numIndices"] += 1

def ind_num_nested(recs):
    inductive(recs, 0)["types"][0]["numNested"] = 1

def ind_ctor_dropped_from_type(recs):
    inductive(recs, 0)["types"][0]["ctors"].pop()

def ctor_cidx(recs):
    inductive(recs, 0)["ctors"][1]["cidx"] = 0

def ctor_field_count(recs):
    inductive(recs, 0)["ctors"][1]["numFields"] = 0

def rec_extra_orphan(recs):
    blk = inductive(recs, 0)
    extra = copy.deepcopy(blk["recs"][0])
    first = next(i for i, r in enumerate(recs) if key(r) == "inductive")
    extra["name"] = [r["in"] for r in recs[:first] if "in" in r][-1]   # a name defined before the block
    extra["all"] = []
    blk["recs"].append(extra)


MUTANTS = [thm_wrong_value, thm_undeclared_universe, def_wrong_type, rec_rules_swapped, rec_rule_field_count, rec_wrong_type,
           rec_k_flag_flipped, rec_k_flag_on_nat, ind_isrec_flipped, ind_num_params, ind_num_indices, ind_num_nested,
           ind_ctor_dropped_from_type, ctor_cidx, ctor_field_count, rec_extra_orphan]


def run(recs):
    with tempfile.NamedTemporaryFile("w", suffix=".ndjson", delete=False) as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":")) + "\n")
        path = f.name
    try:
        p = subprocess.run([LAUNCHER, path], capture_output=True, text=True, timeout=120)
        return p.returncode, p.stdout
    finally:
        os.unlink(path)


def run_text(text):
    with tempfile.NamedTemporaryFile("w", suffix=".ndjson", delete=False) as f:
        f.write(text)
        path = f.name
    try:
        return subprocess.run([LAUNCHER, path], capture_output=True, text=True, timeout=120).returncode
    finally:
        os.unlink(path)


def input_checks():
    """Things that are not exports at all must not be accepted as empty exports."""
    good = open(SOURCE).read()
    first = good.split("\n", 1)[0]
    cases = {
        "empty file": "",
        "blank lines only": "\n\n",
        "no metadata record": good.split("\n", 1)[1],
        "wrong format major version": good.replace('"format":{"version":"3.1.0"}', '"format":{"version":"9.0.0"}', 1),
        "garbage": "this is not json\n",
        "truncated mid-line": good[: len(good) // 2],
    }
    bad = 0
    for name, text in cases.items():
        code = run_text(text)
        verdict = "ok" if code in (1, 3) else f"ACCEPTED({code})"
        print(f"{verdict:8} input: {name}")
        bad += code not in (1, 3)
    return bad


def main():
    bad = 0
    code, out = run(load())
    print(f"{'ok' if code == 0 else 'FAIL':5} unmodified export is accepted")
    bad += code != 0
    for m in MUTANTS:
        recs = load()
        m(recs)
        code, out = run(recs)
        verdict = {1: "ok", 0: "ACCEPTED"}.get(code, f"CRASH({code})")
        reason = next((l for l in out.splitlines() if l.startswith("REJECTED")), "")[:110]
        print(f"{verdict:8} {m.__name__:30} {reason}")
        bad += code != 1
    bad += input_checks()
    print(f"\n{len(MUTANTS)} mutants and 6 malformed inputs, {bad} problem(s)")
    sys.exit(1 if bad else 0)


main()
