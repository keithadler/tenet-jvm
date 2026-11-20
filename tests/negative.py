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


def ind_field_universe_too_big(recs):
    # Put HAdd.{u,v,w} in Sort 3 (Type 2) while its field hAdd : α → β → γ stays at level max u v w + 1,
    # which exceeds 3 for large u. The kernel must refuse the constructor ("too big"); a level comparison
    # that treats a constant left-hand side as "at least anything" accepts this.
    names = {}
    for r in recs:
        if "str" in r:
            names[r["in"]] = (names.get(r["str"]["pre"], "") + "." + r["str"]["str"]).lstrip(".")
    ex = {r["ie"]: r for r in recs if "ie" in r}
    nl = max(r["il"] for r in recs if "il" in r) + 1
    ne = max(ex) + 1
    blk_i = next(i for i, r in enumerate(recs) if key(r) == "inductive"
                 and any(names[t["name"]] == "HAdd" for t in r["inductive"]["types"]))
    t = next(t for t in recs[blk_i]["inductive"]["types"] if names[t["name"]] == "HAdd")
    # level 3 = succ (succ (succ 0)); level 0 is the implicit id 0
    new = [{"succ": 0, "il": nl}, {"succ": nl, "il": nl + 1}, {"succ": nl + 1, "il": nl + 2}, {"sort": nl + 2, "ie": ne}]
    # rebuild the Pi telescope of the type with the new Sort at its end
    chain, e = [], ex[t["type"]]
    while key(e) == "forallE":
        chain.append(e)
        e = ex[e["forallE"]["body"]]
    assert key(e) == "sort"
    body = ne
    for b in reversed(chain):
        ne += 1
        f = copy.deepcopy(b)
        f["ie"], f["forallE"]["body"] = ne, body
        new.append(f)
        body = ne
    t["type"] = body
    recs[blk_i:blk_i] = new


def ind_num_params_wraps_32_bits(recs):
    # numParams + 2^32 everywhere in one block: read modulo 2^32 this is the unmodified, valid block (lean4#16279)
    blk = inductive(recs, 1)
    for part in ("types", "ctors", "recs"):
        for d in blk[part]:
            d["numParams"] += 2 ** 32

def proj_index_wraps_32_bits(recs):
    # a projection index of idx + 2^32: read modulo 2^32 it is the valid projection it was
    for r in recs:
        if "proj" in r:
            r["proj"]["idx"] += 2 ** 32
            return
    raise SystemExit("no projection in the source export")


MUTANTS = [ind_num_params_wraps_32_bits, proj_index_wraps_32_bits, ind_field_universe_too_big, thm_wrong_value, thm_undeclared_universe, def_wrong_type, rec_rules_swapped, rec_rule_field_count, rec_wrong_type,
           rec_k_flag_flipped, rec_k_flag_on_nat, ind_isrec_flipped, ind_num_params, ind_num_indices, ind_num_nested,
           ind_ctor_dropped_from_type, ctor_cidx, ctor_field_count, rec_extra_orphan]


def run_file(path):
    p = subprocess.run([LAUNCHER, "--keep-going", path], capture_output=True, text=True, timeout=120)
    rejected = sorted(l.split(":")[0].split()[-1] for l in p.stdout.splitlines() if l.startswith("REJECTED"))
    return p.returncode, rejected, p.stdout


def as_version(name, old, new):
    """A copy of an export whose metadata claims another Lean version; returns its path."""
    text = open(os.path.join(HERE, "exports", name)).read()
    stamp = '"version":"%s"}}}' % old
    assert text.count(stamp) == 1, f"{name}: expected one Lean version stamp {old}"
    f = tempfile.NamedTemporaryFile("w", suffix=".ndjson", delete=False)
    f.write(text.replace(stamp, '"version":"%s"}}}' % new))
    f.close()
    return f.name


# Which rules apply depends on the Lean that wrote the export (Lean 4.37 changed three; see docs/divergences.md).
# Each row: export, the version it is presented as (None: as written), the declarations that must be rejected.
# Lean's own kernel, 4.36.0 and 4.37.0-rc1, gives these verdicts on the same files.
VERSIONED = [
    ("eta437.ndjson", None, []),
    ("eta437.ndjson", ("4.37.0-rc1", "4.36.0"), ["Eta437.andMajor", "Eta437.partialCtor"]),
    ("acc436.ndjson", None, []),
    ("acc436.ndjson", ("4.36.0", "4.37.0"), ["Acc436.accReduces"]),
    ("partial_constructor_eta.ndjson", None, ["Eta437.boxEta"]),
    ("partial_constructor_eta.ndjson", ("4.37.0-rc1", "4.36.0"), ["Eta437.andMajor", "Eta437.boxEta", "Eta437.partialCtor"]),
]

VERSIONS = {
    "4.37.0-rc1": True, "4.37.0": True, "v4.37.1": True, "4.38.0-rc1": True, "5.0.0": True,
    "4.37.0-nightly-2026-10-21": True, "4.38.0-nightly-2026-11-20": True,
    "4.37.0-nightly-2026-10-20": False, "4.36.0": False, "4.36.0-rc2": False, "4.35.0": False, "4.12.0": False,
    "n/a": False, "garbage": False, "": False,
}


def version_checks():
    bad = 0
    for name, ver, expect in VERSIONED:
        path = as_version(name, *ver) if ver else os.path.join(HERE, "exports", name)
        try:
            code, rejected, _ = run_file(path)
        finally:
            if ver:
                os.unlink(path)
        good = rejected == sorted(expect) and code == (1 if expect else 0)
        shown = f"as Lean {ver[1]}" if ver else "as written"
        print(f"{'ok' if good else 'WRONG':8} {name} {shown}: rejected {rejected or 'nothing'}")
        bad += not good
    java = os.environ.get("JAVA", "java")
    out = subprocess.run([java, "-cp", os.path.join(ROOT, "out"), "tenet.LeanVersion", *VERSIONS], capture_output=True, text=True).stdout.split()
    good = out == [str(v).lower() for v in VERSIONS.values()]
    print(f"{'ok' if good else 'WRONG':8} LeanVersion.kernelHasEta437 on {len(VERSIONS)} version strings")
    bad += not good
    # An inductive whose constructor has a loose bound variable; the reason matters, since the file has no recursors
    # and would be rejected for that alone.
    code, _, out = run_file(os.path.join(HERE, "exports", "loose_bvar_inductive.ndjson"))
    good = code == 1 and "constructor type has free variables: T.mk" in out
    print(f"{'ok' if good else 'WRONG':8} loose_bvar_inductive.ndjson is rejected for the loose bound variable")
    bad += not good
    return bad


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
        verdict = "ok" if code == 1 else f"ACCEPTED({code})" if code == 0 else f"CRASH({code})"
        print(f"{verdict:8} input: {name}")
        bad += code != 1
    return bad


# Exports that must be accepted: each one is a declaration an earlier version of the checker wrongly rejected.
POSITIVE = {
    "copy_potential.ndjson": "structure in Type (u+1) with a Nat field: u+2 >= 1 (navier-stokes-euler, arena)",
}


def main():
    bad = 0
    code, out = run(load())
    print(f"{'ok' if code == 0 else 'FAIL':5} unmodified export is accepted")
    bad += code != 0
    for name, why in POSITIVE.items():
        code = subprocess.run([LAUNCHER, os.path.join(HERE, "exports", name)], capture_output=True, text=True, timeout=120).returncode
        print(f"{'ok' if code == 0 else f'REJECTED({code})':8} accepted: {name}  ({why})")
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
    bad += version_checks()
    print(f"\n{len(MUTANTS)} mutants, {len(POSITIVE)} must-accept exports, 6 malformed inputs and {len(VERSIONED) + 2} version and closedness checks, {bad} problem(s)")
    sys.exit(1 if bad else 0)


main()
