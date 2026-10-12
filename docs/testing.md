# Testing

tenet-jvm is tested, not verified. Evidence is only as good as what was run, so this file says what was
run, how to run it again, and what it does not show.

## 1. Real libraries

`lean4export` produces an export of any Lean module; tenet-jvm must accept all of it.

| Library | Lean | Constants | Inductive groups |
|---|---|---|---|
| `Init` | 4.35.0-rc4 | 59,349 | 604 |
| `Std` (includes `Init`) | 4.35.0-rc4 | 99,619 | 1,028 |

Every declaration is accepted and nothing is taken on trust. These numbers matter for a second reason:
in `Init` and `Std` every inductive type's recursors (types and reduction rules) were *regenerated* by the
kernel and compared with the export, for all 1,028 inductive groups, including nested ones such as
`Lean.Syntax`.

The arena's real-world projects were also checked (`con-leche`, `cedar`, `cslib`; see [status](status.md)),
about 570,000 further constants and 6,300 inductive groups, all accepted.

Reproduce:

```sh
git clone https://github.com/leanprover/lean4export && cd lean4export && lake build
lake env .lake/build/bin/lean4export Init > init.ndjson
bin/tenet-jvm init.ndjson
```

## 2. The Lean Kernel Arena

[The arena](https://github.com/leanprover/lean-kernel-arena) is a shared set of tests for kernels: good
exports that must be accepted, bad ones (including soundness bugs that were really found in the official
kernel and in other checkers) that must be rejected, and corner cases where either answer is allowed.

`tools/arena_check.py` runs tenet-jvm over a locally built copy and scores it the way the arena does:

```sh
cd lean-kernel-arena
for g in tutorial 'bugs/*' 'corner-cases/*' 'other/*' 'perf/*'; do uv run lka.py build-test "$g"; done
cd ../tenet-jvm
uv run --with pyyaml tools/arena_check.py ../lean-kernel-arena
```

Result (arena at 76ddcf8, 12 October 2026): **197 correct, 24 "either", 0 wrongly accepted, 0 wrongly rejected, 2 timed out** (the two `eta-struct-major-*-no-whnf` cases; see [status](status.md))
(tutorial 141 sub-tests, bugs 18, corner cases 19, other 9, perf 28).

The first run was not clean: it wrongly accepted two soundness-bug tests and wrongly rejected one level
test. All three came from the same two causes, a syntactic zero test on universe levels and an incomplete
`imax` normalisation, and are fixed. `docs/divergences.md` has the details.

## 3. Mutation tests

`tests/negative.py` takes a valid export, damages it in one targeted way, and requires a rejection. Sixteen
mutants: a theorem given the wrong proof, a definition given the wrong type, an undeclared universe, swapped
recursor rules, a wrong field count in a rule, a recursor given another type's type, flipped `k`, `isRec`,
`numParams`, `numIndices`, `numNested` flags, a constructor dropped from its type, a wrong `cidx`, a wrong
`numFields`, and an extra orphan recursor. It also feeds six things that are not exports (an empty file, blank
lines, a file with no metadata record, an unsupported format version, garbage, a file cut in half) and
requires that none is accepted, and checks that the unmodified export is accepted.

```sh
make test
```

Two of the most serious bugs of the project were found this way and by running a pipeline: an exception
inside the checker thread ended the process with exit code 0, "accepted", and an empty input (a failed
`lean4export` upstream of a pipe) was accepted as a vacuously valid export. Exit codes now default to *error*
and become *accepted* only when a non-empty file with a metadata record has been processed in full; see
[design](design.md#failing-closed).

## What this does not show

- **Mathlib was checked once, on one machine.** 12 October 2026, Lean 4.34.1 export, JDK 21, `-Xmx9g`: 718,577
  constants, all verified, 823.6 s, peak footprint about 10 GB; two further runs on 0.1.3 the same day took 1,460 s and 1,127 s
  with other work on the machine, and an A/B of the two builds on one export was identical. The arena's own runner (Linux, Nix) then verified it in
  30.1 min. The same arena run found the `navier-stokes-euler` rejection described in [status](status.md): the
  arena's library tests catch what the small groups do not, and should be run before every release.
- **The arena suite is a floor, not a ceiling.** Passing it says no *known* bug is present.
- **Both kinds of error are possible in the kernel's own search for a proof of defeq**: wrongly rejecting a
  valid proof is likely to be noticed; wrongly accepting an invalid one is not. The mutation tests and the
  arena's `bugs/` group exist for that reason, and they are the tests to extend first.
- **Agreement with Lean is not independence.** Where tenet-jvm copies a decision from the reference kernel it
  shares that kernel's mistakes if it had any. [Divergences](divergences.md) lists where it does not.
