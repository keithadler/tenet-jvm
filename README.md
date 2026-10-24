# tenet-jvm

[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)
![Java 21](https://img.shields.io/badge/Java-21%2B-orange.svg)
![Lean 4.34 – 4.35](https://img.shields.io/badge/Lean-4.34%20%E2%80%93%204.35-8a2be2.svg)

**An independent kernel for [Lean 4](https://lean-lang.org), written in Java, with no dependencies.**
It reads the NDJSON that [`lean4export`](https://github.com/leanprover/lean4export) writes and re-checks every
declaration from scratch: types, definitions, theorems, inductive types and their recursors, quotients.
If it accepts, a second, unrelated implementation agrees that the proof is valid.

tenet-jvm is the JVM counterpart to [Tenet](https://github.com/keithadler/tenet) (C#/.NET). It is not a
flag-planting exercise. The more independent kernels check the same proof, the fewer bugs can hide in all of
them at once, and it is maintained alongside Tenet and the rest of the Lean verification chain
(the official kernel, [lean4lean](https://github.com/digama0/lean4lean), [nanoda](https://github.com/ammkrn/nanoda_lib)).

## Status

Version 0.1.3. It checks the Lean libraries it has been given, including all of Mathlib, and it passes every decided test of the
[Lean Kernel Arena](https://arena.lean-lang.org/) groups that have been run. [`docs/status.md`](docs/status.md) is the current account; [`docs/testing.md`](docs/testing.md)
says exactly what was run.

```
$ bin/tenet-jvm lean.ndjson
lean 4.35.0-rc4, export format 3.1.0, 13113386 lines
checked 171705 constants ({AXIOM=4, DEF=79646, THM=79031, OPAQUE=2471, QUOT=4}) and 2860 inductive blocks in 54.17s
axioms declared: propext, Quot.sound, Classical.choice, sorryAx
all declarations verified
```

That is the whole `Lean` library (the compiler and elaborator, including `Init` and `Std`). Exit code `0`.

## Reproduce it

```sh
# 1. an export (any Lean module; this builds lean4export against your toolchain)
git clone https://github.com/leanprover/lean4export && (cd lean4export && lake build)
(cd lean4export && lake env .lake/build/bin/lean4export Init > ../init.ndjson)

# 2. the checker
git clone https://github.com/keithadler/tenet-jvm && cd tenet-jvm
make                       # needs a JDK 21+; nothing else
bin/tenet-jvm ../init.ndjson
```

## Tested against

| | What | Result |
|---|---|---|
| Lean libraries | `Init`: 59,349 constants, 604 inductive groups | all verified, ≈ 25 s |
| | `Std` (includes `Init`): 99,619 constants, 1,028 groups | all verified, ≈ 45 s |
| | `Lean` (includes both): 171,705 constants, 2,860 groups | all verified, ≈ 43 s |
| Real projects (arena) | `con-leche`: 27,959 constants, 333 groups | all verified, ≈ 39 s |
| | `cedar`: 148,832 constants, 1,921 groups | all verified, ≈ 45 s |
| | `cslib`: 394,284 constants, 4,022 groups | all verified, ≈ 348 s |
| Lean Kernel Arena | `tutorial`, `bugs`, `corner-cases`, `other`, `perf` (223 tests) | 197 decided tests right (and 24 where either answer is allowed), **0 wrongly accepted, 0 wrongly rejected**, 2 timed out (the two `eta-struct-major-*-no-whnf` corner cases, on which the official kernel does not terminate either) |
| Mutation tests | 17 targeted corruptions of a valid export, 6 inputs that are not exports, 1 export that must be accepted | all as intended |
| | `Mathlib` (Lean 4.34.1 export, 718,577 constants, 6,798 groups) | all verified, 14–19 min over three runs on the laptop (10 GB peak), 30.1 min on the arena's own runner |
| | `navier-stokes-euler` (129,845 constants, 1,614 groups; built and checked in GitHub Actions, since its Lean 4.34.0-rc2 `lake` crashes on the author's macOS) | all verified on 0.1.3, ≈ 421 s, 5.3 GB peak. Version 0.1.2 wrongly rejected one structure here (`CopyPotential`, a universe-level comparison bug found by the arena, fixed in 0.1.3 and now a test) |

Lean 4.35.0-rc4 exports for the Lean libraries, the arena's 4.34.1 exports for the projects and Mathlib; JDK 21, an
Apple-silicon laptop that was not idle. All rows re-run on v0.1.2 and v0.1.3 on 12 October 2026. Times are indicative. `Init` from Lean 4.35.0 (released
12 October) was checked again on 23 October: 59,349 constants, all verified, 28.7 s.

## Install

There is nothing to install beyond a JDK.

```sh
make            # compiles to out/
make test       # 16 mutation tests, 6 malformed inputs, and a valid export
```

`bin/tenet-jvm` is a small launcher that sets sensible JVM options (throughput collector, most of the
RAM). `JAVA` and `JAVA_OPTS` override the `java` binary and the options.

## Commands

```
bin/tenet-jvm [--keep-going] [--version] <export.ndjson | ->
```

| Exit code | Meaning |
|---|---|
| `0` | every declaration was accepted |
| `1` | something was rejected, or the export is malformed |
| `3` | an internal error or an unreadable file |
| `64` | usage error |

Without `--keep-going` it stops at the first rejection. With it, it reports every rejected declaration
(later ones will often fail only because they depend on an earlier rejection). The process fails closed:
the verdict starts as *error* and becomes *accepted* only when the whole file has been processed, so a
crash can never read as success.

To produce an export, use `lean4export` as shown above; it takes module names and, after `--`, optional
constant names to export just those and what they depend on.

### Scoring against the arena

```sh
uv run --with pyyaml tools/arena_check.py path/to/lean-kernel-arena
```

runs a locally built copy of the arena's tests and scores them the way the arena does (wrongly accepted,
wrongly rejected, declined). See [`docs/arena.md`](docs/arena.md).

## What "checking" means here

tenet-jvm re-implements Lean's trusted core: the type checker (inference, weak head normalisation,
definitional equality with lazy delta reduction, proof irrelevance, eta, structure eta, K-like reduction,
`Nat` and `String` literals, projections, quotients) and the inductive-type machinery. It does **not** run
Lean's elaborator, tactics or `Meta` code, and it does not need them: an export is the fully elaborated
term, and the kernel's job is only to type-check it.

The principle that matters most is **derive, then compare**. For an inductive type, the export contains
the constructors, the recursors and the recursors' reduction rules, as well as flags such as `isRec`.
Lean's own kernel is given only the types and constructor types and *computes* the rest. So does tenet-jvm:
it regenerates every recursor, rule and flag from the declaration and rejects the export if anything
differs. This includes nested inductives (such as `Lean.Syntax`, which contains `Array Syntax`) by
introducing the same auxiliary types the reference kernel does and translating back. See
[`docs/design.md`](docs/design.md).

### What you still have to trust

- **The Java Virtual Machine, the JDK, and this program's source.** Nothing about it is verified. It is
  tested, which is evidence and not proof, and it is small enough to read: about 3,500 lines in
  `src/main/java/tenet`.
- **That the export is of what you meant to check.** The kernel checks that the file is internally valid,
  not that its theorem statements say what their names suggest. A theorem about the wrong definition is
  still a valid proof.
- **The axioms.** The kernel accepts whichever axioms the export declares and prints them
  (`propext`, `Quot.sound` and `Classical.choice` are the usual three). `sorryAx` is declared by Lean's own
  prelude; a proof that depends on it is a proof of nothing, and the kernel does not currently tell you
  which theorems depend on which axiom.
- **That the type theory is consistent.** No program can establish that of itself.
- **What it shares with the reference kernel.** Where tenet-jvm copies a decision from Lean's C++ kernel it
  shares that decision's mistakes if there were any. [`docs/divergences.md`](docs/divergences.md) lists
  every place it does something different, and why.

### Why the checks are not vacuous

A kernel that accepts everything would also print "all declarations verified". The evidence that this one
does not is, in order of strength: the arena's `bugs/` group contains exports of real soundness bugs
(including some in the official kernel), all of which are rejected; the mutation tests corrupt a valid
export sixteen different ways and require rejection with the intended reason; and the first run of the
arena found three genuine errors in this implementation (two soundness holes and a wrong rejection), which
are fixed. Two more were found by the mutation tests and by running a pipeline: a crash that exited with the
"accepted" code, and an empty input that was accepted as a vacuously valid export. Both now fail closed.

## Other checkers

| Checker | Language | Notes |
|---|---|---|
| Lean's kernel | C++ | The reference. Checks what it elaborates, and is what everything else is compared to. |
| [lean4lean](https://github.com/digama0/lean4lean) | Lean | A kernel written in Lean, which makes properties of it provable in Lean. |
| [nanoda](https://github.com/ammkrn/nanoda_lib) | Rust | An independent kernel. |
| [Tenet](https://github.com/keithadler/tenet) | C# | Also reads `.olean` files directly. This project's sibling. |
| tenet-jvm | Java | This project: no dependencies, runs wherever a JVM does. |

The arena runs them side by side. A bug found in one is a test for all.

## Layout

```
src/main/java/tenet/   the kernel (Name, Level, Expr, TypeChecker, InductiveChecker, NestedInductive, Kernel, …)
bin/tenet-jvm          launcher
tests/negative.py      16 mutation tests;  tests/exports/ a small valid export
tools/arena_check.py   scores the checker against a local copy of the Lean Kernel Arena
docs/                  design, divergences from the reference kernel, testing, status, arena notes
```

## Contributing

Issues and pull requests are welcome, especially:

- **a declaration this checker wrongly accepts or rejects**, with the export that shows it. A disagreement
  with the reference kernel is a bug to be investigated, whichever side turns out to be wrong;
- **tests**, particularly for `tests/negative.py` (one more way to corrupt an export) and corner cases for
  the arena;
- results on libraries that have not been tried, and Lean versions other than 4.34 and 4.35.

Please keep code and documentation consistent with the rule at the top of
[`docs/design.md`](docs/design.md): the kernel derives, then compares.

## License

Apache License 2.0, the licence Lean 4 and `lean4export` use. See [`LICENSE`](LICENSE).

## About

Written and maintained by [Keith Adler](https://github.com/keithadler), alongside [Tenet](https://github.com/keithadler/tenet).
