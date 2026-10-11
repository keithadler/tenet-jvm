# leankernel-java

An independent kernel (type checker) for [Lean 4](https://lean-lang.org), written in Java.
It reads the NDJSON output of [`lean4export`](https://github.com/leanprover/lean4export) and
re-checks every declaration from scratch.

## Why this exists

This project is not a flag-planting exercise. The author intends to maintain it fully, alongside
[Tenet](https://www.nuget.org/packages/tenet) (C#) and the other independent checkers in the Lean
ecosystem ([nanoda](https://github.com/ammkrn/nanoda_lib), [lean4lean](https://github.com/digama0/lean4lean)).

The more independent kernels that verify the same proof, the better. A soundness bug in one
implementation is unlikely to appear in another written separately, in a different language, by
different people. Each additional checker shrinks the set of bugs that can slip through unnoticed.
The checkers are meant to be run against each other and compared, for example in the
[Lean Kernel Arena](https://arena.lean-lang.org/).

## Licence and process

Apache License 2.0, the same licence Lean 4 and `lean4export` use (see `LICENSE`). Development is
open: issues, pull requests and bug reports against the kernel are welcome, and any disagreement
with the reference kernel will be treated as a bug to investigate, whichever side is wrong.

## Status

Early. See `STATUS.md` for exactly what is and is not verified. Anything the checker accepts on
trust is listed in its output; it never reports "all declarations verified" while that list is
non-empty.

## Build and run

Requires JDK 21 or later.

```
make
java -cp out leankernel.Main export.ndjson
```

Produce an export with `lean4export`:

```
lake env lean4export Init -- Nat.add_comm > export.ndjson
```
