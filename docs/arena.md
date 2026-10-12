# The Lean Kernel Arena

The [Lean Kernel Arena](https://arena.lean-lang.org/) ranks checkers, in this order, by

1. the number of invalid proofs wrongly accepted,
2. the number of valid proofs wrongly rejected,
3. the time to check Mathlib,
4. the number of declined tests.

## Where tenet-jvm stands

Run locally against the arena's `tutorial`, `bugs`, `corner-cases`, `other` and `perf` groups, tenet-jvm
gets all 197 decided tests right (141 + 18 + 19 + 9 + 28 across the groups, minus the tests where either
answer is allowed), with none wrongly accepted, none wrongly rejected and none declined or timed out. See
[testing](testing.md). The first two criteria are therefore met on everything that has been run.

Mathlib (Lean 4.34.1 export) verifies completely in about 824 s on the author's laptop (10 GB peak). Not run:
`navier-stokes-euler`. The arena's own runner and Linux have not been tried.

## Submitting

A checker is one YAML file in the arena's `checkers/` directory; [`arena/tenet-jvm.yaml`](arena/tenet-jvm.yaml)
is ready apart from the pinned `rev`. The interface is: `$IN` is an NDJSON export, exit code `0` means
accepted, `1` rejected, `2` declined, anything else is a checker error. tenet-jvm follows it.

Building needs a JDK, which the arena's `flake.nix` does not yet provide, so a submission also adds `jdk`
(or `jdk21`) to its `buildInputs`.

Checklist before opening the pull request:

- [ ] repository public, tagged release, `rev` pinned to a commit on `main`
- [ ] `make test` passes
- [ ] `tools/arena_check.py` still reports no wrongly accepted or rejected test
- [ ] the full `Init`, `Std` and (when available) `Mathlib` runs repeated on the pinned commit
- [ ] `docs/divergences.md` is current
