# The Lean Kernel Arena

The [Lean Kernel Arena](https://arena.lean-lang.org/) ranks checkers, in this order, by

1. the number of invalid proofs wrongly accepted,
2. the number of valid proofs wrongly rejected,
3. the time to check Mathlib,
4. the number of declined tests.

## Where tenet-jvm stands

Merged on 12 October 2026 (leanprover/lean-kernel-arena#267). On the arena's own runner, version 0.1.2 scored
206 correct, 24 "either", 1 incorrect and 2 errors: Mathlib verified in 30.1 min; `navier-stokes-euler` was
wrongly rejected (a universe-level comparison bug, fixed in 0.1.3); and the two `eta-struct-major-*-no-whnf`
corner cases timed out, as they do for the official kernel. Locally the small groups score 197 correct, 24
"either", 0 wrong, 2 timed out, the same as on the runner.

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
