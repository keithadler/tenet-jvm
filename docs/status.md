# Status

Version 0.1.0, 11 October 2026.

## Verified against real exports (everything accepted, nothing taken on trust)

| Library | Constants | Inductive groups | Time |
|---|---|---|---|
| `Init` | 59,349 | 604 | ≈ 25 s |
| `Std` (includes `Init`) | 99,619 | 1,028 | ≈ 45 s |
| `Lean` (includes both) | 171,705 | 2,860 | ≈ 55 s |

Lean 4.35.0-rc4, JDK 21. See [testing](testing.md) for what these runs do and do not show.

Real projects from the Lean Kernel Arena (exported with the arena's pinned revisions):

| Project | Lean | Constants | Inductive groups | Time |
|---|---|---|---|---|
| `con-leche` | 4.33.0 | 27,959 | 333 | ≈ 35 s |
| `cedar` | 4.34.1 | 148,832 | 1,921 | ≈ 50 s |
| `cslib` | 4.34.0 | 394,284 | 4,022 | ≈ 455 s |

All accepted. `cedar` declares `native_decide` axioms and `cslib` declares `Lean.ofReduceBool`,
`Lean.ofReduceNat` and `sorryAx`; tenet-jvm accepts declared axioms and lists them, it does not judge them.

## Lean Kernel Arena (local run)

197 decided tests correct, 18 "either", none wrongly accepted, none wrongly rejected, none declined,
over `tutorial`, `bugs`, `corner-cases`, `other` and `perf`. See [arena](arena.md).

## Implemented

- Names, universe levels, expressions
- NDJSON export reader (format 3.x)
- Inference; weak head normalisation; definitional equality with lazy delta reduction, proof irrelevance,
  eta, structure eta, unit-like types, `Nat` and `String` literals, projections, recursor, quotient and
  K-like reduction
- Definitions, theorems, axioms, opaques; the `unsafe` and `partial` rules
- Inductive types: parameter and universe checks, strict positivity, constructor checks, elimination
  universe, K targets, regeneration of every recursor (type and rules) and of the bookkeeping flags
- Mutual and nested inductive types
- Quotient types, compared with the canonical ones
- Fail-closed process exit; a report of the axioms declared

## Known gaps

- **Mathlib has not completed.** It is the arena's reference for time and memory. A run reached 59,000
  declarations in minutes; some category-theory declarations are far slower here than in the official
  kernel (one goal takes about 8 s against a fraction of a second), so total time is the open question.
- **`navier-stokes-euler`** has not been run: it needs Lean 4.34.0-rc2, whose `lake` crashes on the
  machine the project was developed on.
- **No dependency report**: the kernel lists the axioms an export declares but does not say which theorem
  depends on which (in particular, which depend on `sorryAx`).
- **No per-declaration time or memory limit.**
- **Native evaluation** (`Lean.reduceBool`) is not supported; see [divergences](divergences.md).
- **Export formats other than 3.x**, and Lean versions other than 4.34 and 4.35, have not been tried.
- **Performance**: single-threaded. A cache-friendlier term representation and parallel checking of
  independent declarations are the obvious next steps.
