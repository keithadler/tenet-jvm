# Status

Version 0.1.6, 23 November 2026: memory and speed for very large exports, no change to what is accepted.

- **Compact memory.** Expressions live in a chunked store (about 10.6 bytes a node instead of 17) and declarations
  hold ids into it; objects are built on demand into a memo that is dropped between declarations. On the Mathlib
  slice `slice.wide` (415,915 constants) the live heap fell from 2.86 GB to 1.16 GB.
- **Failed definitional-equality checks are cached** for the current declaration, as Tenet does. A cached failure
  can only turn into a rejection, so any rejected declaration is checked again with the cache off and only that
  result counts (`TENET_NO_FAILURE_CACHE=1` turns it off). One theorem of the claimed Lean proof of the Riemann
  Hypothesis went from out of memory at 104 GB to 0.3 s.
- **`--verbose`** prints each declaration with its time and heap, and an out-of-memory error names the declaration.
- **`Nat.shiftLeft 0 n` is `0` for every `n`**, however large; before, a shift count past 2^24 fell back to unfolding
  the definition and did not finish (the arena's new `bugs/nat-shift-huge`).

Checked for this release: the whole claimed Lean proof of the Riemann Hypothesis (1,468,414 declarations, Lean 4.33.1
export, 61.6 GB) all verified in 6 h 05 m at 96.4 GB peak (0.1.5 ran out of memory on it); `Init` and `Lean` on
Lean 4.36.0 and 4.37.0-rc1, the same counts as below; `slice.wide`; and the arena at 99195b6 (23 November), built
locally: 231 correct, 28 "either", 0 wrongly accepted, 0 wrongly rejected, 2 timed out (the two
`eta-struct-major-*-no-whnf` cases, as before). Not rechecked: all of Mathlib and the arena's other large corpora.

Version 0.1.5, 19 November 2026: checked against Lean 4.36.0 and 4.37.0-rc1, with code changes. (0.1.4, 24 October 2026,
was checked against Lean 4.35.0 with no code change from 0.1.3.)

| Library | Lean 4.36.0 | Lean 4.37.0-rc1 |
|---|---|---|
| `Init` | 59,979 constants, 605 inductive groups | 62,454 constants, 613 groups |
| `Lean` (includes `Init` and `Std`) | 175,539 constants, 2,954 groups, 4.2 GB peak | 184,136 constants, 3,118 groups, 4.3 GB peak |

All verified, nothing taken on trust, JDK 26. The machine was busy with other checkers, so these runs give no
usable times. The Lean Kernel Arena's published suite as of that day: 225 of 225 decided correctly (90 rejected,
135 accepted); `magma-list-deep-n36` and `unfold-before-literal-fallback` needed more than 300 s on the loaded
machine, and gave the right verdict when run alone (1,419 s and 107 s). What changed in the code:

- Lean 4.37's three changes to definitional equality (proof irrelevance first, eta for the major premise of a
  subsingleton structure's recursor and no reduction of a proof standing there, structure eta against a partially
  applied constructor) are implemented and apply to exports written by Lean 4.37.0-rc1 or later. Earlier exports
  keep the earlier rules. See [divergences](divergences.md#rules-that-depend-on-the-lean-version).
- Lean 4.37's `Init` did not finish before one fix: `Nat` literal arithmetic refused any term mentioning a free
  variable, which the reference does not, and `Nat.trailingZeros_rec_eq_bits` then compared two copies of 2^64
  one successor at a time.
- Counts and indices beyond 32 bits are refused instead of truncated, and a loose bound variable in an inductive
  declaration is refused up front. Before, the first was accepted (read modulo 2^32) and the second got past the
  closedness check; neither occurs in a real export.

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

197 decided tests correct, 24 "either", none wrongly accepted, none wrongly rejected, two timed out,
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

- **Mathlib is checked, but it is memory-hungry.** A full Lean 4.34.1 Mathlib export (718,577 constants, 6,798
  inductive blocks) verifies in 14 to 19 minutes on an Apple-silicon laptop (824 s, 1,460 s and 1,127 s over three runs, the
  spread being the machine's, not the kernel's: an isolated export times identically on 0.1.2 and 0.1.3), with a peak footprint near 10 GB
  (`-Xmx9g`). Some category-theory declarations are still slower here than in the official kernel.
- **`navier-stokes-euler` is verified on 0.1.3** (129,845 constants, 421 s, 5.3 GB, in GitHub Actions via `arena-library.yml`).
  The history: The arena ran version 0.1.2 on it and found a wrong
  rejection: `NavierStokes.MixedAxisPreservation.CopyPotential`, a structure in `Type (u+1)` with a `Nat` field,
  failed the constructor universe check because `u+2 ≥ 1` was decided as false. The same comparison decided
  `3 ≥ u+1` as true, which would have let a constructor field live above its inductive type; no test had probed
  that direction. Both are fixed in 0.1.3 (`Level.geqCore` now follows the reference kernel's `is_geq_core`
  case for case), the structure's export is a must-accept test and a mutant covers the unsound direction. The
  full library needs Lean 4.34.0-rc2, whose `lake` crashes on the author's macOS, so it is re-run in CI.
- **Two arena corner cases time out.** `eta-struct-major-no-whnf` and `eta-struct-major-and-no-whnf` ask for
  structure eta on a recursor's major premise *before* reducing it, a change the official kernel is
  considering (lean4#14977). tenet-jvm, like the official kernel today, reduces first and does not terminate.
  The tests allow either answer, so these count as declined, not wrong.
  Lean 4.37.0-rc1 has made that change ([lean4#15371](https://github.com/leanprover/lean4/pull/15371)) and
  tenet-jvm now applies it to exports written by 4.37 or later. The two tests have not been re-run: they are not
  in the arena's published test archive, which carries decided tests only, and they are exported by the
  arena's pinned Lean, so under an earlier version stamp they would still be reduced first.
- **No dependency report**: the kernel lists the axioms an export declares but does not say which theorem
  depends on which (in particular, which depend on `sorryAx`).
- **No per-declaration time or memory limit.**
- **Native evaluation** (`Lean.reduceBool`) is not supported; see [divergences](divergences.md).
- **Export formats other than 3.x**, and Lean versions other than 4.34 to 4.37, have not been tried.
- **Performance**: single-threaded. A cache-friendlier term representation and parallel checking of
  independent declarations are the obvious next steps.
