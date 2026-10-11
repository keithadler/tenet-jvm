# Status

## Verified against real exports (all declarations accepted, nothing taken on trust)
- `Init` (Lean 4.35.0-rc4): 59,349 constants, 604 inductive blocks, about 21 s
- `Std`: 99,619 constants, 1,028 inductive blocks, about 43 s

## Implemented
- Names, universe levels (normalisation, equivalence and `>=` decided by splitting on zero/successor),
  expressions
- NDJSON export reader (format 3.x)
- Inference, whnf, definitional equality: lazy delta with reducibility hints, proof irrelevance, eta,
  structure eta, unit-like types, Nat literal arithmetic, string literals, projections, recursor and
  quotient reduction, K
- Definitions, theorems, axioms, opaques, unsafe/partial rules
- Inductive types: parameter and universe checks, positivity, constructor checks, the elimination
  universe, K-target detection, and regeneration of every recursor (type and rules)
- Nested inductives: auxiliary types are introduced, the group is checked, and the generated recursors
  are translated back and compared with the export
- Quotient types, compared with the canonical types

## Principle
The export is never trusted for anything the kernel can derive. Recursors, recursor rules and the
informational flags (`isRec`, `isReflexive`, `numNested`, `numIndices`, K) are recomputed and compared.

## Known gaps
- Not yet run on Mathlib or other large third-party libraries
- No resource limits (time or memory) per declaration
- Negative test suite is just starting: see `tests/`
