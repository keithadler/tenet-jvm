# Status

## Implemented
- Names, universe levels (normalisation, equivalence, `>=`), expressions
- NDJSON export reader (format 3.x)
- Inference, whnf, definitional equality: lazy delta with reducibility hints, proof irrelevance,
  eta, structure eta, unit-like types, Nat literal arithmetic, string literals, projections,
  recursor and quotient reduction, K
- Definitions, theorems, axioms, opaques

## Not yet verified (accepted on trust, and reported as such)
- Inductive declarations: positivity, universe constraints, and regeneration of the recursor
  (type and rules) are not yet checked, only the types are well-typed
- Nested inductives
- Quotient declarations are not yet compared with the canonical types

Until those are done this is **not** a complete kernel: a malicious export could define a bogus
recursor and have it accepted.
