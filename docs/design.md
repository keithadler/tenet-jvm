# Design

This document describes how tenet-jvm is put together and why. It assumes you know what a Lean kernel is:
a small program that type-checks the fully elaborated terms Lean produces, and whose acceptance is what
makes a theorem a theorem. For the type theory itself, see Mario Carneiro's
[*The Type Theory of Lean*](https://github.com/digama0/lean-type-theory/releases) and Chris Bailey's
[*Type Checking in Lean 4*](https://ammkrn.github.io/type_checking_in_lean4/).

## Shape

```
export.ndjson ──► ExportReader ──► Decl / InductiveBlock ──► Kernel.add ──► Env
                                                              │
                                      ┌───────────────────────┼─────────────────────┐
                                      ▼                       ▼                     ▼
                                 TypeChecker           InductiveChecker      quotient check
                           (infer, whnf, defeq)     (+ NestedInductive)
```

| File | Role |
|---|---|
| `Name`, `Level`, `Expr` | The term language. Expressions are immutable, locally nameless (bound variables are de Bruijn indices, free variables are fresh `FVar`s), and carry their loose-bound-variable range, so closed subterms are skipped during substitution. |
| `ExportReader`, `Json` | Streams `lean4export` NDJSON. Declarations are handed to the kernel one at a time, in file order; a file is never held in memory as a whole. |
| `Decl`, `Env` | Constants and the environment. `Env.fork()` gives a scratch layer used while an inductive group is being checked. |
| `TypeChecker` | Inference, weak head normalisation, definitional equality. |
| `InductiveChecker` | Validates an inductive declaration and *generates* its recursors. |
| `NestedInductive` | Replaces nested occurrences (`Array Syntax` inside `Syntax`) by auxiliary types, and translates the generated recursors back. |
| `Kernel` | Adds declarations to the environment: definitions, theorems, axioms, opaques, quotient types, inductive groups. |
| `Main` | Command line, exit codes, fail-closed error handling. |

## The rule: derive, then compare

The export contains more than the kernel needs. Every inductive type arrives with its constructors, its
recursors and the recursors' reduction rules, plus flags such as `isRec`, `isReflexive`, `numNested`, `k`.
Lean's real kernel receives only the *declaration* (types and constructor types) and computes the rest.

tenet-jvm does the same: it takes the types and constructor types out of the export, derives everything
else itself, and then compares the result with what the export claims. A mismatch in any recursor type,
rule, flag or count is a rejection. Nothing in the export is believed that the kernel can work out.
`tests/negative.py` mutates a valid export in sixteen ways to check this; each mutant must be rejected.

## Type checker

The structure follows the reference kernel's algorithm closely, because matching its decisions is what
makes an independent implementation useful as a cross-check.

**Inference** has a checking mode (every application's argument is compared with the binder's type) and
an inference-only mode used on terms that have already been checked. Results are cached per declaration.

**Weak head normal form** is split in two. `whnfCore` does everything that needs no definition to be
unfolded: beta, let (zeta), projections of constructor applications, recursor and quotient reduction,
K-like reduction, structure eta for recursor majors. `whnf` adds delta (unfolding definitions) and the
`Nat` arithmetic shortcuts. `whnfCore` takes two flags, `cheapRec` and `cheapProj`, that stop it from
doing full `whnf` on the major premise or the structure of a projection; the cheap and the full results
are cached separately, because mixing them changes how the two sides of a comparison unfold (see
[divergences](divergences.md)).

**Definitional equality** runs, in order: pointer/structural equality, binder comparison, sort comparison,
cheap `whnfCore` on both sides, proof irrelevance, *lazy delta reduction*, constant/free-variable/projection
congruence, full `whnfCore`, application congruence, eta, structure eta, string-literal expansion, and
unit-like types.

Lazy delta unfolds the side whose head has the greater reducibility height, and when both heads are the
same definition it first tries to settle the comparison on the arguments. When only one side can unfold and
the other is a stuck projection, the projection is reduced first.

**Universe levels** are normalised, and equivalence and `≥` are decided by case-splitting on whether each
parameter that sits in the right-hand side of an `imax` is zero, which removes the `imax` and leaves a
fragment (`max`, `succ`, parameters) where comparison is complete.

**Nat and String literals.** Arithmetic on literals (`Nat.add`, `sub`, `mul`, `div`, `mod`, `gcd`, `beq`,
`ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, `pow`, `log2`, `succ`) is done with `BigInteger`,
only on closed terms. String literals expand to `String.ofList` of `Char.ofNat` applications (or
`String.mk` on older Lean versions).

## Inductive types

For a group of mutual types the checker follows Lean's `add_inductive_fn`:

1. Check the types: shared parameters, a common result universe.
2. Declare the types, with `isRec` and `isReflexive` computed syntactically.
3. Check each constructor: parameters match, field universes fit under the result universe (unless the
   type is a `Prop`), **strict positivity**, and a result type of the form `I params indices` with no
   occurrence of the types being declared in the indices.
4. Declare constructors.
5. Choose the elimination universe: only `Prop` for an inductive predicate unless it is a "syntactic
   subsingleton" (at most one constructor whose non-`Prop` fields all appear in the result type), else a
   fresh universe parameter.
6. Decide whether the type is a K-like target.
7. Build motives, minor premises, recursor types and rules.

Universe tests ("is this level zero?") use level *equivalence*, not syntactic equality: `Sort (imax 1 0)` is
a proposition, and treating it as anything else is a soundness bug in the official kernel that
[lean4#14613](https://github.com/leanprover/lean4/pull/14613) fixed.

### Nested inductives

If a constructor field mentions `J As` where `J` is an existing inductive type and `As` mention the types
being declared, `NestedInductive` introduces an auxiliary type for `J As` (copying `J`'s constructors,
with `As` substituted), rewrites the field to use it, and repeats until no nested occurrence is left. The
enlarged mutual group is checked and its recursors generated as above. The auxiliary types, constructors
and recursors are then translated back to `J As` and compared with the export, where the auxiliary
recursors appear as `I.rec_1`, `I.rec_2`, ….

## Failing closed

A checker's worst failure is saying "accepted" when it did not check. `Main` therefore starts from the
verdict *error*, sets it to *accepted* only after the whole file has been processed with no rejection, and
turns every exception into a non-zero exit. A malformed export (an undefined name or expression id) is a
rejection.

Exit codes: `0` accepted, `1` rejected, `2` declined (reserved; nothing is declined today), `3` internal
error or unreadable input, `64` usage.

## Performance notes

- Structural equality on expressions is a bounded walk that falls back to a walk with a memo of node pairs
  already compared, so two unshared copies of a large DAG are compared in time proportional to the DAG,
  not to its unfolded size.
- A fixed-size, direct-mapped table (`tenet.share.bits`, default 18) makes most structurally equal terms
  the same object. It is lossy and bounded; it only affects speed. Setting `-Dtenet.share.bits=0` turns it
  off, which is faster on library-style workloads and much slower on evaluation-heavy ones.
- Substitution walks small terms with no bookkeeping, and switches to a cache keyed on node identity and
  binder depth when the walk turns out to be large.
- The checker runs in a thread with a very large stack (type checking is deeply recursive) and prefers the
  throughput collector: `-XX:+UseParallelGC`. `bin/tenet-jvm` sets both.
