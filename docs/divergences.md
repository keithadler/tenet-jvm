# Divergences from the reference kernel

An independent kernel is only a useful second opinion if it is clear where it does *not* simply copy the
first. This file lists every place where tenet-jvm decides something differently from Lean's C++ kernel,
or where it adds a rule that Lean's kernel lacks, and why.

"Lean's kernel" below means the C++ implementation in `leanprover/lean4` as described by its sources,
its documentation, and the [Lean Kernel Arena](https://arena.lean-lang.org/) tests that probe it.
Where this file says Lean "does" something it is describing intended behaviour and not quoting code;
corrections are welcome.

## Stricter than Lean (could reject something Lean accepts)

- **Indices of a constructor's result type may not mention the types being declared.** The constructor
  `mk : T (f T)` for a type `T` is rejected. Lean's rule here was not established when this was written;
  rejecting is the safe side. No declaration in `Init` or `Std` (1,028 inductive groups) is affected.
- **A sort that does not reduce to a `Sort` is an error, not "not a proposition".** When deciding whether a
  type is a `Prop` (for proof irrelevance and for projections out of a structure), a type whose own type is
  stuck raises `type expected`. This follows
  [lean4#14807](https://github.com/leanprover/lean4/pull/14807); the arena test `bugs/proj-of-subst-prop`
  exercises it.
- **Anything in the export that the kernel can derive must agree with its own derivation**, including
  informational flags (`isRec`, `isReflexive`, `numNested`, `numIndices`, `k`, constructor `cidx` and
  `numFields`). Lean never sees these in the declaration it receives; here a wrong one is a rejection.
- **Unknown record types in the export are a rejection**, not skipped.

## More complete than a literal port

- **Universe level equivalence and `≥` are decided by case-splitting** on every parameter that occurs in
  the right-hand side of an `imax`. Under every assignment, `imax 1 u = u` and `Sort (imax 1 0)` is `Prop`.
  The arena tests `bugs/level-imax-leq`, `bugs/level-imax-normalization` and
  `corner-cases/imax-right-successor` are about exactly this.
- **"Is this level zero" means "is this level equal to zero for all assignments"**, in the universe checks of
  inductive declarations and in the `Prop` test. A syntactic test is
  [a soundness bug in the official kernel](https://github.com/leanprover/lean4/pull/14613) that
  `bugs/proj-of-imax-prop` reproduces.

## Strategy choices that change what is tried first

None of these change what is accepted, only how a comparison is carried out. They are listed because a
different strategy can turn a quick check into one that never finishes.

- **The cheap and the full `whnfCore` results are cached separately.** A fully reduced result must not be
  returned to a call that asked for the cheap form, or the two sides of a comparison stop unfolding in step.
  (This was found on `Int32` range instances in `Init`, where it meant unfolding `Nat.sub` against a literal
  of 2³¹ one successor at a time.)
- **When only one side of a comparison can be unfolded and the other is a stuck projection, the projection
  is reduced first.** Same reason, same example.
- **After full `whnfCore`, progress is "the term changed structurally"**, not "the term is a different
  object", so equal copies cannot loop.
- **Small substitutions run without a cache; large ones switch to a cache** keyed on node identity and
  binder depth.

## Representation choices

- **Binder names and binder info are ignored by equality.** Alpha-equivalent terms are equal. They are kept
  for error messages and for the names of generated binders.
- **String literals expand through `String.ofList` when the environment has it** and `String.mk` otherwise.
  In Lean 4.35, `String` is a structure over `ByteArray` and `String.mk` is an ordinary definition, so the
  literal expansion has to go through the function that builds a string from characters.
- **`Nat` arithmetic on literals uses `BigInteger`** and is applied only to closed terms.

## Not done

- **Native evaluation.** Lean's kernel can evaluate `Lean.reduceBool` / `Lean.reduceNat` by running compiled
  code. An independent checker cannot, and does not try. A proof that depends on `native_decide` contains
  the axiom `Lean.ofReduceBool`, and the term `Lean.reduceBool c` does not reduce here, so such a proof is
  rejected. Checked on 2026-10-23 with a hand-written export in which `h : P (Lean.reduceBool b)` is offered as
  `P true`: it is rejected, exit code 1. Lean 4.35.0 removed `reduce_native` from its kernel, so from 4.35.0 the
  reference gives the same verdict. Up to 4.34 the reference could have accepted a proof that really ran compiled code.
- **Axiom auditing.** The kernel accepts whatever axioms the export declares and reports them; deciding
  whether `propext`, `Classical.choice` and `Quot.sound` are acceptable is the reader's job.
- **Versions other than export format 3.x.**
- **A per-declaration time or memory limit.**
