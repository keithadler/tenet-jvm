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

## Rules that depend on the Lean version

Lean 4.37.0-rc1 changed three rules of definitional equality (part of
[lean4#14977](https://github.com/leanprover/lean4/issues/14977)). The verdict on a file therefore depends on the
Lean that wrote it, and tenet-jvm reads that from the export's metadata record (`LeanVersion.kernelHasEta437`):
4.37.0-rc1 and later get the new rules, everything earlier keeps the old ones, a 4.37 nightly counts from
2026-10-21 (the changes landed on master on 2026-10-20), and a version that cannot be parsed gets the old rules.

| Lean change | Up to 4.36 | From 4.37 |
|---|---|---|
| [#15103](https://github.com/leanprover/lean4/pull/15103) | Proof irrelevance is tried after the first `whnfCore` of both sides. | It is tried before, on the terms as given. |
| [#15371](https://github.com/leanprover/lean4/pull/15371) | A recursor's major premise is always reduced; structure eta on it is skipped for every `Prop`. | A major premise that is a proof is not reduced; eta is skipped only when the recursor has as many universe parameters as the first inductive type of its block, so `And.rec` gets it. |
| [#15373](https://github.com/leanprover/lean4/pull/15373) | Structure eta needs a fully applied constructor. | A partially applied constructor is compared after applying both sides to fresh variables for the missing fields. |

Neither direction is the lenient one. Under the new rules `And.rec f ⟨x.1, x.2⟩ = And.rec f x` holds by `rfl` and
under the old ones it does not; under the old rules a recursor applied to a proof that only *reduces* to a
constructor (`Acc.rec` on a definition whose body is `Acc.intro ..`) computes, and under the new ones it is stuck.
`tests/exports/eta437.ndjson` and `tests/exports/acc436.ndjson` hold one direction each, and `make test` checks
both files under both rule sets. The expected verdicts were taken from Lean's own kernel, 4.36.0 and 4.37.0-rc1,
replaying the same files.

Lean 4.37.0-rc1 also made its `.olean` format version 4 and briefly extended the unit-like rule
([#15372](https://github.com/leanprover/lean4/pull/15372), reverted before the release candidate). Neither
concerns this checker: it reads exports only, and the unit-like rule is the one every release has had.

## Corrected to match the reference

Found while checking Lean 4.36.0 and 4.37.0-rc1, November 2026. None of these was known to produce a wrong
verdict on a real export.

- **Counts and indices that do not fit in 32 bits are refused.** They used to be read modulo 2^32, so a
  projection index of 2^32 was index 0 and `numParams` of 2^32 was no parameters at all: a block with 2^32 added
  to every `numParams` was accepted as the valid block it started as. Lean fixed the same class in its own kernel
  in 4.37 ([lean4#16279](https://github.com/leanprover/lean4/pull/16279)). Such an export is now rejected as
  malformed, which is stricter than the reference only in rejecting the whole file instead of one declaration.
- **A loose bound variable in an inductive type or a constructor type is refused before anything else.** The
  check existed, but ran after the parameters had been instantiated, by which point a loose variable in a
  constructor field looked bound. The declaration from
  [lean4#16489](https://github.com/leanprover/lean4/issues/16489) got as far as recursor generation. Lean checks
  it up front since 4.37 ([lean4#16512](https://github.com/leanprover/lean4/pull/16512)); here it applies to
  every version, since no well-formed export has one. This is stricter than Lean 4.36 and earlier.
- **Arithmetic on `Nat` literals no longer refuses a term that mentions a free variable.** The reference has no
  such test inside `reduce_nat`, only at one call site in lazy delta reduction, where tenet-jvm has it too. With
  the extra test, `Nat.beq a b` whose arguments reduce to the literal 2^64 but mention a variable along the way
  was compared through the unary definition. One theorem of `Init` in Lean 4.37
  (`Nat.trailingZeros_rec_eq_bits`) does exactly that and did not finish.

## Strategy choices that change what is tried first

None of these change what is accepted, only how a comparison is carried out. They are listed because a
different strategy can turn a quick check into one that never finishes.

- **The cheap and the full `whnfCore` results are cached separately.** A fully reduced result must not be
  returned to a call that asked for the cheap form, or the two sides of a comparison stop unfolding in step.
  (This was found on `Int32` range instances in `Init`, where it meant unfolding `Nat.sub` against a literal
  of 2³¹ one successor at a time.)
- **When only one side of a comparison can be unfolded and the other is a stuck projection, the projection
  is reduced first.** Same reason, same example.
- **Definitional-equality failures are cached per declaration, and a rejection is re-checked without that
  cache.** The reference caches only successes. A cached failure can only make a later comparison answer "not
  equal", which callers turn into a rejection or a reduction not taken, never into an acceptance; so the first
  pass accepts a subset of what the faithful algorithm accepts, and `Kernel.add` re-runs any rejected
  declaration with the cache off, reporting only that outcome. Without the cache, one theorem of the claimed
  RH proof (`Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds.addition_bound_holds`, a 226-node proof)
  repeated the same failing `Int`/`Nat` recursor comparisons until 120 GB of heap ran out; with it, it takes
  0.3 s. Tenet does the same. `TENET_NO_FAILURE_CACHE=1` turns it off.
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
