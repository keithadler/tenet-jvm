# The Lean bug corpus, checked by three independent kernels

Results of running the repros of [leanbugs.com](https://leanbugs.com) (`sflean/leanbugs`) through Tenet (C#),
tenet-hs (Haskell) and tenet-jvm (Java). Each repro is compiled with the Lean version the corpus says it
reproduces on, exported with the matching `lean4export`, and given to each kernel. "rejects" means the
kernel refused the bad declaration; "accepts" means it did not. The driver is `tools/leanbugs/run.sh`;
this page is produced by `tools/leanbugs/report.py`. Entries without a `.lean` repro (0007, 0009, 0010,
0011, 0013, 0015) and lean-0005 (a library `#eval`, nothing a kernel sees) are not run.

| Entry | Built on | tenet-jvm | Tenet | tenet-hs |
|---|---|---|---|---|
| lean-0001 | v4.32.1 | **rejects** | **rejects** | **rejects** |
| lean-0002 | v4.33.0 | **rejects** | **rejects** | **rejects** |
| lean-0003 | v4.33.1 | **accepts** | **accepts** | **accepts** |
| lean-0004 | v4.33.0 | **accepts** | **accepts** | **accepts** |
| lean-0006 | v4.32.1 | **rejects** | **rejects** | **rejects** |
| lean-0008 | v4.33.0 | **rejects** | **rejects** | **rejects** |
| lean-0012 | v4.32.1 | **rejects** | **rejects** | **rejects** |
| lean-0014 | v4.33.0 | **accepts** | **accepts** | **accepts** |

Four of the proofs of `False` (0001, 0002, 0006, 0008) are also in the Lean Kernel Arena's `bugs/` group
as independent exports, where all three kernels reject them too.

## What lean-0003 shows

On Lean 4.33.1 `native_decide` does not reach the export as `Lean.ofReduceBool`; the compiler adds a
per-proof **axiom** (`flt._native.native_decide.ax_1_1`) to the environment, and the export declares it
exactly as it declares `propext`. A kernel that checks exports cannot tell the two apart. All three accept
the file and list the axiom; whether that counts as "fooled" depends on whether anyone reads the axiom
list, which is the corpus's `print-axioms` checker. A checker option that fails on any axiom outside the
standard three would turn this into a rejection.

## Per entry

### lean-0001

proof of `False`: wrong-structure projection (lean4#14576)

- tenet-jvm: rejects — `REJECTED THM bad: application type mismatch`
- Tenet: rejects — `FAILED: 161810 checked, 3 failed, 0 skipped, 169346 constants, 34.4s, 8 jobs`
- tenet-hs: rejects — `inductive E: FAILED: 161810 checked, 3 failed, 483.2s`

### lean-0002

proof of `False`: `is_def_eq` cache depended on the order of checks (lean4#14806)

- tenet-jvm: rejects — `REJECTED inductive Native64TwoHashOwner: arg #3 of 'Native64TwoHashOwner.step' has a non valid occurrence of the datatypes being declared`
- Tenet: rejects — `FAILED: 163421 checked, 1 failed, 0 skipped, 171033 constants, 48.6s, 8 jobs`
- tenet-hs: rejects — `inductive Native64TwoHashOwner: FAILED: 163421 checked, 1 failed, 459.7s`

### lean-0003

FLT by `native_decide` (lean4#14684); the export declares `flt._native.native_decide.ax_1_1` as an axiom

- tenet-jvm: accepts — `axioms declared: Classical.choice, propext, Quot.sound, Lean.trustCompiler, Lean.ofReduceNat, sorryAx, Lean.ofReduceBool, flt._native.native_decide.ax_1_1`
- Tenet: accepts — `OK: 57982 checked, 0 failed, 0 skipped, 59438 constants, 30.3s, 8 jobs`
- tenet-hs: accepts — `OK: 57982 checked, 0 failed, 59438 constants, 241.2s`

### lean-0004

`infer_let` wrong result (lean4#10475): the repro is a valid theorem the 4.24.0 kernel cannot type, so it is built on a fixed Lean and the question is whether the checkers accept it

- tenet-jvm: accepts — `axioms declared: propext, Quot.sound, Classical.choice, sorryAx, Lean.trustCompiler, Lean.ofReduceBool, Lean.ofReduceNat`
- Tenet: accepts — `OK: 163397 checked, 0 failed, 0 skipped, 171003 constants, 56.6s, 8 jobs`
- tenet-hs: accepts — `OK: 163397 checked, 0 failed, 171003 constants, 234.8s`

### lean-0006

proof of `False`: sorts not recognised as `Prop` up to universe normalisation (lean4#14613)

- tenet-jvm: rejects — `REJECTED DEF kmLeak: invalid projection, structure is a proposition but field is not: _f488462.1`
- Tenet: rejects — `FAILED: 71319 checked, 1 failed, 0 skipped, 73815 constants, 32.7s, 8 jobs`
- tenet-hs: rejects — `def kmLeak: FAILED: 71319 checked, 1 failed, 113.5s`

### lean-0008

proof of `False`: `is_prop` did not require a sort (lean4#14807)

- tenet-jvm: rejects — `REJECTED DEF PR14806Subst.observe: type expected: (PR14806Subst.Owner PR14806Subst.witness) has type (Eq.rec.{[2, 1]} Bool PR14806Subst.a (f`
- Tenet: rejects — `FAILED: 163421 checked, 1 failed, 0 skipped, 171030 constants, 77.1s, 8 jobs`
- tenet-hs: rejects — `def PR14806Subst.observe: FAILED: 163421 checked, 1 failed, 181.3s`

### lean-0012

`mutB : Sort u → Sort u` with `u` undeclared (lean4#14608)

- tenet-jvm: rejects — `REJECTED DEF mutB: undeclared universe parameter u`
- Tenet: rejects — `FAILED: 71314 checked, 1 failed, 0 skipped, 73805 constants, 42.9s, 8 jobs`
- tenet-hs: rejects — `def mutB: FAILED: 71314 checked, 1 failed, 107.4s`

### lean-0014

completeness: a valid inductive predicate in `Sort (imax 1 0)` the 4.32.1 kernel rejected (lean4#14615); built on a fixed Lean

- tenet-jvm: accepts — `axioms declared: propext, Quot.sound, Classical.choice, Lean.trustCompiler, Lean.ofReduceNat, sorryAx, Lean.ofReduceBool`
- Tenet: accepts — `OK: 72082 checked, 0 failed, 0 skipped, 74598 constants, 22.4s, 8 jobs`
- tenet-hs: accepts — `OK: 72082 checked, 0 failed, 74598 constants, 109.3s`
