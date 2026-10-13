/-
On v4.24.0 the second `Kernel.check` fails with "type expected", because the first
returned a type with a loose free variable. On v4.25.0 and later all three checks succeed.
From the issue, with `trivial` added to close the goal.
-/

import Lean
open Lean

theorem letDeps (p : ∀ a, a) :
    (let y := Prop; let x : y := True; p x) = p True := by
  run_tac
    let env ← Lean.getEnv
    let lctx ← getLCtx
    let (_, lhs, _) := (← Elab.Tactic.getMainTarget).eq?.get!
    logInfo lhs -- let y := Prop; let x : y := True; p x
    let ty ← ofExceptKernelException <| Lean.Kernel.check env lctx lhs
    logInfo ty -- let x : _kernel_fresh.0 := True; x
    let sort ← ofExceptKernelException <| Lean.Kernel.check env lctx ty
    logInfo sort -- (kernel) type expected: x
  trivial
