import XRPL.Properties.Vault.VaultValid

/-! # Walking an operation's do-block

`walk_ok` splits every hypothesis `h : e = .ok r` whose left side is a `match` or
an `if` (what an unfolded `Except` do-block reduces to) until none is left. Each
resulting goal is one path through the code: a `.error _ = .ok _` hypothesis closes
its goal, and `.ok a = .ok b` is injected and substituted when one side is a
variable. The path conditions stay in context as hypotheses (`heq✝`, `h✝`).

The walk follows the model's control flow rather than naming its steps, so proofs
built on it survive a step being added or reordered. Calls to other functions are
not unfolded: their results stay as `f … = .ok x` hypotheses. -/

namespace XRPL.Model.SingleAssetVault

open Lean Meta Elab Tactic

/-- One step of `walk_ok` on the main goal; fails when no hypothesis can be split. -/
elab "walk_step" : tactic => do
  let g ← getMainGoal
  g.withContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless rhs.isAppOfArity ``Except.ok 3 do continue
      if lhs.isAppOfArity ``Except.error 3 then
        let gs ← g.cases ldecl.fvarId
        replaceMainGoal (gs.toList.map (·.mvarId))
        return
      let s ← saveState
      let name ← mkFreshUserName `hw
      let g' ← g.rename ldecl.fvarId name
      setGoals [g']
      let hId := mkIdent name
      try
        if lhs.isAppOfArity ``Except.ok 3 then
          let h2 := mkIdent (← mkFreshUserName `hw)
          evalTactic (← `(tactic| (injection $hId:ident with $h2:ident; try cases $h2:ident)))
        else if lhs.isAppOf ``MonadExcept.throw || lhs.isAppOf ``throwThe then
          -- newer Lean leaves a handler's `throw e` unreduced; expose the `Except.error`
          evalTactic (← `(tactic| simp only [throw, throwThe, MonadExceptOf.throw] at $hId:ident))
        else
          evalTactic (← `(tactic| split at $hId:ident))
        return
      catch _ =>
        s.restore
    throwError "walk_step: nothing to split"

/-- Split every `… = .ok _` hypothesis into the paths of the code. -/
macro "walk_ok" : tactic => `(tactic| repeat' walk_step)

/-- Rewrite the goal with the record behind the exit's `to_lawful` re-check. -/
macro "rw_lawful" : tactic =>
  `(tactic| rw [(RawVault.to_lawful_ok ‹RawVault.to_lawful _ = Except.ok _›).1])

end XRPL.Model.SingleAssetVault
