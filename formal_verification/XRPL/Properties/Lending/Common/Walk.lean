import XRPL.Properties.Vault.Proofs.Walk

/-! # Walking a lending operation's do-block

`walk_ok'` is `walk_ok`, but it closes a branch whose condition is a literal `false = true` with `simp only`, never
`decide`, which on a `TER` code makes the kernel unfold the whole `TER` match and recurse too deep. -/

namespace XRPL.Model.Lending

open Lean Meta Elab Tactic

/-- One step of `walk_ok'` on the main goal. It fails when no hypothesis can be split. -/
elab "walk_step'" : tactic => do
  let g ← getMainGoal
  g.withContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, lhs, rhs) := ty.eq? | continue
      let rhsOk := rhs.isAppOfArity ``Except.ok 3
      unless rhsOk || rhs.isAppOfArity ``Except.error 3 do continue
      -- two constructors: a mismatch closes the path, `.error a = .error b` identifies them
      if lhs.isAppOfArity ``Except.error 3 || (lhs.isAppOfArity ``Except.ok 3 && !rhsOk) then
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
        else if let (some lem, true) := (XRPL.Model.SingleAssetVault.checkedEqOk? lhs, rhsOk) then
          -- a checked operation that succeeded gives the raw result
          let h2 := mkIdent (← mkFreshUserName `hw)
          evalTactic (← `(tactic|
            (obtain ⟨-, $h2:ident⟩ := ($(mkIdent lem)).mp $hId:ident; clear $hId:ident; try subst $h2:ident)))
        else if lhs.isAppOfArity ``ite 5 then
          let h2 := mkIdent (← mkFreshUserName `hw)
          let hc := mkIdent (← mkFreshUserName `hc)
          evalTactic (← `(tactic|
            ((obtain ⟨$hc:ident, $h2:ident⟩ | ⟨$hc:ident, $h2:ident⟩ :=
                XRPL.Model.SingleAssetVault.ite_eq_cases $hId:ident) <;>
              clear $hId:ident <;>
              try (simp only [Bool.false_eq_true, not_true_eq_false] at $hc:ident; done))))
        else if lhs.isAppOf ``MonadExcept.throw || lhs.isAppOf ``throwThe then
          evalTactic (← `(tactic| simp only [throw, throwThe, MonadExceptOf.throw] at $hId:ident))
        else
          evalTactic (← `(tactic| split at $hId:ident))
        return
      catch _ =>
        s.restore
    throwError "walk_step': nothing to split"

/-- Split every `… = .ok _` hypothesis into the paths of the code. -/
macro "walk_ok'" : tactic => `(tactic| repeat' walk_step')

end XRPL.Model.Lending
