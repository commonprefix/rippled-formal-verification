import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Protocol.Common.FixedWidth

/-! # Walking an operation's do-block

`walk_ok` splits every hypothesis `h : e = .ok r` (or `e = .error x`) whose left side is a `match` or
an `if` until none is left, so each goal is one path through the code. It follows the control flow
rather than naming steps, so proofs survive a step being added or reordered. -/

namespace XRPL.Model.SingleAssetVault

open Lean Meta Elab Tactic

/-- An `if` equal to a value took one of its branches. -/
lemma ite_eq_cases {α : Sort _} {c : Prop} [Decidable c] {a b x : α}
    (h : (if c then a else b) = x) : (c ∧ a = x) ∨ (¬c ∧ b = x) :=
  ite_eq_iff.mp h

/-- The `_eq_ok` lemma of a checked fixed-width operation `X.opChecked`, when `e` is a call of one. -/
def checkedEqOk? (e : Expr) : Option Name :=
  match e.getAppFn.constName? with
  | some n@(.str _ s) => if s.endsWith "Checked" then some (n.appendAfter "_eq_ok") else none
  | _ => none

/-- One step of `walk_ok` on the main goal. It fails when no hypothesis can be split. -/
elab "walk_step" : tactic => do
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
        else if let (some lem, true) := (checkedEqOk? lhs, rhsOk) then
          -- a checked operation that succeeded gives the raw result
          let h2 := mkIdent (← mkFreshUserName `hw)
          evalTactic (← `(tactic|
            (obtain ⟨-, $h2:ident⟩ := ($(mkIdent lem)).mp $hId:ident; clear $hId:ident; try subst $h2:ident)))
        else if lhs.isAppOfArity ``ite 5 then
          -- take the branch with a lemma: `split` simps the whole term, too slow on a large block
          -- a branch whose condition is a false literal (`false = true`) is closed on the spot
          let h2 := mkIdent (← mkFreshUserName `hw)
          let hc := mkIdent (← mkFreshUserName `hc)
          evalTactic (← `(tactic|
            ((obtain ⟨$hc:ident, $h2:ident⟩ | ⟨$hc:ident, $h2:ident⟩ := ite_eq_cases $hId:ident) <;>
              clear $hId:ident <;> try exact absurd $hc:ident (by decide))))
        else if lhs.isAppOf ``MonadExcept.throw || lhs.isAppOf ``throwThe then
          -- Lean leaves a handler's `throw e` unreduced, so expose the `Except.error`
          evalTactic (← `(tactic| simp only [throw, throwThe, MonadExceptOf.throw] at $hId:ident))
        else
          evalTactic (← `(tactic| split at $hId:ident))
        return
      catch _ =>
        s.restore
    throwError "walk_step: nothing to split"

/-- Split every `… = .ok _` hypothesis into the paths of the code. -/
macro "walk_ok" : tactic => `(tactic| repeat' walk_step)

open Lean.Parser.Tactic in
/-- Turn the `TerExcept` and `Except` monad plumbing of a hypothesis (or the goal) into plain
`match` and `if`, ready for `walk_ok`. -/
macro "unfold_ter" loc:(location)? : tactic =>
  `(tactic| simp (config := { maxSteps := 2000000 }) only [ExceptT.run, ExceptT.bind, ExceptT.mk,
      ExceptT.lift, ExceptT.pure, ExceptT.bindCont, ExceptT.tryCatch, bind, pure, Except.bind,
      Except.pure, Except.map, Except.tryCatch, Functor.map, throw, throwThe, MonadExceptOf.throw,
      tryCatch, tryCatchThe, MonadExceptOf.tryCatch, liftM, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
      Bool.and_true, Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
      ↓reduceIte] $[$loc]?)

/-- Rewrite the goal with the record behind the exit's `to_lawful` re-check. -/
macro "rw_lawful" : tactic =>
  `(tactic| rw [(RawVault.to_lawful_ok ‹RawVault.to_lawful _ = Except.ok _›).1])

end XRPL.Model.SingleAssetVault
