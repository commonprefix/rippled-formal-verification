import XRPL.Properties.Protocol.Common.Wrap
import XRPL.Properties.Vault.Proofs.Support.Errors

/-! # No vault helper wraps around

The pricing, dust and cash-update steps of the vault transactions only pass on Protocol errors, and the
`to_lawful` re-check fails only as notLawful. The balances of a lawful vault are normalized, and an amount the
vault stores has a magnitude below `2^63` when the largest value of the vault's type does. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `walk_ok` that proves the facts of `wrap_facts` after each split, so the paths share them. -/
macro "walk_facts" : tactic => `(tactic| (wrap_facts; repeat' (walk_step; all_goals wrap_facts)))

open Lean Meta in
/-- A vault or lending function, or a Protocol rounding helper, whose code `wrap_unfold` and `wrap_inline` may go
through. -/
def isWrapModelFunction (f : Name) : MetaM Bool := do
  let env ← getEnv
  let n := (privateToUserName? f).getD f
  let rounding := (env.getModuleIdxFor? f).any (env.header.moduleNames[·]! == `XRPL.Model.Protocol.Rounding)
  return ((`XRPL.Model.Lending).isPrefixOf n || (`XRPL.Model.SingleAssetVault).isPrefixOf n || rounding) &&
    !(← isMatcher f)

open Lean Elab Tactic Meta in
/-- Unfold the model function `f` in the hypothesis `fvarId`, walk its paths and run `finish` on each. The
hypothesis is replaced, so a later step never unfolds it again, and a recursive function is refused. -/
def wrapInline (fvarId : FVarId) (f : Name) (finish : TSyntax `tactic) : TacticM Unit := do
  let g ← getMainGoal
  let rest := (← getGoals).erase g
  let hn ← mkFreshUserName `hu
  let g ← g.withContext do
    let (h, g) ← (← g.assert hn (← instantiateMVars (← fvarId.getType)) (mkFVar fvarId)).intro1P
    let g ← g.tryClear fvarId
    unfoldLocalDecl g h f
  g.withContext do
    let some d := (← getLCtx).findFromUserName? hn | throwError "wrapInline: the copy is gone"
    if (← instantiateMVars d.type).containsConst (· == f) then throwError "wrapInline: {f} is recursive"
  setGoals [g]
  withTransparency .default do
    evalTactic (← `(tactic| ((try unfold_ter at $(mkIdent hn):ident); walk_ok)))
  for path in ← getGoals do
    setGoals [path]
    evalTactic finish
    unless (← getGoals).isEmpty do throwError "wrapInline: a path is left"
  setGoals rest

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| wrap_unfold) => do
    let g ← getMainGoal
    g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      for ldecl in (← getLCtx) do
        if ldecl.isImplementationDetail then continue
        let some (_, lhs, rhs) := (← instantiateMVars ldecl.type).eq? | continue
        unless rhs.isAppOfArity ``Except.ok 3 && rhs.appArg!.hasAnyFVar tgt.containsFVar do continue
        let some f := (if lhs.isAppOf ``ExceptT.run then lhs.appArg! else lhs).getAppFn.constName? | continue
        unless ← isWrapModelFunction f do continue
        let s ← saveState
        try
          wrapInline ldecl.fvarId f (← `(tactic| ((try dsimp only); wrap_side)))
          return
        catch _ =>
          s.restore
      throwError "wrap_unfold: no model function returned the value"

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| wrap_inline) => do
    let g ← getMainGoal
    g.withContext do
      for ldecl in (← getLCtx) do
        if ldecl.isImplementationDetail then continue
        let some (_, lhs, rhs) := (← instantiateMVars ldecl.type).eq? | continue
        unless rhs.isAppOfArity ``Except.error 3 do continue
        let some f := (if lhs.isAppOf ``ExceptT.run then lhs.appArg! else lhs).getAppFn.constName? | continue
        unless ← isWrapModelFunction f do continue
        let s ← saveState
        try
          wrapInline ldecl.fvarId f (← `(tactic| wrap_leaf))
          return
        catch _ =>
          s.restore
      throwError "wrap_inline: no failed step to close"

lemma RawVault.assetsTotal_ne_wrap (rv : RawVault) (ha : rv.assetsAvailable.isNormalized)
    (hd : rv.assetsDeployed.isNormalized) : rv.assetsTotal ≠ .error .wrap :=
  Number.operator_add_ne_wrap _ _ _ ha hd

lemma RawVault.assetsTotal_isNormalized {rv : RawVault} {n : Number} (ha : rv.assetsAvailable.isNormalized)
    (hd : rv.assetsDeployed.isNormalized) (h : rv.assetsTotal = .ok n) : n.isNormalized :=
  Number.operator_add_isNormalized_any _ _ _ _ ha hd h

lemma Vault.assetsTotalForWithdrawal_ne_wrap (v : Vault) (waive : Bool) :
    v.assetsTotalForWithdrawal waive ≠ .error .wrap := by
  unfold Vault.assetsTotalForWithdrawal
  simp only [bind, Except.bind]
  split_ne_wrap [RawVault.assetsTotal_ne_wrap, Number.operator_sub_ne_wrap]

lemma Vault.assetsTotalForWithdrawal_isNormalized {v : Vault} {waive : Bool} {n : Number}
    (h : v.assetsTotalForWithdrawal waive = .ok n) : n.isNormalized := by
  unfold Vault.assetsTotalForWithdrawal at h
  obtain ⟨t, ht, h⟩ := bind_ok_peel _ _ _ h
  refine Number.operator_sub_isNormalized_any _ _ _ _ (RawVault.assetsTotal_isNormalized ?_ ?_ ht) ?_ h
  all_goals wrap_side

lemma Vault.sharesToAssetsWithdraw_ne_wrap (v : Vault) (shares : STAmount) (waive : Bool)
    (hs : shares.mValue.toNat < 2 ^ 63) : v.sharesToAssetsWithdraw shares waive ≠ .error .wrap := by
  unfold Vault.sharesToAssetsWithdraw
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [Vault.assetsTotalForWithdrawal_ne_wrap, STAmount.toNumber_ne_wrap,
    Number.operator_mul_ne_wrap, Number.operator_div_ne_wrap, STAmount.ofNumber_ne_wrap]

lemma Vault.sharesToAssetsWithdraw_mValue_lt {v : Vault} {shares r : STAmount} {waive : Bool}
    (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (h : v.sharesToAssetsWithdraw shares waive = .ok r) :
    r.mValue.toNat < 2 ^ 63 := by
  unfold Vault.sharesToAssetsWithdraw at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals wrap_side

lemma assetsToSharesWithdraw_ne_wrap (v : Vault) (assets : STAmount) (truncateShares waive : Bool)
    (ha : assets.mValue.toNat < 2 ^ 63) : assetsToSharesWithdraw v assets truncateShares waive ≠ .error .wrap := by
  unfold assetsToSharesWithdraw
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [Vault.assetsTotalForWithdrawal_ne_wrap, STAmount.toNumber_ne_wrap,
    Number.operator_mul_ne_wrap, Number.operator_div_ne_wrap, Number.truncate_ne_wrap,
    STAmount.ofNumber_ne_wrap]

lemma assetsToSharesWithdraw_mValue_lt {v : Vault} {assets r : STAmount} {truncateShares waive : Bool}
    (h : assetsToSharesWithdraw v assets truncateShares waive = .ok r) : r.mValue.toNat < 2 ^ 63 := by
  unfold assetsToSharesWithdraw at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals wrap_side

lemma computeWithdraw_ne_wrap (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (ha : amount.amount.mValue.toNat < 2 ^ 63) : (computeWithdraw v amount waive).run ≠ .error .wrap := by
  intro h
  cases amount <;> simp only [WithdrawAmount.amount] at ha
  all_goals simp only [computeWithdraw] at h
  all_goals unfold_ter at h
  all_goals walk_ok
  all_goals close_wrap [assetsToSharesWithdraw_ne_wrap, Vault.sharesToAssetsWithdraw_ne_wrap]

lemma computeWithdraw_mValue_lt {v : Vault} {amount : WithdrawAmount} {waive : Bool} {r : VaultAmounts}
    (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (ha : amount.amount.mValue.toNat < 2 ^ 63)
    (h : (computeWithdraw v amount waive).run = .ok (.ok r)) :
    r.assets.mValue.toNat < 2 ^ 63 ∧ r.shares.mValue.toNat < 2 ^ 63 := by
  cases amount <;> simp only [WithdrawAmount.amount] at ha
  all_goals simp only [computeWithdraw] at h
  all_goals unfold_ter at h
  all_goals walk_ok
  all_goals exact ⟨by wrap_side, by wrap_side⟩

lemma Vault.checkDebitNotDust_ne_wrap (v : Vault) (amount : Number) (h : amount.isNormalized) :
    v.checkDebitNotDust amount ≠ .error .wrap := by
  intro h
  simp only [Vault.checkDebitNotDust] at h
  unfold_ter at h
  walk_ok
  all_goals close_wrap [Number.operator_sub_ne_wrap, STAmount.ofNumber_ne_wrap]

lemma Vault.adjustBalances_ne_wrap (v : Vault) (change : Lending.PoolBalanceChange)
    (hcash : change.cash.isNormalized) (hdep : change.deployed.isNormalized) (hloss : change.loss.isNormalized)
    (hres : change.reserved.isNormalized) (hyield : change.yield.isNormalized) :
    (v.adjustBalances change).run ≠ .error .wrap := by
  intro h
  simp only [Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  all_goals close_wrap [Number.operator_add_ne_wrap, STAmount.roundToNumericType_ne_wrap]

lemma Vault.adjustAssetsAndShares_ne_wrap (v : Vault) (assets shares : STAmount)
    (ha : assets.mValue.toNat < 2 ^ 63) (hs : shares.mValue.toNat < 2 ^ 63) :
    (v.adjustAssetsAndShares assets shares).run ≠ .error .wrap := by
  intro h
  simp only [Vault.adjustAssetsAndShares] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | close_wrap [STAmount.toNumber_ne_wrap, Number.operator_add_ne_wrap]
    | (refine Vault.adjustBalances_ne_wrap _ _ ?_ ?_ ?_ ?_ ?_ ‹_› <;> wrap_side)

/-- The `to_lawful` re-check fails only as notLawful. -/
lemma RawVault.to_lawful_ne_wrap (rv : RawVault) : rv.to_lawful ≠ .error .wrap := by
  unfold RawVault.to_lawful
  split <;> simp

lemma assetsToSharesClawback_ne_wrap (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (ha : assets.mValue.toNat < 2 ^ 63) : assetsToSharesClawback v assets holderShares waive ≠ .error .wrap := by
  unfold assetsToSharesClawback
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [STAmount.ofNumber_ne_wrap, assetsToSharesWithdraw_ne_wrap]

lemma assetsToSharesClawback_mValue_lt {v : Vault} {assets holderShares r : STAmount} {waive : Bool}
    (hh : holderShares.mValue.toNat < 2 ^ 63) (h : assetsToSharesClawback v assets holderShares waive = .ok r) :
    r.mValue.toNat < 2 ^ 63 := by
  unfold assetsToSharesClawback at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals wrap_side

macro_rules
  | `(tactic| wrap_rule) => `(tactic| first
    | (refine (XRPL.Model.SingleAssetVault.computeWithdraw_mValue_lt ?_ ?_ (by wrap_hyp)).1 <;> wrap_side)
    | (refine (XRPL.Model.SingleAssetVault.computeWithdraw_mValue_lt ?_ ?_ (by wrap_hyp)).2 <;> wrap_side))

lemma computeClawback_ne_wrap (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (ha : assets.mValue.toNat < 2 ^ 63)
    (hh : holderShares.mValue.toNat < 2 ^ 63) :
    (computeClawback v assets holderShares waive).run ≠ .error .wrap := by
  intro h
  simp only [computeClawback] at h
  unfold_ter at h
  walk_ok
  all_goals close_wrap [assetsToSharesClawback_ne_wrap, assetsToSharesWithdraw_ne_wrap,
    Vault.sharesToAssetsWithdraw_ne_wrap, STAmount.toNumber_ne_wrap, STAmount.ofNumber_ne_wrap,
    clampToSumExponent_ne_wrap, STAmount.isFractionalNonPositive_ne_wrap]

lemma computeClawback_mValue_lt {v : Vault} {assets holderShares : STAmount} {waive : Bool} {r : VaultAmounts}
    (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (hh : holderShares.mValue.toNat < 2 ^ 63)
    (h : (computeClawback v assets holderShares waive).run = .ok (.ok r)) :
    r.assets.mValue.toNat < 2 ^ 63 ∧ r.shares.mValue.toNat < 2 ^ 63 := by
  simp only [computeClawback] at h
  unfold_ter at h
  walk_ok
  all_goals exact ⟨by wrap_side, by wrap_side⟩

macro_rules
  | `(tactic| wrap_rule) => `(tactic| first
    | (refine (XRPL.Model.SingleAssetVault.computeClawback_mValue_lt ?_ ?_ (by wrap_hyp)).1 <;> wrap_side)
    | (refine (XRPL.Model.SingleAssetVault.computeClawback_mValue_lt ?_ ?_ (by wrap_hyp)).2 <;> wrap_side))

end XRPL.Model.SingleAssetVault
