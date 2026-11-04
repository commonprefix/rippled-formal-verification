import XRPL.Properties.Lending.LoanBroker.Common.CoverDebit

/-! # Proof bodies for the `LoanBrokerCoverClawback` exits

Proofs for the exits of the clawback's rounding, its check and the clawback. The rounding caps the request at the
cover above the minimum, converts it to the asset and clamps it onto the grid of `coverAvailable` minus the amount. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

/-- What a clawback's rounding computes once the cover is above the minimum: the requested amount
converted to the asset, clamped onto the grid of the difference, and rejected when that is zero. -/
private lemma LoanBroker.roundedCoverClawback_run (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (minimumCover maxClaw claw : Number) (claw' : STAmount)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
      .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw) (hpos : 0 < maxClaw.signum)
    (hreq : LoanBroker.clawRequest maxClaw amount = .ok claw)
    (hof : STAmount.ofNumber lb.numericType claw .to_nearest = .ok claw') :
    (lb.roundedCoverClawback pool amount).run =
      match clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) with
      | .error e => .error e
      | .ok c => if c.isZero = true then .ok (.error .tecPRECISION_LOSS) else .ok (.ok c) := by
  have hp : ¬ maxClaw.signum ≤ 0 := not_le.mpr hpos
  unfold LoanBroker.roundedCoverClawback
  unfold_ter
  rw [hmin]
  simp only
  rw [hsub]
  simp only [hp, if_false]
  cases amount with
  | none =>
    simp only [LoanBroker.clawRequest, Except.pure, Except.ok.injEq] at hreq
    subst hreq
    dsimp only
    rw [hof]
    dsimp only
    cases clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) <;> rfl
  | some a =>
    unfold LoanBroker.clawRequest at hreq
    by_cases ha : a.isZero = true
    · simp only [ha, if_true, Except.pure, Except.ok.injEq] at hreq
      subst hreq
      dsimp only
      rw [if_pos ha, hof]
      dsimp only
      cases clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) <;> rfl
    · simp only [ha, Bool.false_eq_true, if_false] at hreq
      dsimp only
      rw [if_neg ha]
      cases hn : a.toNumber .to_nearest with
      | error e => rw [hn] at hreq; cases hreq
      | ok m =>
        rw [hn] at hreq
        simp only [bind, Except.bind, Except.pure, Except.ok.injEq] at hreq
        subst hreq
        simp only
        rw [hof]
        dsimp only
        cases clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) <;> rfl

/-- Proof body of the no-excess exit of `LoanBroker.roundedCoverClawback_exits`. -/
lemma LoanBroker.roundedCoverClawback_no_excess_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (minimumCover maxClaw : Number)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
      .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw) (hle : maxClaw.signum ≤ 0) :
    (lb.roundedCoverClawback pool amount).run = .ok (.error .tecINSUFFICIENT_FUNDS) := by
  unfold LoanBroker.roundedCoverClawback
  unfold_ter
  rw [hmin]
  simp only
  rw [hsub]
  simp only [hle, if_true]

/-- Proof body of the precision-loss exit of `LoanBroker.roundedCoverClawback_exits`. -/
lemma LoanBroker.roundedCoverClawback_precision_loss_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (minimumCover maxClaw claw : Number) (claw' c : STAmount)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
      .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw) (hpos : 0 < maxClaw.signum)
    (hreq : LoanBroker.clawRequest maxClaw amount = .ok claw)
    (hof : STAmount.ofNumber lb.numericType claw .to_nearest = .ok claw')
    (hcl : clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) = .ok c)
    (hz : c.isZero = true) :
    (lb.roundedCoverClawback pool amount).run = .ok (.error .tecPRECISION_LOSS) := by
  rw [LoanBroker.roundedCoverClawback_run lb pool amount minimumCover maxClaw claw claw' hmin hsub hpos hreq hof,
    hcl]
  simp [hz]

/-- Proof body of the rounded exit of `LoanBroker.roundedCoverClawback_exits`. -/
lemma LoanBroker.roundedCoverClawback_rounded_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (minimumCover maxClaw claw : Number) (claw' c : STAmount)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
      .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw) (hpos : 0 < maxClaw.signum)
    (hreq : LoanBroker.clawRequest maxClaw amount = .ok claw)
    (hof : STAmount.ofNumber lb.numericType claw .to_nearest = .ok claw')
    (hcl : clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) = .ok c)
    (hnz : c.isZero = false) :
    (lb.roundedCoverClawback pool amount).run = .ok (.ok c) := by
  rw [LoanBroker.roundedCoverClawback_run lb pool amount minimumCover maxClaw claw claw' hmin hsub hpos hreq hof,
    hcl]
  simp [hnz]

/-- Proof body of `roundedCoverClawback_zero_eq_none`. -/
lemma LoanBroker.roundedCoverClawback_zero_eq_none_proof (lb : LoanBroker) (pool : α) (a : STAmount)
    (hz : a.isZero = true) :
    lb.roundedCoverClawback pool (some a) = lb.roundedCoverClawback pool none := by
  simp [LoanBroker.roundedCoverClawback, hz]

/-- Proof body of the no-permission exit of `LoanBroker.canCoverClawback_exits`. -/
lemma LoanBroker.canCoverClawback_no_permission_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (hxrp : lb.numericType = .native) :
    lb.canCoverClawback pool amount = .ok .tecNO_PERMISSION := by
  unfold LoanBroker.canCoverClawback
  simp [hxrp]

/-- When the rounding rejects a clawback of an asset that is not XRP, the check returns the same code. -/
lemma LoanBroker.canCoverClawback_rejected_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (hxrp : lb.numericType ≠ .native) (ter : TER)
    (hrej : (lb.roundedCoverClawback pool amount).run = .ok (.error ter)) :
    lb.canCoverClawback pool amount = .ok ter := by
  unfold LoanBroker.canCoverClawback
  simp [hxrp, hrej]

/-- Proof body of the success exit of `LoanBroker.canCoverClawback_exits`. -/
lemma LoanBroker.canCoverClawback_success_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (hxrp : lb.numericType ≠ .native) (c : STAmount)
    (hrounded : (lb.roundedCoverClawback pool amount).run = .ok (.ok c)) :
    lb.canCoverClawback pool amount = .ok .tesSUCCESS :=
  (LoanBroker.canCoverClawback_ok_iff lb pool amount).mpr ⟨hxrp, c, hrounded⟩

/-- Proof body of `canCoverClawback_error_codes`. -/
lemma LoanBroker.canCoverClawback_error_codes_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (ter : TER) (hok : lb.canCoverClawback pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecNO_PERMISSION ∨ ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS := by
  by_cases hxrp : lb.numericType = .native
  · rw [LoanBroker.canCoverClawback_no_permission_proof lb pool amount hxrp] at hok
    cases hok
    exact Or.inr (Or.inl rfl)
  cases h : (lb.roundedCoverClawback pool amount).run with
  | error e => unfold LoanBroker.canCoverClawback at hok; simp [hxrp, h] at hok
  | ok x =>
    cases x with
    | error t =>
      rw [LoanBroker.canCoverClawback_rejected_proof lb pool amount hxrp t h] at hok
      cases hok
      exact Or.inr (Or.inr (LoanBroker.roundedCoverClawback_error_codes lb pool amount _ h))
    | ok c =>
      rw [LoanBroker.canCoverClawback_success_proof lb pool amount hxrp c h] at hok
      cases hok
      exact Or.inl rfl

/-- Proof body of `canCoverClawback_zero_eq_none`. -/
lemma LoanBroker.canCoverClawback_zero_eq_none_proof (lb : LoanBroker) (pool : α) (a : STAmount)
    (hz : a.isZero = true) :
    lb.canCoverClawback pool (some a) = lb.canCoverClawback pool none := by
  unfold LoanBroker.canCoverClawback
  rw [LoanBroker.roundedCoverClawback_zero_eq_none_proof lb pool a hz]

/-- When the rounding rejects a clawback, the clawback returns tecINTERNAL. -/
lemma LoanBroker.coverClawback_rejected_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (ter : TER) (hrej : (lb.roundedCoverClawback pool amount).run = .ok (.error ter)) :
    (lb.coverClawback pool amount).run = .ok (.error .tecINTERNAL) := by
  unfold LoanBroker.coverClawback
  unfold_ter
  rw [show lb.roundedCoverClawback pool amount = .ok (.error ter) from hrej]

/-- Proof body of the negative-cover exit of `LoanBroker.coverClawback_exits`. -/
lemma LoanBroker.coverClawback_negative_cover_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (c : STAmount) (cN c' : Number) (hrounded : (lb.roundedCoverClawback pool amount).run = .ok (.ok c))
    (hnum : c.toNumber .to_nearest = .ok cN)
    (hsub : lb.coverAvailable.operator_sub cN .to_nearest = .ok c')
    (hneg : Number.zero.operator_le c' = false) :
    (lb.coverClawback pool amount).run = .error .notLawful := by
  unfold LoanBroker.coverClawback LoanBroker.applyCoverTransaction
  unfold_ter
  rw [show lb.roundedCoverClawback pool amount = .ok (.ok c) from hrounded]
  simp [hnum, hsub, RawLoanBroker.to_lawful_negative_cover lb c' hneg]

/-- Proof body of the success exit of `LoanBroker.coverClawback_exits`. -/
lemma LoanBroker.coverClawback_success_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (c : STAmount) (cN c' : Number) (hrounded : (lb.roundedCoverClawback pool amount).run = .ok (.ok c))
    (hnum : c.toNumber .to_nearest = .ok cN)
    (hge : lb.coverAvailable.operator_lt cN = false)
    (hsub : lb.coverAvailable.operator_sub cN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, (lb.coverClawback pool amount).run = .ok (.ok ⟨c, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  obtain ⟨lb', htl, hraw⟩ :=
    LoanBroker.debit_lawful lb cN c' (STAmount.toNumber_isNormalized c _ cN hnum) hge hsub
  refine ⟨lb', ?_, hraw⟩
  unfold LoanBroker.coverClawback LoanBroker.applyCoverTransaction
  unfold_ter
  rw [show lb.roundedCoverClawback pool amount = .ok (.ok c) from hrounded]
  simp [hnum, hsub, htl]

/-- Proof body of `coverClawback_zero_eq_none`. -/
lemma LoanBroker.coverClawback_zero_eq_none_proof (lb : LoanBroker) (pool : α) (a : STAmount)
    (hz : a.isZero = true) :
    lb.coverClawback pool (some a) = lb.coverClawback pool none := by
  unfold LoanBroker.coverClawback
  rw [LoanBroker.roundedCoverClawback_zero_eq_none_proof lb pool a hz]

/-- Proof body of `coverClawback_error_codes`. -/
lemma LoanBroker.coverClawback_error_codes_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (ter : TER) (hok : (lb.coverClawback pool amount).run = .ok (.error ter)) : ter = .tecINTERNAL := by
  unfold LoanBroker.coverClawback at hok
  unfold_ter at hok
  walk_ok
  rfl

end XRPL.Model.Lending
