import XRPL.Properties.Lending.LoanBroker.Common.ClawbackExits

/-! # `LoanBrokerCoverClawback` exits

The exits of the clawback's rounding, its check and the clawback. The rounding caps the request at the cover above
minCover and clamps it toward zero onto the grid of CoverAvailable minus the amount. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- The exits of `roundedCoverClawback`, in the order it runs its checks. Each line assumes the checks before it
passed. -/
theorem LoanBroker.roundedCoverClawback_exits (pool : α) (amount : Option STAmount) :
    (∀ minimumCover maxClaw : Number,
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
        .ok minimumCover →
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw → maxClaw.signum ≤ 0 →
      (lb.roundedCoverClawback pool amount).run = .ok (.error .tecINSUFFICIENT_FUNDS)) ∧
    (∀ (minimumCover maxClaw claw : Number) (claw' c : STAmount),
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
        .ok minimumCover →
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw → 0 < maxClaw.signum →
      LoanBroker.clawRequest maxClaw amount = .ok claw → STAmount.ofNumber lb.numericType claw .to_nearest = .ok claw' →
      clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) = .ok c →
      c.isZero = true → (lb.roundedCoverClawback pool amount).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ (minimumCover maxClaw claw : Number) (claw' c : STAmount),
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
        .ok minimumCover →
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw → 0 < maxClaw.signum →
      LoanBroker.clawRequest maxClaw amount = .ok claw → STAmount.ofNumber lb.numericType claw .to_nearest = .ok claw' →
      clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) = .ok c →
      c.isZero = false → (lb.roundedCoverClawback pool amount).run = .ok (.ok c)) :=
  ⟨LoanBroker.roundedCoverClawback_no_excess_proof lb pool amount,
    LoanBroker.roundedCoverClawback_precision_loss_proof lb pool amount,
    LoanBroker.roundedCoverClawback_rounded_proof lb pool amount⟩

/-- A zero amount is the same clawback as no amount: both take all cover above the
minimum. -/
theorem LoanBroker.roundedCoverClawback_zero_eq_none (pool : α) (a : STAmount)
    (hzero : a.isZero = true) :
    lb.roundedCoverClawback pool (some a) = lb.roundedCoverClawback pool none :=
  LoanBroker.roundedCoverClawback_zero_eq_none_proof lb pool a hzero

/-- The only roundedAmount rejections are tecINSUFFICIENT_FUNDS and tecPRECISION_LOSS. -/
theorem LoanBroker.roundedCoverClawback_rejected_code (pool : α)
    (amount : Option STAmount) (ter : TER)
    (hok : (lb.roundedCoverClawback pool amount).run = .ok (.error ter)) :
    ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.roundedCoverClawback_error_codes lb pool amount ter hok

/-- The exits of `canCoverClawback`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.canCoverClawback_exits (pool : α) (amount : Option STAmount) :
    (lb.numericType = .native → lb.canCoverClawback pool amount = .ok .tecNO_PERMISSION) ∧
    (∀ minimumCover maxClaw : Number, lb.numericType ≠ .native →
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
        .ok minimumCover →
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw → maxClaw.signum ≤ 0 →
      lb.canCoverClawback pool amount = .ok .tecINSUFFICIENT_FUNDS) ∧
    (∀ (minimumCover maxClaw claw : Number) (claw' c : STAmount), lb.numericType ≠ .native →
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
        .ok minimumCover →
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw → 0 < maxClaw.signum →
      LoanBroker.clawRequest maxClaw amount = .ok claw → STAmount.ofNumber lb.numericType claw .to_nearest = .ok claw' →
      clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) = .ok c →
      c.isZero = true → lb.canCoverClawback pool amount = .ok .tecPRECISION_LOSS) ∧
    (∀ c : STAmount, lb.numericType ≠ .native → (lb.roundedCoverClawback pool amount).run = .ok (.ok c) →
      lb.canCoverClawback pool amount = .ok .tesSUCCESS) :=
  ⟨LoanBroker.canCoverClawback_no_permission_proof lb pool amount,
    fun minimumCover maxClaw hxrp hmin hsub hle => LoanBroker.canCoverClawback_rejected_proof lb pool amount hxrp _
      (LoanBroker.roundedCoverClawback_no_excess_proof lb pool amount minimumCover maxClaw hmin hsub hle),
    fun minimumCover maxClaw claw claw' c hxrp hmin hsub hpos hreq hof hcl hzero =>
      LoanBroker.canCoverClawback_rejected_proof lb pool amount hxrp _
        (LoanBroker.roundedCoverClawback_precision_loss_proof lb pool amount minimumCover maxClaw claw claw' c hmin
          hsub hpos hreq hof hcl hzero),
    fun c hxrp hrounded => LoanBroker.canCoverClawback_success_proof lb pool amount hxrp c hrounded⟩

/-- A zero amount passes or fails the checks exactly as no amount does. -/
theorem LoanBroker.canCoverClawback_zero_eq_none (pool : α) (a : STAmount)
    (hzero : a.isZero = true) :
    lb.canCoverClawback pool (some a) = lb.canCoverClawback pool none :=
  LoanBroker.canCoverClawback_zero_eq_none_proof lb pool a hzero

/-- Error codes: success, tecNO_PERMISSION, tecINSUFFICIENT_FUNDS or tecPRECISION_LOSS. -/
theorem LoanBroker.canCoverClawback_error_codes (pool : α)
    (amount : Option STAmount) (ter : TER) (hok : lb.canCoverClawback pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecNO_PERMISSION ∨ ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.canCoverClawback_error_codes_proof lb pool amount ter hok

/-- The exits of `coverClawback`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.coverClawback_exits (pool : α) (amount : Option STAmount) :
    (∀ minimumCover maxClaw : Number,
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
        .ok minimumCover →
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw → maxClaw.signum ≤ 0 →
      (lb.coverClawback pool amount).run = .ok (.error .tecINTERNAL)) ∧
    (∀ (minimumCover maxClaw claw : Number) (claw' c : STAmount),
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
        .ok minimumCover →
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw → 0 < maxClaw.signum →
      LoanBroker.clawRequest maxClaw amount = .ok claw → STAmount.ofNumber lb.numericType claw .to_nearest = .ok claw' →
      clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) = .ok c →
      c.isZero = true → (lb.coverClawback pool amount).run = .ok (.error .tecINTERNAL)) ∧
    (∀ (c : STAmount) (cN c' : Number), (lb.roundedCoverClawback pool amount).run = .ok (.ok c) →
      c.toNumber .to_nearest = .ok cN → lb.coverAvailable.operator_sub cN .to_nearest = .ok c' →
      Number.zero.operator_le c' = false → (lb.coverClawback pool amount).run = .error .notLawful) ∧
    -- `c'` - the new CoverAvailable, the difference rounded to nearest
    (∀ (c : STAmount) (cN c' : Number), (lb.roundedCoverClawback pool amount).run = .ok (.ok c) →
      c.toNumber .to_nearest = .ok cN → lb.coverAvailable.operator_lt cN = false →
      lb.coverAvailable.operator_sub cN .to_nearest = .ok c' →
      ∃ lb' : LoanBroker, (lb.coverClawback pool amount).run = .ok (.ok ⟨c, lb'⟩) ∧
        lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' }) :=
  ⟨fun minimumCover maxClaw hmin hsub hle => LoanBroker.coverClawback_rejected_proof lb pool amount _
      (LoanBroker.roundedCoverClawback_no_excess_proof lb pool amount minimumCover maxClaw hmin hsub hle),
    fun minimumCover maxClaw claw claw' c hmin hsub hpos hreq hof hcl hzero =>
      LoanBroker.coverClawback_rejected_proof lb pool amount _
        (LoanBroker.roundedCoverClawback_precision_loss_proof lb pool amount minimumCover maxClaw claw claw' c hmin
          hsub hpos hreq hof hcl hzero),
    LoanBroker.coverClawback_negative_cover_proof lb pool amount, LoanBroker.coverClawback_success_proof lb pool amount⟩

/-- A zero amount claws exactly what no amount claws. -/
theorem LoanBroker.coverClawback_zero_eq_none (pool : α) (a : STAmount)
    (hzero : a.isZero = true) :
    lb.coverClawback pool (some a) = lb.coverClawback pool none :=
  LoanBroker.coverClawback_zero_eq_none_proof lb pool a hzero

/-- The only clawback rejection is tecINTERNAL. -/
theorem LoanBroker.coverClawback_error_codes (pool : α)
    (amount : Option STAmount) (ter : TER)
    (hok : (lb.coverClawback pool amount).run = .ok (.error ter)) : ter = .tecINTERNAL :=
  LoanBroker.coverClawback_error_codes_proof lb pool amount ter hok

end XRPL.Model.Lending
