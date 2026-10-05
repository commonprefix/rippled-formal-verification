import XRPL.Properties.Lending.LoanBroker.Common.ClawbackExits

/-! # `LoanBrokerCoverClawback` exits

The exits of the clawback checks. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- A `coverAvailable` at most the minimum cover: `tecINSUFFICIENT_FUNDS`. -/
theorem LoanBroker.roundedCoverClawback_no_excess (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hle : maxClaw.signum ≤ 0) :
    lb.roundedCoverClawback pool amount = .ok (.rejected .tecINSUFFICIENT_FUNDS) :=
  LoanBroker.roundedCoverClawback_no_excess_proof lb pool amount e minimumCover maxClaw hexp hmin hsub hle

/-- A zero amount is the same clawback as no amount: both take all cover above the
minimum. -/
theorem LoanBroker.roundedCoverClawback_zero_eq_none (pool : α) (a : STAmount)
    (hz : a.isZero = true) :
    lb.roundedCoverClawback pool (some a) = lb.roundedCoverClawback pool none :=
  LoanBroker.roundedCoverClawback_zero_eq_none_proof lb pool a hz

/-- `tecINSUFFICIENT_FUNDS` is the only rejection `roundedCoverClawback` can
return. -/
theorem LoanBroker.roundedCoverClawback_rejected_code (pool : α)
    (amount : Option STAmount) (ter : TER)
    (hok : lb.roundedCoverClawback pool amount = .ok (.rejected ter)) :
    ter = .tecINSUFFICIENT_FUNDS :=
  LoanBroker.roundedCoverClawback_rejected_code_proof lb pool amount ter hok

/-- A `coverAvailable` at most the minimum cover: `tecINSUFFICIENT_FUNDS`. -/
theorem LoanBroker.canCoverClawback_no_excess (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hle : maxClaw.signum ≤ 0) :
    lb.canCoverClawback pool amount = .ok .tecINSUFFICIENT_FUNDS :=
  LoanBroker.canCoverClawback_no_excess_proof lb pool amount e minimumCover maxClaw hexp hmin hsub hle

/-- A clawed amount that is zero, or rounds to zero at the scale of
`coverAvailable`: `tecPRECISION_LOSS`. -/
theorem LoanBroker.canCoverClawback_precision_loss (pool : α)
    (amount : Option STAmount) (claw rn : STAmount)
    (hrounded : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hz : claw.isZero = true ∨
      (roundToCoverScale lb.numericType lb.coverAvailable claw .to_nearest = .ok rn ∧
        rn.signum = 0)) :
    lb.canCoverClawback pool amount = .ok .tecPRECISION_LOSS :=
  LoanBroker.canCoverClawback_precision_loss_proof lb pool amount claw rn hrounded hz

/-- Every guard passes: the clawback is allowed. -/
theorem LoanBroker.canCoverClawback_success (pool : α)
    (amount : Option STAmount) (claw rn : STAmount)
    (hrounded : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnz : claw.isZero = false)
    (hnear : roundToCoverScale lb.numericType lb.coverAvailable claw .to_nearest = .ok rn)
    (hrn : rn.signum ≠ 0) :
    lb.canCoverClawback pool amount = .ok .tesSUCCESS :=
  LoanBroker.canCoverClawback_success_proof lb pool amount claw rn hrounded hnz hnear hrn

/-- A zero amount passes or fails the checks exactly as no amount does. -/
theorem LoanBroker.canCoverClawback_zero_eq_none (pool : α) (a : STAmount)
    (hz : a.isZero = true) :
    lb.canCoverClawback pool (some a) = lb.canCoverClawback pool none :=
  LoanBroker.canCoverClawback_zero_eq_none_proof lb pool a hz

/-- Every outcome of the check: `tecINSUFFICIENT_FUNDS` and `tecPRECISION_LOSS`
are the only rejections `canCoverClawback` can return. -/
theorem LoanBroker.canCoverClawback_error_codes (pool : α)
    (amount : Option STAmount) (ter : TER) (hok : lb.canCoverClawback pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.canCoverClawback_error_codes_proof lb pool amount ter hok

/-- A `coverAvailable` at most the minimum cover makes `coverClawback` fail with
`tecINTERNAL`. -/
theorem LoanBroker.coverClawback_no_excess (pool : α)
    (amount : Option STAmount) (e : Int) (minimumCover maxClaw : Number)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hsub : lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw)
    (hle : maxClaw.signum ≤ 0) :
    lb.coverClawback pool amount = .ok (.error .tecINTERNAL) :=
  LoanBroker.coverClawback_no_excess_proof lb pool amount e minimumCover maxClaw hexp hmin hsub hle

/-- A clawed amount above `coverAvailable` leaves a negative `coverAvailable`:
`.notLawful`. -/
theorem LoanBroker.coverClawback_negative_cover (pool : α)
    (amount : Option STAmount) (claw : STAmount) (clawN c' : Number)
    (hrounded : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hnum : claw.toNumber .to_nearest = .ok clawN)
    (hsub : lb.coverAvailable.operator_sub clawN .to_nearest = .ok c')
    (hneg : Number.zero.operator_le c' = false) :
    lb.coverClawback pool amount = .error .notLawful :=
  LoanBroker.coverClawback_negative_cover_proof lb pool amount claw clawN c' hrounded hnum hsub hneg

/-- Every check passes: the clawback returns the clawed amount and the exact
updated broker, with `coverAvailable` set to the rounded difference `c'`. The
`to_lawful` re-check succeeds, so the `.notLawful` throw is unreachable. -/
theorem LoanBroker.coverClawback_success (pool : α)
    (amount : Option STAmount) (claw : STAmount) (clawN c' : Number)
    (hrounded : lb.roundedCoverClawback pool amount = .ok (.rounded claw))
    (hc : claw.ExactCanonical)
    (hnum : claw.toNumber .to_nearest = .ok clawN)
    (hge : lb.coverAvailable.operator_lt clawN = false)
    (hsub : lb.coverAvailable.operator_sub clawN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, lb.coverClawback pool amount = .ok (.ok ⟨claw, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } :=
  LoanBroker.coverClawback_success_proof lb pool amount claw clawN c' hrounded hc hnum hge hsub

/-- A zero amount claws exactly what no amount claws. -/
theorem LoanBroker.coverClawback_zero_eq_none (pool : α) (a : STAmount)
    (hz : a.isZero = true) :
    lb.coverClawback pool (some a) = lb.coverClawback pool none :=
  LoanBroker.coverClawback_zero_eq_none_proof lb pool a hz

/-- Every outcome of a clawback that runs without a throw: `tecINTERNAL` is the
only rejection `coverClawback` can return. -/
theorem LoanBroker.coverClawback_error_codes (pool : α)
    (amount : Option STAmount) (ter : TER)
    (hok : lb.coverClawback pool amount = .ok (.error ter)) : ter = .tecINTERNAL :=
  LoanBroker.coverClawback_error_codes_proof lb pool amount ter hok

end XRPL.Model.Lending
