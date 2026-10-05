import XRPL.Properties.Lending.LoanBroker.Common.GuardProofs
import XRPL.Properties.Lending.LoanBroker.Common.Create

/-! # `LoanBrokerSet` exits

One theorem per exit of `canCreate` and `canUpdate`, and per reason `create` or
`update` fails its lawfulness re-check. A `.notLawful` throw returns no broker.
-/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- A `debtMaximum` that changes when converted to the vault's `numericType`:
`tecPRECISION_LOSS`. -/
theorem LoanBroker.canCreate_precision_loss (dm : Number) (nt : NumericType)
    (hround : STAmount.equalAfterNumberConvert nt dm = .ok false) : -- the conversion rounds
    LoanBroker.canCreate (some dm) nt = .ok .tecPRECISION_LOSS :=
  LoanBroker.canCreate_precision_loss_proof dm nt hround

/-- No `debtMaximum`, or one that converts unchanged, passes. -/
theorem LoanBroker.canCreate_success (debtMaximum : Option Number) (nt : NumericType)
    -- a requested maximum converts without rounding
    (hexact : ∀ dm ∈ debtMaximum, STAmount.equalAfterNumberConvert nt dm = .ok true) :
    LoanBroker.canCreate debtMaximum nt = .ok .tesSUCCESS :=
  LoanBroker.canCreate_success_proof debtMaximum nt hexact

/-- Every outcome of the check: `tecPRECISION_LOSS` is the only rejection
`canCreate` can return. -/
theorem LoanBroker.canCreate_error_codes (debtMaximum : Option Number) (nt : NumericType)
    (ter : TER) (hok : LoanBroker.canCreate debtMaximum nt = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.canCreate_error_codes_proof debtMaximum nt ter hok

/-- A nonzero new `debtMaximum` that compares below the current `debtTotal`:
`tecLIMIT_EXCEEDED`. -/
theorem LoanBroker.canUpdate_limit_exceeded (dm : Number)
    (hne : dm.signum ≠ 0) -- the new maximum is nonzero
    (hlt : dm.operator_lt lb.debtTotal = true) : -- and compares below the current debt
    lb.canUpdate (some dm) = .ok .tecLIMIT_EXCEEDED :=
  LoanBroker.canUpdate_limit_exceeded_proof lb dm hne hlt

/-- A new `debtMaximum` that passes the debt check but changes when converted to
the vault's `numericType`: `tecPRECISION_LOSS`. -/
theorem LoanBroker.canUpdate_precision_loss (dm : Number)
    -- the debt check does not fire: zero, or not comparing below the debt
    (hguard : (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false)
    (hround : STAmount.equalAfterNumberConvert lb.numericType dm = .ok false) : -- it rounds
    lb.canUpdate (some dm) = .ok .tecPRECISION_LOSS :=
  LoanBroker.canUpdate_precision_loss_proof lb dm hguard hround

/-- No `debtMaximum`, or one that is zero or not below the debt and converts
unchanged, passes. -/
theorem LoanBroker.canUpdate_success (debtMaximum : Option Number)
    -- a requested maximum passes the debt check and converts unchanged
    (hok : ∀ dm ∈ debtMaximum, (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false ∧
      STAmount.equalAfterNumberConvert lb.numericType dm = .ok true) :
    lb.canUpdate debtMaximum = .ok .tesSUCCESS :=
  LoanBroker.canUpdate_success_proof lb debtMaximum hok

/-- Every outcome of the check: `tecLIMIT_EXCEEDED` and `tecPRECISION_LOSS` are
the only rejections `canUpdate` can return. -/
theorem LoanBroker.canUpdate_error_codes (debtMaximum : Option Number)
    (ter : TER) (hok : lb.canUpdate debtMaximum = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecLIMIT_EXCEEDED ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.canUpdate_error_codes_proof lb debtMaximum ter hok

/-- On a lawful broker, a normalized new `debtMaximum` passes exactly when it is
zero or at least `debtTotal`, and the vault asset holds it exactly. -/
theorem LoanBroker.lawful_canUpdate_iff (dm : Number)
    (hnorm : dm.isNormalized) : -- the new maximum is normalized
    lb.canUpdate (some dm) = .ok .tesSUCCESS ↔
      (dm.toRat = 0 ∨ lb.toExact.debtTotal ≤ dm.toRat) ∧
        STAmount.equalAfterNumberConvert lb.numericType dm = .ok true :=
  LoanBroker.lawful_canUpdate_iff_proof lb dm hnorm

/-- A requested `debtMaximum` that is not normalized, compares below zero, or compares
above `2^63 - 1`: `.notLawful`. -/
theorem LoanBroker.create_debtMaximum_out_of_range (tx : LoanBrokerSetCreate) (nt : NumericType)
    (dm : Number) (hdm : tx.debtMaximum = some dm) -- a maximum was requested
    -- and it fails a range clause of `Valid`
    (hbad : ¬ dm.isNormalized ∨ Number.zero.operator_le dm = false ∨
      dm.operator_le debtMaximumCap = false) :
    LoanBroker.create tx nt = .error .notLawful :=
  LoanBroker.create_debtMaximum_out_of_range_proof tx nt dm hdm hbad

/-- A `managementFeeRate` above 10%, or a cover rate above 100%: `.notLawful`. -/
theorem LoanBroker.create_rate_above_maximum (tx : LoanBrokerSetCreate) (nt : NumericType)
    -- a rate is above its maximum
    (hbad : maxManagementFeeRate < tx.managementFeeRate.getD 0 ∨
      maxCoverRate < tx.coverRateMinimum.getD 0 ∨ maxCoverRate < tx.coverRateLiquidation.getD 0) :
    LoanBroker.create tx nt = .error .notLawful :=
  LoanBroker.create_rate_above_maximum_proof tx nt hbad

/-- Exactly one zero cover rate: `.notLawful`. Both rates are set or neither is. -/
theorem LoanBroker.create_cover_rates_uncoupled (tx : LoanBrokerSetCreate) (nt : NumericType)
    -- exactly one cover rate is zero
    (hbad : ¬ (tx.coverRateMinimum.getD 0 = 0 ↔ tx.coverRateLiquidation.getD 0 = 0)) :
    LoanBroker.create tx nt = .error .notLawful :=
  LoanBroker.create_cover_rates_uncoupled_proof tx nt hbad

/-- A new `debtMaximum` that is not normalized, compares below zero or above
`2^63 - 1`, or is nonzero and below the current `debtTotal`: `.notLawful`. -/
theorem LoanBroker.update_not_lawful (dm : Number)
    -- it fails a range clause of `Valid`, or the debt clause
    (hbad : ¬ dm.isNormalized ∨ Number.zero.operator_le dm = false ∨
      dm.operator_le debtMaximumCap = false ∨
      (dm ≠ Number.zero ∧ lb.debtTotal.operator_le dm = false)) :
    lb.update (some dm) = .error .notLawful :=
  LoanBroker.update_not_lawful_proof lb dm hbad

end XRPL.Model.Lending
