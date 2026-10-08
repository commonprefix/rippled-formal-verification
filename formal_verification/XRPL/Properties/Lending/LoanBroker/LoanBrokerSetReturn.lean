import XRPL.Properties.Lending.LoanBroker.Common.GuardProofs
import XRPL.Properties.Lending.LoanBroker.Common.Create
import XRPL.Properties.Lending.LoanBroker.Common.SetWitness

/-! # `LoanBrokerSet` exits

The exits of `canCreate`, `canUpdate`, `create` and `update`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (lb : LoanBroker)

/-- When the requested DebtMaximum doesn't fit an STAmount exactly -> tecPRECISION_LOSS. -/
theorem LoanBroker.canCreate_precision_loss (dm : Number) (nt : NumericType)
    (hround : STAmount.equalAfterNumberConvert nt dm = .ok false) :
    LoanBroker.canCreate (some dm) nt = .ok .tecPRECISION_LOSS :=
  LoanBroker.canCreate_precision_loss_proof dm nt hround

/-- Otherwise -> success. -/
theorem LoanBroker.canCreate_success (debtMaximum : Option Number) (nt : NumericType)
    (hexact : ∀ dm ∈ debtMaximum, STAmount.equalAfterNumberConvert nt dm = .ok true) :
    LoanBroker.canCreate debtMaximum nt = .ok .tesSUCCESS :=
  LoanBroker.canCreate_success_proof debtMaximum nt hexact

/-- When the check returns a code -> success or tecPRECISION_LOSS. -/
theorem LoanBroker.canCreate_error_codes (debtMaximum : Option Number) (nt : NumericType)
    (ter : TER) (hok : LoanBroker.canCreate debtMaximum nt = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.canCreate_error_codes_proof debtMaximum nt ter hok

/-- Witness: an XRP DebtMaximum above 10^17 throws instead of returning an error code. On an XRP
vault a `debtMaximum` of `10^18` drops is in range, but the check throws. -/
theorem LoanBroker.canCreate_error_codes_attained :
    ∃ dm : Number, dm.isNormalized ∧ Number.zero.operator_le dm = true ∧
      dm.operator_le debtMaximumCap = true ∧ LoanBroker.canCreate (some dm) .native = .error .outOfRange :=
  LoanBroker.canCreate_error_codes_witness

/-- When the requested DebtMaximum ≠ 0 and < DebtTotal -> tecLIMIT_EXCEEDED. -/
theorem LoanBroker.canUpdate_limit_exceeded (dm : Number)
    (hne : dm.signum ≠ 0)
    (hlt : dm.operator_lt lb.debtTotal = true) :
    lb.canUpdate (some dm) = .ok .tecLIMIT_EXCEEDED :=
  LoanBroker.canUpdate_limit_exceeded_proof lb dm hne hlt

/-- When the requested DebtMaximum doesn't fit an STAmount exactly -> tecPRECISION_LOSS. -/
theorem LoanBroker.canUpdate_precision_loss (dm : Number)
    (hguard : (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false)
    (hround : STAmount.equalAfterNumberConvert lb.numericType dm = .ok false) :
    lb.canUpdate (some dm) = .ok .tecPRECISION_LOSS :=
  LoanBroker.canUpdate_precision_loss_proof lb dm hguard hround

/-- Otherwise -> success. -/
theorem LoanBroker.canUpdate_success (debtMaximum : Option Number)
    (hok : ∀ dm ∈ debtMaximum, (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false ∧
      STAmount.equalAfterNumberConvert lb.numericType dm = .ok true) :
    lb.canUpdate debtMaximum = .ok .tesSUCCESS :=
  LoanBroker.canUpdate_success_proof lb debtMaximum hok

/-- When the check returns a code -> success, tecLIMIT_EXCEEDED or tecPRECISION_LOSS. -/
theorem LoanBroker.canUpdate_error_codes (debtMaximum : Option Number)
    (ter : TER) (hok : lb.canUpdate debtMaximum = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecLIMIT_EXCEEDED ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.canUpdate_error_codes_proof lb debtMaximum ter hok

/-- Witness: an XRP DebtMaximum above 10^17 throws instead of returning an error code. On an XRP
broker a `debtMaximum` of `10^18` drops is in range, but the check throws. -/
theorem LoanBroker.canUpdate_error_codes_attained :
    ∃ (lb : LoanBroker) (dm : Number), lb.numericType = .native ∧ dm.isNormalized ∧
      Number.zero.operator_le dm = true ∧ dm.operator_le debtMaximumCap = true ∧
      lb.canUpdate (some dm) = .error .outOfRange :=
  LoanBroker.canUpdate_error_codes_witness

/-- Success ⟺ the new DebtMaximum is 0 or ≥ DebtTotal, and it fits an STAmount exactly. -/
theorem LoanBroker.lawful_canUpdate_iff (dm : Number)
    (hnorm : dm.isNormalized) :
    lb.canUpdate (some dm) = .ok .tesSUCCESS ↔
      (dm.toRat = 0 ∨ lb.toExact.debtTotal ≤ dm.toRat) ∧
        STAmount.equalAfterNumberConvert lb.numericType dm = .ok true :=
  LoanBroker.lawful_canUpdate_iff_proof lb dm hnorm

/-- When DebtMaximum ∉ [0, 2^63 − 1] or isn't normalized -> notLawful. -/
theorem LoanBroker.create_debtMaximum_out_of_range (tx : LoanBrokerSetCreate) (nt : NumericType)
    (dm : Number) (hdm : tx.debtMaximum = some dm)
    -- it fails a range clause of `Valid`
    (hbad : ¬ dm.isNormalized ∨ Number.zero.operator_le dm = false ∨
      dm.operator_le debtMaximumCap = false) :
    LoanBroker.create tx nt = .error .notLawful :=
  LoanBroker.create_debtMaximum_out_of_range_proof tx nt dm hdm hbad

/-- When ManagementFeeRate > 10% or a cover rate > 100% -> notLawful. -/
theorem LoanBroker.create_rate_above_maximum (tx : LoanBrokerSetCreate) (nt : NumericType)
    (hbad : maxManagementFeeRate < tx.managementFeeRate.getD 0 ∨
      maxCoverRate < tx.coverRateMinimum.getD 0 ∨ maxCoverRate < tx.coverRateLiquidation.getD 0) :
    LoanBroker.create tx nt = .error .notLawful :=
  LoanBroker.create_rate_above_maximum_proof tx nt hbad

/-- When exactly one cover rate is 0 (CoverRateMinimum or CoverRateLiquidation) -> notLawful. -/
theorem LoanBroker.create_cover_rates_uncoupled (tx : LoanBrokerSetCreate) (nt : NumericType)
    -- exactly one cover rate is zero
    (hbad : ¬ (tx.coverRateMinimum.getD 0 = 0 ↔ tx.coverRateLiquidation.getD 0 = 0)) :
    LoanBroker.create tx nt = .error .notLawful :=
  LoanBroker.create_cover_rates_uncoupled_proof tx nt hbad

/-- When DebtMaximum ∉ [0, 2^63 − 1], isn't normalized, or 0 < DebtMaximum < DebtTotal -> notLawful. -/
theorem LoanBroker.update_not_lawful (dm : Number)
    -- it fails a range clause of `Valid`, or the debt clause
    (hbad : ¬ dm.isNormalized ∨ Number.zero.operator_le dm = false ∨
      dm.operator_le debtMaximumCap = false ∨
      (dm ≠ Number.zero ∧ lb.debtTotal.operator_le dm = false)) :
    lb.update (some dm) = .error .notLawful :=
  LoanBroker.update_not_lawful_proof lb dm hbad

end XRPL.Model.Lending
