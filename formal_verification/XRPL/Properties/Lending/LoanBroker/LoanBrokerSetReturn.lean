import XRPL.Properties.Lending.LoanBroker.Common.GuardProofs
import XRPL.Properties.Lending.LoanBroker.Common.Create

/-! # `LoanBrokerSet` exits

The exits of `canCreate`, `canUpdate`, `create` and `update`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- The exits of `canCreate`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.canCreate_exits (pool : α) :
    (∀ (debtMaximum : Option Number) (nt : NumericType), AssetPool.redemptionDate pool = none →
      LoanBroker.canCreate pool debtMaximum nt = .ok .tecNO_PERMISSION) ∧
    (∀ (dm : Number) (nt : NumericType), AssetPool.redemptionDate pool ≠ none →
      dm.isOnExponentGrid (AssetPool.baseExponent pool) nt = .ok false →
      LoanBroker.canCreate pool (some dm) nt = .ok .tecPRECISION_LOSS) ∧
    (∀ (debtMaximum : Option Number) (nt : NumericType), AssetPool.redemptionDate pool ≠ none →
      (∀ dm ∈ debtMaximum, dm.isOnExponentGrid (AssetPool.baseExponent pool) nt = .ok true) →
      LoanBroker.canCreate pool debtMaximum nt = .ok .tesSUCCESS) :=
  ⟨LoanBroker.canCreate_no_permission_proof pool, LoanBroker.canCreate_precision_loss_proof pool,
    LoanBroker.canCreate_success_proof pool⟩

/-- When the check returns a code -> success, tecNO_PERMISSION or tecPRECISION_LOSS. -/
theorem LoanBroker.canCreate_error_codes (pool : α) (debtMaximum : Option Number) (nt : NumericType)
    (ter : TER) (hok : LoanBroker.canCreate pool debtMaximum nt = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecNO_PERMISSION ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.canCreate_error_codes_proof pool debtMaximum nt ter hok

/-- The exits of `canUpdate`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.canUpdate_exits (pool : α) :
    (∀ dm : Number, dm.signum ≠ 0 → dm.operator_lt lb.debtTotal = true →
      lb.canUpdate pool (some dm) = .ok .tecLIMIT_EXCEEDED) ∧
    (∀ dm : Number, (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false →
      dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType = .ok false →
      lb.canUpdate pool (some dm) = .ok .tecPRECISION_LOSS) ∧
    (∀ debtMaximum : Option Number,
      (∀ dm ∈ debtMaximum, (dm.signum != 0 && dm.operator_lt lb.debtTotal) = false ∧
        dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType = .ok true) →
      lb.canUpdate pool debtMaximum = .ok .tesSUCCESS) :=
  ⟨LoanBroker.canUpdate_limit_exceeded_proof lb pool, LoanBroker.canUpdate_precision_loss_proof lb pool,
    LoanBroker.canUpdate_success_proof lb pool⟩

/-- When the check returns a code -> success, tecLIMIT_EXCEEDED or tecPRECISION_LOSS. -/
theorem LoanBroker.canUpdate_error_codes (pool : α) (debtMaximum : Option Number)
    (ter : TER) (hok : lb.canUpdate pool debtMaximum = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecLIMIT_EXCEEDED ∨ ter = .tecPRECISION_LOSS :=
  LoanBroker.canUpdate_error_codes_proof lb pool debtMaximum ter hok

/-- Success ⟺ the new DebtMaximum is 0 or ≥ DebtTotal, and it is on the vault's base grid. -/
theorem LoanBroker.canUpdate_lawful_iff (pool : α) (dm : Number)
    (hnorm : dm.isNormalized) :
    lb.canUpdate pool (some dm) = .ok .tesSUCCESS ↔
      (dm.toRat = 0 ∨ lb.toExact.debtTotal ≤ dm.toRat) ∧
        dm.isOnExponentGrid (AssetPool.baseExponent pool) lb.numericType = .ok true :=
  LoanBroker.canUpdate_lawful_iff_proof lb pool dm hnorm

/-- A field out of range -> `create` returns notLawful, one line per field rule. -/
theorem LoanBroker.create_not_lawful (tx : LoanBrokerSetCreate) (nt : NumericType) :
    -- it fails a range clause of `Valid`
    (∀ dm : Number, tx.debtMaximum = some dm →
      ¬ dm.isNormalized ∨ Number.zero.operator_le dm = false ∨ dm.operator_le debtMaximumCap = false →
      LoanBroker.create tx nt = .error .notLawful) ∧
    (maxManagementFeeRate < tx.managementFeeRate.getD 0 ∨
        maxCoverRate < tx.coverRateMinimum.getD 0 ∨ maxCoverRate < tx.coverRateLiquidation.getD 0 →
      LoanBroker.create tx nt = .error .notLawful) ∧
    -- exactly one cover rate is zero
    (¬ (tx.coverRateMinimum.getD 0 = 0 ↔ tx.coverRateLiquidation.getD 0 = 0) →
      LoanBroker.create tx nt = .error .notLawful) :=
  ⟨LoanBroker.create_debtMaximum_out_of_range_proof tx nt, LoanBroker.create_rate_above_maximum_proof tx nt,
    LoanBroker.create_cover_rates_uncoupled_proof tx nt⟩

/-- When DebtMaximum ∉ [0, 2^63 − 1], isn't normalized, or 0 < DebtMaximum < DebtTotal -> notLawful. -/
theorem LoanBroker.update_not_lawful (dm : Number)
    -- it fails a range clause of `Valid`, or the debt clause
    (hbad : ¬ dm.isNormalized ∨ Number.zero.operator_le dm = false ∨
      dm.operator_le debtMaximumCap = false ∨
      (dm ≠ Number.zero ∧ lb.debtTotal.operator_le dm = false)) :
    lb.update (some dm) = .error .notLawful :=
  LoanBroker.update_not_lawful_proof lb dm hbad

end XRPL.Model.Lending
