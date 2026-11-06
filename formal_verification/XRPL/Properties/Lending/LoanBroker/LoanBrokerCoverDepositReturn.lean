import XRPL.Properties.Lending.LoanBroker.Common.DepositExits

/-! # `LoanBrokerCoverDeposit` exits

The exits of the deposit's rounding, its check and the deposit. The rounding rejects a credit that is not positive,
and the check a deposit that moves the cover off the base exponent or past the Open limit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- The exits of `roundedCoverAmount`, in the order it runs its checks. Each line assumes the checks before it
passed. -/
theorem LoanBroker.roundedCoverAmount_exits (pool : α) (amount : STAmount) :
    (∀ (r : STAmount) (aN : Number), amount.toNumber .to_nearest = .ok aN →
      sumRoundAndSubtract lb.coverAvailable aN (AssetPool.baseExponent pool) lb.numericType .downward = .ok r →
      r.signum ≤ 0 → (lb.roundedCoverAmount pool amount).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ (r : STAmount) (aN : Number), amount.toNumber .to_nearest = .ok aN →
      sumRoundAndSubtract lb.coverAvailable aN (AssetPool.baseExponent pool) lb.numericType .downward = .ok r →
      0 < r.signum → (lb.roundedCoverAmount pool amount).run = .ok (.ok r)) :=
  ⟨LoanBroker.roundedCoverAmount_precision_loss_proof lb pool amount,
    LoanBroker.roundedCoverAmount_rounded_proof lb pool amount⟩

/-- The only rounding rejection is tecPRECISION_LOSS. -/
theorem LoanBroker.roundedCoverAmount_error_codes (pool : α) (amount : STAmount) (ter : TER)
    (hok : (lb.roundedCoverAmount pool amount).run = .ok (.error ter)) :
    ter = .tecPRECISION_LOSS :=
  LoanBroker.roundedCoverAmount_error_codes_proof lb pool amount ter hok

/-- The exits of `canCoverDeposit`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.canCoverDeposit_exits (pool : α) (amount : STAmount) :
    ((lb.roundedCoverAmount pool amount).run = .ok (.error .tecPRECISION_LOSS) →
      lb.canCoverDeposit pool amount = .ok .tecPRECISION_LOSS) ∧
    (∀ (r : STAmount) (rN : Number) (e : Int), (lb.roundedCoverAmount pool amount).run = .ok (.ok r) →
      r.toNumber .to_nearest = .ok rN →
      postSumExponent lb.coverAvailable rN (AssetPool.baseExponent pool) lb.numericType = .ok e →
      e ≠ AssetPool.baseExponent pool → lb.canCoverDeposit pool amount = .ok .tecLIMIT_EXCEEDED) ∧
    (∀ (r : STAmount) (rN c' limit : Number), (lb.roundedCoverAmount pool amount).run = .ok (.ok r) →
      r.toNumber .to_nearest = .ok rN →
      postSumExponent lb.coverAvailable rN (AssetPool.baseExponent pool) lb.numericType =
        .ok (AssetPool.baseExponent pool) →
      lb.coverAvailable.operator_add rN .towards_zero = .ok c' → AssetPool.openLimit pool = .ok limit →
      c'.operator_gt limit = true → lb.canCoverDeposit pool amount = .ok .tecLIMIT_EXCEEDED) ∧
    (∀ (r : STAmount) (rN c' limit : Number), (lb.roundedCoverAmount pool amount).run = .ok (.ok r) →
      r.toNumber .to_nearest = .ok rN →
      postSumExponent lb.coverAvailable rN (AssetPool.baseExponent pool) lb.numericType =
        .ok (AssetPool.baseExponent pool) →
      lb.coverAvailable.operator_add rN .towards_zero = .ok c' → AssetPool.openLimit pool = .ok limit →
      c'.operator_gt limit = false → lb.canCoverDeposit pool amount = .ok .tesSUCCESS) :=
  ⟨LoanBroker.canCoverDeposit_precision_loss_proof lb pool amount,
    LoanBroker.canCoverDeposit_scale_exceeded_proof lb pool amount,
    LoanBroker.canCoverDeposit_open_limit_exceeded_proof lb pool amount,
    LoanBroker.canCoverDeposit_success_proof lb pool amount⟩

/-- Error codes: success, tecPRECISION_LOSS or tecLIMIT_EXCEEDED. -/
theorem LoanBroker.canCoverDeposit_error_codes (pool : α) (amount : STAmount) (ter : TER)
    (hok : lb.canCoverDeposit pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED :=
  LoanBroker.canCoverDeposit_error_codes_proof lb pool amount ter hok

/-- The exits of `coverDeposit`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem LoanBroker.coverDeposit_exits (pool : α) (amount : STAmount) :
    (∀ ter : TER, (lb.roundedCoverAmount pool amount).run = .ok (.error ter) →
      (lb.coverDeposit pool amount).run = .ok (.error .tecINTERNAL)) ∧
    -- `c'` - the new CoverAvailable, the sum rounded to nearest. A transaction amount is a canonical amount, and the
    -- vault's base exponent is in the IOU exponent range
    (∀ (r : STAmount) (rN c' : Number), (lb.roundedCoverAmount pool amount).run = .ok (.ok r) → amount.Canonical →
      0 ≤ amount.toRat → (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80 →
      r.toNumber .to_nearest = .ok rN → lb.coverAvailable.operator_add rN .to_nearest = .ok c' →
      ∃ lb' : LoanBroker, (lb.coverDeposit pool amount).run = .ok (.ok ⟨r, lb'⟩) ∧
        lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' }) :=
  ⟨LoanBroker.coverDeposit_rejected_proof lb pool amount, LoanBroker.coverDeposit_success_proof lb pool amount⟩

/-- The only deposit rejection is tecINTERNAL. -/
theorem LoanBroker.coverDeposit_error_codes (pool : α) (amount : STAmount) (ter : TER)
    (hok : (lb.coverDeposit pool amount).run = .ok (.error ter)) : ter = .tecINTERNAL :=
  LoanBroker.coverDeposit_error_codes_proof lb pool amount ter hok

end XRPL.Model.Lending
