import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Lending.Loan.Common.DeleteExits

/-! # `LoanDelete` exits

The exits of `canDelete` and `delete`, in the order each runs its checks. A later exit assumes the
earlier checks passed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (loan : Loan)

/-- The exits of `canDelete`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Loan.canDelete_exits :
    (loan.isPending = false → 0 < loan.paymentRemaining → loan.canDelete = .tecHAS_OBLIGATIONS) ∧
    (loan.isPending = true ∨ loan.paymentRemaining = 0 → loan.canDelete = .tesSUCCESS) :=
  ⟨Loan.canDelete_has_obligations_proof loan, Loan.canDelete_success_proof loan⟩

/-- Error codes: success or tecHAS_OBLIGATIONS. -/
theorem Loan.canDelete_error_codes :
    loan.canDelete = .tesSUCCESS ∨ loan.canDelete = .tecHAS_OBLIGATIONS :=
  Loan.canDelete_error_codes_proof loan

/-- Success ⟺ the loan is pending or PaymentRemaining = 0. -/
theorem Loan.canDelete_lawful_iff :
    loan.canDelete = .tesSUCCESS ↔ loan.isPending = true ∨ loan.paymentRemaining = 0 :=
  Loan.canDelete_lawful_iff_proof loan

/-! ## `Loan.delete` -/

open XRPL.Model.SingleAssetVault (Vault RawVault)

variable (v : Vault)

/-- The exits of `delete`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Loan.delete_exits :
    -- `principal'` - PrincipalOutstanding as an amount of the asset, `ad'` - the new AssetsDeployed
    (∀ principal' aa' ad' lu' ar' yu' : Number, loan.isPending = true →
      STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest = .ok principal' →
      Vault.AdjustSums v (loan.deleteChange principal') aa' ad' lu' ar' yu' → ad'.signum < 0 →
      (loan.delete v).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `ar'` - the new AssetsReserved
    (∀ principal' aa' ad' lu' ar' yu' : Number, loan.isPending = true →
      STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest = .ok principal' →
      Vault.AdjustSums v (loan.deleteChange principal') aa' ad' lu' ar' yu' → ar'.signum < 0 →
      (loan.delete v).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `lu'` - the new LossUnrealized
    (∀ principal' aa' ad' lu' ar' yu' : Number, loan.isPending = true →
      STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest = .ok principal' →
      Vault.AdjustSums v (loan.deleteChange principal') aa' ad' lu' ar' yu' →
      0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum →
      lu'.operator_gt ad' = true → (loan.delete v).run = .ok (.error .tecLIMIT_EXCEEDED)) ∧
    -- `raw` - the updated vault, `debtTotal'` - DebtTotal − PrincipalOutstanding
    (∀ (principal' debtTotal' : Number) (raw : RawVault) (v' : Vault) (broker' : LoanBroker), loan.isPending = true →
      STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest = .ok principal' →
      (v.adjustBalances (loan.deleteChange principal')).run = .ok (.ok raw) → raw.to_lawful = .ok v' →
      loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok debtTotal' →
      loan.broker.releaseLoan debtTotal' = .ok broker' →
      (loan.delete v).run = .ok (.ok { broker' := broker', pool' := v' })) ∧
    -- `broker'` - the broker with LoanCount − 1, and DebtTotal = 0 once it holds no loan
    (∀ broker' : LoanBroker, loan.isPending = false → loan.broker.releaseLoan loan.broker.debtTotal = .ok broker' →
      (loan.delete v).run = .ok (.ok { broker' := broker', pool' := v })) :=
  ⟨Loan.delete_deployed_bad_ledger_proof loan v, Loan.delete_reserved_bad_ledger_proof loan v,
    Loan.delete_limit_exceeded_proof loan v, Loan.delete_success_proof loan v, Loan.deleteActive_success_proof loan v⟩

/-- The only delete rejections are tefBAD_LEDGER or tecLIMIT_EXCEEDED. -/
theorem Loan.delete_error_codes (ter : TER) (hok : (loan.delete v).run = .ok (.error ter)) :
    ter = .tefBAD_LEDGER ∨ ter = .tecLIMIT_EXCEEDED :=
  Loan.delete_error_codes_proof loan v ter hok

end XRPL.Model.Lending
