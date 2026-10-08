import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawWitness
import XRPL.Properties.Lending.LoanBroker.Common.AssociateAssetProofs
import XRPL.Properties.Lending.LoanBroker.Common.ReachableDefs
import XRPL.Properties.Lending.LoanBroker.Common.Create

/-! # The `associateAsset` no-op invariant

After each operation C++ rounds the broker's amounts to the asset grid (`associateAsset`).
The model does not, so this file shows when that rounding changes a value: IOU cover
operations can, XRP and MPT ones cannot. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- NOT PROVABLE: all Numbers that are passed to `associateAsset` are exactly representable and
calling `associateAsset` on them is a no-op in terms of rounding. Create and update are proven.
Deposit, withdraw and clawback can leave `coverAvailable` off the grid. -/
theorem LoanBroker.Reachable.associateAsset_noop (lb : LoanBroker) (hr : lb.Reachable) :
    ¬ lb.assetsRounded := by
  have hzero (nt : NumericType) : STAmount.isRounded nt Number.zero = false := by cases nt <;> rfl
  obtain ⟨tx, nt, start, hcan, hc, hrf⟩ := hr
  induction hrf with
  | refl =>
    -- no debt, no cover, and `debtMaximum` passed `canCreate`
    have h := (RawLoanBroker.to_lawful_ok (by unfold LoanBroker.create at hc; exact hc)).1
    have hdm : STAmount.isRounded nt (tx.debtMaximum.getD Number.zero) = false := by
      cases hd : tx.debtMaximum with
      | none => exact hzero nt
      | some dm =>
        rw [hd] at hcan
        exact LoanBroker.canCreate_debtMaximum_not_rounded_proof dm nt hcan
    unfold LoanBroker.assetsRounded
    rw [show start.toRawLoanBroker = _ from h]
    simp [LoanBroker.createRaw, hzero, hdm]
  | update lb lb' dm _ hcanu hok ih =>
    -- only `debtMaximum` changes, and it passed `canUpdate`
    rw [LoanBroker.update_eq] at hok
    have h := (RawLoanBroker.to_lawful_ok hok).1
    have hdm : STAmount.isRounded lb.numericType (dm.getD lb.debtMaximum) = false := by
      cases hd : dm with
      | none =>
        unfold LoanBroker.assetsRounded at ih
        simp only [Option.getD_none]
        cases hr : STAmount.isRounded lb.numericType lb.debtMaximum <;> simp_all
      | some d =>
        rw [hd] at hcanu
        exact LoanBroker.canUpdate_debtMaximum_not_rounded_proof lb d hcanu
    unfold LoanBroker.assetsRounded at ih ⊢
    rw [show lb'.toRawLoanBroker = _ from h]
    simp only [hdm, Bool.false_eq_true, false_or]
    exact fun hor => ih (hor.elim Or.inl (fun hc => Or.inr (Or.inr hc)))
  | coverDeposit lb amount res _ hok ih =>
    -- the new cover can be off the grid (`coverDeposit_associateAsset_rounds`)
    sorry
  | coverWithdraw lb amount res _ hok ih =>
    -- the new cover can be off the grid (`coverWithdraw_associateAsset_rounds`)
    sorry
  | coverClawback lb α pool amount res _ hok ih =>
    -- the new cover can be off the grid (`coverClawback_associateAsset_rounds`)
    sorry

/-- Witness: `associateAsset` can round CoverAvailable after a deposit (it is not a no-op).
Depositing `9999999999999999` onto `9999999999999999` of IOU cover leaves `coverAvailable` at
`19999999999999998`, 17 significant digits. -/
theorem LoanBroker.coverDeposit_associateAsset_rounds :
    ∃ (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded :=
  LoanBroker.coverDeposit_associateAsset_witness

/-- Witness: `associateAsset` can round CoverAvailable after a withdraw (it is not a no-op).
Withdrawing `7.6 * 10^-10` from `10^6` of IOU cover passes the checks and leaves a 17-digit
`coverAvailable`. -/
theorem LoanBroker.coverWithdraw_associateAsset_rounds :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧
      lb.coverWithdraw amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded :=
  LoanBroker.coverWithdraw_associateAsset_witness

/-- Witness: `associateAsset` can round CoverAvailable after a clawback (it is not a no-op). Clawing
`7.5` from `10^16` of IOU cover leaves `coverAvailable` at `9999999999999992.5`, 17 significant
digits. -/
theorem LoanBroker.coverClawback_associateAsset_rounds :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult),
      lb.coverClawback pool amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded :=
  LoanBroker.coverClawback_associateAsset_witness

variable {α : Type} [AssetPool α]

/-- For XRP and MPT, `associateAsset` is a no-op after a deposit of a whole amount, while the new
CoverAvailable stays within the type's max. -/
theorem LoanBroker.coverDeposit_associateAsset_integral (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hnt : lb.numericType.isIntegral = true)
    (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable + amount.toRat < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false :=
  LoanBroker.coverDeposit_associateAsset_integral_proof lb amount res hok hnt hmaxoff hint hsz
    hcint hbound hmax

/-- For XRP and MPT, `associateAsset` is a no-op after a withdraw of a whole amount from a whole
CoverAvailable within the type's max. -/
theorem LoanBroker.coverWithdraw_associateAsset_integral (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hnt : lb.numericType.isIntegral = true)
    (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ amount.toRat)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false :=
  LoanBroker.coverWithdraw_associateAsset_integral_proof lb amount res hok hnt hmaxoff hint hsz
    hnn hcint hbound hmax

/-- For XRP and MPT, `associateAsset` is a no-op after a clawback whose checks pass, from a whole
CoverAvailable within the type's max. -/
theorem LoanBroker.coverClawback_associateAsset_integral (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hnt : lb.numericType.isIntegral = true)
    (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false :=
  LoanBroker.coverClawback_associateAsset_integral_proof lb pool amount res hcan hok hreq hnt
    hmaxoff hcint hbound hmax

end XRPL.Model.Lending
