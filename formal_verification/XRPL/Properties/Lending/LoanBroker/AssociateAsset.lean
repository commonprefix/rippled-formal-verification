import XRPL.Properties.Lending.LoanBroker.Common.OpenZone
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # The `associateAsset` no-op invariant

After each operation C++ rounds the broker's amounts to the asset (`associateAsset`), and the model does not. On a
reachable broker that rounding changes nothing, so a cover transaction stores its new CoverAvailable exactly. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- `associateAsset` changes nothing on a reachable broker: the asset stores every amount the broker records
exactly. -/
theorem LoanBroker.Reachable.associateAsset_noop (lb : LoanBroker) (base : Int) (hr : lb.Reachable base) :
    ¬ lb.assetsRounded := by
  sorry

/-- A broker that keeps the fixed fields, with `associateAsset` a no-op, stores CoverAvailable exactly. -/
private lemma LoanBroker.coverAvailable_stored (lb lb' : LoanBroker) (hf : LoanBroker.SameFixedFields lb lb')
    (h : ¬ lb'.assetsRounded) : STAmount.isRounded lb.numericType lb'.coverAvailable = false := by
  sorry

/-- A cover deposit stores its new CoverAvailable exactly and leaves DebtTotal and DebtMaximum as they were. -/
theorem LoanBroker.coverDeposit_associateAsset_noop (lb : LoanBroker) (base : Int) (v : Vault)
    (amount : STAmount) (res : LoanBrokerCoverResult) (hr : lb.Reachable base)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    -- an XRP or MPT holding never exceeds the asset's maximum amount
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    STAmount.isRounded lb.numericType res.loanBroker'.coverAvailable = false ∧
      res.loanBroker'.debtTotal = lb.debtTotal ∧ res.loanBroker'.debtMaximum = lb.debtMaximum := by
  sorry

/-- A cover withdrawal stores its new CoverAvailable exactly and leaves DebtTotal and DebtMaximum as they were. -/
theorem LoanBroker.coverWithdraw_associateAsset_noop (lb : LoanBroker) (base : Int) (v : Vault)
    (amount : STAmount) (res : LoanBrokerCoverResult) (hr : lb.Reachable base)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    STAmount.isRounded lb.numericType res.loanBroker'.coverAvailable = false ∧
      res.loanBroker'.debtTotal = lb.debtTotal ∧ res.loanBroker'.debtMaximum = lb.debtMaximum := by
  sorry

/-- A cover clawback stores its new CoverAvailable exactly and leaves DebtTotal and DebtMaximum as they were. -/
theorem LoanBroker.coverClawback_associateAsset_noop (lb : LoanBroker) (base : Int) (v : Vault)
    (amount : Option STAmount) (res : LoanBrokerCoverResult) (hr : lb.Reachable base)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hcan : lb.canCoverClawback v amount = .ok .tesSUCCESS)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    STAmount.isRounded lb.numericType res.loanBroker'.coverAvailable = false ∧
      res.loanBroker'.debtTotal = lb.debtTotal ∧ res.loanBroker'.debtMaximum = lb.debtMaximum := by
  sorry

end XRPL.Model.Lending
