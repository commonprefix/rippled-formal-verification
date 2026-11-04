import XRPL.Properties.Lending.LoanBroker.Common.OpenZone
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # The `associateAsset` no-op invariant

After each operation C++ rounds the broker's amounts to the asset (`associateAsset`), and the model does not.
After a cover deposit, withdrawal or clawback on a reachable broker that rounding changes nothing. The reachable broker
itself is in `LoanBroker.Reachable.broker_fields`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- `associateAsset` is a no-op after a deposit into a reachable broker. -/
theorem LoanBroker.coverDeposit_associateAsset_noop (lb : LoanBroker) (base : Int) (v : Vault)
    (amount : STAmount) (res : LoanBrokerCoverResult) (hr : lb.Reachable base)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    -- an XRP or MPT holding never exceeds the asset's maximum amount
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    ¬ res.loanBroker'.assetsRounded :=
  LoanBroker.Reachable.associateAsset_noop_proof res.loanBroker' base
    (LoanBroker.Reachable.coverDeposit_step lb base hr v amount res hvb hnt hc hat hpos hcap hcan hok)
    (by
      rw [(LoanBroker.coverDeposit_fixed_fields lb v amount res hok).numericType]
      exact LoanBroker.maxValue_fits_of_canonical lb amount hc hat)

/-- `associateAsset` is a no-op after a withdrawal from a reachable broker. -/
theorem LoanBroker.coverWithdraw_associateAsset_noop (lb : LoanBroker) (base : Int) (v : Vault)
    (amount : STAmount) (res : LoanBrokerCoverResult) (hr : lb.Reachable base)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    ¬ res.loanBroker'.assetsRounded :=
  LoanBroker.Reachable.associateAsset_noop_proof res.loanBroker' base
    (LoanBroker.Reachable.coverWithdraw_step lb base hr v amount res hvb hnt hc hat hpos hcan hok)
    (by
      rw [(LoanBroker.coverWithdraw_fixed_fields lb v amount res hok).numericType]
      exact LoanBroker.maxValue_fits_of_canonical lb amount hc hat)

/-- `associateAsset` is a no-op after a clawback from a reachable broker. -/
theorem LoanBroker.coverClawback_associateAsset_noop (lb : LoanBroker) (base : Int) (v : Vault)
    (amount : Option STAmount) (res : LoanBrokerCoverResult) (hr : lb.Reachable base)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hcan : lb.canCoverClawback v amount = .ok .tesSUCCESS)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    ¬ res.loanBroker'.assetsRounded :=
  LoanBroker.Reachable.associateAsset_noop_proof res.loanBroker' base
    (LoanBroker.Reachable.coverClawback_step lb base hr v amount res hvb hnt hreq hcan hok)
    (by
      rw [(LoanBroker.coverClawback_fixed_fields lb v amount res hok).numericType]
      exact LoanBroker.Reachable.coverClawback_maxValue_fits lb base hr v amount res hok)

end XRPL.Model.Lending
