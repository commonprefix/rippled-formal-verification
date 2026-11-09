import XRPL.Properties.Lending.LoanBroker.Common.DepositAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.CoverPossible
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.coverDeposit`

A deposit floors CoverAvailable plus the amount onto the grid of the sum and credits the difference. On a reachable
broker that is the amount floored to whole base units, and CoverAvailable grows by exactly that. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable (lb : LoanBroker)

/-- Cover deposit -> roundedAmount = ⌊amount⌋ in whole base units, = amount for XRP or MPT. CoverAvailable rises by
exactly roundedAmount ≤ amount, and the rise converts back to roundedAmount. -/
theorem LoanBroker.coverDeposit_credit :
    (∀ (base : Int) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → amount.Canonical →
      amount.mNumericType = lb.numericType → 0 < amount.toRat →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      res.amount'.toRat = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base) ∧
    (∀ {α : Type} [AssetPool α] (pool : α) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.numericType.isIntegral = true → amount.Canonical → amount.mNumericType = lb.numericType →
      (lb.coverDeposit pool amount).run = .ok (.ok res) → res.amount'.toRat = amount.toRat) ∧
    (∀ (base : Int) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → amount.Canonical → 0 < amount.toRat →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = res.amount'.toRat) ∧
    (∀ (base : Int) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → amount.Canonical → 0 < amount.toRat →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      res.amount'.toRat ≤ amount.toRat) ∧
    -- an XRP or MPT holding never exceeds the asset's maximum amount
    ∀ (base : Int) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → amount.Canonical →
      amount.mNumericType = lb.numericType → 0 < amount.toRat →
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      ∃ (deltaCover : Number) (deltaAmount : STAmount),
        res.loanBroker'.coverAvailable.operator_sub lb.coverAvailable .to_nearest = .ok deltaCover ∧
        STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
        deltaAmount.toRat = res.amount'.toRat :=
  ⟨fun base v amount res hr hvb hnt hc hat hpos hcan hok =>
      LoanBroker.coverDeposit_amount_proof lb base hr (LoanBroker.maxValue_fits_of_canonical lb amount hc hat)
        v hvb hnt amount hc hat hpos hcan res hok,
    fun pool amount res hint hc hat hok =>
      LoanBroker.coverDeposit_integral_amount_proof lb pool amount res hint hc hat hok,
    fun base v amount res hr hvb hnt hc hpos hcan hok =>
      LoanBroker.coverDeposit_credit_proof lb base hr v hvb hnt amount hc hpos hcan res hok,
    fun base v amount res hr hvb hnt hc hpos hcan hok => by
      rw [← LoanBroker.coverDeposit_credit_proof lb base hr v hvb hnt amount hc hpos hcan res hok]
      exact LoanBroker.coverDeposit_credit_le_amount_proof lb base hr v hvb hnt amount hc hpos hcan res hok,
    fun base v amount res hr hvb hnt hc hat hpos hcap hcan hok =>
      LoanBroker.coverDeposit_applied_delta_proof lb base hr (LoanBroker.maxValue_fits_of_canonical lb amount hc hat)
        v hvb hnt amount hc hat hpos hcap hcan res hok⟩

end XRPL.Model.Lending
