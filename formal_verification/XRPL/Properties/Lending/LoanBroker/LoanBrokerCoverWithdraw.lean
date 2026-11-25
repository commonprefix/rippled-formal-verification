import XRPL.Properties.Lending.LoanBroker.Common.WithdrawAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.CoverPossible
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.coverWithdraw`

On a reachable broker a withdrawal pays the amount floored to whole base units, and CoverAvailable
drops by exactly the payout. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable (lb : LoanBroker)

/-- Cover withdrawal -> roundedAmount = ⌊amount⌋ in whole base units, = amount for XRP or MPT. CoverAvailable drops by
exactly roundedAmount ≤ amount, and the drop converts back to roundedAmount. -/
theorem LoanBroker.coverWithdraw_debit (amount : STAmount) :
    (∀ (base : Int) (v : Vault) (res : LoanBrokerCoverResult), lb.Reachable base → v.baseExponent = base →
      v.numericType = lb.numericType → amount.Canonical → amount.mNumericType = lb.numericType → 0 < amount.toRat →
      lb.canCoverWithdraw v amount = .ok .tesSUCCESS → (lb.coverWithdraw v amount).run = .ok (.ok res) →
      res.amount'.toRat = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base) ∧
    (∀ {α : Type} [AssetPool α] (pool : α) (res : LoanBrokerCoverResult),
      lb.numericType.isIntegral = true → amount.Canonical → amount.mNumericType = lb.numericType →
      0 < amount.toRat → (lb.coverWithdraw pool amount).run = .ok (.ok res) → res.amount'.toRat = amount.toRat) ∧
    (∀ (base : Int) (v : Vault) (res : LoanBrokerCoverResult), lb.Reachable base → v.baseExponent = base →
      amount.Canonical → 0 < amount.toRat → lb.canCoverWithdraw v amount = .ok .tesSUCCESS →
      (lb.coverWithdraw v amount).run = .ok (.ok res) →
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat) ∧
    (∀ (base : Int) (v : Vault) (res : LoanBrokerCoverResult), lb.Reachable base → v.baseExponent = base →
      amount.Canonical → 0 < amount.toRat → lb.canCoverWithdraw v amount = .ok .tesSUCCESS →
      (lb.coverWithdraw v amount).run = .ok (.ok res) →
      res.amount'.toRat ≤ amount.toRat) ∧
    (∀ (base : Int) (v : Vault) (res : LoanBrokerCoverResult), lb.Reachable base → v.baseExponent = base →
      v.numericType = lb.numericType → amount.Canonical → 0 < amount.toRat →
      lb.canCoverWithdraw v amount = .ok .tesSUCCESS → (lb.coverWithdraw v amount).run = .ok (.ok res) →
      ∃ (deltaCover : Number) (deltaAmount : STAmount),
        lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
        STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
        deltaAmount.toRat = res.amount'.toRat) :=
  ⟨fun base v res hr hvb hnt hc hat hpos hcan hok =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb amount hc hat
      LoanBroker.coverWithdraw_amount_proof lb base hr hmax v hvb hnt amount hc hat hpos hcan res hok,
    fun pool res hint hc hat hpos hok =>
      LoanBroker.coverWithdraw_integral_amount_proof lb pool amount res hok hint hc hat hpos.le,
    fun base v res hr hvb hc hpos hcan hok =>
      LoanBroker.coverWithdraw_debit_proof lb base hr v hvb amount hc hpos hcan res hok,
    fun base v res hr hvb hc hpos hcan hok => by
      rw [← LoanBroker.coverWithdraw_debit_proof lb base hr v hvb amount hc hpos hcan res hok]
      exact LoanBroker.coverWithdraw_debit_le_amount_proof lb base hr v hvb amount hc hpos hcan res hok,
    fun base v res hr hvb hnt hc hpos hcan hok =>
      LoanBroker.coverWithdraw_applied_delta_proof lb base hr v hvb hnt amount hc hpos hcan res hok⟩

end XRPL.Model.Lending
