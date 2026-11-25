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
        deltaAmount.toRat = res.amount'.toRat) := by
  sorry

end XRPL.Model.Lending
