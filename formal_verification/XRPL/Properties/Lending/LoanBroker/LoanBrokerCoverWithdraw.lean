import XRPL.Properties.Lending.LoanBroker.Common.WithdrawAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.CoverPossible
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.coverWithdraw`

On a reachable broker a withdrawal pays the amount floored to whole base units, and CoverAvailable
drops by exactly the payout. Once its checks pass it always succeeds and keeps the minimum cover. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- Cover withdrawal -> roundedAmount = ⌊amount⌋ in whole base units, and CoverAvailable drops by exactly that, at
most the amount. On any lawful broker a whole XRP or MPT withdrawal drops it by exactly the amount. -/
theorem LoanBroker.coverWithdraw_debit (amount : STAmount) :
    (∀ (base : Int) (v : Vault) (res : LoanBrokerCoverResult), lb.Reachable base → v.baseExponent = base →
      v.numericType = lb.numericType → amount.Canonical → amount.mNumericType = lb.numericType → 0 < amount.toRat →
      lb.canCoverWithdraw v amount = .ok .tesSUCCESS → (lb.coverWithdraw v amount).run = .ok (.ok res) →
      res.amount'.toRat = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base) ∧
    (∀ (base : Int) (v : Vault) (res : LoanBrokerCoverResult), lb.Reachable base → v.baseExponent = base →
      amount.Canonical → 0 < amount.toRat → lb.canCoverWithdraw v amount = .ok .tesSUCCESS →
      (lb.coverWithdraw v amount).run = .ok (.ok res) →
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat) ∧
    (∀ (base : Int) (v : Vault) (res : LoanBrokerCoverResult), lb.Reachable base → v.baseExponent = base →
      amount.Canonical → 0 < amount.toRat → lb.canCoverWithdraw v amount = .ok .tesSUCCESS →
      (lb.coverWithdraw v amount).run = .ok (.ok res) →
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≤ amount.toRat) ∧
    (∀ (base : Int) (v : Vault) (res : LoanBrokerCoverResult), lb.Reachable base → v.baseExponent = base →
      v.numericType = lb.numericType → amount.Canonical → 0 < amount.toRat →
      lb.canCoverWithdraw v amount = .ok .tesSUCCESS → (lb.coverWithdraw v amount).run = .ok (.ok res) →
      ∃ (deltaCover : Number) (deltaAmount : STAmount),
        lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
        STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
        deltaAmount.toRat = res.amount'.toRat) ∧
    -- a canonical XRP or MPT amount that fits an int64 mantissa, and an XRP or MPT balance that is a whole number
    -- below 2^63, as every asset maximum is
    (∀ {α : Type} [AssetPool α] (pool : α) (res : LoanBrokerCoverResult),
      (lb.coverWithdraw pool amount).run = .ok (.ok res) →
      amount.IntegralCanonical → amount.mValue.toNat ≤ 2 ^ 63 - 1 → 0 ≤ amount.toRat →
      lb.toExact.coverAvailable.den = 1 → lb.toExact.coverAvailable < 2 ^ 63 →
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = amount.toRat) :=
  ⟨fun base v res hr hvb hnt hc hat hpos hcan hok =>
      have hmax := LoanBroker.maxValue_fits_of_canonical lb amount hc hat
      LoanBroker.coverWithdraw_amount_proof lb base hr hmax v hvb hnt amount hc hat hpos hcan res hok,
    fun base v res hr hvb hc hpos hcan hok =>
      LoanBroker.coverWithdraw_debit_proof lb base hr v hvb amount hc hpos hcan res hok,
    fun base v res hr hvb hc hpos hcan hok =>
      LoanBroker.coverWithdraw_debit_le_amount_proof lb base hr v hvb amount hc hpos hcan res hok,
    fun base v res hr hvb hnt hc hpos hcan hok =>
      LoanBroker.coverWithdraw_applied_delta_proof lb base hr v hvb hnt amount hc hpos hcan res hok,
    fun pool res hok => LoanBroker.coverWithdraw_debit_integral_proof lb pool amount res hok⟩

/-- Cover withdrawal on any lawful broker -> CoverAvailable' ≤ CoverAvailable. -/
theorem LoanBroker.coverWithdraw_decreases_cover (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw pool amount).run = .ok (.ok res))
    (hc : amount.Canonical) -- a transaction amount is a canonical amount
    -- the vault's base exponent is in the IOU exponent range
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable :=
  LoanBroker.coverWithdraw_decreases_cover_proof lb pool amount res hok hc hb

/-- Cover withdrawal on any lawful broker -> CoverAvailable' ≥ minCover. -/
theorem LoanBroker.coverWithdraw_keeps_minimum (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS)
    (hok : (lb.coverWithdraw pool amount).run = .ok (.ok res)) :
    res.loanBroker'.HasMinimumCover (AssetPool.baseExponent pool) :=
  LoanBroker.coverWithdraw_keeps_minimum_proof lb pool amount res hcan hok

/-- Cover withdrawal on any lawful broker that passes its checks -> it succeeds with roundedAmount. -/
theorem LoanBroker.coverWithdraw_total (pool : α) (amount : STAmount)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS) :
    ∃ a res, clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a ∧
      (lb.coverWithdraw pool amount).run = .ok (.ok res) ∧ res.amount' = a :=
  LoanBroker.coverWithdraw_total_proof lb pool amount hcan

/-- Reachable broker with CoverAvailable ≠ 0 -> a cover withdrawal of all of it, a legal amount, passes its checks and
leaves CoverAvailable' = 0. -/
theorem LoanBroker.coverWithdraw_all (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hnz : lb.toExact.coverAvailable ≠ 0) :
    ∃ (s : STAmount) (res : LoanBrokerCoverResult),
      s.Canonical ∧ s.mNumericType = lb.numericType ∧ s.toRat = lb.toExact.coverAvailable ∧
        lb.canCoverWithdraw v s = .ok .tesSUCCESS ∧ (lb.coverWithdraw v s).run = .ok (.ok res) ∧
        res.loanBroker'.toExact.coverAvailable = 0 :=
  have hpos : 0 < lb.toExact.coverAvailable := lt_of_le_of_ne lb.exact.coverAvailable_nonneg (Ne.symm hnz)
  have hmax := LoanBroker.Reachable.maxValue_fits lb base hr hpos
  LoanBroker.coverWithdraw_all_proof lb base hr hmax v hvb hnt hpos

end XRPL.Model.Lending
