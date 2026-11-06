import XRPL.Properties.Lending.LoanBroker.Common.DepositAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.CoverPossible
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.roundedCoverAmount` and `LoanBroker.coverDeposit`

A deposit floors CoverAvailable plus the amount onto the grid of the sum and credits the difference. On a reachable
broker that is the amount floored to whole base units, and CoverAvailable grows by exactly that. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

variable (lb : LoanBroker)

/-- Cover deposit -> roundedAmount = ⌊amount⌋ in whole base units. For XRP or MPT, on any lawful broker ->
roundedAmount = amount. -/
theorem LoanBroker.roundedCoverAmount_bounds :
    (∀ (base : Int) (v : Vault) (amount r : STAmount), lb.Reachable base → v.baseExponent = base →
      v.numericType = lb.numericType → amount.Canonical → amount.mNumericType = lb.numericType → 0 < amount.toRat →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.roundedCoverAmount v amount).run = .ok (.ok r) →
      r.toRat = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base) ∧
    ∀ {α : Type} [AssetPool α] (pool : α) (amount r : STAmount), lb.numericType.isIntegral = true →
      amount.Canonical → amount.mNumericType = lb.numericType →
      (lb.roundedCoverAmount pool amount).run = .ok (.ok r) → r.toRat = amount.toRat :=
  ⟨fun base v amount r hr hvb hnt hc hat hpos hcan hok =>
      LoanBroker.roundedCoverAmount_bounds_proof lb base hr (LoanBroker.maxValue_fits_of_canonical lb amount hc hat)
        v hvb hnt amount hc hat hpos hcan r hok,
    fun pool amount r hint hc hat hok => LoanBroker.roundedCoverAmount_integral_proof lb pool amount r hint hc hat hok⟩

/-- Cover deposit -> CoverAvailable' − CoverAvailable = roundedAmount ≤ amount, it converts back to roundedAmount and
rounds to itself. On any lawful broker a whole XRP or MPT deposit on a whole cover is credited exactly. -/
theorem LoanBroker.coverDeposit_credit :
    (∀ (base : Int) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → amount.Canonical → 0 < amount.toRat →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = res.amount'.toRat) ∧
    (∀ (base : Int) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → amount.Canonical → 0 < amount.toRat →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable ≤ amount.toRat) ∧
    -- an XRP or MPT holding never exceeds the asset's maximum amount. `amount''` - roundedAmount rounded again as a
    -- deposit
    (∀ (base : Int) (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → amount.Canonical →
      amount.mNumericType = lb.numericType → 0 < amount.toRat →
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat) →
      lb.canCoverDeposit v amount = .ok .tesSUCCESS → (lb.coverDeposit v amount).run = .ok (.ok res) →
      (∃ (deltaCover : Number) (deltaAmount : STAmount),
        res.loanBroker'.coverAvailable.operator_sub lb.coverAvailable .to_nearest = .ok deltaCover ∧
        STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
        deltaAmount.toRat = res.amount'.toRat) ∧
      ∃ amount'' : STAmount, (lb.roundedCoverAmount v res.amount').run = .ok (.ok amount'') ∧
        amount''.toRat = res.amount'.toRat) ∧
    -- a canonical XRP or MPT amount that fits an int64 mantissa, a whole CoverAvailable, and a holding below `2^63`,
    -- as every asset maximum is
    ∀ {α : Type} [AssetPool α] (pool : α) (amount : STAmount) (res : LoanBrokerCoverResult),
      (lb.coverDeposit pool amount).run = .ok (.ok res) → amount.IntegralCanonical →
      amount.mValue.toNat ≤ 2 ^ 63 - 1 → amount.mNumericType = lb.numericType →
      lb.toExact.coverAvailable.den = 1 → lb.toExact.coverAvailable + amount.toRat < 2 ^ 63 →
      res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = amount.toRat :=
  ⟨fun base v amount res hr hvb hnt hc hpos hcan hok =>
      LoanBroker.coverDeposit_credit_proof lb base hr v hvb hnt amount hc hpos hcan res hok,
    fun base v amount res hr hvb hnt hc hpos hcan hok =>
      LoanBroker.coverDeposit_credit_le_amount_proof lb base hr v hvb hnt amount hc hpos hcan res hok,
    fun base v amount res hr hvb hnt hc hat hpos hcap hcan hok =>
      LoanBroker.coverDeposit_applied_delta_proof lb base hr (LoanBroker.maxValue_fits_of_canonical lb amount hc hat)
        v hvb hnt amount hc hat hpos hcap hcan res hok,
    fun pool amount res hok hint hsz hat hcint hbound =>
      LoanBroker.coverDeposit_credit_integral_proof lb pool amount res hok hint hsz hat hcint hbound⟩

/-- Cover deposit on any lawful broker -> CoverAvailable' ≥ CoverAvailable, so a broker at or above minCover stays
there. -/
theorem LoanBroker.coverDeposit_increases_cover (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit pool amount).run = .ok (.ok res))
    (hc : amount.Canonical) -- a transaction amount is a canonical amount
    (hnn : 0 ≤ amount.toRat)
    -- the vault's base exponent is in the IOU exponent range
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80) :
    lb.toExact.coverAvailable ≤ res.loanBroker'.toExact.coverAvailable ∧
    ∀ e : Int, lb.HasMinimumCover e → res.loanBroker'.HasMinimumCover e :=
  ⟨LoanBroker.coverDeposit_increases_cover_proof lb pool amount res hok hc hnn hb,
    fun e hmin => LoanBroker.coverDeposit_keeps_minimum_proof lb pool amount res e hok hc hnn hb hmin⟩

/-- Cover deposit on any lawful broker that passes its checks -> it succeeds with roundedAmount. -/
theorem LoanBroker.coverDeposit_total (pool : α) (amount : STAmount)
    (hc : amount.Canonical) -- a transaction amount is a canonical amount
    (hnn : 0 ≤ amount.toRat)
    -- the vault's base exponent is in the IOU exponent range
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80)
    (hcan : lb.canCoverDeposit pool amount = .ok .tesSUCCESS) :
    ∃ r res, (lb.roundedCoverAmount pool amount).run = .ok (.ok r) ∧
      (lb.coverDeposit pool amount).run = .ok (.ok res) ∧ res.amount' = r :=
  LoanBroker.coverDeposit_total_proof lb pool amount hc hnn hb hcan

/-- On a reachable broker with room for one more base unit under the Open limit, and for XRP or MPT under
the asset's maximum -> there is an amount that raises CoverAvailable. -/
theorem LoanBroker.coverDeposit_increase_possible (base : Int) (hr : lb.Reachable base)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hroom : lb.toExact.coverAvailable + 10 ^ base ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ base)
    -- an XRP or MPT asset has room for one more unit under its maximum amount
    (hone : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + 1 ≤ lb.numericType.maxValue.toNat)
    -- the vault asset accepts whole amounts (offset 0), as XRP, MPT and IOU do
    (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.Canonical ∧ amount.mNumericType = lb.numericType ∧ 0 < amount.toRat ∧
        lb.canCoverDeposit v amount = .ok .tesSUCCESS ∧ (lb.coverDeposit v amount).run = .ok (.ok res) ∧
        lb.toExact.coverAvailable < res.loanBroker'.toExact.coverAvailable :=
  LoanBroker.coverDeposit_increase_possible_proof lb base hr hmax v hvb hnt hroom hone hmaxoff

end XRPL.Model.Lending
