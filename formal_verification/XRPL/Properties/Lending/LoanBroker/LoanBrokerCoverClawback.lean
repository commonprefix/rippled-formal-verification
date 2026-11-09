import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.CoverPossible
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # `LoanBroker.roundedCoverClawback` and `LoanBroker.coverClawback`

A clawback takes the request, or all cover above minCover when there is none, capped at that excess. In the Open
zone it claws that amount floored to whole base units, and CoverAvailable drops by exactly that. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable (lb : LoanBroker)

/-- Cover clawback on any lawful broker in the Open zone, with no amount or amount = 0 -> clawAmount = CoverAvailable −
minCover, and CoverAvailable' = minCover. -/
theorem LoanBroker.roundedCoverClawback_all (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (minimumCover : Number)
    -- CoverAvailable is whole base units within the Open limit, as on every reachable broker
    (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent =
      .ok minimumCover)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.amount'.toRat = lb.toExact.coverAvailable - minimumCover.toRat ∧
      res.loanBroker'.toExact.coverAvailable = minimumCover.toRat :=
  ⟨LoanBroker.roundedCoverClawback_all_proof lb v amount res minimumCover hz hnt hmax hreq hall hmin hok,
    LoanBroker.coverClawback_all_leaves_minimum_proof lb v amount res minimumCover hz hnt hmax hreq hall hmin hok⟩

/-- Witness: off the Open zone the checks pass and clawAmount ≠ CoverAvailable − minCover. On a cover of
`1000000000000001.6` with minCover `1`, a full clawback rounds clawAmount up to `1000000000000001`. -/
theorem LoanBroker.roundedCoverClawback_all_attained :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .ok (.ok res) ∧
      res.amount'.toRat ≠ lb.toExact.coverAvailable - minimumCover.toRat :=
  LoanBroker.roundedCoverClawback_all_witness

/-- Witness: off the Open zone, a run where the checks pass and a full clawback leaves CoverAvailable' ≠
minCover. On the broker of `roundedCoverClawback_all_attained` it leaves `0.6` with minCover `1`. -/
theorem LoanBroker.roundedCoverClawback_all_leaves_minimum_attained :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .ok (.ok res) ∧
      res.loanBroker'.toExact.coverAvailable ≠ minimumCover.toRat :=
  LoanBroker.coverClawback_all_leaves_minimum_witness

/-- Cover clawback on any lawful broker in the Open zone, with amount ≠ 0 -> clawAmount =
⌊min(amount, CoverAvailable − minCover)⌋ in whole base units, and a larger amount never lowers it. -/
theorem LoanBroker.roundedCoverClawback_capped (v : Vault) (minimumCover : Number)
    -- CoverAvailable is whole base units within the Open limit, as on every reachable broker
    (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent =
      .ok minimumCover) :
    (∀ (a : STAmount) (res : LoanBrokerCoverResult),
      a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat → a.isZero = false →
      (lb.coverClawback v (some a)).run = .ok (.ok res) →
      res.amount'.toRat =
        (⌊min a.toRat (lb.toExact.coverAvailable - minimumCover.toRat) / 10 ^ v.baseExponent⌋ : ℚ) *
          10 ^ v.baseExponent) ∧
    ∀ (a b : STAmount) (ra rb : LoanBrokerCoverResult),
      a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat →
      b.CanonicalOrZero ∧ b.mNumericType = lb.numericType ∧ 0 ≤ b.toRat →
      a.isZero = false → b.isZero = false → a.toRat ≤ b.toRat →
      (lb.coverClawback v (some a)).run = .ok (.ok ra) → (lb.coverClawback v (some b)).run = .ok (.ok rb) →
      ra.amount'.toRat ≤ rb.amount'.toRat :=
  ⟨fun a res hreq hnz hok =>
      have hmax := LoanBroker.maxValue_fits_of_canonicalOrZero lb a hreq.1 hnz hreq.2.1
      LoanBroker.roundedCoverClawback_capped_proof lb v a res minimumCover hz hnt hmax hreq hnz hmin hok,
    fun a b ra rb ha hb hza hzb hab hoka hokb =>
      have hmax := LoanBroker.maxValue_fits_of_canonicalOrZero lb a ha.1 hza ha.2.1
      LoanBroker.coverClawback_monotone_proof lb v minimumCover hz hnt hmax hmin a b ha hb hza hzb hab ra rb hoka
        hokb⟩

/-- Cover clawback -> CoverAvailable drops by exactly clawAmount, at most the amount when it is ≠ 0, and the drop
converts back to clawAmount. -/
theorem LoanBroker.coverClawback_debit :
    (∀ (base : Int) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → (lb.coverClawback v amount).run = .ok (.ok res) →
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat) ∧
    (∀ (base : Int) (v : Vault) (a : STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType →
      a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat → a.isZero = false →
      (lb.coverClawback v (some a)).run = .ok (.ok res) →
      res.amount'.toRat ≤ a.toRat) ∧
    (∀ (base : Int) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult), lb.Reachable base →
      v.baseExponent = base → v.numericType = lb.numericType → (lb.coverClawback v amount).run = .ok (.ok res) →
      ∃ (deltaCover : Number) (deltaAmount : STAmount),
        lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
        STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
        deltaAmount.toRat = res.amount'.toRat) :=
  ⟨fun base v amount res hr hvb hok =>
      have hmax := LoanBroker.Reachable.coverClawback_maxValue_fits lb base hr v amount res hok
      LoanBroker.coverClawback_debit_proof lb base hr hmax v hvb amount res hok,
    fun base v a res hr hvb hnt hreq hnz hok => by
      have hmax := LoanBroker.maxValue_fits_of_canonicalOrZero lb a hreq.1 hnz hreq.2.1
      rw [← LoanBroker.coverClawback_debit_proof lb base hr
        (LoanBroker.Reachable.coverClawback_maxValue_fits lb base hr v (some a) res hok) v hvb (some a) res hok]
      exact LoanBroker.coverClawback_debit_le_amount_proof lb base hr hmax v hvb hnt a hreq hnz res hok,
    fun base v amount res hr hvb hnt hok =>
      have hmax := LoanBroker.Reachable.coverClawback_maxValue_fits lb base hr v amount res hok
      LoanBroker.coverClawback_applied_delta_proof lb base hr hmax v hvb hnt amount res hok⟩

end XRPL.Model.Lending
