import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.CoverPossible
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackWitness

/-! # `LoanBroker.roundedCoverClawback` and `LoanBroker.coverClawback`

A clawback takes the request, or all cover above minCover when there is none, capped at that excess. On a cover
that is not coarsened it claws that amount floored to whole base units, and CoverAvailable drops by exactly that. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable (lb : LoanBroker)

/-- Cover clawback on any lawful broker, with no amount or amount = 0 -> clawAmount = CoverAvailable − minCover, and
CoverAvailable' = minCover. -/
theorem LoanBroker.roundedCoverClawback_all (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (minimumCover : Number)
    -- CoverAvailable is whole base units, as on every reachable broker, and is not coarsened
    (hf : lb.CoverFits v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent =
      .ok minimumCover)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.amount'.toRat = lb.toExact.coverAvailable - minimumCover.toRat ∧
      res.loanBroker'.toExact.coverAvailable = minimumCover.toRat := by
  sorry

/-- Witness: a run on a coarsened cover where clawAmount > CoverAvailable − minCover and CoverAvailable' < minCover.
A LoanPay fee takes the cover to `2000001` at the scale `10^-10`, and a full clawback leaves `500.1`. -/
theorem LoanBroker.roundedCoverClawback_all_attained :
    ∃ (l : LendingLedger) (j : Nat) (lb : LoanBroker) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      l.Reachable ∧
      l.broker? j = some lb ∧
      l.vault.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum l.vault.baseExponent = .ok minimumCover ∧
      (lb.coverClawback l.vault amount).run = .ok (.ok res) ∧
      lb.toExact.coverAvailable - minimumCover.toRat < res.amount'.toRat ∧
      res.loanBroker'.toExact.coverAvailable < minimumCover.toRat := by
  sorry

/-- Cover clawback on any lawful broker, with amount ≠ 0 -> clawAmount = ⌊min(amount, CoverAvailable − minCover)⌋ at
the scale of CoverAvailable', whole base units when not coarsened, and a larger amount never lowers it. -/
theorem LoanBroker.roundedCoverClawback_capped (v : Vault) (minimumCover : Number)
    -- CoverAvailable is whole base units, as on every reachable broker, and is not coarsened
    (hf : lb.CoverFits v.baseExponent)
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
      ra.amount'.toRat ≤ rb.amount'.toRat := by
  sorry

/-- Witness: a run on a coarsened cover where clawAmount > CoverAvailable − minCover. A LoanPay fee takes the cover
to `2000001` at the scale `10^-10`, and a clawback of `2000000` claws `1999500.9`, not `1999500.8999999999`. -/
theorem LoanBroker.roundedCoverClawback_capped_attained :
    ∃ (l : LendingLedger) (j : Nat) (lb : LoanBroker) (minimumCover : Number) (a : STAmount)
      (res : LoanBrokerCoverResult),
      l.Reachable ∧
      l.broker? j = some lb ∧
      l.vault.numericType = lb.numericType ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum l.vault.baseExponent = .ok minimumCover ∧
      (a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      a.isZero = false ∧
      (lb.coverClawback l.vault (some a)).run = .ok (.ok res) ∧
      (⌊min a.toRat (lb.toExact.coverAvailable - minimumCover.toRat) / 10 ^ l.vault.baseExponent⌋ : ℚ) * 10 ^
        l.vault.baseExponent < res.amount'.toRat := by
  sorry

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
        deltaAmount.toRat = res.amount'.toRat) := by
  sorry

end XRPL.Model.Lending
