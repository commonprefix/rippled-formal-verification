import XRPL.Properties.Lending.Ledger.Common.BrokerProofs
import XRPL.Properties.Lending.Ledger.Common.CoverClawback
import XRPL.Properties.Lending.Ledger.Common.CoverClawbackWitness

/-! # Brokers on the lending ledger

A broker without loans can always leave, and a clawback of a cover that is not coarsened keeps the minimum cover. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending

variable (l : LendingLedger)

/-- Broker with LoanCount = 0 -> LoanBrokerDelete succeeds, and the cover it returns = CoverAvailable. -/
theorem Lending.broker_exit (hr : l.Reachable) (hnd : l.vaultDeleted = false) (j : Nat) (b : LoanBroker)
    (hb : l.broker? j = some b) (h0 : b.loanCount = 0)
    -- the cover is XRP or an MPT the broker's pseudo-account holds, so it stays within the asset's maximum
    (hcap : l.vault.numericType.isIntegral = true → b.coverAvailable.toRat ≤ l.vault.numericType.maxValue.toNat)
    (c : STAmount) (hc : b.roundedCoverAvailable = .ok c) :
    (l.apply (.loanBrokerDelete j)).run = .ok (.ok (l.commitBroker { index := j, broker := none })) ∧
      -- an XRP or MPT cover, or an IOU cover below `10^16` base units. Above that only C++ associateAsset, which the
      -- model does not run, keeps an IOU cover at 16 digits, see `associateAsset_noop_attained`
      (l.vault.numericType.isIntegral = true ∨ b.coverAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
        c.toRat = b.coverAvailable.toRat) :=
  LendingLedger.broker_exit_proof l hr hnd j b hb h0 hcap c hc

/-- Cover clawback -> with no amount or amount = 0, clawAmount = CoverAvailable − minCover and CoverAvailable' =
minCover, and CoverAvailable' ≥ minCover. -/
theorem Lending.coverClawback_minimum (hr : l.Reachable) (l' : LendingLedger) (j : Nat) (amount : Option STAmount)
    (h : (l.apply (.loanBrokerCoverClawback j amount)).run = .ok (.ok l')) (b b' : LoanBroker)
    (hb : l.broker? j = some b) (hb' : l'.broker? j = some b') (r : LoanBrokerCoverResult)
    (hok : (b.coverClawback l.vault amount).run = .ok (.ok r)) (minimumCover : Number)
    (hmin : minimumBrokerCover b.numericType b.debtTotal b.coverRateMinimum l.vault.baseExponent = .ok minimumCover)
    -- the cover is not coarsened
    (hlt : b.coverAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ((amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) →
      r.amount'.toRat = b.coverAvailable.toRat - minimumCover.toRat ∧
        b'.coverAvailable.toRat = minimumCover.toRat) ∧
    minimumCover.toRat ≤ b'.coverAvailable.toRat :=
  LendingLedger.coverClawback_minimum_proof l hr l' j amount h b b' hb hb' r hok minimumCover hmin hlt

/-- Witness: a run on a coarsened cover where a full clawback leaves CoverAvailable' < minCover. A LoanServiceFee
takes the cover to `2000001` at the scale `10^-10`, and the clawback leaves `500.1`. -/
theorem Lending.coverClawback_minimum_attained :
    ∃ (l l' : LendingLedger) (j : Nat) (amount : Option STAmount) (b b' : LoanBroker) (r : LoanBrokerCoverResult)
      (minimumCover : Number), l.Reachable ∧ (l.apply (.loanBrokerCoverClawback j amount)).run = .ok (.ok l') ∧
      l.broker? j = some b ∧ l'.broker? j = some b' ∧ (b.coverClawback l.vault amount).run = .ok (.ok r) ∧
      minimumBrokerCover b.numericType b.debtTotal b.coverRateMinimum l.vault.baseExponent = .ok minimumCover ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧ b'.coverAvailable.toRat < minimumCover.toRat :=
  LendingLedger.coverClawback_minimum_witness

end XRPL.Model
