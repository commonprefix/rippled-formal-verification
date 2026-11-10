import XRPL.Properties.Lending.Ledger.Common.BrokerProofs

/-! # Brokers on the lending ledger

A broker without loans can always leave. -/

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

end XRPL.Model
