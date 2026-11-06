import XRPL.Properties.Lending.Ledger.Common.DustHolders
import XRPL.Properties.Lending.Ledger.Common.WindDownProofs
import XRPL.Properties.Lending.Ledger.Common.PayoffExit
import XRPL.Properties.Lending.Ledger.Common.PayoffExitWitness
import XRPL.Properties.Lending.Ledger.Common.WindDownRun
import XRPL.Properties.Lending.Ledger.Common.WindDownWitness

/-! # Winding down a vault

Once no broker has a loan, the vault holds only cash. Witnesses for the claims that fail: two holders whose shares
are each worth less than one base unit. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending

/-- LoanCount = 0 for every broker -> AssetsTotal = AssetsAvailable, and AssetsDeployed = LossUnrealized =
AssetsReserved = YieldUnrealized = 0. -/
theorem Lending.Reachable.lifecycle_settles (l : LendingLedger) (hr : l.Reachable)
    (h0 : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.loanCount = 0) :
    l.vault.assetsTotal = .ok l.vault.assetsAvailable ∧ l.vault.assetsDeployed = Number.zero ∧
      l.vault.lossUnrealized = Number.zero ∧ l.vault.assetsReserved = Number.zero ∧
      l.vault.yieldUnrealized = Number.zero :=
  LendingLedger.lifecycle_settles_proof l hr h0

/-- Redemption, every loan closed -> VaultWithdraw of all shares succeeds. The sole holder names every share, and the
withdrawal pays out all the cash and leaves no cash and no shares. -/
theorem Lending.payoff_exit (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (hph : l.vault.phase l.now = .redemption)
    (hclosed : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.paymentRemaining = 0)
    (h : Nat) (hsole : l.isSoleShareholder h = true)
    -- an MPT cash below 2.5·10^17 units. From about 10^18 units the 19-digit price of all the shares can round a
    -- unit above the cash, see `payoff_exit_attained`
    (hmpt : l.vault.numericType = NumericType.int64 → l.vault.assetsAvailable.toRat < 25 * 10 ^ 16) :
    ∃ (shares : STAmount) (l' : LendingLedger), shares.toRat = (l.sharesOf h).toRat ∧
      (l.apply (.vaultWithdraw h (.vaultShares shares))).run = .ok (.ok l') ∧
      l'.vault.assetsAvailable = Number.zero ∧ l'.vault.sharesTotal = Number.zero :=
  LendingLedger.payoff_exit_settled_proof l hr hnd hph hclosed h hsole hmpt

/-- Witness: an MPT vault whose one-day loan is paid 136 years late holds about 1.23·10^18 units. In redemption,
with every loan closed, its sole holder's withdrawal of every share fails with tecINSUFFICIENT_FUNDS. -/
theorem Lending.payoff_exit_attained :
    ∃ (l : LendingLedger) (h : Nat), l.Reachable ∧ l.vaultDeleted = false ∧ l.vault.phase l.now = .redemption ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.paymentRemaining = 0) ∧
      l.isSoleShareholder h = true ∧ l.vault.numericType = NumericType.int64 ∧
      ∀ (shares : STAmount) (l' : LendingLedger), shares.toRat = (l.sharesOf h).toRat →
        (l.apply (.vaultWithdraw h (.vaultShares shares))).run ≠ .ok (.ok l') :=
  LendingLedger.payoff_exit_mpt_witness

/-- Now > RedemptionDate + max GracePeriod -> the vault can be deleted by defaulting loans, deleting loans and brokers,
and withdrawing shares. No VaultDeposit or VaultClawback is needed before VaultDelete succeeds. -/
theorem Lending.Reachable.wind_down (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (s : SingleAssetVault.VaultSchedule) (hs : l.vault.schedule = some s)
    -- the close time is past RedemptionDate, and past RedemptionDate + GracePeriod of every loan
    (hpast : s.redemptionDate < l.now)
    (hgrace : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
      s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat)
    -- with a pending loan the vault is not coarsened. C++ ValidVault rejects its LoanDelete otherwise (FV_M4_22)
    (hpending : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = true → l.NotCoarsened)
    -- with an active loan the vault is not coarsened, where C++ can reject the transfer of its default (FV_M4_27)
    (hactive : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = false →
      e.loan.paymentRemaining ≠ 0 → l.NotCoarsened)
    -- the broker holds its cover as an amount of the asset, a balance the model does not track
    (hca : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.coverAvailable.toRat < 10 ^ 96)
    -- the holders' shares add up to SharesTotal. C++ keeps them so with the share MPT maximum it enforces on a
    -- deposit
    (hsum : l.SharesSum)
    -- while the vault winds down with whole redemptions, no holder is left owning shares worth less than one unit at
    -- the scale of AssetsAvailable (FV_M4_24)
    (hdust : ∀ (txs : List LendingTx) (l' : LendingLedger), l.WindsDownWhole txs l' → (∀ i, l'.loan? i = none) →
      l'.NoDust) :
    ∃ (txs : List LendingTx) (l' : LendingLedger), LendingLedger.Reaches l txs l' ∧ (∀ tx ∈ txs, tx.isWindDown) ∧
      (l'.apply .vaultDelete).run = .ok (.ok { l' with vaultDeleted := true }) :=
  LendingLedger.wind_down_proof l hr hnd s hs hpast hgrace hpending hactive hca hsum hdust

/-- Witness: a run where two holders can never redeem their shares. Past RedemptionDate and loan A's grace period,
with no broker or loan left, each holder's shares are worth half a base unit, so every VaultWithdraw fails. -/
theorem Lending.Reachable.wind_down_attained :
    ∃ (l : LendingLedger) (s : SingleAssetVault.VaultSchedule), l.Reachable ∧ l.vaultDeleted = false ∧
      l.vault.schedule = some s ∧ s.redemptionDate < l.now ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
        s.redemptionDate.toNat + e.loan.schedule.gracePeriod.toNat < l.now.toNat) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = true → l.NotCoarsened) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isPending = false →
        e.loan.paymentRemaining ≠ 0 → l.NotCoarsened) ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      l.SharesSum ∧
      ∀ (txs : List LendingTx) (l' l'' : LendingLedger), LendingLedger.Reaches l txs l' →
        (∀ tx ∈ txs, tx.isWindDown) → (l'.apply .vaultDelete).run ≠ .ok (.ok l'') :=
  LendingLedger.wind_down_dust_witness

end XRPL.Model
