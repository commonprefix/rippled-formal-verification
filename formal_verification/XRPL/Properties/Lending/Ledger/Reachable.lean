import XRPL.Properties.Lending.Ledger.Common.BaseGrid
import XRPL.Properties.Lending.Ledger.Common.DebtInv
import XRPL.Properties.Lending.Ledger.Common.ExtraInterestSum
import XRPL.Properties.Lending.Ledger.Common.IntegralCoverInv
import XRPL.Properties.Lending.Ledger.Common.LoanCountInv
import XRPL.Properties.Lending.Ledger.Common.LossInv
import XRPL.Properties.Lending.Ledger.Common.OpenZoneSteps
import XRPL.Properties.Lending.Ledger.Common.OpenZoneWitness
import XRPL.Properties.Lending.Ledger.Common.ReservedInv
import XRPL.Properties.Lending.Ledger.Common.PhaseProofs
import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Ledger.Common.CapacityMonotone
import XRPL.Properties.Lending.Ledger.Common.CoverOpenZone
import XRPL.Properties.Lending.Ledger.Common.CoverOpenZoneWitness

/-! # Lending ledger reachability

Every reachable vault, broker and loan is lawful, and the vault's balances equal the sums over its brokers and
loans. Each kind of transaction changes only the vault, broker or loan it names. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault)

variable (l l' : LendingLedger) (tx : LendingTx)

/-- Every vault, broker and loan reachable by vault, broker and loan transactions is lawful. -/
theorem Lending.Reachable.lawful (_hr : l.Reachable) :
    (l.vault.toRawVault.WF ∧ l.vault.toRawVault.Valid) ∧
      (∀ b ∈ l.brokers, ∀ lb ∈ b, lb.toRawLoanBroker.WF ∧ lb.toRawLoanBroker.Valid) ∧
      (∀ e ∈ l.loans, ∀ le ∈ e, le.loan.toRawLoan.WF ∧ le.loan.toRawLoan.Valid) :=
  ⟨⟨l.vault.wf, l.vault.valid⟩, fun _ _ lb _ => ⟨lb.wf, lb.valid⟩, fun _ _ le _ => ⟨le.loan.wf, le.loan.valid⟩⟩

/-- Loan transaction -> at most one loan and one broker change, never shares or SharesTotal. LoanBroker transaction ->
at most one broker changes, never loans, shares or the vault. Vault transaction -> no loan or broker. -/
theorem Lending.ops_scope (h : (l.apply tx).run = .ok (.ok l')) :
    (tx.isLoan = true →
      (∃ k : ℕ, ∀ j : ℕ, j ≠ k → l'.loans[j]? = l.loans[j]?) ∧
        (∃ k : ℕ, ∀ j : ℕ, j ≠ k → l'.brokers[j]? = l.brokers[j]?) ∧
        l'.shares = l.shares ∧ l'.vault.sharesTotal = l.vault.sharesTotal) ∧
    (tx.isBroker = true →
      l'.loans = l.loans ∧ l'.shares = l.shares ∧ l'.vault = l.vault ∧
        ∃ k : ℕ, ∀ j : ℕ, j ≠ k → l'.brokers[j]? = l.brokers[j]?) ∧
    (tx.isVault = true ∨ tx = .vaultDelete → l'.loans = l.loans ∧ l'.brokers = l.brokers) :=
  ⟨fun hl => let ⟨hls, hbs, hsh, hst, _⟩ := LendingLedger.loan_ops_scope_proof l l' tx hl h; ⟨hls, hbs, hsh, hst⟩,
    fun hb => LendingLedger.broker_ops_scope_proof l l' tx hb h,
    fun hv => LendingLedger.vault_ops_scope_all_proof l l' tx hv h⟩

/-- Impaired loan with payments left -> when NextPaymentDueDate < now, then only a late payment can pay it. -/
theorem Lending.Reachable.impaired_late (hr : l.Reachable) (j : Nat) (e : LoanEntry) (he : l.loan? j = some e)
    (hi : e.loan.isImpaired = true) (hp : e.loan.paymentRemaining ≠ 0) :
    e.loan.isPaymentLate l.now = true :=
  LendingLedger.impaired_late_proof l hr j e he hi hp

/-- AssetsTotal + YieldUnrealized ≤ the Open limit + extraInterest, where extraInterest = the interest payments
collected beyond the schedule, such as late interest, close interest and overpayment interest. -/
theorem Lending.Reachable.within_open_zone (genesis l : LendingLedger) (txs : List LendingTx)
    (hg : genesis.Genesis) (hrun : LendingLedger.Reaches genesis txs l)
    -- the vault is not coarsened before any step of the sequence
    (hnc : ∀ (pre : List LendingTx) (tx : LendingTx) (l₁ : LendingLedger), pre ++ [tx] <+: txs →
      LendingLedger.Reaches genesis pre l₁ → l₁.NotCoarsened) :
    l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat ≤
      l.openLimit + genesis.extraInterestPaid txs :=
  LendingLedger.within_open_zone_proof genesis l txs _ hg hrun.reachableFromIn_sum
    fun pre tx l₁ _ hp h₁ => hnc pre tx l₁ hp h₁.reaches_sum.1

/-- Witness: a run where deleting a pending loan raises AssetsTotal by rounding. On a coarsened vault a pending
loan of 0.6 is credited back as 1, which leaves the sum 0.4 above the bound. -/
theorem Lending.Reachable.within_open_zone_attained :
    ∃ (genesis l : LendingLedger) (txs : List LendingTx), genesis.Genesis ∧ LendingLedger.Reaches genesis txs l ∧
      ¬ l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat ≤
        l.openLimit + genesis.extraInterestPaid txs := by
  obtain ⟨genesis, l, txs, _, hg, hrun, h⟩ := LendingLedger.within_open_zone_witness
  obtain ⟨hreach, rfl⟩ := hrun.reaches_sum
  exact ⟨genesis, l, txs, hg, hreach, h⟩

/-- AssetsDeployed + YieldUnrealized ≤ the Open limit. -/
theorem Lending.Reachable.deployed_within_open_zone (hr : l.Reachable) :
    l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat ≤ l.openLimit :=
  hr.deployed_yield_le

/-- CoverAvailable ≤ the Open limit + Σ fees the payments paid into the cover. -/
theorem Lending.Reachable.cover_within_open_zone (genesis l : LendingLedger) (txs : List LendingTx)
    (hg : genesis.Genesis) (hrun : LendingLedger.Reaches genesis txs l)
    -- the vault is not coarsened before any step of the sequence
    (hnc : ∀ (pre : List LendingTx) (tx : LendingTx) (l₁ : LendingLedger), pre ++ [tx] <+: txs →
      LendingLedger.Reaches genesis pre l₁ → l₁.NotCoarsened)
    (j : Nat) (b : LoanBroker) (hb : l.broker? j = some b) :
    b.coverAvailable.toRat ≤ l.openLimit + genesis.coverFees j txs :=
  LendingLedger.cover_within_open_zone_proof genesis l txs _ hg hrun.reachableFromIn_sum
    (fun pre tx l₁ _ hp h₁ => hnc pre tx l₁ hp h₁.reaches_sum.1) j b hb

/-- Witness: a run where a default raises the cover past the bound. Broker 1 holds a cover at the Open limit, and on
the coarsened vault defaulting loan B pays the vault a cover of −0.9. -/
theorem Lending.Reachable.cover_within_open_zone_attained :
    ∃ (genesis l : LendingLedger) (txs : List LendingTx) (j : Nat) (b : LoanBroker), genesis.Genesis ∧
      LendingLedger.Reaches genesis txs l ∧ l.broker? j = some b ∧
      ¬ b.coverAvailable.toRat ≤ l.openLimit + genesis.coverFees j txs :=
  let ⟨genesis, l, txs, _, j, b, hg, hrun, hb, h⟩ := LendingLedger.cover_within_open_zone_witness
  ⟨genesis, l, txs, j, b, hg, hrun.reaches_sum.1, hb, h⟩

/-- Regular payment, default, VaultWithdraw or VaultClawback -> AssetsTotal' + YieldUnrealized' ≤ AssetsTotal +
YieldUnrealized. -/
theorem Lending.capacity_monotone (hr : l.Reachable)
    (htx : (∃ i amount, tx = .loanPay i .regular amount) ∨ tx.isOutflow = true)
    (h : (l.apply tx).run = .ok (.ok l'))
    -- an MPT vault and a broker's cover hold less than `2^63` units together, the supply limit the model does not track
    (hsupply : l.vault.numericType = NumericType.int64 → ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
      l.vault.assetsAvailable.toRat + b.coverAvailable.toRat < 2 ^ 63) :
    l'.vault.toRawVault.toExact.assetsTotal + l'.vault.yieldUnrealized.toRat ≤
      l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat :=
  LendingLedger.capacity_monotone_proof l l' tx hr htx h hsupply

/-- On a reachable ledger -> AssetsDeployed, every broker's DebtTotal and LoanCount, LossUnrealized, AssetsReserved
and YieldUnrealized = the matching sums over the vault's brokers and loans. -/
theorem Lending.Reachable.ledger_sums (hr : l.Reachable) :
    l.vault.assetsDeployed.toRat = l.debtSum ∧
    (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.debtTotal.toRat = l.brokerPrincipal j) ∧
    (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.loanCount.toNat = l.loansOf j) ∧
    l.vault.lossUnrealized.toRat = l.principalSum (·.isImpaired) ∧
    l.vault.assetsReserved.toRat = l.principalSum (·.isPending) ∧
    l.vault.yieldUnrealized.toRat = l.interestSum (!·.isPending) :=
  ⟨LendingLedger.assets_lent_proof l hr, LendingLedger.debt_principal_proof l hr, LendingLedger.loanCount_proof l hr,
    LendingLedger.loss_impaired_proof l hr, LendingLedger.reserved_pending_proof l hr,
    LendingLedger.yield_scheduled_proof l hr⟩

/-- LossUnrealized + AssetsReserved ≤ AssetsDeployed. -/
theorem Lending.Reachable.loss_reserved_deployed (hr : l.Reachable) :
    l.vault.lossUnrealized.toRat + l.vault.assetsReserved.toRat ≤ l.vault.assetsDeployed.toRat :=
  LendingLedger.loss_reserved_deployed_proof l hr

/-- AssetsAvailable, AssetsDeployed, AssetsReserved, LossUnrealized, YieldUnrealized and every broker's DebtTotal
and CoverAvailable are whole numbers of base units. -/
theorem Lending.Reachable.base_grid (hr : l.Reachable) :
    Number.OnGrid l.vault.baseExponent l.vault.assetsAvailable ∧
      Number.OnGrid l.vault.baseExponent l.vault.assetsDeployed ∧
      Number.OnGrid l.vault.baseExponent l.vault.assetsReserved ∧
      Number.OnGrid l.vault.baseExponent l.vault.lossUnrealized ∧
      Number.OnGrid l.vault.baseExponent l.vault.yieldUnrealized ∧
      ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        Number.OnGrid l.vault.baseExponent b.debtTotal ∧ Number.OnGrid l.vault.baseExponent b.coverAvailable :=
  LendingLedger.base_grid_all_proof l hr

/-- Reachable ledger, current vault scale = initial vault scale -> a transaction that raises the current vault scale
above the initial vault scale is a payment. -/
theorem Lending.vault_scale_changes (hr : l.Reachable) (h : (l.apply tx).run = .ok (.ok l')) (e e' : Int)
    (he : AssetPool.exponent l.vault l.vault.numericType = .ok e)
    (he' : AssetPool.exponent l'.vault l'.vault.numericType = .ok e')
    (hle : e ≤ l.vault.baseExponent) (hgt : l'.vault.baseExponent < e') :
    ∃ i paymentType amount, tx = .loanPay i paymentType amount :=
  LendingLedger.vault_scale_changes_proof l l' tx hr h e e' he he' hle hgt

end XRPL.Model
