import XRPL.Properties.Lending.Ledger.Common.VaultPrecision
import XRPL.Properties.Lending.Ledger.Common.CoverWitness
import XRPL.Properties.Lending.Ledger.Common.IntegralPrecision

/-! # associateAsset on the lending ledger

C++ rounds the amounts a transaction writes to the vault's asset with `associateAsset`. On a reachable ledger
the asset stores the vault's amounts, every broker's DebtTotal and every loan's outstanding amounts exactly, but a
default can leave a CoverAvailable it rounds. The theorems leave out AssetsTotal, which the model computes from the
other amounts, and DebtMaximum, which only LoanBrokerSet writes after checking it is on the base grid. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending

variable (l : LendingLedger)

/-- Reachable ledger -> associateAsset rounds none of AssetsAvailable, AssetsDeployed, AssetsReserved, LossUnrealized,
YieldUnrealized, AssetsMaximum, DebtTotal, PrincipalOutstanding, TotalValueOutstanding, ManagementFeeOutstanding. -/
theorem Lending.Reachable.associateAsset_noop (hr : l.Reachable) :
    STAmount.isRounded l.vault.numericType l.vault.assetsAvailable = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsDeployed = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsReserved = false ∧
      STAmount.isRounded l.vault.numericType l.vault.lossUnrealized = false ∧
      STAmount.isRounded l.vault.numericType l.vault.yieldUnrealized = false ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        STAmount.isRounded l.vault.numericType b.debtTotal = false) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
        STAmount.isRounded l.vault.numericType e.loan.principalOutstanding = false ∧
          STAmount.isRounded l.vault.numericType e.loan.totalValueOutstanding = false ∧
          STAmount.isRounded l.vault.numericType e.loan.managementFeeOutstanding = false) ∧
      ∀ m ∈ l.vault.assetsMaximum, STAmount.isRounded l.vault.numericType m = false :=
  LendingLedger.associateAsset_exact_proof l hr

/-- Witness: a run where associateAsset rounds CoverAvailable. A default on a reachable ledger leaves a CoverAvailable
of 17 digits. -/
theorem Lending.Reachable.associateAsset_noop_attained :
    ∃ (l l' : LendingLedger) (b b' : LoanBroker), l.Reachable ∧
      (l.apply (.loanManage 2 .default)).run = .ok (.ok l') ∧ l.broker? 0 = some b ∧ l'.broker? 0 = some b' ∧
      STAmount.isRounded l.vault.numericType b.coverAvailable = false ∧
      STAmount.isRounded l'.vault.numericType b'.coverAvailable = true :=
  let ⟨l, l', b, b', hr, h, hb, hb', h0, h1, _⟩ := LendingLedger.cover_rounded_reachable
  ⟨l, l', b, b', hr, h, hb, hb', h0, h1⟩

/-- associateAsset is a no-op after every loan transaction for integral types: on an XRP or MPT vault the amounts of
`associateAsset_noop` and every broker's CoverAvailable are exact. -/
theorem Lending.Reachable.associateAsset_integral (hr : l.Reachable) (hint : l.vault.numericType.isIntegral = true)
    -- the cover is XRP or MPT the broker's pseudo-account holds, so it stays within the asset's maximum
    (hcap : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
      b.coverAvailable.toRat ≤ l.vault.numericType.maxValue.toNat) :
    (STAmount.isRounded l.vault.numericType l.vault.assetsAvailable = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsDeployed = false ∧
      STAmount.isRounded l.vault.numericType l.vault.assetsReserved = false ∧
      STAmount.isRounded l.vault.numericType l.vault.lossUnrealized = false ∧
      STAmount.isRounded l.vault.numericType l.vault.yieldUnrealized = false ∧
      (∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
        STAmount.isRounded l.vault.numericType b.debtTotal = false) ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e →
        STAmount.isRounded l.vault.numericType e.loan.principalOutstanding = false ∧
          STAmount.isRounded l.vault.numericType e.loan.totalValueOutstanding = false ∧
          STAmount.isRounded l.vault.numericType e.loan.managementFeeOutstanding = false) ∧
      ∀ m ∈ l.vault.assetsMaximum, STAmount.isRounded l.vault.numericType m = false) ∧
    ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
      STAmount.isRounded l.vault.numericType b.coverAvailable = false :=
  LendingLedger.associateAsset_integral_proof l hr hint hcap

end XRPL.Model
