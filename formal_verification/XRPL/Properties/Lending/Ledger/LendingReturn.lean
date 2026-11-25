import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Lending.Ledger.Common.WindDownProofs
import XRPL.Properties.Lending.Ledger.Common.AmountRangeWitness

/-! # Ledger transaction exits

Rejections that depend on the whole ledger, not on one vault, broker or loan. A later exit assumes
the earlier checks passed. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault VaultAmounts WithdrawAmount computeDeposit computeWithdraw)

variable (l : LendingLedger)

/-- The VaultDeposit, VaultWithdraw, VaultClawback and VaultDelete exits that depend on the whole ledger. Each line
assumes the checks of its transaction before it passed. -/
theorem Lending.vault_exits :
    -- `amounts` - the deposit's charge and shares, `amountNum` - the charge as a Number
    (∀ (h : Nat) (amount : STAmount) (isDonation : Bool) (roundedAmount : STAmount) (amounts : VaultAmounts)
        (assetsTotal amountNum : Number) (e : Int),
      (LendingTx.vaultDeposit h amount isDonation).preflight l = .tesSUCCESS → l.vaultDeleted = false →
      l.vault.DepositOpen isDonation l.now → (l.vault.roundedDepositAmount amount).run = .ok (.ok roundedAmount) →
      (computeDeposit l.vault roundedAmount isDonation).run = .ok (.ok amounts) →
      l.vault.assetsTotal = .ok assetsTotal → amounts.assets.toNumber .to_nearest = .ok amountNum →
      postSumExponent assetsTotal amountNum l.vault.baseExponent l.vault.numericType = .ok e →
      l.vault.exceedsOpenLimit amountNum = .ok true →
      (l.apply (.vaultDeposit h amount isDonation)).run = .ok (.error .tecLIMIT_EXCEEDED)) ∧
    -- the earlier tecTOO_SOON check passed: the vault has an early-exit fee rate or is not in the investment phase
    (∀ (j : Nat) (e : LoanEntry) (h : Nat) (amount : WithdrawAmount) (amounts : VaultAmounts)
        (sharesTotalAmount : STAmount),
      l.Reachable → l.loan? j = some e → e.loan.principalOutstanding ≠ Number.zero →
      (LendingTx.vaultWithdraw h amount).preflight l = .tesSUCCESS → l.vaultDeleted = false →
      (l.vault.earlyExitFeeRate.isNone && l.vault.phase l.now == .investment) = false →
      (computeWithdraw l.vault amount (l.isSoleShareholder h)).run = .ok (.ok amounts) →
      STAmount.ofNumber .int64 l.vault.sharesTotal .to_nearest = .ok sharesTotalAmount →
      amounts.shares.operator_eq sharesTotalAmount = true →
      (l.apply (.vaultWithdraw h amount)).run = .ok (.error .tecHAS_OBLIGATIONS)) ∧
    (∀ (j : Nat) (e : LoanEntry) (h : Nat) (assets holderShares shares recovered sharesTotalAmount : STAmount),
      l.Reachable → l.loan? j = some e → e.loan.principalOutstanding ≠ Number.zero →
      (LendingTx.vaultClawback h assets).preflight l = .tesSUCCESS → l.vaultDeleted = false →
      STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok holderShares →
      l.vault.ClawbackPriced assets holderShares (l.isSoleShareholder h) shares recovered →
      STAmount.ofNumber .int64 l.vault.sharesTotal .to_nearest = .ok sharesTotalAmount →
      shares.operator_eq sharesTotalAmount = true →
      (l.apply (.vaultClawback h assets)).run = .ok (.error .tecHAS_OBLIGATIONS)) ∧
    (∀ (j : Nat) (b : LoanBroker), l.vaultDeleted = false → l.vault.canVaultDelete = .ok .tesSUCCESS →
      l.broker? j = some b → (l.apply .vaultDelete).run = .ok (.error .tecHAS_OBLIGATIONS)) := by
  sorry

/-- Witness for the first line of `vault_exits`: on a reachable XRP ledger a donation that takes AssetsTotal above the
largest XRP amount ends in an error, not `tecLIMIT_EXCEEDED`. -/
theorem Lending.vault_exits_attained :
    ∃ (l : LendingLedger) (h : Nat) (amount : STAmount) (assetsTotal : Number),
      l.Reachable ∧
      (LendingTx.vaultDeposit h amount true).preflight l = .tesSUCCESS ∧
      l.vault.assetsTotal = .ok assetsTotal ∧
      (10 : ℚ) ^ 17 < assetsTotal.toRat + amount.toRat ∧
      (l.apply (.vaultDeposit h amount true)).run = .error .outOfRange := by
  sorry

end XRPL.Model
