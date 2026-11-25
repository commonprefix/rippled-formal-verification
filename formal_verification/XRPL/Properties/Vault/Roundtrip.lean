import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Proofs.DepositRedemption
import XRPL.Properties.Vault.Proofs.RoundtripWitness
import XRPL.Properties.Vault.Proofs.DepositTight.Charge
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.ShareWorth
import XRPL.Properties.Vault.Proofs.DepositRunWitness

/-! # Depositing and redeeming returns the taken amount

In exact arithmetic the round trip is the identity, so any difference is rounding. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Depositing into a reachable vault and redeeming the issued shares at the same close time never pays
back more than the charge, and pays back at most one base step less. -/
theorem Vault.deposit_withdraw_roundtrip (v : Vault) (amountDeposit : STAmount) (waiveUnrealizedLoss : Bool)
    (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat)
    (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) -- ledger close times never decrease
    (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (r₁ : VaultWithAmounts) (hok₁ : (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁))
    -- the depositor redeems exactly the issued shares from the updated vault, at the same close time
    (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts)
    (hok₂ : (r₁.vault'.withdraw (.vaultShares r₁.shares) waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂)) :
    r₂.assets.toRat ≤ r₁.assets.toRat ∧
      r₁.assets.toRat - r₂.assets.toRat ≤ (10 : ℚ) ^ v.baseExponent := by
  sorry

/-- Witness for the loss side of `deposit_withdraw_roundtrip`: on a reachable vault the redemption
pays back exactly one step of the base grid less than the charge. -/
theorem Vault.deposit_withdraw_roundtrip_loss_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amountDeposit.toRat) (r₁ : VaultWithAmounts)
      (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts),
      Vault.Reachable v t0 ∧
      t0 ≤ t ∧
      amountDeposit.Canonical ∧
      amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁) ∧
      (r₁.vault'.withdraw (.vaultShares r₁.shares) waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂) ∧
      r₁.assets.toRat - r₂.assets.toRat = (10 : ℚ) ^ v.baseExponent := by
  sorry

/-- Witness for the gain side of `deposit_withdraw_roundtrip`: on a reachable vault with shares the
redemption can pay back the whole charge. -/
theorem Vault.deposit_withdraw_roundtrip_gain_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amountDeposit.toRat) (r₁ : VaultWithAmounts)
      (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts),
      Vault.Reachable v t0 ∧
      t0 ≤ t ∧
      amountDeposit.Canonical ∧
      amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁) ∧
      (r₁.vault'.withdraw (.vaultShares r₁.shares) waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂) ∧
      0 < (v.toExact.sharesTotal : ℚ) ∧
      r₂.assets.toRat = r₁.assets.toRat := by
  sorry

/-- Witness that `n` deposits then a withdrawal of their shares can pay back more than was charged: 100 deposits of
0.03 on an IOU vault are charged 2, each charge rounded down to the vault scale, and their 200 shares pay 2.83. -/
theorem Vault.deposits_withdraw_roundtrip_attained :
    ∃ (v w : Vault) (t0 t : UInt32) (n : ℕ) (charged : ℚ) (shares : STAmount)
      (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧
      t0 ≤ t ∧
      Vault.DepositRun v t w charged shares.toRat n ∧
      1 < n ∧
      (w.withdraw (.vaultShares shares) false t hpos).run = .ok (.ok r) ∧
      charged < r.assets.toRat := by
  sorry

end XRPL.Model.SingleAssetVault
