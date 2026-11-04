import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Proofs.DepositRedemption
import XRPL.Properties.Vault.Proofs.RoundtripWitness
import XRPL.Properties.Vault.Proofs.DepositTight.Charge
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.ShareWorth

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
    (hcanon : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hty : amountDeposit.mNumericType = v.numericType) -- of the vault's asset
    (r₁ : VaultWithAmounts) (hok₁ : (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁))
    -- the depositor redeems exactly the issued shares from the updated vault, at the same close time
    (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts)
    (hok₂ : (r₁.vault'.withdraw (.vaultShares r₁.shares) waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂)) :
    r₂.assets.toRat ≤ r₁.assets.toRat ∧
      r₁.assets.toRat - r₂.assets.toRat ≤ (10 : ℚ) ^ v.baseExponent :=
  Vault.deposit_withdraw_roundtrip_proof v amountDeposit waiveUnrealizedLoss t t0 hpos hr ht hcanon hty
    (Vault.maxValue_fits_of_canonical v amountDeposit hcanon hty) r₁ hok₁
    (Vault.Reachable.deposit_mint_fits_proof v t0 hr amountDeposit false t hpos hcanon hty r₁ hok₁) hpos₂ r₂ hok₂

/-- Witness for the loss side of `deposit_withdraw_roundtrip`: on a reachable vault the redemption
pays back exactly one step of the base grid less than the charge. -/
theorem Vault.deposit_withdraw_roundtrip_loss_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amountDeposit.toRat) (r₁ : VaultWithAmounts)
      (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁) ∧
      (r₁.vault'.withdraw (.vaultShares r₁.shares) waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂) ∧
      r₁.assets.toRat - r₂.assets.toRat = (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨v, amountDeposit, waiveUnrealizedLoss, t, t0, hpos, r₁, hpos₂, r₂, hr, ht, hcanon, hty, -,
    hok₁, -, hok₂, heq⟩ := Vault.deposit_withdraw_roundtrip_loss_witness
  exact ⟨v, amountDeposit, waiveUnrealizedLoss, t, t0, hpos, r₁, hpos₂, r₂, hr, ht, hcanon, hty,
    hok₁, hok₂, heq⟩

/-- Witness for the gain side of `deposit_withdraw_roundtrip`: on a reachable vault with shares the
redemption can pay back the whole charge. -/
theorem Vault.deposit_withdraw_roundtrip_gain_attained :
    ∃ (v : Vault) (amountDeposit : STAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amountDeposit.toRat) (r₁ : VaultWithAmounts)
      (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁) ∧
      (r₁.vault'.withdraw (.vaultShares r₁.shares) waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂) ∧
      0 < (v.toExact.sharesTotal : ℚ) ∧ r₂.assets.toRat = r₁.assets.toRat := by
  obtain ⟨v, amountDeposit, waiveUnrealizedLoss, t, t0, hpos, r₁, hpos₂, r₂, hr, ht, hcanon, hty, -,
    hok₁, -, hok₂, hS, heq⟩ := Vault.deposit_withdraw_roundtrip_gain_witness
  exact ⟨v, amountDeposit, waiveUnrealizedLoss, t, t0, hpos, r₁, hpos₂, r₂, hr, ht, hcanon, hty,
    hok₁, hok₂, hS, heq⟩

end XRPL.Model.SingleAssetVault
