import XRPL.Properties.Vault.Proofs.CanEmpty
import XRPL.Properties.Vault.Proofs.WithdrawFee
import XRPL.Properties.Vault.Proofs.WithdrawUpdates

/-! # Emptying a vault

A reachable vault can always be emptied. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- When withdrawals are open, a withdrawal of every share from a reachable vault succeeds, pays out
all the cash, and leaves no cash and no shares. -/
lemma Vault.withdraw_all (v : Vault) (t0 t : UInt32) (hr : Vault.Reachable v t0) (waive : Bool)
    (hopen : v.earlyExitFeeRate.isSome = true ∨ v.phase t ≠ .investment)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hall : shares.toRat = v.toExact.sharesTotal) (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧
      r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
      r.vault'.sharesTotal = Number.zero := by
  sorry

/-- Every reachable vault -> it can be emptied, a full withdrawal by shares succeeds outside a fee-free investment
phase, a full withdrawal pays all the cash, a share withdrawal never lacks funds, only a full withdrawal empties it. -/
theorem Vault.Reachable.canEmpty (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) :
    CanEmpty v t0 ∧
    (∀ (t : UInt32) (waive : Bool), (v.earlyExitFeeRate.isSome = true ∨ v.phase t ≠ .investment) →
      ∀ shares : STAmount, shares.Canonical → shares.mNumericType = .int64 →
      shares.toRat = v.toExact.sharesTotal → ∀ hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat,
      ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧
        r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
        r.vault'.sharesTotal = Number.zero) ∧
    (∀ (shares : STAmount) (waiveUnrealizedLoss : Bool) (t : UInt32)
      (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat),
      shares.Canonical →
      shares.toRat ≤ v.toExact.sharesTotal →
      (v.withdraw (.vaultShares shares) waiveUnrealizedLoss t hpos).run ≠ .ok (.error .tecINSUFFICIENT_FUNDS)) ∧
    ∀ (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat),
      amount.amount.Canonical →
      amount.InAsset v.numericType →
      ∀ r : VaultWithAmounts, (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) →
      (r.shares.toRat = v.toExact.sharesTotal → r.assets.toRat = v.assetsAvailable.toRat) ∧
      (r.shares.toRat = v.toExact.sharesTotal ↔
        r.vault'.toRawVault = { v.toRawVault with assetsAvailable := Number.zero, sharesTotal := Number.zero }) := by
  sorry

end XRPL.Model.SingleAssetVault
