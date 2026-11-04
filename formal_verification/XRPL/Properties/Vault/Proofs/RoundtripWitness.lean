import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DepositDefs

/-! # Witnesses for the round-trip bounds

Each run's result is computed by the model and checked by `native_decide`. Every vault comes from a
reachable history: a create, a deposit, then a donation.

* Loss: a scale-0 IOU vault of `8407255545351891` assets and `3644134340563550` shares takes a
  deposit of `9000000564015`. The issued shares are worth just below the midpoint under the request,
  the deposit's pricing rounds up onto it and charges the whole request, and the redemption, priced
  lower by the issued shares' fraction of that rounding, rounds down and is floored one step below.
* Full refund: an `int64` vault of 4 assets and 4 shares takes a deposit of 2 and pays it back. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.RtWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

def vL : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 none none 0
    [(iouAmount 3644134340563550 0, false), (iouAmount 4763121204788341 0, true)]
def vE : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount 4, false)]

lemma vL_reach : Vault.Reachable vL 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vE_reach : Vault.Reachable vE 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

def xL : STAmount := iouAmount 9000000564015000 (-3)
def xE : STAmount := int64Amount 2
lemma xL_pos : 0 < xL.toRat := by native_decide
lemma xE_pos : 0 < xE.toRat := by native_decide

/-- A deposit's result, then the redemption of its issued shares, computed by the model. -/
def dep (v : Vault) (x : STAmount) (h : 0 < x.toRat) : VaultWithAmounts :=
  ((v.deposit x false 0 h).run.toOption.bind Except.toOption).getD ⟨⟨x, x⟩, v⟩
def red (r : VaultWithAmounts) (h : 0 < (WithdrawAmount.vaultShares r.shares).amount.toRat) : VaultWithAmounts :=
  ((r.vault'.withdraw (.vaultShares r.shares) false 0 h).run.toOption.bind Except.toOption).getD r

/-- The total a deposit prices at, and the net asset value a redemption prices at, computed by the model. -/
def total (v : Vault) : Number := v.assetsTotal.toOption.getD Number.zero
def nav (v : Vault) : Number := (v.assetsTotalForWithdrawal false).toOption.getD Number.zero

lemma rL_pos : 0 < (WithdrawAmount.vaultShares (dep vL xL xL_pos).shares).amount.toRat := by native_decide
lemma rE_pos : 0 < (WithdrawAmount.vaultShares (dep vE xE xE_pos).shares).amount.toRat := by native_decide

end XRPL.Model.SingleAssetVault.RtWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol RtWit

/-- Loss: the redemption pays back one whole step of the base grid less than the charge. -/
lemma Vault.deposit_withdraw_roundtrip_loss_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amountDeposit.toRat) (r₁ : VaultWithAmounts)
      (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁) ∧
      (v.toExact.sharesTotal : ℚ) + r₁.shares.toRat ≤ 2 ^ 63 - 1 ∧
      (r₁.vault'.withdraw (.vaultShares r₁.shares) waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂) ∧
      r₁.assets.toRat - r₂.assets.toRat = (10 : ℚ) ^ v.baseExponent :=
  ⟨vL, xL, false, 0, 0, xL_pos, dep vL xL xL_pos, rL_pos, red (dep vL xL xL_pos) rL_pos, vL_reach, by decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, fun h => absurd h (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Full refund: the redemption pays back the whole charge. -/
lemma Vault.deposit_withdraw_roundtrip_gain_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amountDeposit.toRat) (r₁ : VaultWithAmounts)
      (hpos₂ : 0 < (WithdrawAmount.vaultShares r₁.shares).amount.toRat) (r₂ : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r₁) ∧
      (v.toExact.sharesTotal : ℚ) + r₁.shares.toRat ≤ 2 ^ 63 - 1 ∧
      (r₁.vault'.withdraw (.vaultShares r₁.shares) waiveUnrealizedLoss t hpos₂).run = .ok (.ok r₂) ∧
      0 < (v.toExact.sharesTotal : ℚ) ∧ r₂.assets.toRat = r₁.assets.toRat :=
  ⟨vE, xE, false, 0, 0, xE_pos, dep vE xE xE_pos, rE_pos, red (dep vE xE xE_pos) rE_pos, vE_reach, by decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, fun _ => by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
