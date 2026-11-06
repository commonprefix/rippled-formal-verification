import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Witness for the `sharesToAssetsWithdraw` pricing

Each vault comes from a reachable history the model computes: a create, a deposit, then a donation.

* `vI`: an integral vault of 3 assets / 2 shares, one share is worth `1.5` and is priced `2`
  (ties to even), a full half unit above the worth. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.WdPriceWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

/-- An integral vault: deposit `d`, then donate `g`. -/
def intVault (d g : UInt64) : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount d, false), (int64Amount g, true)]

def vI : Vault := intVault 2 1

lemma vI_reach : Vault.Reachable vI 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
/-- One share. -/
def one : STAmount := int64Amount 1

lemma one_canonical : one.Canonical := STAmount.canonical_of_canonicalB _ (by native_decide)

/-- The net asset value a vault's withdrawal prices at, as the model computes it. -/
def nav (v : Vault) : Number := (v.assetsTotalForWithdrawal false).toOption.getD Number.zero

end XRPL.Model.SingleAssetVault.WdPriceWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WdPriceWit

/-- Integral overshoot: one share worth `1.5` is priced `2`. -/
lemma Vault.sharesToAssetsWithdraw_overshoot_witness :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number),
      Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat < assets.toRat :=
  ⟨vI, 0, one, int64Amount 2, false, nav vI, vI_reach, by native_decide, one_canonical, by native_decide,
    fun _ => by native_decide, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
