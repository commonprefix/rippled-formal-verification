import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Witnesses for the `sharesToAssetsWithdraw` pricing bounds

Each vault comes from a reachable history the model computes: a create, a deposit, then a donation.

* `vI`: an integral vault of 3 assets / 2 shares, one share is worth `1.5` and is priced `2`
  (ties to even), a full half unit above the worth.
* `vF`: a fractional vault of `2000000000000003` assets / 2 shares, one share is worth
  `1000000000000001.5` and is priced `1000000000000002`, half a ULP above.
* `vW`: an integral vault of `8419983878422141` assets / `13252` shares, and `vWF`, the same as a scale-0 IOU
  vault. `13128` shares are worth `8341197431023684.5040…` and are priced `8341197431023684`: the product needs 21
  digits and rounds down, the quotient lands on the tie `…684.500`, which rounds to even, down. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.WdPriceWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

/-- An integral vault: deposit `d`, then donate `g`. -/
def intVault (d g : UInt64) : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount d, false), (int64Amount g, true)]

/-- A fractional scale-0 vault: deposit 2, then donate `g`. -/
def iouVault (g : UInt64) : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 none none 0
    [(iouAmount 2000000000000000 (-15), false), (iouAmount g 0, true)]

def vW : Vault := intVault 13252 8419983878408889
def vWF : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 none none 0
    [(iouAmount 1325200000000000 (-11), false), (iouAmount 8419983878408889 0, true)]

lemma vW_reach : Vault.Reachable vW 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vWF_reach : Vault.Reachable vWF 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

/-- The shares burned in the `vW` runs. -/
def burnW : STAmount := int64Amount 13128

def vI : Vault := intVault 2 1
def vF : Vault := iouVault 2000000000000001

lemma vI_reach : Vault.Reachable vI 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vF_reach : Vault.Reachable vF 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

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
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧ shares.toRat ≤ v.toExact.sharesTotal ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat < assets.toRat :=
  ⟨vI, 0, one, int64Amount 2, false, vI_reach, by native_decide, one_canonical, by native_decide,
    by native_decide, by native_decide⟩

/-- Fractional overshoot: one share worth `1000000000000001.5` is priced `1000000000000002`. -/
lemma Vault.sharesToAssetsWithdraw_overshoot_frac_witness :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.numericType = .fractional ∧ Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧
      shares.toRat ≤ v.toExact.sharesTotal ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat < assets.toRat :=
  ⟨vF, 0, one, iouAmount 1000000000000002 0, false, by native_decide, vF_reach, by native_decide,
    one_canonical, by native_decide, by native_decide, by native_decide⟩

/-- Integral shortfall: `13128` shares worth `8341197431023684.5040…` are priced `8341197431023684`. -/
lemma Vault.sharesToAssetsWithdraw_shortfall_witness :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧ shares.toRat ≤ v.toExact.sharesTotal ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧ assets.isZero = false ∧
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent <
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat :=
  ⟨vW, 0, burnW, int64Amount 8341197431023684, false, vW_reach, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide⟩

/-- Fractional shortfall: the same `13128` shares on the IOU vault `vWF`, priced `8341197431023684`. -/
lemma Vault.sharesToAssetsWithdraw_shortfall_frac_witness :
    ∃ (v : Vault) (t0 : UInt32) (shares assets : STAmount) (waiveUnrealizedLoss : Bool),
      v.numericType = .fractional ∧ Vault.Reachable v t0 ∧ 0 ≤ shares.toRat ∧ shares.Canonical ∧
      shares.toRat ≤ v.toExact.sharesTotal ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧ assets.isZero = false ∧
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent <
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat :=
  ⟨vWF, 0, burnW, iouAmount 8341197431023684 0, false, by native_decide, vWF_reach, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide⟩

/-- `_total` overshoot: one share worth `1.5` at the computed net asset value is priced `2`. -/
lemma Vault.sharesToAssetsWithdraw_total_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ 0 ≤ shares.toRat ∧
      shares.Canonical ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat < assets.toRat :=
  ⟨vI, one, int64Amount 2, false, nav vI, by native_decide, by native_decide, one_canonical,
    fun _ => by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- `_total` shortfall: the `vW` run, within the Open limit, more than half a unit short of the worth at the
computed net asset value. -/
lemma Vault.sharesToAssetsWithdraw_total_shortfall_witness :
    ∃ (v : Vault) (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (netAssetValue : Number),
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧ 0 ≤ shares.toRat ∧
      shares.Canonical ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      assets.isZero = false ∧
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent <
        v.idealAssetsWithdrawAt netAssetValue.toRat shares.toRat - assets.toRat :=
  ⟨vW, burnW, int64Amount 8341197431023684, false, nav vW, by native_decide, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), fun _ => by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
