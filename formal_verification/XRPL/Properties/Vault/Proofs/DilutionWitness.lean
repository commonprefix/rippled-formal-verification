import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.DepositDefs

/-! # Witnesses for dilution

Each run's result is computed by the model and checked by `native_decide`. Every vault comes from a
reachable history: a create, a deposit, then a donation.

* Deposit on an IOU: `1999999999999999` assets and `10¹⁵` shares, deposit `2`: one share, worth
  `1.999999999999999`, is charged `1`, so per-share value falls by all but `10⁻¹⁵` of a step spread over
  `10¹⁵ + 1` shares.
* Withdrawal and clawback: 3 assets and 2 shares, redeem (claw back) one share, worth
  `1.5`, for `2`: per-share value falls by exactly half a unit. A zero clawback amount claws a
  one-share holding the same way.
* Deposit, integral: 5 assets and 2 shares, deposit `3`: one share, worth `2.5`, charged `2`, so per-share value
  falls from `2.5` to `7/3`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.DilWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

def intVault (d g : UInt64) : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount d, false), (int64Amount g, true)]

def vL : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 none none 0
    [(iouAmount 1000000000000000 0, false), (iouAmount 9999999999999990 (-1), true)]
def vO : Vault := intVault 2 1
def vB : Vault := intVault 2 3

lemma vL_reach : Vault.Reachable vL 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vO_reach : Vault.Reachable vO 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vB_reach : Vault.Reachable vB 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

def xL : STAmount := iouAmount 2000000000000000 (-15)
lemma xL_pos : 0 < xL.toRat := by native_decide
def xB : STAmount := int64Amount 3
lemma xB_pos : 0 < xB.toRat := by native_decide

def burn (n : UInt64) : WithdrawAmount := .vaultShares (int64Amount n)
lemma burn1_pos : 0 < (burn 1).amount.toRat := by native_decide
def aO : STAmount := int64Amount 2
def aZ : STAmount := int64Amount 0
lemma aO_nn : 0 ≤ aO.toRat := by native_decide
lemma aZ_nn : 0 ≤ aZ.toRat := by native_decide

/-- The holder's balance: one share. A positive clawback amount sets the shares, a zero one claws it. -/
def hold : STAmount := int64Amount 1

lemma hold_balance : hold.ShareBalance := ⟨rfl, STAmount.canonical_of_canonicalB _ (by native_decide), rfl⟩

/-- A deposit's, a withdrawal's and a clawback's result, computed by the model. -/
def depRun (v : Vault) (x : STAmount) (h : 0 < x.toRat) : VaultWithAmounts :=
  ((v.deposit x false 0 h).run.toOption.bind Except.toOption).getD ⟨⟨x, x⟩, v⟩
def wdRun (v : Vault) (a : WithdrawAmount) (h : 0 < a.amount.toRat) : VaultWithAmounts :=
  ((v.withdraw a false 0 h).run.toOption.bind Except.toOption).getD ⟨⟨a.amount, a.amount⟩, v⟩
def clRun (v : Vault) (a : STAmount) (h : 0 ≤ a.toRat) : VaultWithAmounts :=
  ((v.clawback a hold false h).run.toOption.bind Except.toOption).getD ⟨⟨a, a⟩, v⟩

/-- The total a deposit prices at, and the net asset value a withdrawal prices at, as the model
computes them. -/
def total (v : Vault) : Number := v.assetsTotal.toOption.getD Number.zero
end XRPL.Model.SingleAssetVault.DilWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DilWit

/-- Deposit on an IOU: per-share value falls by all but `10⁻¹⁵` of one base step spread over the share total after the
deposit. -/
lemma Vault.deposit_no_dilution_grid_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 ∧ v.numericType.isIntegral = false ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨vL, xL, 0, 0, xL_pos, depRun vL xL xL_pos, vL_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, fun h => absurd h (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide⟩

/-- Withdrawal half unit: per-share value falls, by half a unit of the payout. -/
lemma Vault.withdraw_no_dilution_half_ulp_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool) (t t0 : UInt32)
      (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧ amount.InAsset v.numericType ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.withdraw amount waiveUnrealizedLoss t hpos).run = .ok (.ok r) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨vO, burn 1, false, 0, 0, burn1_pos, wdRun vO (burn 1) burn1_pos, vO_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), rfl, fun _ => by native_decide, by native_decide,
    by native_decide⟩

/-- Clawback half unit: per-share value falls, by half a unit of the recovery. -/
lemma Vault.clawback_no_dilution_half_ulp_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (t0 : UInt32)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.CanonicalOrZero ∧ holderShares.ShareBalance ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨vO, aO, hold, false, 0, aO_nn, clRun vO aO aO_nn, vO_reach,
    Or.inl (STAmount.canonical_of_canonicalB _ (by native_decide)), hold_balance, fun _ => by native_decide,
    by native_decide, by native_decide⟩

/-- Claw-all half unit: a zero amount claws the whole holding, and per-share value falls, by half a unit of
the recovery. -/
lemma Vault.clawback_no_dilution_zero_half_ulp_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (t0 : UInt32)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ assets.CanonicalOrZero ∧ holderShares.ShareBalance ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      assets.isZero = true ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat = holderShares.toRat ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨vO, aZ, hold, false, 0, aZ_nn, clRun vO aZ aZ_nn, vO_reach, Or.inr (by native_decide), hold_balance,
    fun _ => by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide⟩

/-- The net asset value a vault's withdrawal or clawback prices at, as the model computes it. -/
def navAt (v : Vault) : Number := (v.assetsTotalForWithdrawal false).toOption.getD Number.zero

/-- Claw-all overshoot: a zero amount claws a one-share holding worth `1.5` and recovers `2`. -/
lemma Vault.clawback_zero_overshoot_witness :
    ∃ (v : Vault) (assets holderShares : STAmount) (waiveUnrealizedLoss : Bool) (t0 : UInt32)
      (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts) (netAssetValue : Number),
      Vault.Reachable v t0 ∧ holderShares.ShareBalance ∧ assets.isZero = true ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.clawback assets holderShares waiveUnrealizedLoss hnn).run = .ok (.ok r) ∧
      r.shares.toRat = holderShares.toRat ∧
      v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue ∧
      v.idealAssetsWithdrawAt netAssetValue.toRat r.shares.toRat < r.assets.toRat :=
  ⟨vO, aZ, hold, false, 0, aZ_nn, clRun vO aZ aZ_nn, navAt vO, vO_reach, hold_balance, by native_decide,
    fun _ => by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Integral deposit: charged half a unit below the issued share's worth, the deposit lowers per-share value. -/
lemma Vault.deposit_no_dilution_integral_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ amountDeposit.mNumericType = v.numericType ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 ∧ v.numericType.isIntegral = true ∧
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) < v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  ⟨vB, xB, 0, 0, xB_pos, depRun vB xB xB_pos, vB_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
