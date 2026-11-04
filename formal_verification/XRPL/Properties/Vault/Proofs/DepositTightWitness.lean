import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.DepositDefs

/-! # Witnesses for the tight deposit share and charge bounds

Each run's result is computed by the model and checked by `native_decide`. Every vault comes from a
reachable history: a create, a deposit, then a donation.

* Share shortfall: a scale-10 vault of `10873.632` assets and `100038414774144` shares, deposit
  `100000.0000113088`. The ideal sits `4.1·10⁻⁴` above a whole share, the product rounds down by
  almost half a step and the quotient just below the whole share, which is truncated: more than one
  share short.
* Share overshoot: a scale-10 vault of `100000.0005` assets and `100001000500005` shares, deposit
  `100000.0000899901`. The ideal sits just below a whole share and both stages round up onto it, so
  the deposit issues more shares than the ideal.
* Charge shortfall: `1999999999999999` assets and `10¹⁵` shares, deposit `2`: one share, worth
  `1.999999999999999`, charged `1`.
* Integral charge past half a unit: `12203` assets and `10270` shares, deposit `8999999999987162`:
  `7574366958933717` shares, worth `8999999999987161.4947…`, charged `8999999999987162`. The 20-digit product rounds
  up and the 19-digit quotient lands on the tie `…161.500`, which rounds to even, up.
* IOU charge above the worth: a scale-0 vault of `3·10^15` assets and `2·10^15` shares, deposit `1000000000000004`:
  `666666666666669` shares, worth `1000000000000003.5`, charged `1000000000000004`. The 16-digit price rounds the
  tie to even, up onto the next base unit, and the floor keeps it.
* Integral charge below the worth: 5 assets and 2 shares, deposit `3`: one share, worth `2.5`, charged `2`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.DepTightWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

def vS : Vault :=
  createHistory.vault Vault.placeholder .fractional 10 none none 0
    [(iouAmount 1000384147741440 (-11), false), (iouAmount 8697905225856000 (-13), true)]
def vO : Vault :=
  createHistory.vault Vault.placeholder .fractional 10 none none 0
    [(iouAmount 1000010005000050 (-11), false), (iouAmount 8999990044999950 (-11), true)]
def vL : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 none none 0
    [(iouAmount 1000000000000000 0, false), (iouAmount 9999999999999990 (-1), true)]
def vM : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount 10270, false), (int64Amount 1933, true)]

lemma vS_reach : Vault.Reachable vS 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vO_reach : Vault.Reachable vO 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vL_reach : Vault.Reachable vL 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vM_reach : Vault.Reachable vM 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

def vA : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 none none 0
    [(iouAmount 2000000000000000 0, false), (iouAmount 1000000000000000 0, true)]
def vB : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount 2, false), (int64Amount 3, true)]

lemma vA_reach : Vault.Reachable vA 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vB_reach : Vault.Reachable vB 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

def xS : STAmount := iouAmount 1000000000113088 (-10)
def xO : STAmount := iouAmount 1000000000899901 (-10)
def xL : STAmount := iouAmount 2000000000000000 (-15)
def xM : STAmount := int64Amount 8999999999987162
def xA : STAmount := iouAmount 1000000000000004 0
def xB : STAmount := int64Amount 3

lemma xS_pos : 0 < xS.toRat := by native_decide
lemma xO_pos : 0 < xO.toRat := by native_decide
lemma xL_pos : 0 < xL.toRat := by native_decide
lemma xM_pos : 0 < xM.toRat := by native_decide
lemma xA_pos : 0 < xA.toRat := by native_decide
lemma xB_pos : 0 < xB.toRat := by native_decide

/-- A deposit's result, computed by the model. -/
def run (v : Vault) (x : STAmount) (h : 0 < x.toRat) : VaultWithAmounts :=
  ((v.deposit x false 0 h).run.toOption.bind Except.toOption).getD ⟨⟨x, x⟩, v⟩

/-- The amount a deposit is rounded to, computed by the model. -/
def rounded (v : Vault) (x : STAmount) : STAmount :=
  ((v.roundedDepositAmount x).run.toOption.bind Except.toOption).getD x

/-- The vault total a deposit prices at, as the model computes it. -/
def total (v : Vault) : Number := v.assetsTotal.toOption.getD Number.zero

end XRPL.Model.SingleAssetVault.DepTightWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DepTightWit

/-- Share shortfall: more than one share below the ideal. -/
lemma Vault.deposit_sharesIssued_shortfall_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit roundedAmount : STAmount) (hposA : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      r.shares.toRat ≤ v.idealSharesDeposit roundedAmount.toRat - 1 :=
  ⟨vS, 0, 0, xS, rounded vS xS, xS_pos, run vS xS xS_pos, vS_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide, by native_decide⟩

/-- Share overshoot: more shares than the ideal. -/
lemma Vault.deposit_sharesIssued_overshoot_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit roundedAmount : STAmount) (hposA : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      v.idealSharesDeposit roundedAmount.toRat < r.shares.toRat :=
  ⟨vO, 0, 0, xO, rounded vO xO, xO_pos, run vO xO xO_pos, vO_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide, by native_decide⟩

/-- `_total` share shortfall: more than one share below the ideal. -/
lemma Vault.deposit_sharesIssued_total_shortfall_witness :
    ∃ (v : Vault) (t : UInt32) (amountDeposit roundedAmount : STAmount) (assetsTotal : Number)
      (hposA : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      r.shares.toRat ≤ v.idealSharesDeposit roundedAmount.toRat - 1 :=
  ⟨vS, 0, xS, rounded vS xS, total vS, xS_pos, run vS xS xS_pos,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- `_total` share overshoot: more shares than the ideal at the computed total. -/
lemma Vault.deposit_sharesIssued_total_overshoot_witness :
    ∃ (v : Vault) (t : UInt32) (amountDeposit roundedAmount : STAmount) (assetsTotal : Number)
      (hposA : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat < r.shares.toRat :=
  ⟨vO, 0, xO, rounded vO xO, total vO, xO_pos, run vO xO xO_pos,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Charge shortfall: the charge falls short of the issued shares' worth by all but `10⁻¹⁵` of one
step of the base grid. -/
lemma Vault.deposit_charge_lower_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDeposit r.shares.toRat - r.assets.toRat = (1 - 1 / 10 ^ 15) * (10 : ℚ) ^ v.baseExponent :=
  ⟨vL, 0, 0, xL, xL_pos, run vL xL xL_pos, vL_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide⟩

/-- Integral charge overshoot: the charge exceeds the issued shares' worth by more than half a unit. -/
lemma Vault.deposit_charge_upper_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.numericType.isIntegral = true ∧ 1 / 2 < r.assets.toRat - v.idealChargeDeposit r.shares.toRat :=
  ⟨vM, 0, 0, xM, xM_pos, run vM xM xM_pos, vM_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide⟩

/-- `_total` charge shortfall: all but `10⁻¹⁵` of one step of the base grid. -/
lemma Vault.deposit_charge_total_lower_witness :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat - r.assets.toRat =
        (1 - 1 / 10 ^ 15) * (10 : ℚ) ^ v.baseExponent :=
  ⟨vL, 0, xL, total vL, xL_pos, run vL xL xL_pos, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- `_total` integral charge overshoot: more than half a unit above the issued shares' worth. -/
lemma Vault.deposit_charge_total_upper_witness :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = true ∧ 1 / 2 < r.assets.toRat - v.idealChargeDeposit r.shares.toRat :=
  ⟨vM, 0, xM, total vM, xM_pos, run vM xM xM_pos, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Integral charge overshoot: more than half a unit above the issued shares' worth. -/
lemma Vault.deposit_charge_integral_witness :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.numericType.isIntegral = true ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      1 / 2 < r.assets.toRat - v.idealChargeDeposit r.shares.toRat :=
  ⟨vM, 0, xM, total vM, xM_pos, run vM xM xM_pos, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- IOU charge above the worth: a reachable IOU deposit charges more than the issued shares are worth. -/
lemma Vault.deposit_charge_overcharge_frac_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.numericType.isIntegral = false ∧ v.idealChargeDeposit r.shares.toRat < r.assets.toRat :=
  ⟨vA, 0, 0, xA, xA_pos, run vA xA xA_pos, vA_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide⟩

/-- Integral charge below the worth: a reachable integral deposit charges less than the issued shares are worth. -/
lemma Vault.deposit_charge_undercharge_integral_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.numericType.isIntegral = true ∧ r.assets.toRat < v.idealChargeDeposit r.shares.toRat :=
  ⟨vB, 0, 0, xB, xB_pos, run vB xB xB_pos, vB_reach, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide⟩

/-- `_total` IOU charge above the worth at the computed total. -/
lemma Vault.deposit_charge_total_overcharge_frac_witness :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = false ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat < r.assets.toRat :=
  ⟨vA, 0, xA, total vA, xA_pos, run vA xA xA_pos, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- `_total` integral charge below the worth at the computed total. -/
lemma Vault.deposit_charge_total_undercharge_integral_witness :
    ∃ (v : Vault) (t : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = true ∧
      r.assets.toRat < v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat :=
  ⟨vB, 0, xB, total vB, xB_pos, run vB xB xB_pos, STAmount.canonical_of_canonicalB _ (by native_decide),
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
