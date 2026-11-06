import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.DepositDefs

/-! # Witnesses for the deposit share count and charge

Each run's result is computed by the model and checked by `native_decide`. Every vault comes from a
reachable history: a create, a deposit, then a donation.

* Share shortfall: a scale-10 vault of `10873.632` assets and `100038414774144` shares, deposit
  `100000.0000113088`. The ideal sits `4.1·10⁻⁴` above a whole share, the product rounds down by
  almost half a step and the quotient just below the whole share, which is truncated: more than one
  share short.
* Share overshoot: a scale-10 vault of `100000.0005` assets and `100001000500005` shares, deposit
  `100000.0000899901`. The ideal sits just below a whole share and both stages round up onto it, so
  the deposit issues more shares than the ideal.
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
lemma vS_reach : Vault.Reachable vS 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vO_reach : Vault.Reachable vO 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
def vA : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 none none 0
    [(iouAmount 2000000000000000 0, false), (iouAmount 1000000000000000 0, true)]
def vB : Vault :=
  createHistory.vault Vault.placeholder .int64 0 none none 0 [(int64Amount 2, false), (int64Amount 3, true)]

lemma vA_reach : Vault.Reachable vA 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vB_reach : Vault.Reachable vB 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

def xS : STAmount := iouAmount 1000000000113088 (-10)
def xO : STAmount := iouAmount 1000000000899901 (-10)
def xA : STAmount := iouAmount 1000000000000004 0
def xB : STAmount := int64Amount 3

lemma xS_pos : 0 < xS.toRat := by native_decide
lemma xO_pos : 0 < xO.toRat := by native_decide
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

/-- Share shortfall: fewer shares than the ideal rounded down. -/
lemma Vault.deposit_sharesCreated_shortfall_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit roundedAmount : STAmount) (assetsTotal : Number)
      (hposA : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      r.shares.toRat < ⌊v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat⌋ :=
  ⟨vS, 0, 0, xS, rounded vS xS, total vS, xS_pos, run vS xS xS_pos, vS_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Share overshoot: more shares than the ideal rounded down. -/
lemma Vault.deposit_sharesCreated_overshoot_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit roundedAmount : STAmount) (assetsTotal : Number)
      (hposA : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      (v.deposit amountDeposit false t hposA).run = .ok (.ok r) ∧
      v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat ∧
      ⌊v.idealSharesDepositAt assetsTotal.toRat roundedAmount.toRat⌋ < r.shares.toRat :=
  ⟨vO, 0, 0, xO, rounded vO xO, total vO, xO_pos, run vO xO xO_pos, vO_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- IOU charge above the worth: a reachable IOU deposit charges more than the issued shares are worth. -/
lemma Vault.deposit_charge_overcharge_frac_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = false ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat < r.assets.toRat :=
  ⟨vA, 0, 0, xA, total vA, xA_pos, run vA xA xA_pos, vA_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Integral charge below the worth: a reachable integral deposit charges less than the issued shares are worth. -/
lemma Vault.deposit_charge_undercharge_integral_witness :
    ∃ (v : Vault) (t t0 : UInt32) (amountDeposit : STAmount) (assetsTotal : Number)
      (hpos : 0 < amountDeposit.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ amountDeposit.Canonical ∧ v.assetsTotal = .ok assetsTotal ∧
      (v.deposit amountDeposit false t hpos).run = .ok (.ok r) ∧
      v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent ∧
      v.numericType.isIntegral = true ∧
      r.assets.toRat < v.idealChargeDepositAt assetsTotal.toRat r.shares.toRat :=
  ⟨vB, 0, 0, xB, total vB, xB_pos, run vB xB xB_pos, vB_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
