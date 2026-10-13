import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs

/-! # Witnesses for the tight deposit share and charge bounds

Each is closed by `native_decide` over the model; every result record is computed
by `Vault.deposit`, not written out.

* Shortfall (shares): 3689348814741910330 shares over `10.00000008161533702` assets,
  deposit `2.5`: the product `2^63 + 17` is a tie rounded down to even, the quotient
  ends in `9` and is truncated, for a shortfall of one share plus `99.998%` of
  `ideal·sharesShortε`.
* Overshoot (shares): 1844674407372756839 shares over `9999999999998012.24` assets,
  deposit `5·10^15`: both stages round up by almost a half-step at the top of the
  mantissa range, for an overshoot of `99.999997%` of `ideal·sharesOverε`.
* Charge, lower: assets `0.9999999999999995`, 1 share, deposit `10^15 + 1`: the
  ideal is `10^15 + 0.4999999999999995`, the charge `10^15 - 1`, short by
  `1.4999999999999995 = 3/2 - 5·10⁻¹⁶` steps of the post-deposit grid `10^0`.
* Charge, upper: assets `4.5·10^15`, `3·10^15 + 1` shares, deposit `1.5·10^15`: the
  ideal is `1.5·10^15 - 1/2 + 1/(6·10^15 + 2)`, the charge `1.5·10^15`, over by
  `1/2 - 1/(6·10^15 + 2)` of its last digit. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.DepTightWit

open XRPL.Model.Protocol

/-- A lawful fractional vault with the given totals, all assets available. -/
def rawF (A ST : Number) : RawVault :=
  { assetsTotal := A, assetsAvailable := A, assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ST, lossUnrealized := Number.zero }

/-- The deposit's result, computed by the model. -/
def run (v : Vault) (x : STAmount) (h : 0 < x.toRat) : DepositResult :=
  (v.deposit x false h).toOption.getD (DepositResult.rejected v .tecINTERNAL)

-- shortfall: the product is a tie rounded down, the quotient is truncated from a trailing 9
def vS : Vault := ⟨rawF ⟨false, 1000000008161533702, -17⟩ ⟨false, 3689348814741910330, 0⟩,
  by native_decide, by native_decide⟩
def xS : STAmount := STAmount.unchecked .fractional 2500000000000000 (-15) false
lemma xS_pos : 0 < xS.toRat := by native_decide
def rS : DepositResult := run vS xS xS_pos

-- overshoot: both stages round up by almost a half-step
def vO : Vault := ⟨rawF ⟨false, 9999999999998012240, -3⟩ ⟨false, 1844674407372756839, 0⟩,
  by native_decide, by native_decide⟩
def xO : STAmount := STAmount.unchecked .fractional 5000000000000000 0 false
lemma xO_pos : 0 < xO.toRat := by native_decide
def rO : DepositResult := run vO xO xO_pos

-- charge, lower: a tiny total just under one grid step
def vL : Vault := ⟨rawF ⟨false, 9999999999999995000, -19⟩ ⟨false, 1000000000000000000, -18⟩,
  by native_decide, by native_decide⟩
def xL : STAmount := STAmount.unchecked .fractional 1000000000000001 0 false
lemma xL_pos : 0 < xL.toRat := by native_decide
def rL : DepositResult := run vL xL xL_pos

-- charge, upper: an ideal just past a half-unit, rounded up and kept by the clamp
def vU : Vault := ⟨rawF ⟨false, 4500000000000000000, -3⟩ ⟨false, 3000000000000001000, -3⟩,
  by native_decide, by native_decide⟩
def xU : STAmount := STAmount.unchecked .fractional 1500000000000000 0 false
lemma xU_pos : 0 < xU.toRat := by native_decide
def rU : DepositResult := run vU xU xU_pos

lemma frac_canonical (m : UInt64) (e : Int) (h1 : 10 ^ 15 ≤ m.toNat) (h2 : m.toNat < 10 ^ 16)
    (h3 : (-96 : ℤ) ≤ e) (h4 : e ≤ 80) :
    (STAmount.unchecked .fractional m e false).Canonical :=
  ⟨fun h => absurd h (by simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]),
    fun _ => ⟨rfl, h1, h2, h3, h4⟩⟩

end XRPL.Model.SingleAssetVault.DepTightWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DepTightWit

set_option maxRecDepth 10000

/-- A deposit issues one share plus `99.998%` of `ideal·sharesShortε` fewer than the ideal. -/
lemma Vault.deposit_sharesIssued_shortfall_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.Canonical ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      v.sharesTotal.toRat + r.sharesIssued.toRat ≤ maxRep.toNat ∧
      let ideal := v.idealSharesDeposit roundedAmount.toRat
      let issued := r.sharesIssued.toRat
      1 + ideal * sharesShortε * (99998150 / 10 ^ 8) < ideal - issued :=
  ⟨vS, xS, xS, xS_pos, rS, by native_decide,
    frac_canonical _ _ (by decide) (by decide) (by decide) (by decide), by native_decide, by native_decide,
    by native_decide, by unfold sharesShortε; native_decide⟩

/-- A deposit issues `99.999997%` of `ideal·sharesOverε` more than the ideal. -/
lemma Vault.deposit_sharesIssued_overshoot_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.Canonical ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      v.sharesTotal.toRat + r.sharesIssued.toRat ≤ maxRep.toNat ∧
      let ideal := v.idealSharesDeposit roundedAmount.toRat
      let issued := r.sharesIssued.toRat
      ideal * sharesOverε * (99999997 / 10 ^ 8) < issued - ideal :=
  ⟨vO, xO, xO, xO_pos, rO, by native_decide,
    frac_canonical _ _ (by decide) (by decide) (by decide) (by decide), by native_decide, by native_decide,
    by native_decide, by unfold sharesOverε; native_decide⟩

/-- The `3/2`-grid-step shortfall of `deposit_charge` is attained up to `10⁻¹⁵` of a
step. -/
lemma Vault.deposit_charge_lower_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat) (r : DepositResult)
      (e : ℤ),
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      postSumExponent v.assetsTotal amountDeposit = .ok e ∧
      (3 / 2 - 1 / 10 ^ 15) * (10 : ℚ) ^ e <
        v.idealChargeDeposit r.sharesIssued.toRat - r.amountDeposit'.toRat :=
  ⟨vL, xL, xL_pos, rL, 0, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The half-ULP overcharge of `deposit_charge` is attained up to `10⁻¹⁵` of a unit
of the charge's last digit. -/
lemma Vault.deposit_charge_upper_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat) (r : DepositResult),
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      (1 / 2 - 1 / 10 ^ 15) * (10 : ℚ) ^ r.amountDeposit'.exponent <
        r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat :=
  ⟨vU, xU, xU_pos, rU, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
