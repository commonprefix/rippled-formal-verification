import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Approx
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs

/-! # Witnesses for the tight deposit share and charge bounds

Each is closed by `native_decide` over the model; every result record is computed
by `Vault.deposit`, not written out.

* Truncation (shares): 1 asset, 2 shares, deposit `0.999999999999999`: the ideal is
  `1.999999999999998`, the vault issues `1` share, short by `1 - 2·10⁻¹⁵` of the
  one-share truncation budget.
* Relative (shares): 1844674407370955163 shares over `99999999999889682.7` assets,
  deposit `5·10^15`: the product `9223372036854775815·10^15` is a tie rounded up by
  `5` in its last place, the quotient rounds up by almost `5` again, for an overshoot
  of `1.0841995·10⁻¹⁸` relative.
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

-- truncation: 1 asset, 2 shares
def vT : Vault := ⟨rawF ⟨false, 1000000000000000000, -18⟩ ⟨false, 2000000000000000000, -18⟩,
  by native_decide, by native_decide⟩
def xT : STAmount := STAmount.unchecked .fractional 9999999999999990 (-16) false
lemma xT_pos : 0 < xT.toRat := by native_decide
def rT : DepositResult := run vT xT xT_pos

-- two-stage relative overshoot of the share count
def vR : Vault := ⟨rawF ⟨false, 9999999999988968270, -2⟩ ⟨false, 1844674407370955163, 0⟩,
  by native_decide, by native_decide⟩
def xR : STAmount := STAmount.unchecked .fractional 5000000000000000 0 false
lemma xR_pos : 0 < xR.toRat := by native_decide
def rR : DepositResult := run vR xR xR_pos

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

end XRPL.Model.SingleAssetVault.DepTightWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DepTightWit

set_option maxRecDepth 10000

/-- The one-share truncation term of `deposit_sharesIssued` is attained up to `10⁻¹⁴`. -/
lemma Vault.deposit_sharesIssued_trunc_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      1 - 1 / 10 ^ 14 <
        v.idealSharesDeposit roundedAmount.toRat * (1 - sharesε) - r.sharesIssued.toRat :=
  ⟨vT, xT, xT, xT_pos, rT, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The share count overshoots the ideal by more than `1.084·10⁻¹⁸` relative, `98.5%`
of the sharp `11·10⁻¹⁹` budget. -/
lemma Vault.deposit_sharesIssued_sharp_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      v.idealSharesDeposit roundedAmount.toRat * (1084 / 10 ^ 21) <
        r.sharesIssued.toRat - v.idealSharesDeposit roundedAmount.toRat :=
  ⟨vR, xR, xR, xR_pos, rR, by native_decide, by native_decide, by native_decide, by native_decide⟩

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
