import XRPL.Properties.Vault.Proofs.DepositTight
import XRPL.Properties.Vault.Proofs.Reachable

/-! # The charge a deposit takes

On a reachable vault the cash a deposit leaves stays inside the Open zone, so the charge is clamped
onto the base grid. It falls short of the issued shares' worth by less than one step of that grid. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepTight

/-- A deposit charges a nonnegative canonical amount of the vault's asset, or nothing. -/
lemma Vault.deposit_charge_form (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok r)) :
    r.assets.CanonicalOrZero ∧ r.assets.mNumericType = v.numericType ∧ 0 ≤ r.assets.toRat := by
  obtain ⟨ra, amounts, -, hra, hcomp, -, -, -, hras, -⟩ :=
    Vault.deposit_ok_reduces v amountDeposit isDonation t hpos r hok
  have hmax := Vault.maxValue_fits_of_canonical v amountDeposit hcanon hty
  obtain ⟨hra1, hra2, -⟩ := v.roundedDepositAmount_form amountDeposit ra hcanon hty hra
  rw [hras]
  exact computeDeposit_assets_form v ra isDonation amounts hra1 hra2 hmax hcomp

/-- A deposit into an Open-zone vault leaves its cash inside the Open zone, below `9·10^(15+base)`. -/
lemma Vault.OpenZone.deposit_open {v : Vault} (hz : v.OpenZone) (amountDeposit : STAmount)
    (isDonation : Bool) (t : UInt32) (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok r)) :
    v.assetsAvailable.toRat + r.assets.toRat ≤ 9 * (10 : ℚ) ^ (15 + v.baseExponent) := by
  obtain ⟨hAA', hz'⟩ := Vault.deposit_openZone v amountDeposit isDonation t hpos hcanon hty hz r hok
  obtain ⟨k, hk, hkv⟩ := hz'.cash
  rw [← hAA', hkv, Vault.deposit_baseExponent v amountDeposit isDonation t hpos r hok, zpow_add₀ (by norm_num)]
  have hk' : (k : ℚ) ≤ 9 * 10 ^ 15 := by exact_mod_cast hk
  have : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  push_cast
  nlinarith

/-- A deposit that takes nothing happens only on an integral vault, and only when the issued
shares' worth at the computed total, less `sharesε` of it, is at most one half: the charge is priced to nearest. -/
lemma Vault.deposit_charge_zero (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hz : r.assets.isZero = true) :
    v.numericType.isIntegral = true ∧
      v.idealChargeDepositAt navN.toRat r.shares.toRat * (1 - sharesε) ≤ 1 / 2 := by
  obtain ⟨-, priced, navN', -, -, -, -, -, hshc, hshnt, hshpos, hsad, -, hat', hcl, hfnp⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  have hcmv : r.assets.mValue = 0 := by simpa [STAmount.isZero] using hz
  have hty := Vault.deposit_amount_numericType v amountDeposit t hpos hcanon r hok
  obtain ⟨-, hct, -⟩ := Vault.deposit_charge_form v amountDeposit false t hpos hcanon hty r hok
  -- a zero fractional charge fails the zero check, so the vault is integral
  have hint : v.numericType.isIntegral = true := by
    by_contra hfr
    rw [STAmount.isFractionalNonPositive_zero _
      (hct.trans (NumericType.eq_fractional_of_not_integral (by simpa using hfr))) hcmv] at hfnp
    exact absurd (Except.ok.inj hfnp) (by decide)
  refine ⟨hint, ?_⟩
  -- an integral charge is the priced amount, so that is zero too
  have hpnn := sharesToAssetsDeposit_nonneg v r.shares priced hshc hshnt hshpos hsad
  have hpnt := sharesToAssetsDeposit_mNumericType v r.shares priced hsad
  have hcp : r.assets = priced :=
    clampToSumExponent_integral_nonneg navN priced r.assets v.baseExponent
      (by show priced.mNumericType.isIntegral = true; rw [hpnt]; exact hint) hpnn hcl
  have hp0 : priced.toRat = 0 := (STAmount.toRat_eq_zero_iff _).mpr (by rw [← hcp]; exact hcmv)
  have hεnn : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  by_cases hmz : navN.mantissa_ = 0
  · -- an empty vault charges the share count, which is positive
    exfalso
    have := (charge_empty_integral v r.shares priced hint hshc hshnt hshpos navN hat hmz hsad).2
    linarith
  obtain ⟨Q, hQc, hIpos, hQcases⟩ := charge_nonempty v r.shares priced hshc hshnt hshpos navN hat hmz hsad
  rcases hQcases with ⟨-, hQn, hQneg, hQb⟩ | ⟨-, hIsmall⟩
  · -- the priced value rounds to zero, so it is at most one half
    have hh := abs_le.mp (STAmount.ofNumber_integral_within_half v.numericType Q priced hint hQn hQneg hQc)
    have hQb' := abs_le.mp hQb
    rw [hp0] at hh
    nlinarith [hh.1, hQb'.1]
  · -- the priced value underflowed, and the worth is tiny
    have hsmall : (10 : ℚ) ^ (-32700 : ℤ) ≤ 1 / 2 :=
      le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-32700 : ℤ) ≤ -1)) (by norm_num)
    nlinarith [mul_nonneg hIpos.le hεnn]

/-- The charge of a deposit into a reachable vault, within `sharesε` and a rounding step of the issued shares'
worth. A reachable vault prices at its cash exactly, and the clamp grid is the base grid. -/
lemma Vault.Reachable.deposit_charge_proof (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hr : Vault.Reachable v t0) (hcanon : amountDeposit.Canonical)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    r.assets.toRat ≤ amountDeposit.toRat ∧
    v.idealChargeDeposit r.shares.toRat - (10 : ℚ) ^ v.baseExponent < r.assets.toRat ∧
    (r.assets.isZero = true →
      v.numericType.isIntegral = true ∧ v.idealChargeDeposit r.shares.toRat * (1 - sharesε) ≤ 1 / 2) ∧
    r.assets.toRat - v.idealChargeDeposit r.shares.toRat ≤
      v.idealChargeDeposit r.shares.toRat * sharesε + 1 / 2 * (10 : ℚ) ^ r.assets.exponent := by
  have hty := Vault.deposit_amount_numericType v amountDeposit t hpos hcanon r hok
  have hz := Vault.Reachable.openZone_proof v t0 hr (Vault.maxValue_fits_of_canonical v amountDeposit hcanon hty)
  obtain ⟨h1, -, -, h4, h5⟩ :=
    Vault.deposit_charge_at_proof v amountDeposit t hcanon hpos v.assetsAvailable hz.assetsTotal_eq r hok
  have h3 := Vault.deposit_charge_zero v amountDeposit t hcanon hpos v.assetsAvailable hz.assetsTotal_eq r hok
  have hI : v.idealChargeDepositAt v.assetsAvailable.toRat r.shares.toRat = v.idealChargeDeposit r.shares.toRat := by
    rw [← hz.depositNav_eq, RawVault.idealChargeDepositAt_depositNav]
  rw [hI] at h3 h4 h5
  exact ⟨h1, h5, h3, h4⟩

/-- The charge of a deposit into any lawful vault. The sides a lower price can only help keep the exact ideal.
The shortfall sides are measured against the charge at the computed total. -/
lemma Vault.deposit_charge_total_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    r.assets.toRat ≤ amountDeposit.toRat ∧
    v.idealChargeDepositAt navN.toRat r.shares.toRat - (10 : ℚ) ^ v.baseExponent < r.assets.toRat ∧
    (r.assets.isZero = true →
      v.numericType.isIntegral = true ∧
        v.idealChargeDepositAt navN.toRat r.shares.toRat * (1 - sharesε) ≤ 1 / 2) ∧
    r.assets.toRat - v.idealChargeDeposit r.shares.toRat ≤
      v.idealChargeDeposit r.shares.toRat * sharesε + 1 / 2 * (10 : ℚ) ^ r.assets.exponent := by
  obtain ⟨h1, -, -, h4, h5⟩ := Vault.deposit_charge_at_proof v amountDeposit t hcanon hpos navN hat r hok
  refine ⟨h1, h5, Vault.deposit_charge_zero v amountDeposit t hcanon hpos navN hat r hok, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hshpos, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  have hle := Vault.idealChargeDepositAt_le v navN hat r.shares.toRat hshpos.le
  have hεnn : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  nlinarith [mul_le_mul_of_nonneg_right hle hεnn]

end XRPL.Model.SingleAssetVault
