import XRPL.Properties.Vault.Proofs.DepositTight.Clamp
import XRPL.Properties.Vault.Proofs.DepositTight.Price
import XRPL.Properties.Vault.Proofs.DepositAccuracy
import XRPL.Properties.Vault.Proofs.DepositRounding.Charge
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Vault.Proofs.Support.GridFloor

/-! # Deposit charge pricing facts -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

/-- On an empty integral vault the priced charge is the ideal one exactly. -/
lemma charge_empty_integral (v : Vault) (shares c : STAmount)
    (hint : v.numericType.isIntegral = true)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat) (navN : Number) (hat : v.assetsTotal = .ok navN) (hmz : navN.mantissa_ = 0)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    c.toRat = v.idealChargeDeposit shares.toRat ∧ c.toRat = shares.toRat := by
  have hshmax : shares.mValue.toNat ≤ maxRep.toNat := by
    have hr := hshc.in_range; rw [hshnt] at hr
    calc shares.mValue.toNat ≤ NumericType.int64.maxValue.toNat := hr
      _ = maxRep.toNat := by decide
  unfold sharesToAssetsDeposit at hsad
  obtain ⟨navN', hat', hsad⟩ := bind_ok_peel _ _ _ hsad
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  have hA0 : v.toExact.assetsTotal = 0 := (Vault.assetsTotal_eq_zero_iff v navN hat).mp hmz
  have hscale : v.scale = 0 := v.wf.scale_integral hint
  have hshexp : shares.exponent = 0 := hshc.offset_zero
  have hideal : v.idealChargeDeposit shares.toRat = shares.toRat := by
    unfold RawVault.idealChargeDeposit
    rw [if_pos hA0, hscale]
    show shares.toRat / (10 : ℚ) ^ (0 : UInt8).toNat = shares.toRat
    norm_num
  rw [if_pos hmz] at hsad
  obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  rw [hceq] at hc
  rw [STAmount.checked] at hc
  have hoff0 : (STAmount.unchecked v.numericType shares.mantissa
      (shares.exponent - (v.scale.toNat : ℤ)) false).mOffset = 0 := by
    show shares.exponent - (v.scale.toNat : ℤ) = 0
    rw [hshexp, hscale]; rfl
  have hval0 : (STAmount.unchecked v.numericType shares.mantissa
      (shares.exponent - (v.scale.toNat : ℤ)) false).mValue.toNat ≤ maxRep.toNat := by
    show shares.mantissa.toNat ≤ maxRep.toNat
    exact hshmax
  have hcval := STAmount.canonicalize_integral_toRat _ c .to_nearest
    (show (STAmount.unchecked v.numericType shares.mantissa
      (shares.exponent - (v.scale.toNat : ℤ)) false).integral = true from hint) hoff0 hval0 hc
  have hun : (STAmount.unchecked v.numericType shares.mantissa
      (shares.exponent - (v.scale.toNat : ℤ)) false).toRat = (shares.mValue.toNat : ℚ) := by
    rw [STAmount.toRat_of_offset_zero
      (STAmount.unchecked v.numericType shares.mantissa
        (shares.exponent - (v.scale.toNat : ℤ)) false) hoff0]
    unfold STAmount.signedDrops STAmount.unchecked STAmount.mantissa
    simp
  have hsh : shares.toRat = (shares.mValue.toNat : ℚ) := by
    rw [STAmount.toRat_of_offset_zero shares hshexp]
    unfold STAmount.signedDrops
    rw [STAmount.mIsNegative_false_of_pos shares hshpos]
    simp
  rw [hideal, hcval, hun, hsh]
  exact ⟨rfl, rfl⟩

/-- On an empty vault the charge priced at the computed total is the exact ideal charge. -/
private lemma empty_charge_at (v : Vault) (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hmz : navN.mantissa_ = 0) (shares : ℚ) :
    v.idealChargeDepositAt navN.toRat shares = v.idealChargeDeposit shares := by
  unfold RawVault.idealChargeDepositAt RawVault.idealChargeDeposit
  rw [if_pos (Number.toRat_eq_zero_of_mantissa_zero navN hmz),
    if_pos ((Vault.assetsTotal_eq_zero_iff v navN hat).mp hmz)]

/-- The deposit grid is the post-sum exponent of the computed total and the requested amount. -/
private lemma Vault.depositExponent_reduces (v : Vault) (amountDeposit : STAmount) (e : Int)
    (he : v.depositExponent amountDeposit = .ok e) :
    ∃ (assetsTotal amountNumber : Number), v.assetsTotal = .ok assetsTotal ∧
      amountDeposit.toNumber .to_nearest = .ok amountNumber ∧
      postSumExponent assetsTotal amountNumber v.baseExponent amountDeposit.numericType = .ok e := by
  unfold Vault.depositExponent at he
  obtain ⟨a, ha, he⟩ := bind_ok_peel _ _ _ he
  obtain ⟨n, hn, he⟩ := bind_ok_peel _ _ _ he
  exact ⟨a, n, ha, hn, he⟩

/-- Two canonical amounts on nested grids differ by at least the finer step. -/
private lemma grid_gap (p c : STAmount) (ep : ℤ) (hexp : p.exponent ≤ ep)
    (hc : ∃ z : ℤ, c.toRat = (z : ℚ) * 10 ^ ep) (hlt : c.toRat < p.toRat) :
    c.toRat ≤ p.toRat - 10 ^ p.exponent := by
  obtain ⟨m, hm⟩ := STAmount.exists_int_grid p
  obtain ⟨z, hz⟩ := hc
  have := grid_diff_ge p.toRat c.toRat p.exponent ep m z hm hz hlt
  rw [min_eq_left hexp] at this
  linarith

/-- A charge whose sum stays below the Open-zone limit plus a base step is clamped onto the base grid.
A coarser grid needs a sum of at least `10^(16 + base)`, and the clamp takes off less than one step of it. -/
private lemma clamp_base_of_open (A : Number) (p c : STAmount) (pn : Number) (b ep : ℤ)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hp : p.IOUCanonical) (hppos : 0 < p.toRat)
    (hlo : -96 ≤ b) (hhi : b ≤ 80) (hpn : p.toNumber .to_nearest = .ok pn)
    (hep : postSumExponent A pn b .fractional = .ok ep)
    (hcl : clampToSumExponent A p b = .ok c) (hc : c.mValue ≠ 0)
    (hopen : A.toRat + c.toRat < 9 * (10 : ℚ) ^ (15 + b) + 10 ^ b) : ep = b := by
  obtain ⟨hge, hep_lo, hep_hi⟩ := postSumExponent_range _ _ _ _ _ hlo hhi hep
  by_contra hne
  have hgt : b < ep := lt_of_le_of_ne hge (Ne.symm hne)
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact p .to_nearest hp
  rw [hsn, Except.ok.injEq] at hpn
  subst hpn
  obtain ⟨s, hs, hne'⟩ := postSumExponent_reduces _ _ _ _ _ hep
  have hr1 := operator_add_rounded_to_nearest _ _ _ hA hsnn hs
  have hsn' := operator_add_isNormalized_to_nearest_sz _ _ _ hA hsnn hs
  have hs0 : 0 ≤ s.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg s _ hr1 (by rw [hsnv]; linarith)
  obtain ⟨-, hlarge⟩ := numberExponent_frac_lower s _ ep hsn' hs0 (by omega) hne' hgt
  -- the sum is above the largest 19-digit `Number` below `10 ^ (ep + 15)`
  obtain ⟨y, hyn, hyv⟩ := Exact.exists_normalized_grid (10 ^ 18 - 1) (ep - 3) (by norm_num) (by norm_num)
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hpe : (0 : ℚ) < 10 ^ ep := zpow_pos (by norm_num) _
  have hy : y.toRat = 10 ^ ep * 10 ^ 15 - 10 ^ ep / 1000 := by
    rw [hyv, zpow_sub₀ (by norm_num)]
    push_cast
    ring
  have hgtY : y.toRat < A.toRat + sn.toRat := by
    by_contra hle
    push Not at hle
    have := Number.RoundsToRepresentable.le_of_le_normalized s _ hr1 y hyn hle
    have h15 : (10 : ℚ) ^ (ep + 15) = 10 ^ ep * 10 ^ 15 := by rw [zpow_add₀ (by norm_num)]; norm_num
    rw [h15] at hlarge
    have : (0 : ℚ) < 10 ^ ep / 1000 := by positivity
    linarith
  -- the clamp takes off less than one step of the post-sum grid
  have hclow := clamp_sum_ge A p c sn b ep hp hppos hlo hhi hsn hep hcl hc
  have hstep : 10 * (10 : ℚ) ^ b ≤ 10 ^ ep := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 10) (show b + 1 ≤ ep by omega)
    rw [zpow_add_one₀ (by norm_num)] at h
    linarith
  have h9 : 9 * (10 : ℚ) ^ (15 + b) = 9 * 10 ^ 15 * 10 ^ b := by rw [zpow_add₀ (by norm_num)]; norm_num; ring
  have hb : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  rw [hsnv] at hgtY
  nlinarith

/-- The grid point above a floored amount lies a whole unit of the amount above it. -/
private lemma floor_next_grid (p : STAmount) (ep : ℤ) (hexp : p.exponent ≤ ep) :
    p.toRat + 10 ^ p.exponent ≤ ((⌊p.toRat / 10 ^ ep⌋ : ℚ) + 1) * 10 ^ ep := by
  obtain ⟨m, hm⟩ := STAmount.exists_int_grid p
  have hpe : (0 : ℚ) < 10 ^ ep := zpow_pos (by norm_num) _
  have hlt : p.toRat < ((⌊p.toRat / 10 ^ ep⌋ : ℚ) + 1) * 10 ^ ep := by
    have h := Int.lt_floor_add_one (p.toRat / 10 ^ ep)
    rw [div_lt_iff₀ hpe] at h
    linarith
  have := grid_diff_ge (((⌊p.toRat / 10 ^ ep⌋ : ℚ) + 1) * 10 ^ ep) p.toRat ep p.exponent
    (⌊p.toRat / 10 ^ ep⌋ + 1) m (by push_cast; ring) hm hlt
  rw [min_eq_right hexp] at this
  linarith

/-- The to-nearest pricing never rounds below a grid point the worth reaches. A charge priced within half
a unit of a value within `sharesε` of the worth `I`, then floored onto a no finer grid, stays above `I` less a step. -/
private lemma floor_charge_gt (p c : STAmount) (Q I : ℚ) (ep : ℤ) (hp : p.IOUCanonical) (hppos : 0 < p.toRat)
    (hexp : p.exponent ≤ ep) (hc : c.toRat = (⌊p.toRat / 10 ^ ep⌋ : ℚ) * 10 ^ ep)
    (hpQ : |p.toRat - Q| ≤ 1 / 2 * (10 : ℚ) ^ p.exponent) (hQI : |Q - I| ≤ I * sharesε) :
    I - 10 ^ ep < c.toRat := by
  by_contra hle
  push Not at hle
  have hX : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  -- the next point of the grid lies a whole unit above the priced charge, and at most at the worth
  have hstep := floor_next_grid p ep hexp
  rw [hc] at hle
  -- so the worth sits half a unit above the priced number, yet within `sharesε` of it
  have hpQ' := abs_le.mp hpQ
  have hQI' := abs_le.mp hQI
  have hbd := (STAmount.IOUCanonical.toRat_bounds p hp hppos).2
  have h16 : (10 : ℚ) ^ (p.exponent + 16) = 10 ^ 16 * 10 ^ p.exponent := by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  rw [h16] at hbd
  unfold sharesε at hQI'
  linarith [hpQ'.1, hpQ'.2, hQI'.1, hQI'.2]

/-- The charge of a fractional vault: the priced value is a positive canonical amount that the clamp floors
onto the base grid, since the inflow check keeps the total inside the Open zone. -/
private lemma frac_charge_floor (v : Vault) (navN : Number) (hat : v.assetsTotal = .ok navN)
    (shares priced c : STAmount) (hint : v.numericType.isIntegral = false)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64) (hshpos : 0 < shares.toRat)
    (hsad : sharesToAssetsDeposit v shares = .ok priced)
    (hcl : clampToSumExponent navN priced v.baseExponent = .ok c)
    (hfnp : c.isFractionalNonPositive = .ok false)
    (hop : navN.toRat + c.toRat < 9 * (10 : ℚ) ^ (15 + v.baseExponent) + 10 ^ v.baseExponent) :
    priced.IOUCanonical ∧ priced.mValue ≠ 0 ∧ 0 < priced.toRat ∧ c.IOUCanonical ∧ c.mValue ≠ 0 ∧
      priced.exponent ≤ v.baseExponent ∧
      c.toRat = (⌊priced.toRat / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent ∧
      ∃ pn : Number, priced.toNumber .to_nearest = .ok pn ∧
        postSumExponent navN pn v.baseExponent .fractional = .ok v.baseExponent := by
  have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral hint
  have hpfr : priced.mNumericType = .fractional := by
    rw [sharesToAssetsDeposit_mNumericType v shares priced hsad, hvfr]
  have hpint : priced.integral = false := by unfold STAmount.integral; rw [hpfr]; rfl
  have hpcz : priced.FracCanonZero := ⟨hpfr, by
    rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares priced hshc hshnt hsad with h | h
    · exact Or.inl (h.iouCanonical hpint)
    · exact Or.inr h⟩
  have hshape := clampToSumExponent_frac_shape navN priced c v.baseExponent hpcz hcl
  -- a fractional charge that survives the zero check is nonzero
  have hcmv : c.mValue ≠ 0 := by
    intro h0
    rw [STAmount.isFractionalNonPositive_zero _ hshape.1 h0] at hfnp
    exact absurd (Except.ok.inj hfnp) (by decide)
  have hpmv : priced.mValue ≠ 0 := fun h => hcmv (clampToSumExponent_zero navN priced c _ h hcl)
  have hpiou : priced.IOUCanonical := hpcz.2.resolve_right hpmv
  have hppos : 0 < priced.toRat :=
    lt_of_le_of_ne (sharesToAssetsDeposit_nonneg v shares priced hshc hshnt hshpos hsad)
      (Ne.symm (STAmount.toRat_ne_zero priced hpmv))
  obtain ⟨hAn, hAD⟩ := Vault.assetsTotal_ge_deployed v navN hat
  have hA0 : 0 ≤ navN.toRat := le_trans v.exact.assetsDeployed_nonneg hAD
  obtain ⟨hlo, hhi⟩ := v.baseExponent_range
  obtain ⟨pn, hpn, -, -⟩ := STAmount.toNumber_iou_exact priced .to_nearest hpiou
  obtain ⟨pn', ep, hpn', hep, -, hcval⟩ :=
    clampToSumExponent_frac_floor navN priced c v.baseExponent hpcz hlo hhi hcmv hcl
  rw [hpn, Except.ok.injEq] at hpn'
  subst hpn'
  rw [show priced.numericType = .fractional from hpfr] at hep
  have hpexp := post_exp_ge navN priced pn v.baseExponent ep hAn hA0 hpiou hppos hpn hep
  have hepb : ep = v.baseExponent :=
    clamp_base_of_open navN priced c pn v.baseExponent ep hAn hA0 hpiou hppos hlo hhi hpn hep hcl hcmv hop
  subst hepb
  exact ⟨hpiou, hpmv, hppos, hshape.2.resolve_right hcmv, hcmv, hpexp, by rw [hcval, abs_of_pos hppos],
    pn, hpn, hep⟩

end XRPL.Model.SingleAssetVault.DepTight

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

/-- A successful deposit is of the vault's asset: the charge it prices has the vault's type, and
the request's. -/
lemma Vault.deposit_amount_numericType (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    amountDeposit.mNumericType = v.numericType := by
  obtain ⟨ra, priced, -, hra, hrc, hrp, -, -, hshc, hshnt, -, hsad, hgt, -, -, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  obtain ⟨-, hpty⟩ := DepAcc.Vault.deposit_priced_le v r.shares priced ra hshc hshnt hsad hrc hrp hgt
  obtain ⟨navR, -, hclR, -⟩ := roundedDepositAmount_rounded v amountDeposit ra hra
  obtain ⟨hlo, hhi⟩ := v.baseExponent_range
  obtain ⟨-, hraty, -⟩ := clampToSumExponent_canonicalOrZero navR amountDeposit ra v.baseExponent
    (Or.inl hcanon) hlo hhi hclR
  rw [← hraty, ← hpty, sharesToAssetsDeposit_mNumericType v r.shares priced hsad]

/-- A successful deposit keeps the total below the Open-zone limit plus one base step, on any valid
vault: the inflow check compares a capacity that never rounds below the total plus the charge. -/
lemma Vault.deposit_open_bound (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType) (navN : Number) (hat : v.assetsTotal = .ok navN)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok r)) :
    navN.toRat + r.assets.toRat < 9 * (10 : ℚ) ^ (15 + v.baseExponent) + 10 ^ v.baseExponent := by
  obtain ⟨ra, amounts, -, hra, hcomp, hin, -, -, hras, -⟩ :=
    Vault.deposit_ok_reduces v amountDeposit isDonation t hpos r hok
  have hmax := Vault.maxValue_fits_of_canonical v amountDeposit hcanon hty
  obtain ⟨hra1, hra2, -⟩ := v.roundedDepositAmount_form amountDeposit ra hcanon hty hra
  obtain ⟨hac, -, hac0⟩ := computeDeposit_assets_form v ra isDonation amounts hra1 hra2 hmax hcomp
  rw [hras]
  exact Vault.checkOpenLimit_bound v amounts.assets hac hac0 navN hat hin

/-- Tight deposit charge bound, priced at the computed total. The charge never exceeds the request and stays
within one base step below the shares' worth: in the Open zone the pricing error never crosses a base grid point. -/
lemma Vault.deposit_charge_at_proof (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    r.assets.toRat ≤ amountDeposit.toRat ∧
    (∀ e, v.depositExponent amountDeposit = .ok e →
      v.idealChargeDepositAt navN.toRat r.shares.toRat * (1 - sharesε) - (10 : ℚ) ^ e ≤ r.assets.toRat) ∧
    (r.assets.isZero = true →
      v.idealChargeDepositAt navN.toRat r.shares.toRat * (1 - sharesε) <
        if v.numericType.isIntegral then 1 else (10 : ℚ) ^ (-81 : ℤ)) ∧
    r.assets.toRat - v.idealChargeDepositAt navN.toRat r.shares.toRat ≤
      v.idealChargeDepositAt navN.toRat r.shares.toRat * sharesε + 1 / 2 * (10 : ℚ) ^ r.assets.exponent ∧
    v.idealChargeDepositAt navN.toRat r.shares.toRat - (10 : ℚ) ^ v.baseExponent < r.assets.toRat := by
  obtain ⟨ra, priced, navN', hra, hrc, hrp, hats, hshz, hshc, hshnt, hshpos, hsad, hgt, hat', hcl, hfnp⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  obtain ⟨hAn, hAD⟩ := Vault.assetsTotal_ge_deployed v navN hat
  have hA0 : 0 ≤ navN.toRat := le_trans v.exact.assetsDeployed_nonneg hAD
  have hεnn : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  have hpnn := sharesToAssetsDeposit_nonneg v r.shares priced hshc hshnt hshpos hsad
  have hpnt := sharesToAssetsDeposit_mNumericType v r.shares priced hsad
  have hcle := DepRnd.Vault.deposit_charge_le v r.shares priced r.assets navN hshc hshnt hshpos hsad hcl
  have hcnn := DepAcc.Vault.deposit_charge_nonneg v r.shares priced r.assets navN hshc hshnt hshpos hsad hcl
  obtain ⟨hple, hpty⟩ := DepAcc.Vault.deposit_priced_le v r.shares priced ra hshc hshnt hsad hrc hrp hgt
  -- the rounded amount never exceeds the request, and keeps its asset
  obtain ⟨navR, hatR, hclR, -⟩ := roundedDepositAmount_rounded v amountDeposit ra hra
  rw [hat, Except.ok.injEq] at hatR
  subst hatR
  obtain ⟨hlo, hhi⟩ := v.baseExponent_range
  obtain ⟨-, hraty, -⟩ := clampToSumExponent_canonicalOrZero navN amountDeposit ra v.baseExponent
    (Or.inl hcanon) hlo hhi hclR
  have hrale : ra.toRat ≤ amountDeposit.toRat := by
    have h := clampToSumExponent_le_abs navN amountDeposit ra v.baseExponent (Or.inl hcanon) hlo hhi hclR
    rwa [abs_of_pos hpos] at h
  have hxty : amountDeposit.mNumericType = v.numericType := by rw [← hraty, ← hpty, hpnt]
  have hop := Vault.deposit_open_bound v amountDeposit false t hpos hcanon hxty navN hat r hok
  refine ⟨by linarith, ?_⟩
  by_cases hint : v.numericType.isIntegral = true
  · -- integral vault
    have hcp : r.assets = priced :=
      clampToSumExponent_integral_nonneg navN priced r.assets v.baseExponent
        (by show priced.mNumericType.isIntegral = true; rw [hpnt]; exact hint) hpnn hcl
    rw [hcp] at hop ⊢
    have hbase : v.baseExponent = 0 := (Vault.baseExponent_bounds v).2.2 hint
    have hge1 : ∀ e, v.depositExponent amountDeposit = .ok e → (1 : ℚ) ≤ 10 ^ e := by
      intro e he
      obtain ⟨_, _, _, _, hps⟩ := Vault.depositExponent_reduces v amountDeposit e he
      obtain ⟨_, _, hne⟩ := postSumExponent_reduces _ _ _ _ e hps
      have := numberExponent_ge _ _ _ e hne
      exact one_le_zpow₀ (by norm_num) (by omega)
    have hpexp : priced.exponent = 0 :=
      (sharesToAssetsDeposit_integral_canonical v r.shares priced hint hsad).1.offset_zero
    have hb1 : (1 : ℚ) ≤ 10 ^ v.baseExponent := by rw [hbase, zpow_zero]
    by_cases hmz : navN.mantissa_ = 0
    · obtain ⟨hex, hexs⟩ := charge_empty_integral v r.shares priced hint hshc hshnt hshpos navN hat hmz hsad
      rw [← empty_charge_at v navN hat hmz] at hex
      refine ⟨fun e he => ?_, fun hz => ?_, ?_, ?_⟩
      · have h1 := hge1 e he
        rw [← hex]
        nlinarith [mul_nonneg hpnn hεnn]
      · exfalso
        have hz' : priced.toRat = 0 :=
          (STAmount.toRat_eq_zero_iff priced).mpr (beq_iff_eq.mp (by simpa [STAmount.isZero] using hz))
        linarith
      · rw [hex, sub_self]
        have : 0 ≤ v.idealChargeDepositAt navN.toRat r.shares.toRat := by rw [← hex]; exact hpnn
        positivity
      · rw [← hex]
        nlinarith [mul_nonneg hpnn hεnn]
    obtain ⟨Q, hQc, hIpos, hQcases⟩ :=
      charge_nonempty v r.shares priced hshc hshnt hshpos navN hat hmz hsad
    rcases hQcases with ⟨-, hQn, hQneg, hQb⟩ | ⟨hQm, hIsmall⟩
    · have hQb' := abs_le.mp hQb
      have hh' := abs_le.mp (STAmount.ofNumber_integral_within_half v.numericType Q priced hint hQn hQneg hQc)
      refine ⟨fun e he => ?_, fun hz => ?_, ?_, ?_⟩
      · have h1 := hge1 e he
        nlinarith
      · have hz' : priced.toRat = 0 :=
          (STAmount.toRat_eq_zero_iff priced).mpr (beq_iff_eq.mp (by simpa [STAmount.isZero] using hz))
        rw [if_pos hint]
        nlinarith
      · rw [hpexp, zpow_zero]
        linarith
      · -- the cash bound keeps the charge below `9·10^15`, where the pricing error is under half a unit
        rw [hbase] at hop ⊢
        rw [zpow_zero]
        norm_num at hop
        unfold sharesε at hQb'
        linarith [hQb'.1, hQb'.2, hh'.1, hh'.2]
    · -- the priced number underflowed: nothing is charged and the ideal is tiny
      have hp0 : priced.toRat = 0 := by
        by_contra hne
        exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .to_nearest priced hint hQc
          (fun h => hne ((STAmount.toRat_eq_zero_iff priced).mpr h)) hQm
      have htiny : v.idealChargeDepositAt navN.toRat r.shares.toRat < 1 :=
        lt_of_le_of_lt hIsmall (zpow_lt_one_of_neg₀ (by norm_num) (by norm_num))
      refine ⟨fun e he => ?_, fun _ => ?_, ?_, ?_⟩
      · have h1 := hge1 e he
        rw [hp0]
        nlinarith
      · rw [if_pos hint]
        nlinarith
      · rw [hp0]
        have : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
        nlinarith [mul_nonneg hIpos.le hεnn]
      · rw [hp0]
        nlinarith
  · -- fractional vault
    obtain ⟨hpiou, hpmv, hppos, hRiou, hcmv, hpexp, hcval', pn, hpn, hep⟩ := frac_charge_floor v navN hat
      r.shares priced r.assets (by simpa using hint) hshc hshnt hshpos hsad hcl hfnp hop
    have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    have hrpos : 0 < r.assets.toRat := lt_of_le_of_ne hcnn (Ne.symm (STAmount.toRat_ne_zero _ hcmv))
    -- the to-nearest pricing and the floor onto the base grid lose less than one step of it
    obtain ⟨-, hL⟩ :=
      STAmount.IOUCanonical.floor_bounds priced r.assets v.baseExponent hpiou hRiou hrpos hcval'
    have hre : (10 : ℚ) ^ r.assets.exponent ≤ 10 ^ v.baseExponent := zpow_le_zpow_right₀ (by norm_num)
      (le_trans (STAmount.IOUCanonical.exponent_le _ _ hRiou hpiou hrpos hcle) hpexp)
    have hlow : priced.toRat + 1 / 2 * (10 : ℚ) ^ priced.exponent - 10 ^ v.baseExponent ≤ r.assets.toRat := by
      have : (0 : ℚ) < 10 ^ r.assets.exponent := zpow_pos (by norm_num) _
      have hm : max (1 / 2 * (10 : ℚ) ^ r.assets.exponent)
          ((10 : ℚ) ^ v.baseExponent - 1 / 2 * (10 : ℚ) ^ r.assets.exponent) ≤ 10 ^ v.baseExponent :=
        max_le (by linarith) (by linarith)
      linarith
    -- the base grid is never coarser than the grid of the request
    have hepe : ∀ e, v.depositExponent amountDeposit = .ok e → (10 : ℚ) ^ v.baseExponent ≤ 10 ^ e := by
      intro e he
      obtain ⟨navE, an, hatE, han, hps⟩ := Vault.depositExponent_reduces v amountDeposit e he
      rw [hat, Except.ok.injEq] at hatE
      subst hatE
      obtain ⟨an', han', hanv, hann⟩ := STAmount.toNumber_canonical_exact amountDeposit .to_nearest hcanon
      rw [han', Except.ok.injEq] at han
      subst han
      obtain ⟨pn', hpn', hpnv, hpnn'⟩ := STAmount.toNumber_iou_exact priced .to_nearest hpiou
      rw [hpn, Except.ok.injEq] at hpn'
      subst hpn'
      rw [show amountDeposit.numericType = .fractional by show amountDeposit.mNumericType = _; rw [hxty, hvfr]]
        at hps
      exact zpow_le_zpow_right₀ (by norm_num) (postSumExponent_mono navN pn an' v.baseExponent v.baseExponent
        e hAn hA0 hpnn' hann (by rw [hpnv]; exact hpnn) (by rw [hpnv, hanv]; linarith) hlo hep hps)
    have hgrid : ∃ z : ℤ, r.assets.toRat = (z : ℚ) * 10 ^ v.baseExponent := ⟨_, hcval'⟩
    have hcz : r.assets.isZero = false := by simpa [STAmount.isZero] using hcmv
    by_cases hmz : navN.mantissa_ = 0
    · have hex := empty_frac_charge_exact v ra r.shares priced (by simpa using hint) navN hat hmz hrc hrp
        (by rw [hraty, hxty, hvfr]) hats hshz hsad
      rw [← empty_charge_at v navN hat hmz] at hex
      have hp0 : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
      refine ⟨fun e he => ?_, fun hz => absurd hz (by rw [hcz]; decide), ?_, ?_⟩
      · have h1 := hepe e he
        rw [← hex]
        nlinarith [mul_nonneg hpnn hεnn]
      · have : (0 : ℚ) < 10 ^ r.assets.exponent := zpow_pos (by norm_num) _
        rw [← hex]
        nlinarith [mul_nonneg hpnn hεnn]
      · rw [← hex]
        nlinarith [mul_nonneg hpnn hεnn]
    obtain ⟨Q, hQc, hIpos, hQcases⟩ :=
      charge_nonempty v r.shares priced hshc hshnt hshpos navN hat hmz hsad
    rcases hQcases with ⟨hQm, hQn, -, hQb⟩ | ⟨hQm, -⟩
    · have hQb' := abs_le.mp hQb
      rw [hvfr] at hQc
      have hh' := abs_le.mp (STAmount.ofNumber_iou_to_nearest_within_half Q priced hQn hQm hQc hpmv)
      refine ⟨fun e he => ?_, fun hz => absurd hz (by rw [hcz]; decide), ?_, ?_⟩
      · have h1 := hepe e he
        nlinarith
      rotate_left
      · have h2 := floor_charge_gt priced r.assets Q.toRat _ v.baseExponent hpiou hppos hpexp hcval'
          (STAmount.ofNumber_iou_to_nearest_within_half Q priced hQn hQm hQc hpmv) hQb
        linarith
      · rcases lt_or_eq_of_le hcle with hlt | heq
        · -- a clamped charge sits a whole step of the priced grid below it, under `Q`
          have hgap := grid_gap priced r.assets v.baseExponent hpexp hgrid hlt
          have : (0 : ℚ) < 10 ^ r.assets.exponent := zpow_pos (by norm_num) _
          have : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
          nlinarith
        · -- the clamp kept the priced charge, so both amounts share one grid
          have h1 := STAmount.IOUCanonical.exponent_le _ _ hRiou hpiou hrpos heq.le
          have h2 := STAmount.IOUCanonical.exponent_le _ _ hpiou hRiou hppos heq.ge
          rw [heq, le_antisymm h1 h2]
          linarith
    · exact absurd hQm (STAmount.ofNumber_source_ne_zero _ Q .to_nearest priced hQc hpmv)

/-- Where a charge sits against its pricing. On a vault with assets the charge comes from a priced value
`q` at least the worth less `sharesε` of it, half a unit of the grid `10^e` below the next base point above it. -/
lemma Vault.deposit_charge_open_grid (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN) (hmz : navN.mantissa_ ≠ 0)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) :
    ∃ (q : ℚ) (e : ℤ), -96 ≤ e ∧ e ≤ v.baseExponent ∧
      v.idealChargeDepositAt navN.toRat r.shares.toRat * (1 - sharesε) ≤ q ∧
      q + 1 / 2 * (10 : ℚ) ^ e ≤ r.assets.toRat + 10 ^ v.baseExponent ∧
      r.assets.toRat + 10 ^ v.baseExponent ≤ 10 ^ (e + 16) ∧
      (v.numericType.isIntegral = true → e = 0) := by
  obtain ⟨-, priced, navN', -, -, -, -, -, hshc, hshnt, hshpos, hsad, -, hat', hcl, hfnp⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  have hA0 : 0 ≤ navN.toRat :=
    le_trans v.exact.assetsDeployed_nonneg (Vault.assetsTotal_ge_deployed v navN hat).2
  have hεnn : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  have hpnn := sharesToAssetsDeposit_nonneg v r.shares priced hshc hshnt hshpos hsad
  have hpnt := sharesToAssetsDeposit_mNumericType v r.shares priced hsad
  have hcnn := DepAcc.Vault.deposit_charge_nonneg v r.shares priced r.assets navN hshc hshnt hshpos hsad hcl
  have hop := Vault.deposit_open_bound v amountDeposit false t hpos hcanon
    (Vault.deposit_amount_numericType v amountDeposit t hpos hcanon r hok) navN hat r hok
  obtain ⟨Q, hQc, hIpos, hQcases⟩ :=
    charge_nonempty v r.shares priced hshc hshnt hshpos navN hat hmz hsad
  by_cases hint : v.numericType.isIntegral = true
  · -- integral vault
    have hcp : r.assets = priced :=
      clampToSumExponent_integral_nonneg navN priced r.assets v.baseExponent
        (by show priced.mNumericType.isIntegral = true; rw [hpnt]; exact hint) hpnn hcl
    have hbase : v.baseExponent = 0 := (Vault.baseExponent_bounds v).2.2 hint
    rw [hbase] at hop ⊢
    norm_num at hop
    rcases hQcases with ⟨-, hQn, hQneg, hQb⟩ | ⟨hQm, hIsmall⟩
    · have hQb' := abs_le.mp hQb
      have hh' := abs_le.mp (STAmount.ofNumber_integral_within_half v.numericType Q priced hint hQn hQneg hQc)
      refine ⟨Q.toRat, 0, by norm_num, le_rfl, by linarith [hQb'.1], ?_, ?_, fun _ => rfl⟩
      · rw [hcp]; norm_num; linarith [hh'.1]
      · norm_num; linarith
    · -- the priced number underflowed: nothing is charged and the worth is tiny
      have hp0 : priced.toRat = 0 := by
        by_contra hne
        exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .to_nearest priced hint hQc
          (fun h => hne ((STAmount.toRat_eq_zero_iff priced).mpr h)) hQm
      have htiny : v.idealChargeDepositAt navN.toRat r.shares.toRat < 1 :=
        lt_of_le_of_lt hIsmall (zpow_lt_one_of_neg₀ (by norm_num) (by norm_num))
      refine ⟨v.idealChargeDepositAt navN.toRat r.shares.toRat * (1 - sharesε), 0, by norm_num, le_rfl, le_rfl,
        ?_, ?_, fun _ => rfl⟩
      · have hI1 : v.idealChargeDepositAt navN.toRat r.shares.toRat ≤ 1 / 10 := le_trans hIsmall (by
          rw [show (1 / 10 : ℚ) = 10 ^ (-1 : ℤ) by norm_num]
          exact zpow_le_zpow_right₀ (by norm_num) (by norm_num))
        rw [hcp, hp0]
        nlinarith [mul_nonneg hIpos.le hεnn]
      · norm_num; linarith
  · -- fractional vault
    obtain ⟨hpiou, hpmv, hppos, -, hcmv, hpexp, hcval', -, -, -⟩ := frac_charge_floor v navN hat
      r.shares priced r.assets (by simpa using hint) hshc hshnt hshpos hsad hcl hfnp hop
    have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    rcases hQcases with ⟨hQm, hQn, -, hQb⟩ | ⟨hQm, -⟩
    · have hQb' := abs_le.mp hQb
      rw [hvfr] at hQc
      have hh' := abs_le.mp (STAmount.ofNumber_iou_to_nearest_within_half Q priced hQn hQm hQc hpmv)
      have hnext := floor_next_grid priced v.baseExponent hpexp
      rw [add_mul, one_mul, ← hcval'] at hnext
      obtain ⟨-, hbd⟩ := STAmount.IOUCanonical.toRat_bounds priced hpiou hppos
      refine ⟨Q.toRat, priced.exponent, hpiou.exp_lo, hpexp, by linarith [hQb'.1], by linarith [hh'.1], ?_,
        fun h => absurd h hint⟩
      -- the charge is a positive whole number of base steps below `10^(e+16)`, so one more step fits
      have hrpos : 0 < r.assets.toRat := lt_of_le_of_ne hcnn (Ne.symm (STAmount.toRat_ne_zero _ hcmv))
      have hB : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
      have hcle : r.assets.toRat ≤ priced.toRat := by
        rw [hcval']
        have := Int.floor_le (priced.toRat / 10 ^ v.baseExponent)
        rw [le_div_iff₀ hB] at this
        linarith
      have hlt : r.assets.toRat < 10 ^ (priced.exponent + 16) := by
        have : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
        linarith
      have hbe : v.baseExponent ≤ priced.exponent + 16 := by
        by_contra hgt
        push Not at hgt
        have hk1 : (1 : ℚ) ≤ ⌊priced.toRat / 10 ^ v.baseExponent⌋ := by
          by_contra hk
          push Not at hk
          have hk' : ⌊priced.toRat / 10 ^ v.baseExponent⌋ < 1 := by exact_mod_cast hk
          have hk0 : (⌊priced.toRat / 10 ^ v.baseExponent⌋ : ℚ) ≤ 0 := by
            exact_mod_cast (show ⌊priced.toRat / 10 ^ v.baseExponent⌋ ≤ 0 by omega)
          nlinarith
        have : (10 : ℚ) ^ (priced.exponent + 16) ≤ 10 ^ v.baseExponent :=
          zpow_le_zpow_right₀ (by norm_num) hgt.le
        nlinarith
      have hsplit : (10 : ℚ) ^ (priced.exponent + 16) =
          ((10 ^ (priced.exponent + 16 - v.baseExponent).toNat : ℤ) : ℚ) * 10 ^ v.baseExponent := by
        rw [Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num),
          Int.toNat_of_nonneg (by omega)]
        congr 1; ring
      rw [hsplit] at hlt ⊢
      rw [hcval'] at hlt ⊢
      have hz : ⌊priced.toRat / 10 ^ v.baseExponent⌋ < 10 ^ (priced.exponent + 16 - v.baseExponent).toNat :=
        by exact_mod_cast lt_of_mul_lt_mul_right hlt hB.le
      have hz' : ((⌊priced.toRat / 10 ^ v.baseExponent⌋ + 1 : ℤ) : ℚ) ≤
          ((10 ^ (priced.exponent + 16 - v.baseExponent).toNat : ℤ) : ℚ) := by exact_mod_cast hz
      push_cast at hz' ⊢
      nlinarith
    · exact absurd hQm (STAmount.ofNumber_source_ne_zero _ Q .to_nearest priced (hvfr ▸ hQc) hpmv)

end XRPL.Model.SingleAssetVault
