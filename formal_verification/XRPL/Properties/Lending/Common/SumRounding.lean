import XRPL.Properties.Lending.Loan.Common.ManageRoundToExponent
import XRPL.Properties.Lending.Common.Reduction
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.Add.Common.NormalizedSum
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent
import XRPL.Properties.Vault.Proofs.Support.EarlyExitFee
import XRPL.Properties.Vault.Proofs.Support.OfNumberFractional
import XRPL.Properties.Vault.Proofs.Support.VaultBalances

/-! # Rounding a sum onto its grid

`sumRoundAndSubtract` floors a balance plus an amount onto the grid of the sum and credits the difference. The credit
never exceeds the amount, and on a balance of whole base units it is the amount floored to whole base units. -/

namespace XRPL.Model.Protocol

/-- A fractional amount that is canonical or zero converts to a `Number` of the same value. -/
lemma STAmount.FracCanonZero.toNumber_val {s : STAmount} (h : s.FracCanonZero) (mode : rounding_mode)
    (n : Number) (hn : s.toNumber mode = .ok n) : n.toRat = s.toRat := by
  rcases h.2 with hc | hz
  · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact s mode hc
    rw [hsn, Except.ok.injEq] at hn
    rw [← hn, hv]
  · have hfr : s.integral = false := by unfold STAmount.integral; rw [h.1]; rfl
    rw [STAmount.toNumber_zero_fractional s mode hfr hz, Except.ok.injEq] at hn
    rw [← hn, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero s hz]

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- An `ofNumber` result converts back to a `Number` of the same value. A fractional result is
stored canonically or is zero, an integral one is canonical when its source is not negative. -/
lemma STAmount.ofNumber_toNumber_exact (nt : NumericType) (n : Number) (mode mode' : rounding_mode)
    (r : STAmount) (m : Number) (hn : n.isNormalized) (hint : nt.isIntegral = true → 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n mode = .ok r) (hm : r.toNumber mode' = .ok m) :
    m.toRat = r.toRat ∧ m.isNormalized := by
  by_cases hz : r.mValue = 0
  · exact STAmount.toNumber_zero_facts r mode' m hz hm
  by_cases hnt : nt.isIntegral = true
  · have hc := STAmount.ofNumber_exactCanonical nt n mode r hn (hint hnt) hok hz
    obtain ⟨sn, hsn, hv, hnorm⟩ := STAmount.toNumber_exact_canonical r mode' hc
    rw [hsn, Except.ok.injEq] at hm
    subst hm
    exact ⟨hv, hnorm⟩
  · have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hnt)
    subst hfr
    have hnz : n.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional n mode r hok hz
    obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hnz
    have hc := (STAmount.ofNumber_iou_ok_facts n mode r hlo hhi (Number.exponent_ge_min n hn hnz) hok hz).1
    obtain ⟨sn, hsn, hv, hnorm⟩ := STAmount.toNumber_iou_exact r mode' hc
    rw [hsn, Except.ok.injEq] at hm
    subst hm
    exact ⟨hv, hnorm⟩

/-- A downward `ofNumber` stays at or below its source when the source is not negative, and at or
below zero otherwise. -/
lemma STAmount.ofNumber_downward_le_max (nt : NumericType) (n : Number) (r : STAmount) (hn : n.isNormalized)
    (hint : nt.isIntegral = true → 0 ≤ n.toRat) (hok : STAmount.ofNumber nt n .downward = .ok r) :
    r.toRat ≤ max n.toRat 0 := by
  by_cases hz : r.mValue = 0
  · rw [STAmount.toRat_eq_zero_of_mValue_zero r hz]; exact le_max_right _ _
  by_cases h0 : 0 ≤ n.toRat
  · exact le_trans (STAmount.ofNumber_downward_floor_bounds nt n r hn
      (Number.negative_false_of_nonneg n hn h0) hok hz).1 (le_max_left _ _)
  · push Not at h0
    have hnt : nt.isIntegral = false := by
      cases h : nt.isIntegral
      · rfl
      · exact absurd (hint h) (not_le.mpr h0)
    have hneg : n.negative_ = true := by
      by_contra hc
      exact absurd (Number.toRat_nonneg_of_nonnegative n (by simpa using hc)) (not_le.mpr h0)
    exact le_trans (STAmount.ofNumber_signtrue_nonpos nt n _ r hnt hn hneg hok) (le_max_right _ _)

/-- Rounding down to a fractional asset at a scale stays between zero and a value that is not
negative. -/
lemma STAmount.roundToNumericType_downward_le (x c : Number) (e : Int) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (he : (-96 : ℤ) ≤ e ∧ e ≤ 80)
    (h : STAmount.roundToNumericType .fractional x .downward (some e) = .ok c) :
    0 ≤ c.toRat ∧ c.toRat ≤ x.toRat ∧ c.isNormalized := by
  have hcn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ h
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber .fractional x .downward with
  | error err => rw [hof] at h; exact absurd h (by simp)
  | ok ret =>
    rw [hof] at h
    have hneg := Number.negative_false_of_nonneg x hx h0
    have hret0 := STAmount.ofNumber_nonneg _ x _ ret hx hneg hof
    have hretle : ret.toRat ≤ x.toRat := by
      have := STAmount.ofNumber_downward_le_max .fractional x ret hx (by simp [NumericType.isIntegral]) hof
      rwa [max_eq_left h0] at this
    have hint : ret.integral = false := by
      unfold STAmount.integral; rw [STAmount.ofNumber_mNumericType _ _ _ _ hof]; rfl
    simp only [hint, Bool.false_eq_true, if_false] at h
    cases hre : STAmount.roundToExponent ret e .downward with
    | error err => rw [hre] at h; exact absurd h (by simp)
    | ok rounded =>
      rw [hre] at h
      simp only at h
      -- the rounded amount is the floor of `ret` on the scale grid, or zero
      have hrv : 0 ≤ rounded.toRat ∧ rounded.toRat ≤ ret.toRat := by
        by_cases hz : rounded.mValue = 0
        · rw [STAmount.toRat_eq_zero_of_mValue_zero rounded hz]; exact ⟨le_refl _, hret0⟩
        by_cases hrz : ret.mValue = 0
        · have : rounded = ret := by
            rw [STAmount.roundToExponent_eq_self ret _ _ (Or.inr (Or.inl (by simp [STAmount.isZero, hrz]))),
              Except.ok.injEq] at hre
            exact hre.symm
          rw [this]; exact ⟨hret0, le_refl _⟩
        have hnz : x.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional x _ ret hof hrz
        obtain ⟨hlo, hhi⟩ := hx.mantissaBounds_nat hnz
        have hc := (STAmount.ofNumber_iou_ok_facts x _ ret hlo hhi (Number.exponent_ge_min x hx hnz) hof hrz).1
        have hfl := STAmount.roundToExponent_rounded ret rounded e .downward hc he.1 he.2 hz hre
        have hp : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
        change rounded.toRat = (⌊ret.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e at hfl
        rw [hfl]
        refine ⟨by positivity, ?_⟩
        have := Int.floor_le (ret.toRat / 10 ^ e)
        rw [le_div_iff₀ hp] at this
        exact this
      -- the rounded amount is stored canonically, so its `Number` has the same value
      have hfc := STAmount.roundToExponent_fczr ret rounded e .downward
        (STAmount.ofNumber_fractional_fczr x _ ret hof) hre
      have hcv : c.toRat = rounded.toRat := by
        rcases hfc.2 with hc' | hz'
        · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact rounded .downward hc'
          rw [hsn, Except.ok.injEq] at h
          rw [← h, hv]
        · exact (STAmount.toNumber_zero_facts rounded _ c hz' h).1
      rw [hcv]
      exact ⟨hrv.1, hrv.2.trans hretle, hcn⟩

/-- The credit floored onto the posterior grid never exceeds the amount added. Every step rounds down on a value
that is not negative, and the result converts back to a `Number` of the same value. -/
lemma sumRoundAndSubtract_downward_le (A c : Number) (e : Int) (nt : NumericType) (st : STAmount)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (he : (-96 : ℤ) ≤ e ∧ e ≤ 80)
    (h : sumRoundAndSubtract A c e nt .downward = .ok st) :
    st.toRat ≤ c.toRat ∧ ∀ m, st.toNumber .to_nearest = .ok m → m.toRat = st.toRat ∧ m.isNormalized := by
  unfold sumRoundAndSubtract at h
  by_cases hint : nt.isIntegral = true
  · rw [if_pos hint] at h
    obtain ⟨x, hx, h⟩ := bind_ok_peel _ _ _ h
    have hxs : x = st := Except.ok.inj h
    subst hxs
    refine ⟨?_, fun m hm => STAmount.ofNumber_toNumber_exact nt c _ _ x m hc (fun _ => hc0) hx hm⟩
    have := STAmount.ofNumber_downward_le_max nt c x hc (fun _ => hc0) hx
    rwa [max_eq_left hc0] at this
  · rw [if_neg hint] at h
    have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    subst hfr
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨d, hd, h⟩ := bind_ok_peel _ _ _ h

    have hErange : (-96 : ℤ) ≤ E ∧ E ≤ 80 := (postSumExponent_range _ _ _ _ _ he.1 he.2 hE).2

    -- each step rounds down
    obtain ⟨hs1, hs0⟩ := Number.operator_add_downward_nonneg_le A c sum hA hc hA0 hc0 hsum
    have hsn := Number.operator_add_isNormalized_any A c sum _ hA hc hsum
    obtain ⟨-, hs'1, hs'n⟩ := STAmount.roundToNumericType_downward_le sum sum' E hsn hs0 hErange hsum'
    have hdn := Number.operator_sub_isNormalized_any sum' A d _ hs'n hA hd
    have hdle : d.toRat ≤ c.toRat ∨ d.toRat ≤ 0 := by
      by_cases hd0 : d.mantissa_ = 0
      · exact Or.inr (le_of_eq (Number.toRat_eq_zero_of_mantissa_zero d hd0))
      · obtain ⟨n, hn, hv⟩ := operator_sub_rounded_downward sum' A d hs'n hA hd hd0
        exact Or.inl (by rw [hv]; linarith [Number.lower_le _ n hn])
    have hst := STAmount.ofNumber_downward_le_max .fractional d st hdn (by simp [NumericType.isIntegral]) h
    refine ⟨?_, fun m hm => STAmount.ofNumber_toNumber_exact _ d _ _ st m hdn
      (by simp [NumericType.isIntegral]) h hm⟩
    rcases hdle with h1 | h1
    · exact le_trans hst (max_le h1 hc0)
    · exact le_trans hst (max_le (h1.trans hc0) hc0)

/-- A value between two neighbouring grid points floors to the lower one. -/
private lemma floor_grid_eq (s : ℚ) (k : ℤ) (b : ℤ) (h1 : (k : ℚ) * 10 ^ b ≤ s)
    (h2 : s < ((k : ℚ) + 1) * 10 ^ b) :
    ⌊s / 10 ^ b⌋ = k := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  rw [Int.floor_eq_iff]
  exact ⟨by rw [le_div_iff₀ hp]; exact h1, by rw [div_lt_iff₀ hp]; exact h2⟩

/-- A sum of two values that are not negative is zero only when both are. -/
private lemma add_zero_sum (x y r : Number) (mode : rounding_mode) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hok : x.operator_add y mode = .ok r) (hr0 : r.mantissa_ = 0) :
    x.toRat + y.toRat = 0 := by
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have hrx : r = x := by
      unfold Number.operator_add at hok; rw [if_pos hy_guard] at hok; exact (Except.ok.inj hok).symm
    rw [Number.toRat_eq_zero_of_mantissa_zero y (Number.mantissa_eq_zero_of_operator_eq_zero hy_guard), ← hrx,
      Number.toRat_eq_zero_of_mantissa_zero r hr0]
    ring
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have hry : r = y := by
      unfold Number.operator_add at hok; rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj hok).symm
    rw [Number.toRat_eq_zero_of_mantissa_zero x (Number.mantissa_eq_zero_of_operator_eq_zero hx_guard), ← hry,
      Number.toRat_eq_zero_of_mantissa_zero r hr0]
    ring
  by_cases heq : x.operator_eq y.operator_neg = true
  · have h := (operator_eq_iff _ _ hx (Number.operator_neg_isNormalized y hy)).mp heq
    rw [Number.toRat_neg] at h
    linarith
  · exfalso
    have hxm : x.mantissa_ ≠ 0 := fun h => hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
    have hym : y.mantissa_ ≠ 0 := fun h => hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
    have hsign : x.negative_ = y.negative_ := by
      rw [Number.negative_false_of_nonneg x hx hx0, Number.negative_false_of_nonneg y hy hy0]
    obtain ⟨_, _, _, _, _, hspec⟩ := operator_add_algorithmic_facts_same_sign_anyMode x y r mode hx hy hxm hym
      hsign heq hok
    exact hspec.result_mant_ne hr0

/-- A downward sum of two values that are not negative never lands below a representable value under the
exact sum. -/
private lemma add_downward_ge (x y r w : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hok : x.operator_add y .downward = .ok r)
    (hw : w.isNormalized) (hwt : w.toRat ≤ x.toRat + y.toRat) : w.toRat ≤ r.toRat := by
  by_cases hr0 : r.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero r hr0]
    linarith [add_zero_sum x y r _ hx hy hx0 hy0 hok hr0]
  · obtain ⟨n, hn, hv⟩ := operator_add_rounded_downward x y r hx hy hok hr0
    rw [hv]
    exact Number.lower_tight _ n hn w hw hwt

/-- A difference of two values that are not negative is exact, in every mode, when a `Number` holds it. -/
private lemma sub_exact (x y r w : Number) (mode : rounding_mode) (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hok : x.operator_sub y mode = .ok r)
    (hw : w.isNormalized) (hwt : w.toRat = x.toRat - y.toRat) : r.toRat = x.toRat - y.toRat := by
  unfold Number.operator_sub at hok
  have hyn := Number.operator_neg_isNormalized y hy
  by_cases hym : y.mantissa_ = 0
  · rw [Number.operator_neg_of_mantissa_zero y hym, Number.operator_add_zero_right] at hok
    rw [← Except.ok.inj hok, Number.toRat_eq_zero_of_mantissa_zero y hym]
    ring
  have hnm : y.operator_neg.mantissa_ ≠ 0 := by rw [Number.operator_neg_mantissa_of_ne y hym]; exact hym
  by_cases hxm : x.mantissa_ = 0
  · have hx' : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx hxm
    have hr : r = y.operator_neg := by
      replace hok := Number.operator_add_ok_spec hok
      unfold Number.operator_addSpec at hok
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hnm), hx', if_pos (by decide)] at hok
      exact (Except.ok.inj hok).symm
    rw [hr, Number.toRat_neg, hx', Number.toRat_zero]
    ring
  have hdiff : x.negative_ ≠ y.operator_neg.negative_ := by
    rw [Number.negative_false_of_nonneg x hx hx0, Number.operator_neg_negative_of_ne y hym,
      Number.negative_false_of_nonneg y hy hy0]
    decide
  have h := operator_add_exact_diff_sign x y.operator_neg r mode hx hyn hxm hnm hdiff w hw
    (by rw [hwt, Number.toRat_neg]; ring) hok
  rw [h, Number.toRat_neg]
  ring

/-- A whole number of units below `10^16` at a scale in range is a normalized `Number`. -/
lemma Number.exists_units_normalized (k : ℕ) (b : Int) (hk : k < 10 ^ 16) (hb : (-81 : ℤ) ≤ b ∧ b ≤ 0) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (k : ℚ) * 10 ^ b := by
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (k : ℤ) b (by omega)
    (by unfold minExponent maxExponent; omega)
  exact ⟨w, hw, by rw [hwv]; norm_cast⟩

/-- A nonzero normalized value that is not negative is at least `10^18` units of its exponent. -/
lemma Number.pow_exponent_add_le_toRat (n : Number) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (hnz : n.mantissa_ ≠ 0) :
    (10 : ℚ) ^ (n.exponent_ + 18) ≤ n.toRat := by
  obtain ⟨hlo, -⟩ := hn.mantissaBounds_nat hnz
  have hm : ((10 : ℚ) ^ 18) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
  rw [Number.toRat_of_nonneg n (Number.negative_false_of_nonneg n hn h0), zpow_add₀ (by norm_num), mul_comm]
  have : (10 : ℚ) ^ (18 : ℤ) = 10 ^ 18 := by norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_right hm (zpow_pos (by norm_num) _).le

/-- When AssetsAvailable is whole base units, and the sum keeps the base exponent and stays below
`10^(16 + b)`, the credit is the amount floored to whole base units. -/
lemma sumRoundAndSubtract_at_base_of_exponent (A c : Number) (b : Int) (st : STAmount) (a : ℕ)
    (hA : A.isNormalized) (hAv : A.toRat = (a : ℚ) * 10 ^ b) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hb : (-81 : ℤ) ≤ b ∧ b ≤ 0) (hE : postSumExponent A c b .fractional = .ok b)
    (hlt : A.toRat + c.toRat < (10 : ℚ) ^ (16 + b))
    (h : sumRoundAndSubtract A c b .fractional .downward = .ok st) :
    st.toRat = (⌊c.toRat / 10 ^ b⌋ : ℚ) * 10 ^ b := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ A.toRat := by rw [hAv]; positivity
  have hpow16 : (10 : ℚ) ^ (16 + b) = (10 : ℚ) ^ 16 * 10 ^ b := by rw [zpow_add₀ (by norm_num)]; norm_num

  -- the credit in whole base units
  have hk0 : 0 ≤ ⌊c.toRat / 10 ^ b⌋ := Int.floor_nonneg.mpr (div_nonneg hc0 hp.le)
  obtain ⟨kn, hkn⟩ : ∃ kn : ℕ, (kn : ℤ) = ⌊c.toRat / 10 ^ b⌋ := ⟨_, Int.toNat_of_nonneg hk0⟩
  have hk1 : (kn : ℚ) * 10 ^ b ≤ c.toRat := by
    have := Int.floor_le (c.toRat / 10 ^ b)
    rw [← hkn, le_div_iff₀ hp] at this
    exact_mod_cast this
  have hk2 : c.toRat < ((kn : ℚ) + 1) * 10 ^ b := by
    have := Int.lt_floor_add_one (c.toRat / 10 ^ b)
    rw [← hkn, div_lt_iff₀ hp] at this
    exact_mod_cast this
  rw [← hkn]
  have hK : a + kn < 10 ^ 16 := by
    have h1 : ((a + kn : ℕ) : ℚ) * 10 ^ b < (10 : ℚ) ^ 16 * 10 ^ b := by
      rw [← hpow16]; push_cast; nlinarith
    have h2 : ((a + kn : ℕ) : ℚ) < (10 : ℚ) ^ 16 := lt_of_mul_lt_mul_right h1 hp.le
    exact_mod_cast h2
  obtain ⟨F, hF, hFv⟩ := Number.exists_units_normalized (a + kn) b hK hb

  unfold sumRoundAndSubtract at h
  rw [if_neg (by decide)] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨E, hE', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d, hd, hst⟩ := bind_ok_peel _ _ _ h
  have hEb : E = b := by rw [hE] at hE'; exact (Except.ok.inj hE').symm
  subst hEb

  -- the downward sum sits between the base-grid floor and the exact sum
  have hsn := Number.operator_add_isNormalized_any _ _ _ _ hA hc hsum
  obtain ⟨hsle, hs0'⟩ := Number.operator_add_downward_nonneg_le A c sum hA hc hA0 hc0 hsum
  have hsge : F.toRat ≤ sum.toRat := add_downward_ge A c sum F hA hc hA0 hc0 hsum hF (by
    rw [hFv, hAv]; push_cast; linarith)
  have hsfloor : ⌊sum.toRat / 10 ^ E⌋ = ((a + kn : ℕ) : ℤ) := by
    have hcast : (((a + kn : ℕ) : ℤ) : ℚ) = ((a + kn : ℕ) : ℚ) := by push_cast; ring
    apply floor_grid_eq
    · rw [hcast, ← hFv]; exact hsge
    · rw [hcast]; push_cast; rw [hAv] at hsle; nlinarith

  -- rounding the sum down onto the base grid gives the floor
  have hcn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hsum'
  have hsum'v : sum'.toRat = F.toRat := by
    unfold STAmount.roundToNumericType at hsum'
    cases hof : STAmount.ofNumber .fractional sum .downward with
    | error err => rw [hof] at hsum'; exact absurd hsum' (by simp)
    | ok ret =>
      rw [hof] at hsum'
      have hint : ret.integral = false := by
        unfold STAmount.integral; rw [STAmount.ofNumber_mNumericType _ _ _ _ hof]; rfl
      simp only [hint, Bool.false_eq_true, if_false] at hsum'
      cases hre : STAmount.roundToExponent ret E .downward with
      | error err => rw [hre] at hsum'; exact absurd hsum' (by simp)
      | ok rounded =>
        rw [hre] at hsum'
        simp only at hsum'
        have hrv : rounded.toRat = F.toRat := by
          by_cases hrz : ret.mValue = 0
          · -- a zero pack comes from a sum below one base unit, so the floor is zero
            have hsmall : sum.toRat < 10 ^ E := by
              by_cases h0 : sum.mantissa_ = 0
              · rw [Number.toRat_eq_zero_of_mantissa_zero sum h0]; exact hp
              have hlt : sum.exponent_ < -99 := by
                by_contra hc'
                exact STAmount.ofNumber_iou_ne_zero_of_exponent sum _ ret hsn h0 (by omega) hof hrz
              obtain ⟨-, hhi⟩ := hsn.mantissaBounds_nat h0
              have hm : (sum.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hhi
              have hv := Number.toRat_of_nonneg sum (Number.negative_false_of_nonneg sum hsn hs0')
              have h1 : (10 : ℚ) ^ sum.exponent_ * 10 ^ 19 ≤ 10 ^ E := by
                rw [show (10 : ℚ) ^ 19 = 10 ^ (19 : ℤ) by norm_num, ← zpow_add₀ (by norm_num)]
                exact zpow_le_zpow_right₀ (by norm_num) (by omega)
              have h2 : (0 : ℚ) < 10 ^ sum.exponent_ := zpow_pos (by norm_num) _
              rw [hv]; nlinarith
            have hK0 : a + kn = 0 := by
              have h1 : F.toRat < 10 ^ E := lt_of_le_of_lt hsge hsmall
              rw [hFv] at h1
              have h2 : ((a + kn : ℕ) : ℚ) < 1 := by nlinarith
              have h3 : a + kn < 1 := by exact_mod_cast h2
              omega
            have hrr : rounded = ret := by
              rw [STAmount.roundToExponent_eq_self ret _ _ (Or.inr (Or.inl (by simp [STAmount.isZero, hrz]))),
                Except.ok.injEq] at hre
              exact hre.symm
            rw [hrr, STAmount.toRat_eq_zero_of_mValue_zero ret hrz, hFv, hK0]
            simp
          · have hnz : sum.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional sum _ ret hof hrz
            obtain ⟨hlo, hhi⟩ := hsn.mantissaBounds_nat hnz
            have hc' := (STAmount.ofNumber_iou_ok_facts sum _ ret hlo hhi (Number.exponent_ge_min sum hsn hnz) hof
              hrz).1
            have hfl := STAmount.ofNumber_iou_downward_floor sum ret hsn hnz hs0' hof hrz
            change ret.toRat = (⌊sum.toRat / 10 ^ (sum.exponent_ + 3)⌋ : ℚ) * 10 ^ (sum.exponent_ + 3) at hfl
            have hrnd := STAmount.roundToExponent_rounded_of_scale ret rounded E .downward hc' hb.1 (by omega) hre
            change rounded.toRat = (⌊ret.toRat / 10 ^ E⌋ : ℚ) * 10 ^ E at hrnd
            -- the sum's 16-digit grid is no coarser than the base grid
            have hg : sum.exponent_ + 3 ≤ E := by
              have h1 := Number.pow_exponent_add_le_toRat sum hsn hs0' hnz
              have h2 : sum.toRat < 10 ^ (16 + E) := by linarith
              have h3 : (10 : ℚ) ^ (sum.exponent_ + 18) < 10 ^ (16 + E) := lt_of_le_of_lt h1 h2
              have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h3
              omega
            rw [hrnd, hfl, floor_grid_floor_of_le _ _ _ hg, hsfloor, hFv]
            push_cast
            ring
        -- the rounded amount converts back exactly
        have hfc := STAmount.roundToExponent_fczr ret rounded E .downward
          (STAmount.ofNumber_fractional_fczr sum _ ret hof) hre
        rcases hfc.2 with hc' | hz'
        · obtain ⟨sn, hsn', hv, -⟩ := STAmount.toNumber_iou_exact rounded .downward hc'
          rw [hsn', Except.ok.injEq] at hsum'
          rw [← hsum', hv, hrv]
        · rw [(STAmount.toNumber_zero_facts rounded _ sum' hz' hsum').1, hrv]

  -- the difference with AssetsAvailable is the credit, exactly
  obtain ⟨w, hw, hwv⟩ := Number.exists_units_normalized kn E (by omega) hb
  have hdv : d.toRat = (kn : ℚ) * 10 ^ E := by
    rw [sub_exact sum' A d w _ hcn hA (by rw [hsum'v, hFv]; positivity) hA0 hd hw
      (by rw [hwv, hsum'v, hFv, hAv]; push_cast; ring), hsum'v, hFv, hAv]
    push_cast
    ring
  have hdn := Number.operator_sub_isNormalized_any _ _ _ _ hcn hA hd

  -- the credit already fits the asset, so the downward pack keeps it
  by_cases hkz : kn = 0
  · have hd0 : d = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hdn).mp (by rw [hdv, hkz]; simp)
    rw [hd0, STAmount.ofNumber_fractional_zero, Except.ok.injEq] at hst
    rw [← hst, hkz]
    simp [STAmount.toRat]
  · have hdpos : (10 : ℚ) ^ E ≤ d.toRat := by
      rw [hdv]
      have : (1 : ℚ) ≤ kn := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hkz
      nlinarith
    have hd0 : d.mantissa_ ≠ 0 := fun h0 => by
      rw [Number.toRat_eq_zero_of_mantissa_zero d h0] at hdpos; linarith
    obtain ⟨-, hdhi⟩ := hdn.mantissaBounds_nat hd0
    have hdv' := Number.toRat_of_nonneg d (Number.negative_false_of_nonneg d hdn (le_trans hp.le hdpos))
    -- the credit's exponent is in range and its grid is no coarser than the base grid
    have hdm : (d.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hdhi
    have he_lo : (-99 : ℤ) ≤ d.exponent_ := by
      by_contra hc'
      push Not at hc'
      have h1 : (10 : ℚ) ^ d.exponent_ * 10 ^ 19 ≤ 10 ^ E := by
        rw [show (10 : ℚ) ^ 19 = 10 ^ (19 : ℤ) by norm_num, ← zpow_add₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (0 : ℚ) < 10 ^ d.exponent_ := zpow_pos (by norm_num) _
      rw [hdv'] at hdpos; nlinarith
    have hst0 := STAmount.ofNumber_iou_ne_zero_of_exponent d _ st hdn hd0 he_lo hst
    have hfl := STAmount.ofNumber_iou_downward_floor d st hdn hd0 (le_trans hp.le hdpos) hst hst0
    change st.toRat = (⌊d.toRat / 10 ^ (d.exponent_ + 3)⌋ : ℚ) * 10 ^ (d.exponent_ + 3) at hfl
    have hg : d.exponent_ + 3 ≤ E := by
      have h1 := Number.pow_exponent_add_le_toRat d hdn (le_trans hp.le hdpos) hd0
      have h2 : d.toRat < 10 ^ (16 + E) := by
        rw [hdv, hpow16]
        have : (kn : ℚ) < 10 ^ 16 := by exact_mod_cast (show kn < 10 ^ 16 by omega)
        nlinarith
      have h3 : (10 : ℚ) ^ (d.exponent_ + 18) < 10 ^ (16 + E) := lt_of_le_of_lt h1 h2
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h3
      omega
    -- `kn` base units are a whole number of units of the finer grid
    have hsplit : (10 : ℚ) ^ E = ((10 ^ (E - (d.exponent_ + 3)).toNat : ℕ) : ℚ) * 10 ^ (d.exponent_ + 3) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      congr 1
      omega
    have hq : d.toRat / 10 ^ (d.exponent_ + 3) = ((kn * 10 ^ (E - (d.exponent_ + 3)).toNat : ℕ) : ℤ) := by
      rw [hdv, hsplit]
      have : (0 : ℚ) < 10 ^ (d.exponent_ + 3) := zpow_pos (by norm_num) _
      field_simp
      push_cast
      ring
    rw [hfl, hq, Int.floor_intCast, hsplit]
    push_cast
    ring

/-- On the base grid the credit is the amount floored to whole base units. When AssetsAvailable is a
whole number of base units and the sum stays a unit below `10^(16 + b)`, it lands exactly on the base grid. -/
lemma sumRoundAndSubtract_at_base (A c : Number) (b : Int) (st : STAmount) (a : ℕ)
    (hA : A.isNormalized) (hAv : A.toRat = (a : ℚ) * 10 ^ b) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hb : (-81 : ℤ) ≤ b ∧ b ≤ 0) (hroom : A.toRat + c.toRat ≤ (10 : ℚ) ^ (16 + b) - 10 ^ b)
    (h : sumRoundAndSubtract A c b .fractional .downward = .ok st) :
    st.toRat = (⌊c.toRat / 10 ^ b⌋ : ℚ) * 10 ^ b := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ A.toRat := by rw [hAv]; positivity
  have hpow16 : (10 : ℚ) ^ (16 + b) = (10 : ℚ) ^ 16 * 10 ^ b := by rw [zpow_add₀ (by norm_num)]; norm_num
  obtain ⟨W, hW, hWv⟩ := Number.exists_units_normalized (10 ^ 16 - 1) b (by norm_num) hb
  have hWq : W.toRat = (10 : ℚ) ^ (16 + b) - 10 ^ b := by
    rw [hWv, hpow16]; push_cast; ring

  -- the posterior exponent is the base exponent: the nearest sum stays below `10^(16 + b)`
  have hE : postSumExponent A c b .fractional = .ok b := by
    have h' := h
    unfold sumRoundAndSubtract at h'
    rw [if_neg (by decide)] at h'
    obtain ⟨_, -, h'⟩ := bind_ok_peel _ _ _ h'
    obtain ⟨E, hE, -⟩ := bind_ok_peel _ _ _ h'
    obtain ⟨s0, hs0, hE'⟩ := postSumExponent_reduces _ _ _ _ _ hE
    have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hs0
    have hs0le : s0.toRat ≤ W.toRat :=
      operator_add_le_of_le_normalized _ _ _ _ hA hc hs0 hW (by rw [hWq]; exact hroom)
    have hs00 : 0 ≤ s0.toRat := operator_add_nonneg _ _ _ hA hc hs0 (by linarith)
    have hge := numberExponent_ge _ _ _ _ hE'
    rw [hE]
    by_contra hne
    have hlt : b < E := lt_of_le_of_ne hge (fun h => hne (by rw [h]))
    obtain ⟨-, hbig⟩ := numberExponent_frac_lower s0 b E hs0n hs00 (by omega) hE' hlt
    have h1 : (10 : ℚ) ^ (16 + b) ≤ 10 ^ (E + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  exact sumRoundAndSubtract_at_base_of_exponent A c b st a hA hAv hc hc0 hb hE (by linarith) h

/-- A downward IOU conversion of a negative value rounds toward zero. The conversion rounds the magnitude down,
so the stored amount is at least the value. -/
private lemma STAmount.ofNumber_frac_downward_neg_ge (d : Number) (st : STAmount) (hd : d.isNormalized)
    (hneg : d.negative_ = true) (hexp : d.exponent_ + 4 ≤ maxExponent)
    (h : STAmount.ofNumber .fractional d .downward = .ok st) : d.toRat ≤ st.toRat := by
  have hdm := Number.mantissa_ne_zero_of_negative d hd hneg
  set w := d.operator_neg with hwdef
  have hwm : w.mantissa_ = d.mantissa_ := Number.operator_neg_mantissa_of_ne d hdm
  have hwe : w.exponent_ = d.exponent_ := by rw [hwdef]; unfold Number.operator_neg; simp [hdm]
  have hwneg : w.negative_ = false := by rw [hwdef, Number.operator_neg_negative_of_ne d hdm, hneg]; rfl
  have hwn := Number.operator_neg_isNormalized d hd
  have hdw : d.toRat = -w.toRat := by rw [hwdef, Number.toRat_neg]; ring
  obtain ⟨hlo19, hhi19⟩ := hd.mantissaBounds_nat hdm
  have hemin := Number.exponent_ge_min d hd hdm
  have hemax : d.exponent_ ≤ maxExponent := by
    rcases hd with h0 | ⟨_, _, _, hhi⟩
    · exact absurd (by rw [h0]; rfl) hdm
    · exact hhi.2
  have hw_lo : 10 ^ 18 ≤ w.mantissa_.toNat := by rw [hwm]; exact hlo19
  have hw_hi : w.mantissa_.toNat < 10 ^ 19 := by rw [hwm]; exact hhi19
  -- both conversions round the same magnitude
  have hsig : decide (d.signum < 0) = true := by rw [Number.signum_neg_decide, hneg]
  unfold STAmount.ofNumber at h
  rw [if_neg (by decide)] at h
  simp only [hsig, if_true] at h
  rw [← hwdef] at h
  cases hnorm : w.normalizeToRange kMinValue kMaxValue .downward with
  | error e => rw [hnorm] at h; cases h
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at h
    simp only [] at h
    have hnorm' : w.normalizeToRange cMinValue cMaxValue .downward = .ok (mant, exp) := hnorm
    obtain ⟨hval, hEeq⟩ := normalizeToRange_16_floor_pos w mant exp .downward (Or.inl rfl) hwneg hw_lo hw_hi
      (by rw [hwe]; omega) (by rw [hwe]; omega) hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, -, hsgn⟩ := normalizeToRange_iou_ok_facts w .downward mant exp hw_lo hw_hi
      (by rw [hwe]; omega) (by rw [hwe]; omega) hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hwneg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
      exact this
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
      omega
    -- the floor of the magnitude is at most the magnitude
    have hfloor : (mant.toUInt64.toNat : ℚ) * 10 ^ exp ≤ w.toRat := by
      have hcast : (mant.toUInt64.toNat : ℚ) = (mant.toInt : ℚ) := by
        rw [← hmant_natAbs, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hmant_pos)]
      rw [hcast, hval, Number.toRat_of_nonneg w hwneg, zpow_add₀ (by norm_num)]
      have h1 : ((w.mantissa_.toNat / 1000 : ℕ) : ℚ) * 1000 ≤ (w.mantissa_.toNat : ℚ) := by
        exact_mod_cast Nat.div_mul_le_self _ _
      have hp : (0 : ℚ) < 10 ^ w.exponent_ := zpow_pos (by norm_num) _
      have : (10 : ℚ) ^ (3 : ℤ) = 1000 := by norm_num
      rw [this]
      nlinarith
    -- the stored amount is the negated floor, or zero
    have h_int : ¬ (STAmount.unchecked .fractional mant.toUInt64 exp true).integral = true := by
      simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
    have h_fit : mant.toUInt64.toNat < 2 ^ 63 := by omega
    have h_sd : (STAmount.unchecked .fractional mant.toUInt64 exp true).signedDrops.toInt64
        = -mant.toUInt64.toInt64 := by
      apply Int64.toInt_inj.mp
      rw [STAmount.signedDrops_toInt64_toInt _
            (show (STAmount.unchecked .fractional mant.toUInt64 exp true).mValue.toNat < 10 ^ 16 from hmtu_hi)]
      have := signed_mantissa_toInt true mant.toUInt64 h_fit
      simp only [if_true] at this
      rw [this]
      show (STAmount.unchecked .fractional mant.toUInt64 exp true).signedDrops = _
      unfold STAmount.signedDrops STAmount.unchecked
      simp
    have hiou : (STAmount.unchecked .fractional mant.toUInt64 exp true).iou .downward
        = (if exp > cMaxOffset then .error .overflow
           else if exp < cMinOffset then .ok IOUAmount.zero
           else .ok ⟨-mant.toUInt64.toInt64, exp⟩) := by
      rw [STAmount.iou_of_lt .downward h_int h_fit]
      unfold IOUAmount.ofMantissaExp
      rw [h_sd]
      have := IOUAmount.normalize_canonical16 mant.toUInt64 exp true .downward hmtu_lo hmtu_hi
        (by rw [hEeq, hwe]; omega) (by rw [hEeq, hwe]; omega)
      simpa using this
    obtain ⟨vpeel, hvpeel, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨-, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hvpeel
    rw [STAmount.checked] at h
    unfold STAmount.canonicalize at h
    rw [if_neg h_int, hiou] at h
    have hd0 : d.toRat ≤ 0 := by rw [hdw]; linarith [Number.toRat_nonneg_of_nonnegative w hwneg]
    split_ifs at h with h1 h2
    · obtain rfl := (Except.ok.inj h).symm
      rw [STAmount.toRat_signed]
      simpa using hd0
    · obtain rfl := (Except.ok.inj h).symm
      have hpos : 0 < mant.toUInt64.toNat := by omega
      have hxneg := signed_mantissa_decide_neg true mant.toUInt64 h_fit hpos
      simp only [if_true, decide_eq_true_eq] at hxneg
      have hsig' : IOUAmount.signum ⟨-mant.toUInt64.toInt64, exp⟩ = -1 := by
        unfold IOUAmount.signum; exact if_pos hxneg
      have hlt : IOUAmount.signum ⟨-mant.toUInt64.toInt64, exp⟩ < 0 := by rw [hsig']; decide
      rw [STAmount.toRat_signed]
      simp only [hlt, decide_true, if_true]
      rw [← Int64.neg_toUInt64_eq_magnitude hxneg, Int64.neg_neg]
      show d.toRat ≤ -1 * ((mant.toUInt64.toInt64.toUInt64.toNat : ℕ) : ℚ) * 10 ^ exp
      rw [show mant.toUInt64.toInt64.toUInt64 = mant.toUInt64 from rfl, hdw]
      linarith

/-- A credit floored onto the posterior grid never takes a balance below zero. The difference with the
balance is at least minus the balance, and the stored credit rounds a negative difference toward zero. -/
lemma sumRoundAndSubtract_downward_cover_nonneg (A c : Number) (e : Int) (nt : NumericType) (st : STAmount)
    (m : Number) (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hAb : nt = .fractional → A.toRat < 10 ^ 96)
    (hc : c.isNormalized)
    (hc0 : 0 ≤ c.toRat) (he : (-96 : ℤ) ≤ e ∧ e ≤ 80)
    (h : sumRoundAndSubtract A c e nt .downward = .ok st) (hm : st.toNumber .to_nearest = .ok m) :
    0 ≤ A.toRat + m.toRat := by
  unfold sumRoundAndSubtract at h
  by_cases hint : nt.isIntegral = true
  · rw [if_pos hint] at h
    obtain ⟨x, hx, h⟩ := bind_ok_peel _ _ _ h
    obtain rfl : x = st := Except.ok.inj h
    have hst0 := STAmount.ofNumber_nonneg nt c _ x hc (Number.negative_false_of_nonneg c hc hc0) hx
    rw [(STAmount.ofNumber_toNumber_exact nt c _ _ x m hc (fun _ => hc0) hx hm).1]
    linarith
  · rw [if_neg hint] at h
    have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    subst hfr
    have hAb := hAb rfl
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨d, hd, h⟩ := bind_ok_peel _ _ _ h
    have hErange : (-96 : ℤ) ≤ E ∧ E ≤ 80 := (postSumExponent_range _ _ _ _ _ he.1 he.2 hE).2
    obtain ⟨-, hs0⟩ := Number.operator_add_downward_nonneg_le A c sum hA hc hA0 hc0 hsum
    have hsn := Number.operator_add_isNormalized_any A c sum _ hA hc hsum
    obtain ⟨hs'0, -, hs'n⟩ := STAmount.roundToNumericType_downward_le sum sum' E hsn hs0 hErange hsum'
    have hdn := Number.operator_sub_isNormalized_any sum' A d _ hs'n hA hd
    have hdA : -A.toRat ≤ d.toRat := by
      by_cases hdm : d.mantissa_ = 0
      · rw [Number.toRat_eq_zero_of_mantissa_zero d hdm]; linarith
      · obtain ⟨n, hn, hv⟩ := operator_sub_rounded_downward sum' A d hs'n hA hd hdm
        rw [hv]
        have := Number.lower_tight _ n hn A.operator_neg (Number.operator_neg_isNormalized A hA)
          (by rw [Number.toRat_neg]; linarith)
        rwa [Number.toRat_neg] at this
    rw [(STAmount.ofNumber_toNumber_exact .fractional d _ _ st m hdn (fun h => by cases h) h hm).1]
    by_cases hd0 : 0 ≤ d.toRat
    · have := STAmount.ofNumber_nonneg .fractional d _ st hdn (Number.negative_false_of_nonneg d hdn hd0) h
      linarith
    · push Not at hd0
      have hdm : d.mantissa_ ≠ 0 := fun h0 => by
        rw [Number.toRat_eq_zero_of_mantissa_zero d h0] at hd0; exact lt_irrefl _ hd0
      have hneg : d.negative_ = true := by
        cases hn : d.negative_
        · have := Number.toRat_nonneg_of_nonnegative d hn; linarith
        · rfl
      -- a value of magnitude below `10^96` has an exponent far below the top
      have hexp : d.exponent_ + 4 ≤ maxExponent := by
        obtain ⟨hlo, -⟩ := hdn.mantissaBounds_nat hdm
        have hv := Number.toRat_of_neg d hneg
        by_contra hc'
        push Not at hc'
        have hme : maxExponent = 32768 := rfl
        have hbig : (10 : ℚ) ^ (96 : ℤ) ≤ (d.mantissa_.toNat : ℚ) * 10 ^ d.exponent_ := by
          have h1 : (10 : ℚ) ^ (18 : ℕ) ≤ (d.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
          have h2 : (10 : ℚ) ^ (78 : ℤ) ≤ 10 ^ d.exponent_ := zpow_le_zpow_right₀ (by norm_num) (by omega)
          calc (10 : ℚ) ^ (96 : ℤ) = 10 ^ (18 : ℕ) * 10 ^ (78 : ℤ) := by norm_num
            _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)
        have : (10 : ℚ) ^ (96 : ℤ) = 10 ^ 96 := by norm_num
        linarith
      have := STAmount.ofNumber_frac_downward_neg_ge d st hdn hneg hexp h
      linarith

/-- A value below `10^(16 + b)` reports the base exponent `b` as its scale. -/
lemma numberExponent_at_base (n : Number) (b : Int) (nt : NumericType) (e : Int) (hn : n.isNormalized)
    (h0 : 0 ≤ n.toRat) (hb : (-96 : ℤ) ≤ b) (hint : nt.isIntegral = true → b = 0)
    (hlt : n.toRat < 10 ^ (16 + b)) (h : numberExponent n b nt = .ok e) : e = b := by
  have hge := numberExponent_ge _ _ _ _ h
  cases hnt : nt with
  | fractional =>
    rw [hnt] at h
    by_contra hne
    have hlt' : b < e := lt_of_le_of_ne hge (Ne.symm hne)
    obtain ⟨-, hbig⟩ := numberExponent_frac_lower n b e hn h0 (by omega) h hlt'
    have : (10 : ℚ) ^ (16 + b) ≤ 10 ^ (e + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  | integral mv mo ms msh =>
    have hb0 := hint (by rw [hnt]; rfl)
    subst hb0
    unfold numberExponent at h
    by_cases hz : n.operator_eq Number.zero = true
    · simp only [hz, if_true, pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
    · simp only [hz, Bool.false_eq_true, if_false] at h
      cases ha : STAmount.ofNumber nt n .downward with
      | error err => rw [ha] at h; simp [bind, Except.bind] at h
      | ok st =>
        rw [ha] at h
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        have hoff := (STAmount.ofNumber_integral_canonical nt n _ st (by rw [hnt]; rfl) ha).1.offset_zero
        rw [← h, show st.exponent = st.mOffset from rfl, hoff]
        rfl

end XRPL.Model.Lending
