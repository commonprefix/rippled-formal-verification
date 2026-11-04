import XRPL.Properties.Vault.Proofs.WithdrawMono.Exponent
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Vault.Common.MonotoneCore
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.SameSign

/-! # `postSumExponent` monotonicity

A larger delta never gives a finer post-sum grid. The sum packs downward to 16 digits, so its
exponent steps up exactly at the powers of ten, and a `to_nearest` sum only crosses such a power when
the exact sum sits just below it, where the rounding picks a nearest representable. -/

namespace XRPL.Model.Protocol

open XRPL.Model.SingleAssetVault

/-- The downward 16-digit pack of a positive 19-digit mantissa truncates. -/
private lemma normalizeToRange_16_downward_eq (n : Number) (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat)
    (h_hi : n.mantissa_.toNat < 10 ^ 19) (hneg : n.negative_ = false)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 3 ≤ maxExponent) :
    n.normalizeToRange cMinValue cMaxValue .downward
      = .ok ((n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
  obtain ⟨g, _, hsbit, _, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ .downward h_lo h_hi he_lo he_hi
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hb : (g.round .downward == 1 ||
      (g.round .downward == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = false := by
    have : g.round .downward = -1 ∨ g.round .downward = -2 := by
      unfold Guard.round
      rw [hsbit, hneg]
      split_ifs <;> simp_all
    rcases this with h | h <;> rw [h] <;> rfl
  unfold Number.normalizeToRange
  rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) .downward .normalize2 hb
    (by rw [cMinValue_val, hm3]; omega) (by rw [cMaxValue_val, hm3]; omega) (by omega) (by omega)]
  simp [RoundResult.toNumber, hneg]

/-- A nonzero nonnegative normalized `Number` sits below `10 ^ (exponent + 19)`. -/
private lemma Number.toRat_lt_pow_exponent_add (n : Number) (hn : n.isNormalized) (hnz : n.mantissa_ ≠ 0)
    (hneg : n.negative_ = false) : n.toRat < (10 : ℚ) ^ (n.exponent_ + 19) := by
  obtain ⟨-, hm_hi⟩ := hn.mantissaBounds_nat hnz
  have hm : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ 19 := by exact_mod_cast hm_hi
  rw [Number.toRat_of_nonneg n hneg, show n.exponent_ + 19 = n.exponent_ + (19 : ℕ) by push_cast; ring,
    zpow_add₀ (by norm_num), zpow_natCast, mul_comm]
  exact mul_lt_mul_of_pos_left hm (zpow_pos (by norm_num) _)

/-- Exponent of a positive fractional `.downward` `ofNumber`. The pack drops three digits, so the exponent is
three above the `Number`'s, unless it underflows and the result is zero. -/
private lemma STAmount.ofNumber_frac_downward_exp (n : Number) (r : STAmount) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hnz : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber .fractional n .downward = .ok r) :
    (n.exponent_ + 3 < -96 ∧ r.mValue = 0 ∧ r.exponent = -100) ∨
      (-96 ≤ n.exponent_ + 3 ∧ r.mValue ≠ 0 ∧ r.exponent = n.exponent_ + 3) := by
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ n.exponent_ := Number.exponent_ge_min n hn hnz
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true))] at hok
  rw [hneg_dec] at hok
  simp only [Bool.false_eq_true, if_false] at hok
  cases hnorm : n.normalizeToRange kMinValue kMaxValue .downward with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : n.normalizeToRange cMinValue cMaxValue .downward = .ok (mant, exp) := hnorm
    have he_hi := normalizeToRange_iou_exp_hi n .downward mant exp hr_lo hr_hi hnorm'
    rw [normalizeToRange_16_downward_eq n hr_lo hr_hi hneg (by omega) he_hi, Except.ok.injEq, Prod.mk.injEq] at hnorm'
    obtain ⟨hmant, hexp⟩ := hnorm'
    subst hmant hexp
    have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
      m_div_thousand_toNat n.mantissa_
    have hmu : (n.mantissa_ / 10 / 10 / 10).toInt64.toUInt64 = n.mantissa_ / 10 / 10 / 10 := rfl
    rw [hmu] at hok
    have hlo15 : 10 ^ 15 ≤ (n.mantissa_ / 10 / 10 / 10).toNat := by rw [hm3]; omega
    have hhi16 : (n.mantissa_ / 10 / 10 / 10).toNat < 10 ^ 16 := by rw [hm3]; omega
    by_cases hz : r.mValue = 0
    · obtain ⟨hlt, hoff⟩ := WdMono.checked_frac_zero _ _ false .downward hlo15 hhi16 (by omega) he_hi r hok hz
      exact Or.inl ⟨hlt, hz, hoff⟩
    · obtain ⟨hlo96, _, hres⟩ := STAmount.checked_iou_cases .fractional _ _ false .downward rfl hlo15 hhi16
        (by omega) he_hi r hok hz
      exact Or.inr ⟨hlo96, hz, by rw [hres]; rfl⟩

/-- A post-sum exponent above the floor marks a large sum. That exponent is three above the sum's own, so the
sum reaches `10 ^ (e + 15)`. -/
lemma numberExponent_frac_lower (n : Number) (exponent e : Int) (hn : n.isNormalized)
    (hnn : 0 ≤ n.toRat) (hlo : -100 ≤ exponent)
    (hok : numberExponent n exponent .fractional = .ok e) (hgt : exponent < e) :
    e = n.exponent_ + 3 ∧ (10 : ℚ) ^ (e + 15) ≤ n.toRat := by
  unfold numberExponent at hok
  by_cases hz : n.operator_eq Number.zero = true
  · simp only [hz, if_true, pure, Except.pure, Except.ok.injEq] at hok
    omega
  simp only [hz, Bool.false_eq_true, if_false] at hok
  have hnz : n.mantissa_ ≠ 0 := by
    intro hm
    rw [Number.eq_zero_of_mantissa_zero n hn hm] at hz
    exact hz (by decide)
  have hneg : n.negative_ = false := Number.negative_false_of_nonneg n hn hnn
  cases ha : STAmount.ofNumber .fractional n .downward with
  | error err => rw [ha] at hok; simp [bind, Except.bind, pure, Except.pure] at hok
  | ok a =>
    rw [ha] at hok
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hok
    have hmax : max exponent a.exponent = e := hok
    rcases STAmount.ofNumber_frac_downward_exp n a hn hneg hnz ha with ⟨_, _, hae⟩ | ⟨_, _, hae⟩
    · omega
    · have he : e = n.exponent_ + 3 := by omega
      refine ⟨he, ?_⟩
      obtain ⟨hm_lo, -⟩ := hn.mantissaBounds_nat hnz
      have hm : ((10 : ℚ) ^ 18) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hm_lo
      rw [Number.toRat_of_nonneg n hneg, he, show n.exponent_ + 3 + 15 = n.exponent_ + (18 : ℕ) by push_cast; ring,
        zpow_add₀ (by norm_num), zpow_natCast, mul_comm]
      exact mul_le_mul_of_nonneg_right hm (zpow_pos (by norm_num) _).le

/-- A large sum lifts the post-sum exponent. A sum of at least `10 ^ (k + 15)` reports an
exponent of at least `k`. -/
lemma numberExponent_frac_of_le (n : Number) (exponent e k : Int) (hn : n.isNormalized)
    (hk96 : -96 ≤ k) (hk : (10 : ℚ) ^ (k + 15) ≤ n.toRat)
    (hok : numberExponent n exponent .fractional = .ok e) : k ≤ e := by
  have hpos : 0 < n.toRat := lt_of_lt_of_le (zpow_pos (by norm_num) _) hk
  have hnz : n.mantissa_ ≠ 0 := fun hm => by
    rw [Number.toRat_eq_zero_of_mantissa_zero n hm] at hpos; exact lt_irrefl _ hpos
  have hneg : n.negative_ = false := Number.negative_false_of_nonneg n hn hpos.le
  -- the sum sits below `10 ^ (exponent_ + 19)`, so `k ≤ exponent_ + 3`
  have hk3 : k ≤ n.exponent_ + 3 := by
    by_contra hc
    push Not at hc
    have h1 := Number.toRat_lt_pow_exponent_add n hn hnz hneg
    have h2 : (10 : ℚ) ^ (n.exponent_ + 19) ≤ 10 ^ (k + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  unfold numberExponent at hok
  have hz : ¬ n.operator_eq Number.zero = true := Number.not_operator_eq_zero_of_mantissa_ne hnz
  simp only [hz, Bool.false_eq_true, if_false] at hok
  cases ha : STAmount.ofNumber .fractional n .downward with
  | error err => rw [ha] at hok; simp [bind, Except.bind, pure, Except.pure] at hok
  | ok a =>
    rw [ha] at hok
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hok
    have hmax : max exponent a.exponent = e := hok
    rcases STAmount.ofNumber_frac_downward_exp n a hn hneg hnz ha with ⟨hlt, _, _⟩ | ⟨_, _, hae⟩
    · omega
    · omega

/-- A post-sum exponent bounds the sum from above. The sum stays below `10 ^ (e + 16)`, sixteen
digits above the grid it reports. -/
lemma numberExponent_frac_lt (n : Number) (exponent e : Int) (hn : n.isNormalized) (hlo : -97 ≤ exponent)
    (hok : numberExponent n exponent .fractional = .ok e) : n.toRat < (10 : ℚ) ^ (e + 16) := by
  have hep : (0 : ℚ) < (10 : ℚ) ^ (e + 16) := zpow_pos (by norm_num) _
  by_cases hpos : n.toRat ≤ 0
  · linarith
  push Not at hpos
  have hnz : n.mantissa_ ≠ 0 := fun hm => by
    rw [Number.toRat_eq_zero_of_mantissa_zero n hm] at hpos; exact lt_irrefl _ hpos
  have hneg : n.negative_ = false := Number.negative_false_of_nonneg n hn hpos.le
  have h1 := Number.toRat_lt_pow_exponent_add n hn hnz hneg
  unfold numberExponent at hok
  have hz : ¬ n.operator_eq Number.zero = true := Number.not_operator_eq_zero_of_mantissa_ne hnz
  simp only [hz, Bool.false_eq_true, if_false] at hok
  cases ha : STAmount.ofNumber .fractional n .downward with
  | error err => rw [ha] at hok; simp [bind, Except.bind, pure, Except.pure] at hok
  | ok a =>
    rw [ha] at hok
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hok
    have hmax : max exponent a.exponent = e := hok
    have hle : n.exponent_ + 19 ≤ e + 16 := by
      rcases STAmount.ofNumber_frac_downward_exp n a hn hneg hnz ha with ⟨hlt, _, _⟩ | ⟨_, _, hae⟩
      · omega
      · omega
    exact lt_of_lt_of_le h1 (zpow_le_zpow_right₀ (by norm_num) hle)

/-- A same-sign positive `to_nearest` sum whose truth lies just below `10 ^ 18 · 10 ^ j`, above the
grid point `(10 ^ 18 - 1) · 10 ^ j`, is a nearest representable. -/
lemma add_nearestTo_below_pow (x y s : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hxn : x.negative_ = false) (hyn : y.negative_ = false)
    (hnz : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .to_nearest = .ok s) (j : ℤ)
    (hlo : (999999999999999999 : ℚ) * 10 ^ j < x.toRat + y.toRat)
    (hhi : x.toRat + y.toRat < (1000000000000000000 : ℚ) * 10 ^ j) :
    s.NearestTo (x.toRat + y.toRat) := by
  obtain ⟨zm, ze', f, g, res_pos, hzm_lo, hzm_hi, hf_nn, hf_lt, -, hval, hrup, habs, hres_ne,
      hrep, hsneg, -, -, -⟩ :=
    operator_add_algorithmic_facts_same_sign_to_nearest x y s hx hy hxm hym (by rw [hxn, hyn]) hnz hok
  set t := x.toRat + y.toRat with ht_def
  have hj : (0 : ℚ) < 10 ^ j := zpow_pos (by norm_num) _
  have hpos : 0 < t := lt_trans (by positivity) hlo
  have htv : t = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by rw [← abs_of_pos hpos, hval]
  have hze : (0 : ℚ) < 10 ^ ze' := zpow_pos (by norm_num) _
  have hmaxUp : maxRepUp.toNat = 9223372036854775810 := by decide
  have hzmq_hi : (zm.toNat : ℚ) ≤ 9223372036854775810 := by exact_mod_cast (hmaxUp ▸ hzm_hi)
  have hzmq_lo : (922337203685477580 : ℚ) ≤ (zm.toNat : ℚ) := by exact_mod_cast hzm_lo
  have htlo : (zm.toNat : ℚ) * 10 ^ ze' ≤ t := by rw [htv]; nlinarith
  have hthi : t < ((zm.toNat : ℚ) + 1) * 10 ^ ze' := by rw [htv]; nlinarith
  -- the cell sits at `ze' = j` with `zm = 10 ^ 18 - 1`
  have hze_eq : ze' = j := by
    rcases lt_trichotomy ze' j with h | h | h
    · exfalso
      have h1 : (10 : ℚ) ^ ze' * 10 ≤ 10 ^ j := by
        rw [← zpow_add_one₀ (by norm_num)]; exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : t < 9223372036854775811 * 10 ^ ze' := by nlinarith
      nlinarith
    · exact h
    · exfalso
      have h1 : (10 : ℚ) ^ j * 10 ≤ 10 ^ ze' := by
        rw [← zpow_add_one₀ (by norm_num)]; exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : (9223372036854775800 : ℚ) * 10 ^ j ≤ t := by nlinarith
      nlinarith
  subst hze_eq
  have hzm_eq : zm.toNat = 999999999999999999 := by
    have ha : (zm.toNat : ℚ) < 1000000000000000000 := by nlinarith
    have hb : (999999999999999998 : ℚ) < (zm.toNat : ℚ) := by nlinarith
    have ha' : zm.toNat < 1000000000000000000 := by exact_mod_cast ha
    have hb' : 999999999999999998 < zm.toNat := by exact_mod_cast hb
    omega
  have hmax : maxRep.toNat = 9223372036854775807 := by decide
  have hclean : zm.toNat + 1 ≤ maxRep.toNat := by omega
  have hs_nn : 0 ≤ s.toRat := Number.toRat_nonneg_of_nonnegative s (hsneg.trans hxn)
  have hs_abs : s.toRat = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ := by
    rw [← abs_of_nonneg hs_nn]; exact habs
  have hcase := doRoundUp_clean_down_up g zm ze' f res_pos s _ hrep hrup hs_abs hres_ne hclean
  exact Number.nearestTo_of_gap t f zm ze' s hpos htv hf_nn hf_lt (by omega) (by omega) hcase

/-- The post-sum exponent is monotone in the delta. On a nonnegative total, a larger nonnegative
delta never gives a finer post-sum grid. -/
lemma postSumExponent_mono (A d₁ d₂ : Number) (exponent e₁ e₂ : Int)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (hd₁ : d₁.isNormalized) (hd₂ : d₂.isNormalized)
    (hd₁0 : 0 ≤ d₁.toRat) (hle : d₁.toRat ≤ d₂.toRat) (hlo : -96 ≤ exponent)
    (he₁ : postSumExponent A d₁ exponent .fractional = .ok e₁)
    (he₂ : postSumExponent A d₂ exponent .fractional = .ok e₂) :
    e₁ ≤ e₂ := by
  obtain ⟨s₁, hs₁, hn₁⟩ := postSumExponent_reduces A d₁ exponent .fractional e₁ he₁
  obtain ⟨s₂, hs₂, hn₂⟩ := postSumExponent_reduces A d₂ exponent .fractional e₂ he₂
  have hge₂ := numberExponent_ge s₂ exponent .fractional e₂ hn₂
  by_cases hgt : exponent < e₁
  swap
  · omega
  have hd₂0 : 0 ≤ d₂.toRat := le_trans hd₁0 hle
  have hr₁ := operator_add_rounded_to_nearest A d₁ s₁ hA hd₁ hs₁
  have hr₂ := operator_add_rounded_to_nearest A d₂ s₂ hA hd₂ hs₂
  have hs₁n : s₁.isNormalized := operator_add_isNormalized_to_nearest_sz A d₁ s₁ hA hd₁ hs₁
  have hs₂n : s₂.isNormalized := operator_add_isNormalized_to_nearest_sz A d₂ s₂ hA hd₂ hs₂
  have hs₁0 : 0 ≤ s₁.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg s₁ _ hr₁ (by linarith)
  obtain ⟨-, hP₁⟩ := numberExponent_frac_lower s₁ exponent e₁ hs₁n hs₁0 (by omega) hn₁ hgt
  have he₁hi : e₁ ≤ 80 := by
    rcases numberExponent_range s₁ exponent .fractional e₁ hn₁ with h | h | h <;> omega
  refine numberExponent_frac_of_le s₂ exponent e₂ e₁ hs₂n (by omega) ?_ hn₂
  have hj : (0 : ℚ) < 10 ^ (e₁ - 3) := zpow_pos (by norm_num) _
  have hpow : (10 : ℚ) ^ (e₁ + 15) = 1000000000000000000 * 10 ^ (e₁ - 3) := by
    rw [show e₁ + 15 = (e₁ - 3) + (18 : ℕ) by push_cast; ring, zpow_add₀ (by norm_num), zpow_natCast]
    ring
  obtain ⟨P, hPn, hPv⟩ := Number.exists_normalized_int_mul_pow 1 (e₁ + 15) (by norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hPv' : P.toRat = 10 ^ (e₁ + 15) := by rw [hPv]; push_cast; ring
  by_cases hbig : (10 : ℚ) ^ (e₁ + 15) ≤ A.toRat + d₂.toRat
  · rw [← hPv']
    exact Number.RoundsToRepresentable.ge_of_ge_normalized s₂ _ hr₂ P hPn (by rw [hPv']; exact hbig)
  push Not at hbig
  -- the grid point just below the power bounds the smaller exact sum from below
  obtain ⟨L, hLn, hLv⟩ := Number.exists_normalized_int_mul_pow 999999999999999999 (e₁ - 3) (by norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hLv' : L.toRat = 999999999999999999 * 10 ^ (e₁ - 3) := by rw [hLv]; push_cast; ring
  have hlo₁ : (999999999999999999 : ℚ) * 10 ^ (e₁ - 3) < A.toRat + d₁.toRat := by
    by_contra hc
    push Not at hc
    have := Number.RoundsToRepresentable.le_of_le_normalized s₁ _ hr₁ L hLn (by rw [hLv']; exact hc)
    rw [hLv'] at this
    nlinarith
  have hhi₂ : A.toRat + d₂.toRat < 1000000000000000000 * 10 ^ (e₁ - 3) := by rw [← hpow]; exact hbig
  by_cases hAm : A.mantissa_ = 0
  · -- a zero total: both sums are exact
    have hA0' : A.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero A hAm
    have h1 := Number.RoundsToRepresentable.eq_of_representable s₁ _ hr₁ d₁ hd₁ (by rw [hA0']; ring)
    have h2 := Number.RoundsToRepresentable.eq_of_representable s₂ _ hr₂ d₂ hd₂ (by rw [hA0']; ring)
    rw [h2]
    rw [h1] at hP₁
    linarith
  by_cases hd₁m : d₁.mantissa_ = 0
  · -- a zero delta: the smaller sum is the total, which is already below the power
    have hd0 : d₁.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero d₁ hd₁m
    have h1 := Number.RoundsToRepresentable.eq_of_representable s₁ _ hr₁ A hA (by rw [hd0]; ring)
    rw [h1] at hP₁
    linarith
  have hd₂m : d₂.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero d₂ h] at hle
    exact Number.toRat_ne_zero_of_mantissa_ne_zero d₁ hd₁m (le_antisymm hle hd₁0)
  have hAn : A.negative_ = false := Number.negative_false_of_nonneg A hA hA0
  have hd₁n : d₁.negative_ = false := Number.negative_false_of_nonneg d₁ hd₁ hd₁0
  have hd₂n : d₂.negative_ = false := Number.negative_false_of_nonneg d₂ hd₂ hd₂0
  have hnz : ∀ y : Number, y.mantissa_ ≠ 0 → y.negative_ = false →
      ¬ A.operator_eq y.operator_neg = true := by
    intro y hym hyn h
    unfold Number.operator_eq Number.operator_neg at h
    simp [hym, hAn, hyn] at h
  -- both sums round to a nearest representable in this window
  have hn₁ := add_nearestTo_below_pow A d₁ s₁ hA hd₁ hAm hd₁m hAn hd₁n (hnz d₁ hd₁m hd₁n) hs₁
    (e₁ - 3) hlo₁ (by linarith)
  have hn₂ := add_nearestTo_below_pow A d₂ s₂ hA hd₂ hAm hd₂m hAn hd₂n (hnz d₂ hd₂m hd₂n) hs₂
    (e₁ - 3) (by linarith) hhi₂
  have hmono := round_mono_core _ _ s₁ s₂ hn₁ hn₂ hs₁n hs₂n (by linarith) (fun heq => by
    have hdd : d₁ = d₂ := Number.isNormalized.toRat_inj hd₁ hd₂ (by linarith)
    rw [hdd] at hs₁
    rw [Except.ok.inj (hs₁.symm.trans hs₂)])
  linarith

/-- Clamping twice changes nothing. A positive amount clamped onto the post-sum grid of a nonnegative total
is unchanged by a second clamp that keeps it nonzero. -/
lemma clampToSumExponent_twice (A : Number) (a c c' : STAmount) (exponent : Int)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat) (ha : a.Canonical) (hpos : 0 < a.toRat)
    (hlo : -96 ≤ exponent) (hhi : exponent ≤ 80)
    (h₁ : clampToSumExponent A a exponent = .ok c) (h₂ : clampToSumExponent A c exponent = .ok c')
    (hc'0 : c'.mValue ≠ 0) : c' = c := by
  by_cases hint : a.integral = true
  · -- integral amounts pass through both clamps
    have hca : c = a := clampToSumExponent_integral_nonneg A a c exponent hint hpos.le h₁
    subst hca
    exact clampToSumExponent_integral_nonneg A c c' exponent hint hpos.le h₂
  have hfr : a.integral = false := by simpa using hint
  have hia : a.IOUCanonical := ha.2 hfr
  have hcz_a : a.FracCanonZero := ⟨hia.is_fractional, Or.inl hia⟩
  have hc0 : c.mValue ≠ 0 := fun h => hc'0 (clampToSumExponent_zero A c c' exponent h h₂)
  obtain ⟨aNum, e₁, haN, he₁, -, hcval⟩ :=
    clampToSumExponent_frac_floor A a c exponent hcz_a hlo hhi hc0 h₁
  have hcF : c.FracCanonZero := clampToSumExponent_frac_shape A a c exponent hcz_a h₁
  have hci : c.IOUCanonical := hcF.2.resolve_right hc0
  have hcpos : 0 < c.toRat :=
    lt_of_le_of_ne (clampToSumExponent_frac_bounds A a c exponent hcz_a hlo hhi h₁).1
      (STAmount.toRat_ne_zero c hc0).symm
  have hcneg : c.mIsNegative = false := STAmount.mIsNegative_false_of_pos c hcpos
  have hcfr : c.integral = false := by unfold STAmount.integral; rw [hci.is_fractional]; rfl
  obtain ⟨cNum, e₂, hcN, he₂, hround⟩ := clampToSumExponent_frac_reduces A c c' exponent hcfr h₂
  rw [show c.negative = false from hcneg, if_neg (by decide)] at hround
  -- the amounts convert exactly, and the clamped one is the smaller
  obtain ⟨an, han, hanv, hann⟩ := STAmount.toNumber_iou_exact a .to_nearest hia
  obtain ⟨cn, hcn, hcnv, hcnn⟩ := STAmount.toNumber_iou_exact c .to_nearest hci
  rw [han, Except.ok.injEq] at haN
  rw [hcn, Except.ok.injEq] at hcN
  subst haN hcN
  have hnta : a.numericType = .fractional := hia.is_fractional
  have hntc : c.numericType = .fractional := hci.is_fractional
  rw [hnta] at he₁
  rw [hntc] at he₂
  have hle : cn.toRat ≤ an.toRat := by
    rw [hcnv, hanv]
    have := (clampToSumExponent_frac_bounds A a c exponent hcz_a hlo hhi h₁).2
    rwa [abs_of_pos hpos] at this
  have h21 : e₂ ≤ e₁ :=
    postSumExponent_mono A cn an exponent e₂ e₁ hA hA0 hcnn hann (by rw [hcnv]; exact hcpos.le) hle hlo he₂ he₁
  by_cases hge : e₂ ≤ c.exponent
  · exact STAmount.roundToExponent_ok_eq_self c c' e₂ .towards_zero (Or.inr (Or.inr hge)) hround
  -- off the early exit, the second clamp recomputes a canonical amount of the same value
  obtain ⟨-, he₂lo, he₂hi⟩ := postSumExponent_range A cn exponent .fractional e₂ hlo hhi he₂
  have hrnd := STAmount.roundToExponent_rounded c c' e₂ .towards_zero hci he₂lo he₂hi hc'0 hround
  simp only [RoundsToRepresentableAt] at hrnd
  change c'.toRat = _ at hrnd
  rw [if_pos hcpos.le] at hrnd
  have hgrid : ∃ z : ℤ, c.toRat = (z : ℚ) * 10 ^ e₂ := by
    refine ⟨⌊|a.toRat| / 10 ^ e₁⌋ * 10 ^ (e₁ - e₂).toNat, ?_⟩
    rw [hcval]
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]
    congr 2
    ring
  obtain ⟨z, hz⟩ := hgrid
  have hval : c'.toRat = c.toRat := by
    rw [hrnd, hz, mul_div_assoc, div_self (zpow_pos (by norm_num : (0 : ℚ) < 10) e₂).ne', mul_one,
      Int.floor_intCast]
  have hc'F : c'.FracCanonZero := STAmount.roundToExponent_fczr c c' e₂ .towards_zero hcF hround
  exact STAmount.eq_of_exactCanonical c' c (Or.inl (hc'F.2.resolve_right hc'0)) (Or.inl hci)
    (hc'F.1.trans hcF.1.symm) hc'0 hval

end XRPL.Model.Protocol
