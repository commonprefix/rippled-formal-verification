import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRange
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.Number.Add.RoundsWithin
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.Common.STAmountToNumber

/-! # Grid arithmetic for the conditional `associateAsset` results

When a fractional stored total `X` is on the asset's `STAmount` grid and a positive
canonical payout is clamped to the post-subtraction exponent, the stored difference is
again on the grid, unless it underflows the IOU floor `10⁻⁸¹`. -/

namespace XRPL.Model.SingleAssetVault.CatHI

open XRPL.Model.Protocol

/-- A normalized non-negative `Number` has a clear sign bit. -/
lemma Number.negative_false_of_norm_nonneg (n : Number) (hn : n.isNormalized)
    (h0 : 0 ≤ n.toRat) : n.negative_ = false := by
  rcases hb : n.negative_ with _ | _
  · rfl
  · exfalso
    have hle := Number.toRat_nonpos_of_negative n hb
    have hm0 : n.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp (le_antisymm hle h0)
    exact Number.mantissa_ne_zero_of_negative n hn hb hm0


/-- `STAmount.checked` is the identity on a canonical 16-digit non-negative IOU record. -/
lemma STAmount.checked_iou_id (mant : UInt64) (exp : Int) (mode : rounding_mode)
    (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16)
    (he_lo : (-96 : Int) ≤ exp) (he_hi : exp ≤ 80) :
    STAmount.checked .fractional mant exp false mode
      = .ok ⟨.fractional, mant, exp, false⟩ := by
  set s : STAmount := ⟨.fractional, mant, exp, false⟩ with hs
  have hc : s.IOUCanonical := ⟨rfl, h_lo, h_hi, he_lo, he_hi⟩
  have hint : ¬ s.integral = true := by
    unfold STAmount.integral; rw [hs]; exact Bool.false_ne_true
  have hiou := STAmount.iou_canonical_id s mode hc
  have hfit : mant.toNat < 2 ^ 63 := by omega
  have hsd : s.signedDrops = (mant.toNat : Int) := by
    unfold STAmount.signedDrops; simp [hs]
  have hsdi : s.signedDrops.toInt64 = mant.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt s (show s.mValue.toNat < 10 ^ 16 from h_hi), hsd]
    exact (UInt64.toInt64_toInt_of_lt mant hfit).symm
  have hmi : mant.toInt64.toInt = (mant.toNat : Int) := UInt64.toInt64_toInt_of_lt mant hfit
  have hzero : (0 : Int64).toInt = 0 := by decide
  have hnneg : ¬ (mant.toInt64 < 0) := by
    rw [Int64.lt_iff_toInt_lt, hmi, hzero]; omega
  have hne : ¬ (mant.toInt64 = 0) := by
    intro h; rw [h, hzero] at hmi; omega
  unfold STAmount.checked STAmount.canonicalize
  rw [show STAmount.unchecked .fractional mant exp false = s from rfl]
  rw [if_neg hint, hiou]
  simp only [IOUAmount.signum, hsdi, if_neg hnneg, bne_iff_ne, ne_eq, hne, not_false_eq_true, if_true]
  norm_num
  rfl



/-- `Number.operator_eq` is structural equality. -/
lemma Number.eq_of_operator_eq {x y : Number} (h : x.operator_eq y = true) : x = y := by
  unfold Number.operator_eq at h
  obtain ⟨a, b, c⟩ := x; obtain ⟨d, e, f⟩ := y
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  subst h1; subst h2; subst h3; rfl

/-- `decide (n.signum < 0)` is the stored sign flag. -/
lemma Number.signum_neg_decide' (n : Number) : decide (n.signum < 0) = n.negative_ := by
  unfold Number.signum
  cases hneg : n.negative_
  · simp only [Bool.false_eq_true, if_false]
    split <;> simp
  · simp

/-- **`ofNumber` is the identity on a 16-digit-representable normalized `Number`.**
A non-negative normalized `Number` whose 19-digit mantissa has three trailing zeros,
at an offset the IOU range admits, packs to the `STAmount` with the same value. -/
lemma STAmount.ofNumber_frac_grid (x : Number) (mode : rounding_mode)
    (hneg : x.negative_ = false)
    (h_lo : 10 ^ 18 ≤ x.mantissa_.toNat) (h_hi : x.mantissa_.toNat < 10 ^ 19)
    (h_mod : x.mantissa_.toNat % 1000 = 0)
    (he_lo : (-96 : Int) ≤ x.exponent_ + 3) (he_hi : x.exponent_ + 3 ≤ 80) :
    STAmount.ofNumber .fractional x mode
      = .ok ⟨.fractional, x.mantissa_ / 10 / 10 / 10, x.exponent_ + 3, false⟩ := by
  have hm3 : (x.mantissa_ / 10 / 10 / 10).toNat = x.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat x.mantissa_
  have hmlo : 10 ^ 15 ≤ (x.mantissa_ / 10 / 10 / 10).toNat := by rw [hm3]; omega
  have hmhi : (x.mantissa_ / 10 / 10 / 10).toNat < 10 ^ 16 := by rw [hm3]; omega
  have hnr : x.normalizeToRange cMinValue cMaxValue mode
      = .ok ((x.mantissa_ / 10 / 10 / 10).toInt64, x.exponent_ + 3) := by
    rw [normalizeToRange_16_exact x mode h_lo h_hi h_mod
      (by unfold minExponent; omega) (by unfold maxExponent; omega), hneg]
    simp
  unfold STAmount.ofNumber
  simp only [Number.signum_neg_decide', hneg, Bool.false_eq_true, if_false]
  rw [if_neg (show ¬ (NumericType.fractional.isIntegral = true) from by decide)]
  rw [nr_aux x mode hnr]
  simp only []
  rw [show ((x.mantissa_ / 10 / 10 / 10).toInt64).toUInt64 = x.mantissa_ / 10 / 10 / 10 from rfl]
  exact STAmount.checked_iou_id _ _ mode hmlo hmhi he_lo he_hi
where
  nr_aux (x : Number) (mode : rounding_mode)
      (h : x.normalizeToRange cMinValue cMaxValue mode
        = .ok ((x.mantissa_ / 10 / 10 / 10).toInt64, x.exponent_ + 3)) :
      x.normalizeToRange kMinValue kMaxValue mode
        = .ok ((x.mantissa_ / 10 / 10 / 10).toInt64, x.exponent_ + 3) := h



/-- `Number.zero` is exact for any asset. -/
lemma STAmount.isRounded_zero (nt : NumericType) : STAmount.isRounded nt Number.zero = false := by
  cases nt <;> rfl

/-- **The grid criterion.** A non-negative normalized `Number` whose 19-digit mantissa
has three trailing zeros, at an offset the IOU range admits, is on the fractional
`STAmount` grid: `associateAsset` would not move it. -/
lemma STAmount.isRounded_frac_false_of_grid (x : Number)
    (hneg : x.negative_ = false)
    (h_lo : 10 ^ 18 ≤ x.mantissa_.toNat) (h_hi : x.mantissa_.toNat < 10 ^ 19)
    (h_mod : x.mantissa_.toNat % 1000 = 0)
    (he_lo : (-96 : Int) ≤ x.exponent_ + 3) (he_hi : x.exponent_ + 3 ≤ 80) :
    STAmount.isRounded .fractional x = false := by
  set m : UInt64 := x.mantissa_ / 10 / 10 / 10 with hm
  have hm3 : m.toNat = x.mantissa_.toNat / 1000 := m_div_thousand_toNat x.mantissa_
  have hmlo : 10 ^ 15 ≤ m.toNat := by rw [hm3]; omega
  have hmhi : m.toNat < 10 ^ 16 := by rw [hm3]; omega
  have hback : m * 10 * 10 * 10 = x.mantissa_ := by
    apply UInt64.toNat_inj.mp
    rw [m_mul_thousand_no_overflow hmhi, hm3]
    omega
  have hof := STAmount.ofNumber_frac_grid x .to_nearest hneg h_lo h_hi h_mod he_lo he_hi
  have hc : (⟨.fractional, m, x.exponent_ + 3, false⟩ : STAmount).IOUCanonical :=
    ⟨rfl, hmlo, hmhi, he_lo, he_hi⟩
  have htn := STAmount.toNumber_iou_canonical (⟨.fractional, m, x.exponent_ + 3, false⟩ : STAmount)
    .to_nearest hc
  have hx : (⟨false, m * 10 * 10 * 10, x.exponent_ + 3 - 3⟩ : Number) = x := by
    rw [hback, show x.exponent_ + 3 - 3 = x.exponent_ from by ring]
    obtain ⟨xn, xm, xe⟩ := x
    simp only at hneg ⊢
    rw [hneg]
  have heq : Number.operator_eq x x = true := by unfold Number.operator_eq; simp
  have hconv : STAmount.equalAfterNumberConvert .fractional x = .ok true := by
    unfold STAmount.equalAfterNumberConvert
    simp only [hof]
    show (do let numValue ← (⟨.fractional, m, x.exponent_ + 3, false⟩ : STAmount).toNumber .to_nearest
             pure (numValue.operator_eq x)) = .ok true
    rw [htn]
    show Except.ok ((⟨false, m * 10 * 10 * 10, x.exponent_ + 3 - 3⟩ : Number).operator_eq x) = _
    rw [hx, heq]
  unfold STAmount.isRounded
  rw [hconv]
  rfl



/-- **The grid criterion, converse direction.** If `associateAsset` would not move a
normalized `Number`, then it is zero or its mantissa has three trailing zeros at an
offset the IOU range admits. -/
lemma Number.grid_of_isRounded_frac_false (x : Number) (hx : x.isNormalized)
    (h : STAmount.isRounded .fractional x = false) :
    x.mantissa_ = 0 ∨
      (x.mantissa_.toNat % 1000 = 0 ∧ (-96 : Int) ≤ x.exponent_ + 3 ∧ x.exponent_ + 3 ≤ 80) := by
  -- peel `isRounded`
  unfold STAmount.isRounded at h
  cases hconv : STAmount.equalAfterNumberConvert .fractional x with
  | error e => rw [hconv] at h; exact absurd h (by simp)
  | ok b =>
    rw [hconv] at h
    have hb : b = true := by cases b <;> simp at h ⊢
    subst hb
    unfold STAmount.equalAfterNumberConvert at hconv
    obtain ⟨st, hst, hconv⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hconv
    obtain ⟨n, hn, hconv⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hconv
    have hneq : n.operator_eq x = true :=
      Except.ok.inj (show (Except.ok (n.operator_eq x) : Except Error Bool) = .ok true from hconv)
    have hnx : n = x := Number.eq_of_operator_eq hneq
    rcases STAmount.ofNumber_frac_shape .fractional x .to_nearest st (by decide) hx hst with hc | hz
    · -- canonical: the lift pins the shape
      rw [STAmount.toNumber_iou_canonical st .to_nearest hc] at hn
      have hn' : (⟨st.mIsNegative, st.mValue * 10 * 10 * 10, st.mOffset - 3⟩ : Number) = x := by
        rw [← hnx]; exact Except.ok.inj hn
      have hmant : x.mantissa_ = st.mValue * 10 * 10 * 10 := by rw [← hn']
      have hexp : x.exponent_ = st.mOffset - 3 := by rw [← hn']
      refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [hmant, m_mul_thousand_no_overflow hc.mant_hi]; omega
      · rw [hexp]; have := hc.exp_lo; omega
      · rw [hexp]; have := hc.exp_hi; omega
    · -- flushed to zero: the round-trip returns the canonical zero
      have hnz : n = Number.zero := STAmount.toNumber_zero_eq st .to_nearest n hz hn
      rw [hnx] at hnz
      exact Or.inl (by rw [hnz]; rfl)



/-- `x` sits on the decimal grid of step `10 ^ g`. -/
def OnGridAt (x : ℚ) (g : ℤ) : Prop := ∃ k : ℤ, x = (k : ℚ) * 10 ^ g

lemma OnGridAt.mono {x : ℚ} {g g' : ℤ} (h : OnGridAt x g) (hle : g' ≤ g) : OnGridAt x g' := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * 10 ^ (g - g').toNat, ?_⟩
  have hg : (g - g').toNat = g - g' := Int.toNat_of_nonneg (by omega)
  push_cast
  rw [show ((10 : ℚ) ^ ((g - g').toNat : ℕ)) = (10 : ℚ) ^ (((g - g').toNat : ℕ) : ℤ) from
        (zpow_natCast 10 _).symm, hg, mul_assoc, ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0),
      show g - g' + g' = g from by ring]

lemma OnGridAt.sub {x y : ℚ} {g : ℤ} (hx : OnGridAt x g) (hy : OnGridAt y g) :
    OnGridAt (x - y) g := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; ring⟩

/-- A non-negative grid point bounded by `10¹⁶` steps has a natural coefficient `≤ 10¹⁶`. -/
lemma OnGridAt.nat_coeff {x : ℚ} {g : ℤ} (h : OnGridAt x g) (hnn : 0 ≤ x)
    (hub : x < (10 ^ 16 + 1) * (10 : ℚ) ^ g) :
    ∃ K : ℕ, K ≤ 10 ^ 16 ∧ x = (K : ℚ) * 10 ^ g := by
  obtain ⟨k, rfl⟩ := h
  have hpos : (0 : ℚ) < 10 ^ g := zpow_pos (by norm_num) _
  have hk0 : 0 ≤ k := by
    by_contra hneg
    push Not at hneg
    have : (k : ℚ) < 0 := by exact_mod_cast hneg
    nlinarith
  have hkle : k ≤ 10 ^ 16 := by
    by_contra hgt
    push Not at hgt
    have hq : ((10 : ℤ) ^ 16 + 1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hgt
    push_cast at hq
    nlinarith
  refine ⟨k.toNat, by omega, ?_⟩
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hk0).symm


/-! ## Bridges from the model records to `OnGridAt` -/

lemma Number.onGridAt_toRat (x : Number) (hneg : x.negative_ = false)
    (h_mod : x.mantissa_.toNat % 1000 = 0) : OnGridAt x.toRat (x.exponent_ + 3) := by
  refine ⟨(x.mantissa_.toNat / 1000 : ℕ), ?_⟩
  have hdiv : ((x.mantissa_.toNat / 1000 : ℕ) : ℚ) * 1000 = (x.mantissa_.toNat : ℚ) := by
    have h := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
    exact_mod_cast h
  have hpow : (10 : ℚ) ^ (x.exponent_ + 3) = (10 : ℚ) ^ x.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
    norm_num
  rw [Number.toRat_of_nonneg x hneg, hpow, ← hdiv]
  simp only [Int.cast_natCast]
  ring

lemma Number.toRat_lt_pow (x : Number) (hneg : x.negative_ = false)
    (h_hi : x.mantissa_.toNat < 10 ^ 19) :
    x.toRat < 10 ^ 16 * (10 : ℚ) ^ (x.exponent_ + 3) := by
  have hpow : (10 : ℚ) ^ (x.exponent_ + 3) = (10 : ℚ) ^ x.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
  have hp : (0 : ℚ) < (10 : ℚ) ^ x.exponent_ := zpow_pos (by norm_num) _
  have hm : (x.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast h_hi
  rw [Number.toRat_of_nonneg x hneg, hpow]
  nlinarith

lemma STAmount.onGridAt_toRat (s : STAmount) (hneg : s.mIsNegative = false) :
    OnGridAt s.toRat s.mOffset :=
  ⟨(s.mValue.toNat : ℤ), by rw [STAmount.toRat_of_nonneg s hneg]; push_cast; ring⟩

lemma STAmount.toRat_lt_pow (s : STAmount) (hneg : s.mIsNegative = false)
    (h_hi : s.mValue.toNat < 10 ^ 16) :
    s.toRat < 10 ^ 16 * (10 : ℚ) ^ s.mOffset := by
  have hp : (0 : ℚ) < (10 : ℚ) ^ s.mOffset := zpow_pos (by norm_num) _
  have hm : (s.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast h_hi
  rw [STAmount.toRat_of_nonneg s hneg]
  nlinarith



/-! ## The normalized witness for a grid value -/

/-- **Grid values are `Number`s, and on-grid ones.** A positive `K·10^g` with
`K ≤ 10¹⁶` that is neither below the IOU floor nor above the stored total's decade
is represented by a normalized `Number` whose mantissa has three trailing zeros and
whose 16-digit offset is in range — i.e. by an on-grid `Number`. -/
lemma Number.exists_grid_witness (K : ℕ) (g E : ℤ)
    (hKpos : 0 < K) (hK : K ≤ 10 ^ 16)
    (hg_lo : (-96 : ℤ) ≤ g) (hg_hi : g ≤ 80) (hE : E ≤ 80)
    (hlo : (10 : ℚ) ^ (-81 : ℤ) ≤ (K : ℚ) * 10 ^ g)
    (hhi : (K : ℚ) * 10 ^ g < 10 ^ 16 * (10 : ℚ) ^ E) :
    ∃ w : Number, w.isNormalized ∧ w.negative_ = false ∧ w.mantissa_ ≠ 0 ∧
      w.toRat = (K : ℚ) * 10 ^ g ∧ w.mantissa_.toNat % 1000 = 0 ∧
      10 ^ 18 ≤ w.mantissa_.toNat ∧ w.mantissa_.toNat < 10 ^ 19 ∧
      (-96 : ℤ) ≤ w.exponent_ + 3 ∧ w.exponent_ + 3 ≤ 80 := by
  -- pick a representation `k · 10 ^ s` with `k < 10¹⁶`
  obtain ⟨k, s, hk1, hk2, hs_lo, hs_hi, hval⟩ :
      ∃ (k : ℕ) (s : ℤ), 1 ≤ k ∧ k < 10 ^ 16 ∧ minExponent + 18 ≤ s ∧ s ≤ maxExponent ∧
        (k : ℚ) * 10 ^ s = (K : ℚ) * 10 ^ g := by
    by_cases hfull : K = 10 ^ 16
    · refine ⟨10 ^ 15, g + 1, by norm_num, by norm_num,
        by unfold minExponent; omega, by unfold maxExponent; omega, ?_⟩
      rw [hfull, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
      push_cast
      ring
    · exact ⟨K, g, hKpos, by omega, by unfold minExponent; omega,
        by unfold maxExponent; omega, rfl⟩
  obtain ⟨w, hwnorm, hwneg, hwne, hwval, hwmod, -, -⟩ :=
    exists_normalized_of_int_mul_pow k s hk1 hk2 hs_lo hs_hi
  rw [hval] at hwval
  obtain ⟨hm_lo, hm_hi⟩ := hwnorm.mantissaBounds_nat hwne
  -- value brackets from the mantissa window
  have hpow3 : (10 : ℚ) ^ (w.exponent_ + 3) = (10 : ℚ) ^ w.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
  have hp : (0 : ℚ) < (10 : ℚ) ^ w.exponent_ := zpow_pos (by norm_num) _
  have hmq_lo : ((10 : ℕ) ^ 18 : ℚ) ≤ (w.mantissa_.toNat : ℚ) := by exact_mod_cast hm_lo
  have hmq_hi : (w.mantissa_.toNat : ℚ) < ((10 : ℕ) ^ 19 : ℚ) := by exact_mod_cast hm_hi
  have hvform : w.toRat = (w.mantissa_.toNat : ℚ) * 10 ^ w.exponent_ :=
    Number.toRat_of_nonneg w hwneg
  have hband_lo : 10 ^ 15 * (10 : ℚ) ^ (w.exponent_ + 3) ≤ w.toRat := by
    rw [hvform, hpow3]; push_cast at hmq_lo; nlinarith
  have hband_hi : w.toRat < 10 ^ 16 * (10 : ℚ) ^ (w.exponent_ + 3) := by
    rw [hvform, hpow3]; push_cast at hmq_hi; nlinarith
  -- exponent window
  have he_hi : w.exponent_ + 3 ≤ 80 := by
    by_contra hcon
    push Not at hcon
    have h1 : (10 : ℚ) ^ (E + 1) ≤ (10 : ℚ) ^ (w.exponent_ + 3) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (E + 1) = (10 : ℚ) ^ E * 10 := by
      rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
    have hpE : (0 : ℚ) < (10 : ℚ) ^ E := zpow_pos (by norm_num) _
    rw [hwval] at hband_lo
    nlinarith
  have he_lo : (-96 : ℤ) ≤ w.exponent_ + 3 := by
    by_contra hcon
    push Not at hcon
    have h1 : (10 : ℚ) ^ (w.exponent_ + 3) ≤ (10 : ℚ) ^ (-97 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (-81 : ℤ) = 10 ^ 16 * (10 : ℚ) ^ (-97 : ℤ) := by
      rw [show (-81 : ℤ) = 16 + (-97 : ℤ) from by ring,
          zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
      norm_num
    rw [hwval] at hband_hi
    nlinarith [hlo, hband_hi, h1, h2]
  exact ⟨w, hwnorm, hwneg, hwne, hwval, hwmod, hm_lo, hm_hi, he_lo, he_hi⟩


/-! ## The stored subtraction -/

/-- **A subtraction whose exact difference is a grid value stores that value, and stores
it on-grid.** The `Number` window is 19 digits and a `K ≤ 10¹⁶` grid value needs 16, so
the stored `operator_sub` does not round; the stored record is then the grid witness of
`Number.exists_grid_witness`, which `STAmount.isRounded` accepts. -/
lemma Number.sub_grid_isRounded_false (X dn res : Number) (K : ℕ) (g E : ℤ)
    (hX : X.isNormalized) (hXneg : X.negative_ = false) (hXne : X.mantissa_ ≠ 0)
    (hd : dn.isNormalized) (hdneg : dn.negative_ = false) (hdne : dn.mantissa_ ≠ 0)
    (hres : res.isNormalized)
    (hK : K ≤ 10 ^ 16) (hg_lo : (-96 : ℤ) ≤ g) (hg_hi : g ≤ 80) (hE : E ≤ 80)
    (hval : X.toRat - dn.toRat = (K : ℚ) * 10 ^ g)
    (hhi : (K : ℚ) * 10 ^ g < 10 ^ 16 * (10 : ℚ) ^ E)
    (hnf : res.mantissa_ = 0 ∨ (10 : ℚ) ^ (-81 : ℤ) ≤ res.toRat)
    (hok : X.operator_sub dn .to_nearest = .ok res) :
    STAmount.isRounded .fractional res = false := by
  by_cases hz : res.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero res hres hz]
    exact STAmount.isRounded_zero .fractional
  -- the result is stored nonzero, so the side condition bites
  have hres_lo : (10 : ℚ) ^ (-81 : ℤ) ≤ res.toRat := hnf.resolve_left hz
  -- the negated subtrahend
  have hny : (dn.operator_neg).isNormalized := Number.operator_neg_isNormalized dn hd
  have hny_ne : (dn.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne dn hdne]; exact hdne
  have hny_neg : (dn.operator_neg).negative_ = true := by
    rw [Number.operator_neg_negative_of_ne dn hdne, hdneg]; rfl
  have hdiff : X.negative_ ≠ (dn.operator_neg).negative_ := by rw [hXneg, hny_neg]; simp
  have hnegval : (dn.operator_neg).toRat = -dn.toRat := Number.toRat_neg dn
  have hadd : Number.operator_add X dn.operator_neg .to_nearest = .ok res := hok
  -- the fast path would have stored zero, so the guard is open
  have hnot_eq : ¬ X.operator_eq (dn.operator_neg).operator_neg := by
    intro hq
    have : Number.operator_add X dn.operator_neg .to_nearest = .ok Number.zero := by
      unfold Number.operator_add
      rw [show (dn.operator_neg.operator_eq Number.zero) = false from by
            rw [Bool.eq_false_iff]; intro hg
            exact hny_ne (Number.mantissa_eq_zero_of_operator_eq_zero hg),
          show (X.operator_eq Number.zero) = false from by
            rw [Bool.eq_false_iff]; intro hg
            exact hXne (Number.mantissa_eq_zero_of_operator_eq_zero hg),
          show (X.operator_eq dn.operator_neg.operator_neg) = true from by simpa using hq]
      rfl
    rw [hadd] at this
    exact hz (by rw [Except.ok.inj this]; rfl)
  -- the rounding bound pins the exact difference away from zero
  have hround := operator_add_rounds_to_nearest X dn.operator_neg res hX hny hXne hny_ne
    hnot_eq hadd hz
  simp only [RoundsWithin, RatValued.toRat, hnegval] at hround
  have hround' : |res.toRat - (X.toRat - dn.toRat)| ≤ |X.toRat - dn.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) := by
    have : X.toRat + -dn.toRat = X.toRat - dn.toRat := by ring
    rwa [this] at hround
  rw [hval] at hround'
  -- so `K ≥ 1`, and in fact the value clears the IOU floor
  have hpg : (0 : ℚ) < (10 : ℚ) ^ g := zpow_pos (by norm_num) _
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with hk0 | hk
    · exfalso
      rw [hk0] at hround'
      simp only [Nat.cast_zero, zero_mul, sub_zero, abs_zero, zero_mul] at hround'
      have : res.toRat ≤ 0 := by
        have h := abs_le.mp hround'
        linarith [h.2]
      have hpos : (0 : ℚ) < (10 : ℚ) ^ (-81 : ℤ) := zpow_pos (by norm_num) _
      linarith
    · exact hk
  have hvalpos : (0 : ℚ) < (K : ℚ) * 10 ^ g := by
    have : (0 : ℚ) < (K : ℚ) := by exact_mod_cast hKpos
    positivity
  have hfloor : (10 : ℚ) ^ (-81 : ℤ) ≤ (K : ℚ) * 10 ^ g := by
    -- `res` is within a relative `6/(2^63-3)` of the value, and the value is a
    -- positive multiple of `10 ^ g` with `g ≥ -96`, so it cannot sit under the floor
    have hgap := abs_le.mp hround'
    have hge : res.toRat ≤ (K : ℚ) * 10 ^ g * (1 + 6 / (9223372036854775805 : ℚ)) := by
      rw [abs_of_pos hvalpos] at hgap
      nlinarith [hgap.2]
    -- integer coefficient at scale `10 ^ (-96)`
    have hmul : (K : ℚ) * 10 ^ g = ((K * 10 ^ (g + 96).toNat : ℕ) : ℚ) * 10 ^ (-96 : ℤ) := by
      have hgt : ((g + 96).toNat : ℤ) = g + 96 := Int.toNat_of_nonneg (by omega)
      push_cast
      rw [show ((10 : ℚ) ^ ((g + 96).toNat : ℕ)) = (10 : ℚ) ^ (((g + 96).toNat : ℕ) : ℤ) from
            (zpow_natCast 10 _).symm, hgt, mul_assoc, ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0),
          show g + 96 + (-96 : ℤ) = g from by ring]
    set N : ℕ := K * 10 ^ (g + 96).toNat with hN
    have h96 : (0 : ℚ) < (10 : ℚ) ^ (-96 : ℤ) := zpow_pos (by norm_num) _
    have hfl : (10 : ℚ) ^ (-81 : ℤ) = 10 ^ 15 * (10 : ℚ) ^ (-96 : ℤ) := by
      rw [show (-81 : ℤ) = 15 + (-96 : ℤ) from by ring, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
      norm_num
    rw [hmul] at hge ⊢
    rw [hfl] at hres_lo ⊢
    -- divide the floor comparison through by the grid step
    have hchain : (10 : ℚ) ^ 15 * (10 : ℚ) ^ (-96 : ℤ)
        ≤ ((N : ℚ) * (1 + 6 / (9223372036854775805 : ℚ))) * (10 : ℚ) ^ (-96 : ℤ) := by
      refine le_trans hres_lo ?_
      calc res.toRat ≤ (N : ℚ) * (10 : ℚ) ^ (-96 : ℤ) * (1 + 6 / (9223372036854775805 : ℚ)) := hge
        _ = ((N : ℚ) * (1 + 6 / (9223372036854775805 : ℚ))) * (10 : ℚ) ^ (-96 : ℤ) := by ring
    have hdiv : (10 : ℚ) ^ 15 ≤ (N : ℚ) * (1 + 6 / (9223372036854775805 : ℚ)) :=
      le_of_mul_le_mul_right hchain h96
    have hNn : (10 : ℕ) ^ 15 ≤ N := by
      by_contra hcon
      push Not at hcon
      have hNle : (N : ℚ) ≤ (10 : ℚ) ^ 15 - 1 := by
        have h1 : N + 1 ≤ 10 ^ 15 := by omega
        have h2 : ((N : ℕ) : ℚ) + 1 ≤ (((10 : ℕ) ^ 15 : ℕ) : ℚ) := by exact_mod_cast h1
        push_cast at h2
        linarith
      have hNnn : (0 : ℚ) ≤ (N : ℚ) := by positivity
      have heps : (0 : ℚ) < 6 / (9223372036854775805 : ℚ) := by norm_num
      nlinarith [hdiv, hNle, hNnn, heps]
    have hNq : ((10 : ℕ) ^ 15 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hNn
    push_cast at hNq
    exact mul_le_mul_of_nonneg_right hNq (le_of_lt h96)
  -- build the grid witness and identify the stored record with it
  obtain ⟨w, hwnorm, hwneg, hwne, hwval, hwmod, hwm_lo, hwm_hi, hwe_lo, hwe_hi⟩ :=
    Number.exists_grid_witness K g E hKpos hK hg_lo hg_hi hE hfloor hhi
  have hwsum : w.toRat = X.toRat + (dn.operator_neg).toRat := by
    rw [hwval, hnegval, ← hval]; ring
  have hexact := operator_add_exact_diff_sign X dn.operator_neg res .to_nearest hX hny
    hXne hny_ne hdiff w hwnorm hwsum hadd
  have hres_eq : res = w := by
    refine hres.toRat_inj hwnorm ?_
    rw [hexact, hwsum]
  subst hres_eq
  exact STAmount.isRounded_frac_false_of_grid res hwneg hwm_lo hwm_hi hwmod hwe_lo hwe_hi


/-! ## The `postSumExponent` bracket for a negative delta -/

/-- The negated payout, as a canonical record. -/
lemma STAmount.operator_neg_iou (p : STAmount) (hpc : p.IOUCanonical)
    (hpneg : p.mIsNegative = false) :
    p.operator_neg = ⟨.fractional, p.mValue, p.mOffset, true⟩ ∧
      (p.operator_neg).IOUCanonical ∧ (p.operator_neg).toRat = -p.toRat := by
  have hne : p.mValue ≠ 0 := by have := hpc.mant_lo; intro h; rw [h] at this; simp at this
  have hfr : p.mNumericType = .fractional := hpc.is_fractional
  have hrec : p.operator_neg = ⟨.fractional, p.mValue, p.mOffset, true⟩ := by
    unfold STAmount.operator_neg
    rw [if_neg (by simpa using hne)]
    obtain ⟨nt, mv, mo, mn⟩ := p
    simp only at hpneg hfr ⊢
    subst hpneg; subst hfr; rfl
  refine ⟨hrec, ?_, ?_⟩
  · exact ⟨by rw [hrec], by rw [hrec]; exact hpc.mant_lo, by rw [hrec]; exact hpc.mant_hi,
      by rw [hrec]; exact hpc.exp_lo, by rw [hrec]; exact hpc.exp_hi⟩
  · rw [STAmount.toRat_of_neg _ (by rw [hrec]), STAmount.toRat_of_nonneg p hpneg, hrec]

/-- **`postSumExponent` bracket, negative delta.** The exponent the model clamps to is
either a live 16-digit offset that brackets the exact difference from above, or the
`-100` zero sentinel, in which case the difference is below `10⁻⁸⁰`. -/
lemma postSumExponent_neg_bracket (T : Number) (p : STAmount) (s : ℤ)
    (hTnorm : T.isNormalized) (hTneg : T.negative_ = false) (hTne : T.mantissa_ ≠ 0)
    (hTehi : T.exponent_ + 3 ≤ 80) (hThi : T.mantissa_.toNat < 10 ^ 19)
    (hpc : p.IOUCanonical) (hpneg : p.mIsNegative = false)
    (hple : p.toRat ≤ T.toRat)
    (hok : postSumExponent T p.operator_neg = .ok s) :
    ((-96 : ℤ) ≤ s ∧ s ≤ 80 ∧ T.toRat - p.toRat ≤ (10 ^ 16 - (1 : ℚ) / 4) * 10 ^ s)
      ∨ (s = -100 ∧ T.toRat - p.toRat ≤ (10 : ℚ) ^ (-80 : ℤ)) := by
  obtain ⟨hnrec, hnc, hnval⟩ := STAmount.operator_neg_iou p hpc hpneg
  -- peel `postSumExponent`
  unfold postSumExponent at hok
  simp only [] at hok
  obtain ⟨pn, hpn, hok⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hok
  obtain ⟨R, hR, hok⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hok
  have hnt : (p.operator_neg).numericType = .fractional := by rw [hnrec]; rfl
  rw [hnt] at hok
  unfold numberExponent at hok
  obtain ⟨a, ha, hsa⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hok
  have hs : a.exponent = s :=
    Except.ok.inj (show (Except.ok a.exponent : Except Error Int) = .ok s from hsa)
  -- the lifted negated payout
  have hpn_eq : pn = ⟨true, p.mValue * 10 * 10 * 10, p.mOffset - 3⟩ := by
    rw [STAmount.toNumber_iou_canonical _ .to_nearest hnc] at hpn
    have := Except.ok.inj hpn
    rw [← this, hnrec]
  have hpn_val : pn.toRat = -p.toRat := by
    have h := STAmount.toNumber_iou_canonical_toRat (p.operator_neg) hnc
    rw [hnval, hnrec] at h
    rw [hpn_eq]
    simpa using h
  -- shape of the lifted delta
  have hncanon : (p.operator_neg).Canonical := by
    refine ⟨fun hi => absurd hi ?_, fun _ => hnc⟩
    unfold STAmount.integral; rw [hnrec]; exact Bool.false_ne_true
  obtain ⟨pn', hpn', hpn'_val, hpn'_norm⟩ :=
    STAmount.toNumber_canonical_exact (p.operator_neg) .to_nearest hncanon
  have hpn_same : pn = pn' := Except.ok.inj (hpn.symm.trans hpn')
  have hpn_norm : pn.isNormalized := by rw [hpn_same]; exact hpn'_norm
  have hpn_ne : pn.mantissa_ ≠ 0 := by
    rw [hpn_eq]
    intro h
    have h1 : (p.mValue * 10 * 10 * 10).toNat = p.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hpc.mant_hi
    have h2 : ((0 : UInt64)).toNat = 0 := rfl
    have := hpc.mant_lo
    simp only at h
    rw [h] at h1
    omega
  have hpn_neg : pn.negative_ = true := by rw [hpn_eq]
  have hdiffsign : T.negative_ ≠ pn.negative_ := by rw [hTneg, hpn_neg]; simp
  have hdiff_nn : 0 ≤ T.toRat - p.toRat := by linarith
  have hsum_eq : T.toRat + pn.toRat = T.toRat - p.toRat := by rw [hpn_val]; ring
  -- the `a.mValue = 0` cases share the `-100` sentinel
  have hsent : a.mValue = 0 → s = -100 := by
    intro hz
    have h := (STAmount.ofNumber_frac_exp_range .fractional R .to_nearest a (by decide) ha).1 hz
    rw [← hs]; exact h
  by_cases hRz : R.mantissa_ = 0
  · -- the sum flushed: the difference is astronomically small
    refine Or.inr ⟨hsent ?_, ?_⟩
    · by_contra hane
      exact (STAmount.ofNumber_source_ne_zero
        .fractional R .to_nearest a ha hane) hRz
    · by_cases hfast : T.operator_eq pn.operator_neg = true
      · -- exact cancellation: the two sides are the same record
        have hTeq : T = pn.operator_neg := Number.eq_of_operator_eq hfast
        have : T.toRat = p.toRat := by
          rw [hTeq, Number.toRat_neg, hpn_val]; ring
        rw [this]
        simp only [sub_self]
        positivity
      · have hsmall := operator_add_underflow_truth_small T pn R .to_nearest hTnorm hpn_norm
          hTne hpn_ne hdiffsign (by simpa using hfast) hR hRz
        rw [hsum_eq] at hsmall
        rw [abs_of_nonneg hdiff_nn] at hsmall
        have hmin : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ (10 : ℚ) ^ (-80 : ℤ) := by
          have h1 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ)
              = (10 : ℚ) ^ ((18 : ℤ) + minExponent) := by
            rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
          rw [h1]
          exact zpow_le_zpow_right₀ (by norm_num) (by unfold minExponent; omega)
        linarith
  · -- the sum survives
    have hRnorm : R.isNormalized :=
      operator_add_isNormalized_to_nearest T pn R hTnorm hpn_norm hR hRz
    have hnot_eq : ¬ T.operator_eq pn.operator_neg := by
      intro hq
      have hTeq : T = pn.operator_neg := Number.eq_of_operator_eq (by simpa using hq)
      -- then the model's fast path stored the canonical zero
      have hz0 : Number.operator_add T pn .to_nearest = .ok Number.zero := by
        unfold Number.operator_add
        rw [show (pn.operator_eq Number.zero) = false from by
              rw [Bool.eq_false_iff]; intro hg
              exact hpn_ne (Number.mantissa_eq_zero_of_operator_eq_zero hg),
            show (T.operator_eq Number.zero) = false from by
              rw [Bool.eq_false_iff]; intro hg
              exact hTne (Number.mantissa_eq_zero_of_operator_eq_zero hg),
            show (T.operator_eq pn.operator_neg) = true from by rw [hTeq]; simp [Number.operator_eq]]
        rfl
      rw [hR] at hz0
      exact hRz (by rw [Except.ok.inj hz0]; rfl)
    have hround := operator_add_rounds_to_nearest T pn R hTnorm hpn_norm hTne hpn_ne
      hnot_eq hR hRz
    simp only [RoundsWithin, RatValued.toRat, hsum_eq] at hround
    rw [abs_of_nonneg hdiff_nn] at hround
    rw [show (6 / (2 ^ 63 - 3 : ℚ)) = 6 / (9223372036854775805 : ℚ) from by norm_num] at hround
    have hgap := abs_le.mp hround
    have hD0 : 0 ≤ T.toRat - p.toRat := hdiff_nn
    have hlow : (T.toRat - p.toRat) * (1 - 6 / (9223372036854775805 : ℚ)) ≤ R.toRat := by
      have e : (T.toRat - p.toRat) * (1 - 6 / (9223372036854775805 : ℚ))
          = (T.toRat - p.toRat) - (T.toRat - p.toRat) * (6 / (9223372036854775805 : ℚ)) := by ring
      rw [e]; linarith [hgap.1]
    have hhigh : R.toRat ≤ (T.toRat - p.toRat) * (1 + 6 / (9223372036854775805 : ℚ)) := by
      have e : (T.toRat - p.toRat) * (1 + 6 / (9223372036854775805 : ℚ))
          = (T.toRat - p.toRat) + (T.toRat - p.toRat) * (6 / (9223372036854775805 : ℚ)) := by ring
      rw [e]; linarith [hgap.2]
    have hRnn : 0 ≤ R.toRat :=
      le_trans (mul_nonneg hD0 (by norm_num)) hlow
    have hRneg : R.negative_ = false :=
      Number.negative_false_of_norm_nonneg R hRnorm hRnn
    by_cases haz : a.mValue = 0
    · -- the 16-digit pack flushed: the sum is under the IOU floor
      refine Or.inr ⟨hsent haz, ?_⟩
      have hbelow := STAmount.ofNumber_iou_zero_below_min
        .fractional R .to_nearest a (by decide) hRnorm hRneg hRz ha haz
      have hz80 : (0 : ℚ) < (10 : ℚ) ^ (-80 : ℤ) := zpow_pos (by norm_num) _
      have h81 : (10 : ℚ) ^ (-81 : ℤ) = (10 : ℚ) ^ (-80 : ℤ) * (1 / 10) := by
        rw [show (-81 : ℤ) = (-80) + (-1) from by ring,
            zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
        norm_num
      -- `(T-p)·(9/10) ≤ (T-p)(1-ε) ≤ R < 10⁻⁸¹ = 10⁻⁸⁰/10`
      have h1 : (T.toRat - p.toRat) * (9 / 10 : ℚ)
          ≤ (T.toRat - p.toRat) * (1 - 6 / (9223372036854775805 : ℚ)) :=
        mul_le_mul_of_nonneg_left (by norm_num) hD0
      rw [h81] at hbelow
      have h2 : (T.toRat - p.toRat) * (9 / 10 : ℚ) < (10 : ℚ) ^ (-80 : ℤ) * (1 / 10) :=
        lt_of_le_of_lt (le_trans h1 hlow) hbelow
      -- `linarith` does not see through a negative-exponent `zpow` literal, so abstract it
      have hgen : ∀ A : ℚ, 0 < A → (T.toRat - p.toRat) * (9 / 10 : ℚ) < A * (1 / 10) →
          T.toRat - p.toRat ≤ A := by intro A hA h; linarith
      exact hgen _ hz80 h2
    · -- the pack is canonical: the half-ULP bracket caps the difference
      obtain ⟨hRlo, hRhi⟩ := hRnorm.mantissaBounds_nat hRz
      have hRelo : minExponent ≤ R.exponent_ := by
        rcases hRnorm with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show R.mantissa_ = 0 by rw [h0]; rfl) hRz
        · exact hlo
      -- `R` is bounded by (a little more than) the pre-state total
      have hTub : T.toRat < 10 ^ 16 * (10 : ℚ) ^ (T.exponent_ + 3) :=
        Number.toRat_lt_pow T hTneg hThi
      have hpow80 : (10 : ℚ) ^ (T.exponent_ + 3) ≤ (10 : ℚ) ^ (80 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hTehi
      have h1696 : (10 : ℚ) ^ 16 * (10 : ℚ) ^ (80 : ℤ) = (10 : ℚ) ^ (96 : ℤ) := by
        rw [show ((10 : ℚ) ^ 16) = (10 : ℚ) ^ ((16 : ℕ) : ℤ) from (zpow_natCast 10 16).symm,
            ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
        norm_num
      have hp3 : (0 : ℚ) < (10 : ℚ) ^ (T.exponent_ + 3) := zpow_pos (by norm_num) _
      have hTlt96 : T.toRat < (10 : ℚ) ^ (96 : ℤ) := by
        rw [← h1696]
        calc T.toRat < 10 ^ 16 * (10 : ℚ) ^ (T.exponent_ + 3) := hTub
          _ ≤ 10 ^ 16 * (10 : ℚ) ^ (80 : ℤ) := by
              have : (0 : ℚ) ≤ (10 : ℚ) ^ 16 := by positivity
              exact mul_le_mul_of_nonneg_left hpow80 this
      have hpnn : (0 : ℚ) ≤ p.toRat := by
        rw [STAmount.toRat_of_nonneg p hpneg]; positivity
      have hRlt : R.toRat < 2 * (10 : ℚ) ^ (96 : ℤ) := by
        have h2 : (T.toRat - p.toRat) * (1 + 6 / (9223372036854775805 : ℚ))
            ≤ T.toRat * (1 + 6 / (9223372036854775805 : ℚ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
        have h3 : T.toRat * (1 + 6 / (9223372036854775805 : ℚ)) < 2 * (10 : ℚ) ^ (96 : ℤ) := by
          have hTnn : (0 : ℚ) ≤ T.toRat := by linarith
          nlinarith [hTlt96, hTnn]
        linarith
      -- so its 19-digit exponent is nowhere near the top of the window
      have hRval : R.toRat = (R.mantissa_.toNat : ℚ) * 10 ^ R.exponent_ :=
        Number.toRat_of_nonneg R hRneg
      have hRmlo : (10 : ℚ) ^ (18 : ℕ) ≤ (R.mantissa_.toNat : ℚ) := by exact_mod_cast hRlo
      have hRexp_hi : R.exponent_ + 4 ≤ maxExponent := by
        by_contra hcon
        push Not at hcon
        have hge : (10 : ℚ) ^ (97 : ℤ) ≤ (10 : ℚ) ^ R.exponent_ :=
          zpow_le_zpow_right₀ (by norm_num) (by unfold maxExponent at hcon; omega)
        have hbig : (10 : ℚ) ^ (115 : ℤ) ≤ R.toRat := by
          rw [hRval]
          have hsplit : (10 : ℚ) ^ (115 : ℤ) = (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (97 : ℤ) := by
            rw [show ((10 : ℚ) ^ (18 : ℕ)) = (10 : ℚ) ^ ((18 : ℕ) : ℤ) from (zpow_natCast 10 18).symm,
                ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
            norm_num
          rw [hsplit]
          have h18 : (0 : ℚ) < (10 : ℚ) ^ (18 : ℕ) := by positivity
          exact mul_le_mul hRmlo hge (by positivity) (le_of_lt (lt_of_lt_of_le (by positivity) hRmlo))
        have hlt115 : 2 * (10 : ℚ) ^ (96 : ℤ) < (10 : ℚ) ^ (115 : ℤ) := by
          have : (10 : ℚ) ^ (97 : ℤ) ≤ (10 : ℚ) ^ (115 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by norm_num)
          have h97 : (10 : ℚ) ^ (97 : ℤ) = 10 * (10 : ℚ) ^ (96 : ℤ) := by
            rw [show (97 : ℤ) = 1 + 96 from by ring, zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
            norm_num
          have h96p : (0 : ℚ) < (10 : ℚ) ^ (96 : ℤ) := zpow_pos (by norm_num) _
          linarith
        linarith
      -- the canonical record and its window
      have hane : a.mValue ≠ 0 := haz
      have hac : a.IOUCanonical := by
        rcases STAmount.ofNumber_iou_canonical_or_zero R .to_nearest a
          hRlo hRhi hRelo ha with h | h
        · exact h
        · exact absurd h hane
      have hsm : a.mOffset = s := hs
      obtain ⟨hhalf, hexpR⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional R a rfl
        hRlo hRhi hRelo hRexp_hi ha hane
      have hps : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
      have hexpR' : R.exponent_ + 3 ≤ s := by rw [← hsm]; exact hexpR
      have hpowle : (10 : ℚ) ^ (R.exponent_ + 3) ≤ (10 : ℚ) ^ s :=
        zpow_le_zpow_right₀ (by norm_num) hexpR'
      have habs : |a.toRat| = (a.mValue.toNat : ℚ) * 10 ^ a.mOffset := STAmount.abs_toRat a
      have hamq : (a.mValue.toNat : ℚ) ≤ 10 ^ 16 - 1 := by
        have hh := hac.mant_hi
        have h : ((a.mValue.toNat : ℕ) : ℚ) ≤ (((10 ^ 16 - 1 : ℕ) : ℕ) : ℚ) := by
          exact_mod_cast Nat.le_pred_of_lt hh
        push_cast at h
        linarith
      have ha_ub : a.toRat ≤ (10 ^ 16 - 1) * (10 : ℚ) ^ s := by
        have h1 : a.toRat ≤ |a.toRat| := le_abs_self _
        rw [habs, hsm] at h1
        have h2 : (a.mValue.toNat : ℚ) * (10 : ℚ) ^ s ≤ (10 ^ 16 - 1) * (10 : ℚ) ^ s :=
          mul_le_mul_of_nonneg_right hamq (le_of_lt hps)
        linarith
      have hhalf' := abs_le.mp hhalf
      have hhalfpow : (1 / 2 : ℚ) * (10 : ℚ) ^ (R.exponent_ + 3) ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ s := by
        linarith
      have hRcap : R.toRat ≤ (10 ^ 16 - (1 : ℚ) / 2) * (10 : ℚ) ^ s := by
        have h1 : R.toRat - a.toRat ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ (R.exponent_ + 3) := by
          linarith [hhalf'.1]
        linarith
      -- and therefore so is the exact difference
      have hexp_lo : (-96 : ℤ) ≤ s := by
        rw [← hsm]
        exact ((STAmount.ofNumber_frac_exp_range
          .fractional R .to_nearest a (by decide) ha).2 hane).1
      have hexp_hi : s ≤ 80 := by
        rw [← hsm]
        exact ((STAmount.ofNumber_frac_exp_range
          .fractional R .to_nearest a (by decide) ha).2 hane).2
      refine Or.inl ⟨hexp_lo, hexp_hi, ?_⟩
      -- `(T-p)(1-ε) ≤ R ≤ (10¹⁶-½)·10^s` and `(10¹⁶-½) ≤ (10¹⁶-¼)(1-ε)`
      have hkey : (T.toRat - p.toRat) * (1 - 6 / (9223372036854775805 : ℚ))
          ≤ (10 ^ 16 - (1 : ℚ) / 2) * (10 : ℚ) ^ s := le_trans hlow hRcap
      have hfac : (10 ^ 16 - (1 : ℚ) / 2)
          ≤ (10 ^ 16 - (1 : ℚ) / 4) * (1 - 6 / (9223372036854775805 : ℚ)) := by norm_num
      have hpos : (0 : ℚ) < 1 - 6 / (9223372036854775805 : ℚ) := by norm_num
      have hstep : (T.toRat - p.toRat) * (1 - 6 / (9223372036854775805 : ℚ))
          ≤ ((10 ^ 16 - (1 : ℚ) / 4) * (10 : ℚ) ^ s) * (1 - 6 / (9223372036854775805 : ℚ)) := by
        have e2 : ((10 ^ 16 - (1 : ℚ) / 4) * (10 : ℚ) ^ s) * (1 - 6 / (9223372036854775805 : ℚ))
            = ((10 ^ 16 - (1 : ℚ) / 4) * (1 - 6 / (9223372036854775805 : ℚ))) * (10 : ℚ) ^ s := by ring
        rw [e2]
        exact le_trans hkey (mul_le_mul_of_nonneg_right hfac (le_of_lt hps))
      exact le_of_mul_le_mul_right hstep hpos


/-! ## The clamp's negative branch -/

/-- **The clamp's negative branch reports a grid amount that keeps the total coarse.**
The reported payout `d` lies on a grid `10 ^ gd` with `gd ≥ kMinOffset`, never exceeds
the priced payout, and leaves `T − d` under `(10¹⁶+1)` steps of `10 ^ min(E, gd)` — so,
being itself a multiple of that step, `T − d` needs at most 16 significant digits. -/
lemma clampToSumExponent_neg_grid (T : Number) (p d : STAmount)
    (hTnorm : T.isNormalized) (hTneg : T.negative_ = false) (hTne : T.mantissa_ ≠ 0)
    (_hTmod : T.mantissa_.toNat % 1000 = 0)
    (hTelo : (-96 : ℤ) ≤ T.exponent_ + 3) (hTehi : T.exponent_ + 3 ≤ 80)
    (hThi : T.mantissa_.toNat < 10 ^ 19)
    (hpc : p.IOUCanonical) (hpneg : p.mIsNegative = false) (hple : p.toRat ≤ T.toRat)
    (hclamp : clampToSumExponent T p.operator_neg = .ok d) (hdne : d.mValue ≠ 0) :
    d.IOUCanonical ∧ d.mIsNegative = false ∧
    ∃ gd : ℤ, (-96 : ℤ) ≤ gd ∧ OnGridAt d.toRat gd ∧ 0 ≤ d.toRat ∧ d.toRat ≤ p.toRat ∧
      T.toRat - d.toRat < (10 ^ 16 + 1) * (10 : ℚ) ^ (min (T.exponent_ + 3) gd) := by
  obtain ⟨hnrec, hnc, hnval⟩ := STAmount.operator_neg_iou p hpc hpneg
  have hpne : p.mValue ≠ 0 := by have := hpc.mant_lo; intro h; rw [h] at this; simp at this
  have hprec : p = ⟨.fractional, p.mValue, p.mOffset, false⟩ := by
    obtain ⟨nt, mv, mo, mn⟩ := p
    simp only at hpneg ⊢
    have hf : nt = .fractional := hpc.is_fractional
    subst hpneg; subst hf; rfl
  have hnegneg : (p.operator_neg).operator_neg = p := by
    rw [hnrec]
    unfold STAmount.operator_neg
    simp only [beq_iff_eq]
    rw [if_neg hpne]
    simp only [Bool.not_true]
    exact hprec.symm
  have hpnn : (0 : ℚ) ≤ p.toRat := by rw [STAmount.toRat_of_nonneg p hpneg]; positivity
  have hTnn : (0 : ℚ) ≤ T.toRat := le_trans hpnn hple
  -- peel the clamp
  unfold clampToSumExponent at hclamp
  simp only [] at hclamp
  have hdelta_neg : (p.operator_neg).negative = true := by rw [hnrec]; rfl
  have hdelta_int : (p.operator_neg).integral = false := by rw [hnrec]; rfl
  rw [hdelta_neg, if_pos rfl] at hclamp
  rw [hdelta_int] at hclamp
  simp only [Bool.false_eq_true, if_false, if_true, hnegneg, pure_bind] at hclamp
  obtain ⟨s, hs, hclamp⟩ := XRPL.Model.SingleAssetVault.bind_ok_peel _ _ _ hclamp
  -- the bracket
  have hbr := postSumExponent_neg_bracket T p s hTnorm hTneg hTne hTehi hThi hpc hpneg hple hs
  -- shape of `roundToExponent`
  have hpint : p.integral = false := by rw [hprec]; rfl
  have hpzero : p.isZero = false := by unfold STAmount.isZero; simpa using hpne
  have hTub : T.toRat < 10 ^ 16 * (10 : ℚ) ^ (T.exponent_ + 3) :=
    Number.toRat_lt_pow T hTneg hThi
  have hpE : (0 : ℚ) < (10 : ℚ) ^ (T.exponent_ + 3) := zpow_pos (by norm_num) _
  by_cases hshort : p.exponent ≥ s
  · -- the clamp is inert: it reports the priced payout unchanged
    have hdp : d = p := by
      unfold STAmount.roundToExponent at hclamp
      rw [if_neg (by rw [hpint]; exact Bool.false_ne_true),
          if_neg (by rw [hpzero]; exact Bool.false_ne_true), if_pos hshort] at hclamp
      exact (Except.ok.inj hclamp).symm
    refine ⟨by rw [hdp]; exact hpc, by rw [hdp]; exact hpneg,
      p.mOffset, hpc.exp_lo, ?_, ?_, ?_, ?_⟩
    · rw [hdp]; exact STAmount.onGridAt_toRat p hpneg
    · rw [hdp]; exact hpnn
    · rw [hdp]
    · rw [hdp]
      have hmin_le : min (T.exponent_ + 3) p.mOffset ≤ T.exponent_ + 3 := min_le_left _ _
      have hmin_le' : min (T.exponent_ + 3) p.mOffset ≤ p.mOffset := min_le_right _ _
      have hpmin : (0 : ℚ) < (10 : ℚ) ^ (min (T.exponent_ + 3) p.mOffset) :=
        zpow_pos (by norm_num) _
      rcases hbr with ⟨hslo, _, hbound⟩ | ⟨hs100, hbound⟩
      · -- the live case: `s ≤ p.mOffset`, so the bound transfers to the coarser grid
        have hsle : s ≤ p.mOffset := hshort
        rcases le_or_gt (T.exponent_ + 3) p.mOffset with hcase | hcase
        · -- `min = T.exponent_+3`
          rw [min_eq_left hcase]
          linarith [hTub, hpnn, hpE]
        · -- `min = p.mOffset`
          rw [min_eq_right (le_of_lt hcase)]
          have h1 : (10 : ℚ) ^ s ≤ (10 : ℚ) ^ p.mOffset :=
            zpow_le_zpow_right₀ (by norm_num) hsle
          have h2 : (0 : ℚ) < (10 : ℚ) ^ p.mOffset := zpow_pos (by norm_num) _
          nlinarith [hbound, h1, h2]
      · -- the sentinel case: the difference is under `10⁻⁸⁰ ≤ 10¹⁶·10^min`
        have hge : (10 : ℚ) ^ (-80 : ℤ) ≤ 10 ^ 16 * (10 : ℚ) ^ (min (T.exponent_ + 3) p.mOffset) := by
          have hmin96 : (-96 : ℤ) ≤ min (T.exponent_ + 3) p.mOffset :=
            le_min hTelo hpc.exp_lo
          have h1 : (10 : ℚ) ^ (-96 : ℤ) ≤ (10 : ℚ) ^ (min (T.exponent_ + 3) p.mOffset) :=
            zpow_le_zpow_right₀ (by norm_num) hmin96
          have h2 : (10 : ℚ) ^ (-80 : ℤ) = 10 ^ 16 * (10 : ℚ) ^ (-96 : ℤ) := by
            rw [show (-80 : ℤ) = 16 + (-96 : ℤ) from by ring,
                zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
            norm_num
          rw [h2]
          have : (0 : ℚ) ≤ (10 : ℚ) ^ 16 := by positivity
          exact mul_le_mul_of_nonneg_left h1 this
        linarith [hbound, hge, hpmin]
  · -- the clamp floors the payout onto the `10 ^ s` grid
    push Not at hshort
    have hbr' : (-96 : ℤ) ≤ s ∧ s ≤ 80 ∧
        T.toRat - p.toRat ≤ (10 ^ 16 - (1 : ℚ) / 4) * 10 ^ s := by
      rcases hbr with h | ⟨hs100, -⟩
      · exact h
      · exfalso; rw [hs100] at hshort; have := hpc.exp_lo; unfold STAmount.exponent at hshort; omega
    obtain ⟨hslo, hshi, hbound⟩ := hbr'
    have hrx : STAmount.roundToExponent p s .downward = .ok d := by
      unfold STAmount.roundToExponent at hclamp ⊢
      rw [if_neg (by rw [hpint]; exact Bool.false_ne_true),
          if_neg (by rw [hpzero]; exact Bool.false_ne_true),
          if_neg (by exact not_le.mpr hshort)] at hclamp ⊢
      exact hclamp
    have hgrid := STAmount.roundToExponent_rounded p d s .downward hpc hslo hshi hdne hrx
    have hdval : d.toRat = (⌊p.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s := hgrid
    have hps : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
    have hdfcz : d.FracCanonZero :=
      STAmount.roundToExponent_fczr p d s .downward ⟨hpc.is_fractional, Or.inl hpc⟩ hrx
    have hdc : d.IOUCanonical := hdfcz.2.resolve_right hdne
    have hdnn0 : 0 ≤ d.toRat := by
      rw [hdval]
      have h0 : (0 : ℤ) ≤ ⌊p.toRat / 10 ^ s⌋ := Int.floor_nonneg.mpr (by positivity)
      have hq : (0 : ℚ) ≤ (⌊p.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast h0
      positivity
    have hdsgn : d.mIsNegative = false := by
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      have hneg : d.toRat < 0 := by
        rw [STAmount.toRat_of_neg d hcon]
        have hmv : (0 : ℚ) < (d.mValue.toNat : ℚ) := by
          have := hdc.mant_lo
          have : 0 < d.mValue.toNat := by omega
          exact_mod_cast this
        have : (0 : ℚ) < (d.mValue.toNat : ℚ) * (10 : ℚ) ^ d.mOffset := by positivity
        linarith
      linarith
    refine ⟨hdc, hdsgn, s, hslo, ⟨⌊p.toRat / 10 ^ s⌋, hdval⟩, ?_, ?_, ?_⟩
    · rw [hdval]
      have : (0 : ℚ) ≤ (⌊p.toRat / 10 ^ s⌋ : ℚ) := by
        have : (0 : ℤ) ≤ ⌊p.toRat / 10 ^ s⌋ := Int.floor_nonneg.mpr (by positivity)
        exact_mod_cast this
      positivity
    · rw [hdval]
      have hfl : (⌊p.toRat / 10 ^ s⌋ : ℚ) ≤ p.toRat / 10 ^ s := Int.floor_le _
      calc (⌊p.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ (p.toRat / 10 ^ s) * 10 ^ s :=
            mul_le_mul_of_nonneg_right hfl (le_of_lt hps)
        _ = p.toRat := div_mul_cancel₀ _ (ne_of_gt hps)
    · -- `T − d = (T − p) + (p − d)` with `p − d < 10^s`
      have hlt : p.toRat / 10 ^ s < (⌊p.toRat / 10 ^ s⌋ : ℚ) + 1 := Int.lt_floor_add_one _
      have hpd : p.toRat - d.toRat < 10 ^ s := by
        rw [hdval]
        have := mul_lt_mul_of_pos_right hlt hps
        rw [div_mul_cancel₀ _ (ne_of_gt hps)] at this
        linarith
      rcases le_or_gt (T.exponent_ + 3) s with hcase | hcase
      · rw [min_eq_left hcase]
        have hdnn : (0 : ℚ) ≤ d.toRat := by
          rw [hdval]
          have : (0 : ℤ) ≤ ⌊p.toRat / 10 ^ s⌋ := Int.floor_nonneg.mpr (by positivity)
          have hq : (0 : ℚ) ≤ (⌊p.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast this
          positivity
        linarith [hTub, hpE]
      · rw [min_eq_right (le_of_lt hcase)]
        linarith [hbound, hpd, hps]


/-! ## The headline arithmetic lemma -/

/-- **A clamped payout keeps a vault asset field on the grid.** `X` is the stored field
(`assetsTotal` or `assetsAvailable`), `T` the stored total the clamp is computed against,
`p` the priced payout and `rep` the clamped one. Provided the stored difference does not
underflow the IOU floor, it stays on the asset's `STAmount` grid. -/
lemma clamped_field_on_grid (T X : Number) (p rep : STAmount) (repN res : Number)
    (hTnorm : T.isNormalized) (hTneg : T.negative_ = false)
    (hTgrid : STAmount.isRounded .fractional T = false)
    (hXnorm : X.isNormalized) (hXneg : X.negative_ = false)
    (hXgrid : STAmount.isRounded .fractional X = false)
    (hXle : X.toRat ≤ T.toRat)
    (hpc : p.IOUCanonical) (hpneg : p.mIsNegative = false) (hpX : p.toRat ≤ X.toRat)
    (hclamp : clampToSumExponent T p.operator_neg = .ok rep) (hrepne : rep.mValue ≠ 0)
    (hrepN : rep.toNumber .to_nearest = .ok repN)
    (hresnorm : res.isNormalized)
    (hsub : X.operator_sub repN .to_nearest = .ok res)
    (hnf : res.mantissa_ = 0 ∨ (10 : ℚ) ^ (-81 : ℤ) ≤ res.toRat) :
    STAmount.isRounded .fractional res = false := by
  -- the payout is strictly positive
  have hppos : 0 < p.toRat := by
    rw [STAmount.toRat_of_nonneg p hpneg]
    have hm : 0 < p.mValue.toNat := by have := hpc.mant_lo; omega
    have : (0 : ℚ) < (p.mValue.toNat : ℚ) := by exact_mod_cast hm
    positivity
  have hXpos : 0 < X.toRat := lt_of_lt_of_le hppos hpX
  have hTpos : 0 < T.toRat := lt_of_lt_of_le hXpos hXle
  -- shapes of the two stored fields
  have hTne : T.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hTpos)
  have hXne : X.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hXpos)
  obtain ⟨hTmod, hTelo, hTehi⟩ :=
    (Number.grid_of_isRounded_frac_false T hTnorm hTgrid).resolve_left hTne
  obtain ⟨hXmod, hXelo, hXehi⟩ :=
    (Number.grid_of_isRounded_frac_false X hXnorm hXgrid).resolve_left hXne
  obtain ⟨hTlo19, hThi19⟩ := hTnorm.mantissaBounds_nat hTne
  obtain ⟨hXlo19, hXhi19⟩ := hXnorm.mantissaBounds_nat hXne
  -- the clamp's grid data
  obtain ⟨hrepc, hrepsgn, gd, hgd_lo, hgdgrid, hrep_nn, hrep_le, hTbound⟩ :=
    clampToSumExponent_neg_grid T p rep hTnorm hTneg hTne hTmod hTelo hTehi hThi19
      hpc hpneg (le_trans hpX hXle) hclamp hrepne
  -- the lifted clamped payout
  have hrepN_eq : repN = ⟨rep.mIsNegative, rep.mValue * 10 * 10 * 10, rep.mOffset - 3⟩ := by
    rw [STAmount.toNumber_iou_canonical rep .to_nearest hrepc] at hrepN
    exact (Except.ok.inj hrepN).symm
  have hrepN_val : repN.toRat = rep.toRat := by
    rw [hrepN_eq]; exact STAmount.toNumber_iou_canonical_toRat rep hrepc
  have hrepN_neg : repN.negative_ = false := by rw [hrepN_eq]; exact hrepsgn
  have hrepN_ne : repN.mantissa_ ≠ 0 := by
    rw [hrepN_eq]
    intro h
    have h1 : (rep.mValue * 10 * 10 * 10).toNat = rep.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hrepc.mant_hi
    have hlo := hrepc.mant_lo
    have h2 : ((0 : UInt64)).toNat = 0 := rfl
    simp only at h
    rw [h, h2] at h1
    omega
  obtain ⟨repN', hrepN', hrepN'_val, hrepN'_norm⟩ :=
    STAmount.toNumber_canonical_exact rep .to_nearest (STAmount.Canonical.of_iou rep hrepc)
  have hrepN_norm : repN.isNormalized := by
    rw [show repN = repN' from Except.ok.inj (hrepN.symm.trans hrepN')]; exact hrepN'_norm
  -- the common grid
  set g : ℤ := min (X.exponent_ + 3) gd with hgdef
  have hg_lo : (-96 : ℤ) ≤ g := le_min hXelo hgd_lo
  have hg_hi : g ≤ 80 := le_trans (min_le_left _ _) hXehi
  have hgX : OnGridAt X.toRat g :=
    (Number.onGridAt_toRat X hXneg hXmod).mono (min_le_left _ _)
  have hgrep : OnGridAt repN.toRat g := by
    rw [hrepN_val]; exact hgdgrid.mono (min_le_right _ _)
  have hgsub : OnGridAt (X.toRat - repN.toRat) g := hgX.sub hgrep
  -- and the bound
  have hpg : (0 : ℚ) < (10 : ℚ) ^ g := zpow_pos (by norm_num) _
  have hXub : X.toRat < 10 ^ 16 * (10 : ℚ) ^ (X.exponent_ + 3) :=
    Number.toRat_lt_pow X hXneg hXhi19
  have hbound : X.toRat - repN.toRat < (10 ^ 16 + 1) * (10 : ℚ) ^ g := by
    rw [hrepN_val]
    rcases le_or_gt (X.exponent_ + 3) gd with hcase | hcase
    · have : g = X.exponent_ + 3 := min_eq_left hcase
      rw [this]
      have hp3 : (0 : ℚ) < (10 : ℚ) ^ (X.exponent_ + 3) := zpow_pos (by norm_num) _
      linarith
    · have hgg : g = gd := min_eq_right (le_of_lt hcase)
      have hminle : min (T.exponent_ + 3) gd ≤ g := by rw [hgg]; exact min_le_right _ _
      have hpowle : (10 : ℚ) ^ (min (T.exponent_ + 3) gd) ≤ (10 : ℚ) ^ g :=
        zpow_le_zpow_right₀ (by norm_num) hminle
      have h16 : (0 : ℚ) ≤ (10 : ℚ) ^ 16 + 1 := by positivity
      calc X.toRat - rep.toRat ≤ T.toRat - rep.toRat := by linarith
        _ < (10 ^ 16 + 1) * (10 : ℚ) ^ (min (T.exponent_ + 3) gd) := hTbound
        _ ≤ (10 ^ 16 + 1) * (10 : ℚ) ^ g := mul_le_mul_of_nonneg_left hpowle h16
  have hsub_nn : 0 ≤ X.toRat - repN.toRat := by
    rw [hrepN_val]; linarith [le_trans hrep_le hpX]
  obtain ⟨K, hK, hKval⟩ := hgsub.nat_coeff hsub_nn hbound
  -- and the value is under the field's own decade
  have hhi : (K : ℚ) * 10 ^ g < 10 ^ 16 * (10 : ℚ) ^ (X.exponent_ + 3) := by
    rw [← hKval]
    have : 0 ≤ repN.toRat := by rw [hrepN_val]; exact hrep_nn
    linarith
  exact Number.sub_grid_isRounded_false X repN res K g (X.exponent_ + 3)
    hXnorm hXneg hXne hrepN_norm hrepN_neg hrepN_ne hresnorm hK hg_lo hg_hi hXehi
    hKval hhi hnf hsub


end XRPL.Model.SingleAssetVault.CatHI
