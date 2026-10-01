import XRPL.Properties.Vault.Proofs.ClawbackTight.Price
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.Number.Add.RoundsWithin
import XRPL.Properties.Protocol.Number.Compare.Compare

/-! # The fractional clamp of a positive recovery -/

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

lemma neg_neg_of_ne (p : STAmount) (h : p.mValue ≠ 0) : p.operator_neg.operator_neg = p := by
  unfold STAmount.operator_neg
  simp [h]

/-- The fractional clamp of a positive amount rounds it down onto the grid of the
post-operation total's exponent. -/
lemma clamp_unfold (A : Number) (p rec : STAmount) (hp : p.IOUCanonical) (hneg : p.mIsNegative = false)
    (h : clampToSumExponent A p.operator_neg = .ok rec) :
    ∃ s, postSumExponent A p.operator_neg = .ok s ∧
      STAmount.roundToExponent p s .downward = .ok rec := by
  have hm : p.mValue ≠ 0 := by
    intro h0; have := hp.mant_lo; rw [h0] at this; simp at this
  have hint : p.operator_neg.integral = false := by
    show p.operator_neg.mNumericType.isIntegral = false
    unfold STAmount.operator_neg; split <;> rw [hp.is_fractional] <;> rfl
  have hn : p.operator_neg.negative = true := by
    show p.operator_neg.mIsNegative = true
    unfold STAmount.operator_neg; simp [hm, hneg]
  unfold clampToSumExponent at h
  simp only [hn, hint, if_true, Bool.false_eq_true, if_false, neg_neg_of_ne p hm, bind,
    Except.bind] at h
  walk_ok
  exact ⟨_, ‹_›, ‹_›⟩

lemma le_log10 (x : ℚ) (n : ℤ) (hx : 0 < x) (h : (10 : ℚ) ^ n ≤ x) : n ≤ Int.log 10 x :=
  (Int.zpow_le_iff_le_log (b := 10) (by norm_num) hx).mp (by exact_mod_cast h)

lemma pow_le_grid (x : ℚ) (n : ℤ) (hx : 0 < x) (h : (10 : ℚ) ^ n ≤ x) :
    (10 : ℚ) ^ (n - 15) ≤ (10 : ℚ) ^ (Int.log 10 x - 15) :=
  zpow_le_zpow_right₀ (by norm_num) (by have := le_log10 x n hx h; omega)

/-- The clamp's shortfall fits one grid step of the post-operation total. -/
lemma key_arith (A P R : ℚ) (e : ℤ) (k : ℕ) (z : ℤ) (hk : 1 ≤ k) (hz1 : 1 ≤ z)
    (hPR : P - R = z * 10 ^ e) (hlt : P - R < 10 ^ (e + k))
    (hT : (10 ^ 15 - 51 / 1000) * 10 ^ (e + k) ≤ A - P) :
    1 / 2 * 10 ^ e + (P - R) ≤ (10 : ℚ) ^ (Int.log 10 (A - R) - 15) := by
  have hu : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hG : (10 : ℚ) ^ (e + k) = 10 ^ e * 10 ^ k := by
    rw [zpow_add₀ (by norm_num), zpow_natCast]
  have hk10 : (10 : ℚ) ≤ 10 ^ k := by
    calc (10 : ℚ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hzlt : z < (10 : ℤ) ^ k := by
    have h1 : (z : ℚ) * 10 ^ e < 10 ^ k * 10 ^ e := by rw [← hPR, mul_comm]; rw [← hG]; exact hlt
    have h2 : (z : ℚ) < 10 ^ k := lt_of_mul_lt_mul_right h1 hu.le
    exact_mod_cast h2
  have hzle : (z : ℚ) ≤ 10 ^ k - 1 := by
    have : z ≤ (10 : ℤ) ^ k - 1 := by omega
    exact_mod_cast this
  have hz1q : (1 : ℚ) ≤ z := by exact_mod_cast hz1
  have hGpos : (0 : ℚ) < 10 ^ (e + k) := zpow_pos (by norm_num) _
  have hAP : 0 < A - P := by nlinarith
  have hX : 0 < A - R := by nlinarith
  have h15 : (10 : ℚ) ^ (15 + (e + k)) = 10 ^ 15 * 10 ^ (e + k) := by
    rw [zpow_add₀ (by norm_num)]; norm_num
  by_cases hbig : (10 : ℚ) ^ (15 + (e + k)) ≤ A - R
  · have := pow_le_grid (A - R) _ hX hbig
    rw [show 15 + (e + k) - 15 = e + k by ring] at this
    have hl : 1 / 2 * 10 ^ e + (P - R) ≤ 10 ^ (e + k) := by
      rw [hPR, hG]; nlinarith
    linarith
  · replace hbig := not_le.mp hbig
    have h14 : (10 : ℚ) ^ (14 + (e + k)) ≤ A - R := by
      have : (10 : ℚ) ^ (14 + (e + k)) = 10 ^ 14 * 10 ^ (e + k) := by
        rw [zpow_add₀ (by norm_num)]; norm_num
      rw [this]; nlinarith
    have := pow_le_grid (A - R) _ hX h14
    rw [show 14 + (e + k) - 15 = e + k - 1 by ring] at this
    have hG1 : (10 : ℚ) ^ (e + k - 1) = 10 ^ (e + k) / 10 := by
      rw [zpow_sub₀ (by norm_num)]; norm_num
    rw [hG1] at this
    have hL : P - R < 51 / 1000 * 10 ^ (e + k) := by rw [h15] at hbig; nlinarith
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      rw [hG] at hL
      have : (1 : ℚ) * 10 ^ e ≤ z * 10 ^ e := mul_le_mul_of_nonneg_right hz1q hu.le
      rw [hPR] at hL; norm_num at hL; nlinarith
    · have hk100 : (100 : ℚ) ≤ 10 ^ k := by
        calc (100 : ℚ) = 10 ^ 2 := by norm_num
          _ ≤ 10 ^ k := pow_le_pow_right₀ (by norm_num) hk2
      have hue : 10 ^ e * 100 ≤ (10 : ℚ) ^ (e + k) := by
        rw [hG]; exact mul_le_mul_of_nonneg_left hk100 hu.le
      linarith

lemma canon_exp_le (a b : STAmount) (ha : a.IOUCanonical) (hb : b.IOUCanonical)
    (hna : a.mIsNegative = false) (hnb : b.mIsNegative = false) (h : a.toRat = b.toRat) :
    b.mOffset ≤ a.mOffset := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  rw [STAmount.toRat_of_nonneg a hna, STAmount.toRat_of_nonneg b hnb] at h
  obtain ⟨d, hd⟩ : ∃ d : ℕ, b.mOffset = a.mOffset + (d + 1 : ℕ) := ⟨(b.mOffset - a.mOffset - 1).toNat, by omega⟩
  rw [hd, zpow_add₀ (by norm_num), zpow_natCast, mul_comm ((10 : ℚ) ^ a.mOffset), ← mul_assoc] at h
  have hpos : (0 : ℚ) < 10 ^ a.mOffset := zpow_pos (by norm_num) _
  have h2 : (a.mValue.toNat : ℚ) = b.mValue.toNat * 10 ^ (d + 1) :=
    mul_right_cancel₀ hpos.ne' h
  have hb1 : (10 ^ 15 : ℚ) ≤ b.mValue.toNat := by exact_mod_cast hb.mant_lo
  have ha1 : (a.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast ha.mant_hi
  have h10 : (10 : ℚ) ≤ 10 ^ (d + 1) := by
    calc (10 : ℚ) = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

lemma neg_canon (p : STAmount) (hp : p.IOUCanonical) : p.operator_neg.IOUCanonical := by
  unfold STAmount.operator_neg
  split
  · exact hp
  · exact ⟨hp.is_fractional, hp.mant_lo, hp.mant_hi, hp.exp_lo, hp.exp_hi⟩

lemma neg_toRat (p : STAmount) : p.operator_neg.toRat = -p.toRat := by
  unfold STAmount.operator_neg
  split
  · rename_i h
    have : p.mValue = 0 := by simpa using h
    rw [(STAmount.toRat_eq_zero_iff p).mpr this]; simp
  · rw [STAmount.toRat_signed, STAmount.toRat_signed]
    cases p.mIsNegative <;> simp

/-- The recovery's post-operation total, read off `postSumExponent`, is at least
`10^15 - 0.051` grid steps. -/
lemma post_total_ge (A : Number) (hA : A.isNormalized) (p : STAmount) (hp : p.IOUCanonical)
    (hPA : p.toRat ≤ A.toRat) (s : ℤ) (hps : postSumExponent A p.operator_neg = .ok s)
    (hs : (-96 : ℤ) < s) :
    s ≤ 80 ∧ (10 ^ 15 - 51 / 1000) * (10 : ℚ) ^ s ≤ A.toRat - p.toRat := by
  obtain ⟨dn, sum, Q, hdn, hsum, hQ, hQe⟩ := postSumExponent_reduces A p.operator_neg s hps
  have hnt : p.operator_neg.numericType = .fractional := by
    show p.operator_neg.mNumericType = .fractional
    unfold STAmount.operator_neg; split <;> exact hp.is_fractional
  rw [hnt] at hQ
  obtain ⟨hz, hr⟩ := STAmount.ofNumber_frac_exp_range _ _ _ _ rfl hQ
  have hQm : Q.mValue ≠ 0 := by
    intro h0; have := hz h0; omega
  obtain ⟨dn', hdn', hdnv, hdnn⟩ := STAmount.toNumber_iou_exact _ .to_nearest (neg_canon p hp)
  obtain rfl := Except.ok.inj (hdn'.symm.trans hdn)
  rw [neg_toRat] at hdnv
  have hsm := STAmount.ofNumber_source_ne_zero _ _ _ _ hQ hQm
  have hsn := operator_add_isNormalized _ _ _ _ hA hdnn hsum hsm
  have hrr := operator_add_rounded_to_nearest A dn' sum hA hdnn hsum
  rw [hdnv] at hrr
  have hs0 : 0 ≤ sum.toRat :=
    Number.RoundsToRepresentable.nonneg_of_nonneg _ _ hrr (by linarith)
  have hspos : 0 < sum.toRat :=
    lt_of_le_of_ne hs0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hsm))
  have hsneg := Number.negative_false_of_pos sum hspos
  obtain ⟨hlo, hhi⟩ := hsn.mantissaBounds_nat hsm
  have hexp_lo : minExponent ≤ sum.exponent_ := by
    rcases hsn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show sum.mantissa_ = 0 by rw [h0]; rfl) hsm
    · exact hlo
  obtain ⟨hQc, hexp_hi⟩ := STAmount.ofNumber_iou_ok_facts sum _ Q hlo hhi hexp_lo hQ hQm
  obtain ⟨hb, he⟩ := STAmount.ofNumber_iou_within_half_ulp .fractional sum Q rfl hlo hhi
    hexp_lo hexp_hi hQ hQm
  have hQnn := ofNumber_nonneg _ _ _ _ hsn hsneg hQ
  refine ⟨by have := (hr hQm).2; omega, ?_⟩
  have hQneg : Q.mIsNegative = false := by
    rcases h : Q.mIsNegative with _ | _
    · rfl
    · exfalso
      have h1 := STAmount.toRat_nonpos_of Q h
      have h2 : Q.toRat ≠ 0 := fun h0 => hQm ((STAmount.toRat_eq_zero_iff Q).mp h0)
      exact h2 (le_antisymm h1 hQnn)
  have hG : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hQlo : 10 ^ 15 * (10 : ℚ) ^ s ≤ Q.toRat := by
    rw [STAmount.toRat_of_nonneg Q hQneg, ← hQe]
    show 10 ^ 15 * (10 : ℚ) ^ Q.mOffset ≤ _
    have : (10 ^ 15 : ℚ) ≤ Q.mValue.toNat := by exact_mod_cast hQc.mant_lo
    exact mul_le_mul_of_nonneg_right this (zpow_pos (by norm_num) _).le
  rw [hQe] at he
  have hsum_lo : 10 ^ 15 * (10 : ℚ) ^ s - 1 / 20 * 10 ^ s ≤ sum.toRat := by
    by_cases hbig : 10 ^ 15 * (10 : ℚ) ^ s ≤ sum.toRat
    · linarith
    replace hbig := not_le.mp hbig
    have hsv := Number.toRat_of_nonneg sum hsneg
    have hml : (10 ^ 18 : ℚ) ≤ sum.mantissa_.toNat := by exact_mod_cast hlo
    have hlt : sum.exponent_ + 3 ≤ s - 1 := by
      by_contra hc
      replace hc := not_le.mp hc
      have h1 : (10 : ℚ) ^ s ≤ 10 ^ (sum.exponent_ + 3) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (10 : ℚ) ^ (sum.exponent_ + 3) = 10 ^ 3 * 10 ^ sum.exponent_ := by
        rw [zpow_add₀ (by norm_num)]; ring
      have h3 : 10 ^ 18 * (10 : ℚ) ^ sum.exponent_ ≤ sum.toRat := by
        rw [hsv]; exact mul_le_mul_of_nonneg_right hml (zpow_pos (by norm_num) _).le
      nlinarith
    have h4 : (10 : ℚ) ^ (sum.exponent_ + 3) ≤ 10 ^ (s - 1) := zpow_le_zpow_right₀ (by norm_num) hlt
    have h5 : (10 : ℚ) ^ (s - 1) = 10 ^ s / 10 := by rw [zpow_sub₀ (by norm_num)]; norm_num
    have := (abs_le.mp hb).2
    linarith
  -- a representable point just below: `(10^19 - 510) · 10^(s-4)`
  have hwn : (⟨false, 9999999999999999490, s - 4⟩ : Number).isNormalized := by
    refine Or.inr ⟨show largeRange.min ≤ (9999999999999999490 : UInt64) by decide,
      show (9999999999999999490 : UInt64) ≤ largeRange.max by decide,
      Or.inr (show (9999999999999999490 : UInt64).toNat % 10 = 0 by decide), ?_, ?_⟩
    · show minExponent ≤ s - 4; unfold minExponent; omega
    · show s - 4 ≤ maxExponent; unfold maxExponent; have := (hr hQm).2; omega
  have hwv : (⟨false, 9999999999999999490, s - 4⟩ : Number).toRat =
      (10 ^ 15 - 51 / 1000) * (10 : ℚ) ^ s := by
    rw [Number.toRat_of_nonneg _ rfl]
    show ((9999999999999999490 : UInt64).toNat : ℚ) * (10 : ℚ) ^ (s - 4) = _
    rw [show (9999999999999999490 : UInt64).toNat = 9999999999999999490 from rfl,
      zpow_sub₀ (by norm_num)]
    field_simp
    norm_num
  by_contra hc
  replace hc := not_le.mp hc
  have := Number.RoundsToRepresentable.le_of_le_normalized sum _ hrr _ hwn (by rw [hwv]; linarith)
  rw [hwv] at this
  nlinarith

/-- The fractional clamp of a positive priced recovery: unchanged, or snapped down by
a whole number of its own last digits, by at most one grid step of the
post-operation total. -/
lemma clamp_frac (A : Number) (hA : A.isNormalized) (p rec : STAmount) (hp : p.IOUCanonical)
    (hpos : 0 < p.toRat) (hPA : p.toRat ≤ A.toRat)
    (h : clampToSumExponent A p.operator_neg = .ok rec) (hrec : rec.mValue ≠ 0) :
    rec.IOUCanonical ∧ rec.toRat ≤ p.toRat ∧
      ((rec.toRat = p.toRat ∧ rec.exponent = p.exponent) ∨
        (rec.toRat + 10 ^ p.exponent ≤ p.toRat ∧
          1 / 2 * 10 ^ p.exponent + (p.toRat - rec.toRat) ≤
            (10 : ℚ) ^ (Int.log 10 (A.toRat - rec.toRat) - 15))) := by
  have hneg : p.mIsNegative = false := by
    rcases h' : p.mIsNegative with _ | _
    · rfl
    · have := STAmount.toRat_nonpos_of p h'; linarith
  obtain ⟨s, hps, hrt⟩ := clamp_unfold A p rec hp hneg h
  have hfc : STAmount.FracCanonZero p := ⟨hp.is_fractional, Or.inl hp⟩
  have hrc : rec.IOUCanonical := by
    rcases (STAmount.roundToExponent_fczr p rec s .downward hfc hrt).2 with h1 | h1
    · exact h1
    · exact absurd h1 hrec
  refine ⟨hrc, ?_⟩
  have hint : p.integral = false := by
    show p.mNumericType.isIntegral = false; rw [hp.is_fractional]; rfl
  have hnz : ¬ p.isZero = true := by
    intro h0
    have : p.mValue = 0 := by simpa [STAmount.isZero] using h0
    have := hp.mant_lo; simp_all
  by_cases hes : p.exponent ≥ s
  · have : rec = p := by
      unfold STAmount.roundToExponent at hrt
      rw [if_neg (by rw [hint]; decide), if_neg hnz, if_pos hes] at hrt
      exact (Except.ok.inj hrt).symm
    subst this
    exact ⟨le_rfl, Or.inl ⟨rfl, rfl⟩⟩
  replace hes := not_le.mp hes
  have he96 : (-96 : ℤ) ≤ p.exponent := hp.exp_lo
  obtain ⟨hs80, hT⟩ := post_total_ge A hA p hp hPA s hps (by omega)
  have hrv : rec.toRat = ⌊p.toRat / 10 ^ s⌋ * 10 ^ s :=
    STAmount.roundToExponent_rounded p rec s .downward hp (by omega) hs80 hrec hrt
  have hG : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hRle : rec.toRat ≤ p.toRat := by
    rw [hrv]
    have := Int.floor_le (p.toRat / 10 ^ s)
    calc (⌊p.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ p.toRat / 10 ^ s * 10 ^ s :=
          mul_le_mul_of_nonneg_right this hG.le
      _ = p.toRat := by field_simp
  refine ⟨hRle, ?_⟩
  rcases eq_or_lt_of_le hRle with hRP | hRP
  · have hrn : rec.mIsNegative = false := by
      rcases h' : rec.mIsNegative with _ | _
      · rfl
      · have := STAmount.toRat_nonpos_of rec h'; linarith
    exact Or.inl ⟨hRP, le_antisymm (canon_exp_le p rec hp hrc hneg hrn hRP.symm)
      (canon_exp_le rec p hrc hp hrn hneg hRP)⟩
  right
  obtain ⟨k, hk⟩ : ∃ k : ℕ, s = p.exponent + k := ⟨(s - p.exponent).toNat, by omega⟩
  have hk1 : 1 ≤ k := by omega
  set e := p.exponent with he_def
  have hu : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hPv : p.toRat = (p.mValue.toNat : ℚ) * 10 ^ e := STAmount.toRat_of_nonneg p hneg
  have hGs : (10 : ℚ) ^ s = 10 ^ e * 10 ^ k := by rw [hk, zpow_add₀ (by norm_num), zpow_natCast]
  set z : ℤ := (p.mValue.toNat : ℤ) - ⌊p.toRat / 10 ^ s⌋ * 10 ^ k with hz
  have hPR : p.toRat - rec.toRat = z * 10 ^ e := by
    rw [hrv, hz, hGs]; push_cast; rw [hPv]; ring
  have hz1 : 1 ≤ z := by
    have : (0 : ℚ) < z * 10 ^ e := by rw [← hPR]; linarith
    have : (0 : ℚ) < z := pos_of_mul_pos_left this hu.le
    have : 0 < z := by exact_mod_cast this
    omega
  have hlt : p.toRat - rec.toRat < 10 ^ s := by
    rw [hrv]
    have := Int.lt_floor_add_one (p.toRat / 10 ^ s)
    have h2 : p.toRat < (⌊p.toRat / 10 ^ s⌋ + 1) * 10 ^ s := by
      rw [← div_lt_iff₀ hG]; exact_mod_cast this
    linarith
  have hz1q : (1 : ℚ) ≤ z := by exact_mod_cast hz1
  refine ⟨by nlinarith, ?_⟩
  rw [hk] at hlt hT
  exact key_arith A.toRat p.toRat rec.toRat e k z hk1 hz1 hPR hlt hT

end XRPL.Model.SingleAssetVault.ClwTight
