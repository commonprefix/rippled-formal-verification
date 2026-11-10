import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128Facts
import XRPL.Properties.Protocol.Number.Common.Closest.NearestDefs

/-! # The 128-bit normalization hands `doRoundUp` a guard that rounds like the exact fraction -/

namespace XRPL.Model.Protocol

/-- `to_nearest` rounding of a non-empty guard, with the digits compared as natural numbers. -/
private lemma round_to_nearest_toNat {g : Guard} (hne : ¬ g.empty = true) :
    g.round .to_nearest = if 5 * 2 ^ 60 < g.digits_.toNat then 1
      else if g.digits_.toNat < 5 * 2 ^ 60 then -1 else if g.xbit_ then 1 else 0 := by
  rw [round_to_nearest_def hne]
  simp only [GT.gt, UInt64.lt_iff_toNat_lt, toNat_half_mark]
  norm_num

/-- A guard is empty exactly when its digits are zero and its sticky bit is clear. -/
private lemma empty_iff_toNat (g : Guard) : g.empty = true ↔ g.digits_.toNat = 0 ∧ g.xbit_ = false := by
  unfold Guard.empty Guard.unrecoverable
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
  rw [← UInt64.toNat_inj]
  rfl

/-- Pushing a decimal digit `d` onto a guard that is empty exactly when `φ = 0` gives a guard that rounds
`(φ + d) / 10` like exact rounding. -/
lemma Guard.roundsLike_push {g : Guard} {φ : ℚ} {d : UInt64} (he : g.empty = true ↔ φ = 0)
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hd : d.toNat < 10) :
    (g.push d).RoundsLike ((φ + (d.toNat : ℚ)) / 10) := by
  have hdig : (g.push d).digits_.toNat = g.digits_.toNat / 16 + d.toNat * 2 ^ 60 := by
    rw [toNat_push_digits, Nat.mod_eq_of_lt (by omega : d.toNat < 16)]
  have hx : (g.push d).xbit_ = (g.xbit_ || decide (g.digits_.toNat % 16 ≠ 0)) := by
    rw [xbit_push]; unfold nibble; rw [pow_zero, Nat.div_one]
  have hlow : g.digits_.toNat / 16 < 2 ^ 60 := by have := g.digits_.toNat_lt; omega
  rw [empty_iff_toNat] at he
  have hd_q : (0 : ℚ) ≤ d.toNat := Nat.cast_nonneg _
  have hd9 : (d.toNat : ℚ) ≤ 9 := by exact_mod_cast (by omega : d.toNat ≤ 9)
  have hE : (g.push d).empty = true ↔ d.toNat = 0 ∧ φ = 0 := by
    rw [empty_iff_toNat, hdig, hx, ← he, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, by omega, h2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, h3, by omega⟩
  have hf0 : (φ + (d.toNat : ℚ)) / 10 = 0 ↔ d.toNat = 0 ∧ φ = 0 := by
    constructor
    · intro h
      have h' : φ + (d.toNat : ℚ) = 0 := by linarith [div_eq_zero_iff.mp h]
      have hd0 : (d.toNat : ℚ) = 0 := by linarith
      exact ⟨by exact_mod_cast hd0, by linarith⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]; norm_num
  refine ⟨hE.trans hf0.symm, ?_⟩
  by_cases hemp : (g.push d).empty = true
  · obtain ⟨h1, h2⟩ := hE.mp hemp
    have hr : (g.push d).round .to_nearest = -2 := by unfold Guard.round; rw [if_pos hemp]
    rw [hr, h1, h2]
    norm_num
  rw [round_to_nearest_toNat hemp, hdig, hx]
  rcases Nat.lt_trichotomy d.toNat 5 with hlt | heq | hgt
  · have hlt' : (d.toNat : ℚ) ≤ 4 := by exact_mod_cast (by omega : d.toNat ≤ 4)
    have hf : (φ + (d.toNat : ℚ)) / 10 < 1 / 2 := by
      rw [div_lt_iff₀ (by norm_num)]; linarith
    rw [if_neg (by omega), if_pos (by omega)]
    constructor
    · constructor
      · intro h; norm_num at h
      · intro h; linarith
    · constructor
      · intro h; norm_num at h
      · intro h; linarith
  · rw [heq]
    rw [heq] at hE
    push_cast
    by_cases hD : g.digits_.toNat / 16 = 0
    · rw [if_neg (by omega), if_neg (by omega)]
      by_cases hφ : φ = 0
      · obtain ⟨hD0, hx0⟩ := he.mpr hφ
        rw [hx0, hD0, if_neg (by decide), hφ]
        norm_num
      · have hx1 : (g.xbit_ || decide (g.digits_.toNat % 16 ≠ 0)) = true := by
          cases hgx' : g.xbit_
          · simp only [Bool.false_or, decide_eq_true_eq]
            intro hm
            exact hφ (he.mp ⟨by omega, hgx'⟩)
          · rfl
        have hφpos : 0 < φ := lt_of_le_of_ne hφ0 (Ne.symm hφ)
        rw [if_pos hx1]
        refine ⟨⟨fun _ => by rw [lt_div_iff₀ (by norm_num)]; linarith, fun _ => rfl⟩, ?_⟩
        constructor
        · intro h; norm_num at h
        · intro h; linarith
    · rw [if_pos (by omega)]
      have hφpos : φ ≠ 0 := fun h => by
        have := he.mpr h
        omega
      have hφpos' : 0 < φ := lt_of_le_of_ne hφ0 (Ne.symm hφpos)
      constructor
      · exact ⟨fun _ => by rw [lt_div_iff₀ (by norm_num)]; linarith, fun _ => rfl⟩
      · constructor
        · intro h; norm_num at h
        · intro h; linarith
  · have hge : (6 : ℚ) ≤ d.toNat := by exact_mod_cast (by omega : 6 ≤ d.toNat)
    have hf : 1 / 2 < (φ + (d.toNat : ℚ)) / 10 := by
      rw [lt_div_iff₀ (by norm_num)]; linarith
    rw [if_pos (by omega)]
    constructor
    · exact ⟨fun _ => hf, fun _ => rfl⟩
    · constructor
      · intro h; norm_num at h
      · intro h; linarith

/-- `RoundsLike` only sees whether the fraction is zero, above one half or exactly one half. -/
private lemma Guard.RoundsLike.congr {g : Guard} {x y : ℚ} (h : g.RoundsLike x) (h0 : x = 0 ↔ y = 0)
    (h1 : 1 / 2 < x ↔ 1 / 2 < y) (h2 : x = 1 / 2 ↔ y = 1 / 2) : g.RoundsLike y :=
  ⟨h.1.trans h0, h.2.1.trans h1, h.2.2.trans h2⟩

/-- `doNormalize_scaleDown128Spec` keeps the value with the exact fraction `φ`. Its final guard rounds the final
fraction like exact rounding when the starting guard did, or when at least one digit is pushed. -/
private lemma doNormalize_scaleDown128_roundsLike (m : UInt128) (e : Int) (g : Guard) (φ : ℚ)
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (he : g.empty = true ↔ φ = 0)
    (hrl : g.RoundsLike φ ∨ m > toUInt128 largeRange.max)
    (out : UInt128 × Int × Guard)
    (hok : doNormalize_scaleDown128Spec largeRange.max m e g = .ok out) :
    ∃ φ₂ : ℚ, 0 ≤ φ₂ ∧ φ₂ < 1 ∧
      ((m.toNat : ℚ) + φ) * 10 ^ e = ((out.1.toNat : ℚ) + φ₂) * 10 ^ out.2.1 ∧
      out.2.2.RoundsLike φ₂ := by
  induction m, e, g using doNormalize_scaleDown128Spec.induct (maxMantissa := largeRange.max)
    generalizing φ with
  | case1 m e g hgt hge =>
    rw [show doNormalize_scaleDown128Spec largeRange.max m e g = .error .normalize1 from by
      rw [doNormalize_scaleDown128Spec.eq_def]
      rw [dif_pos hgt, if_pos hge]] at hok
    exact absurd hok (by intro h; cases h)
  | case2 m e g hgt hnge ih =>
    rw [show doNormalize_scaleDown128Spec largeRange.max m e g
        = doNormalize_scaleDown128Spec largeRange.max (m / 10) (e + 1) (g.push (toUInt64 (m % 10)))
        from by
      rw [doNormalize_scaleDown128Spec.eq_def]
      rw [dif_pos hgt, if_neg hnge]] at hok
    have h10 : ((10 : UInt128)).toNat = 10 := by decide
    have h_div : (m / 10 : UInt128).toNat = m.toNat / 10 := by
      rw [BitVec.toNat_udiv, h10]
    have h_mod : (m % 10 : UInt128).toNat = m.toNat % 10 := by
      rw [BitVec.toNat_umod, h10]
    have h_d_toNat : (toUInt64 (m % 10)).toNat = m.toNat % 10 := by
      rw [toNat_toUInt64 (by rw [h_mod]; have : m.toNat % 10 < 10 := Nat.mod_lt _ (by norm_num); omega), h_mod]
    have h_d_lt : (toUInt64 (m % 10)).toNat < 10 := by
      rw [h_d_toNat]; exact Nat.mod_lt _ (by norm_num)
    have hrl' := Guard.roundsLike_push he hφ0 hφ1 h_d_lt
    have hd_nn : (0 : ℚ) ≤ ((toUInt64 (m % 10)).toNat : ℚ) := Nat.cast_nonneg _
    have hd9 : ((toUInt64 (m % 10)).toNat : ℚ) ≤ 9 := by
      exact_mod_cast Nat.lt_succ_iff.mp h_d_lt
    have hφ'_nn : 0 ≤ (φ + ((toUInt64 (m % 10)).toNat : ℚ)) / 10 := div_nonneg (by linarith) (by norm_num)
    have hφ'_lt : (φ + ((toUInt64 (m % 10)).toNat : ℚ)) / 10 < 1 := by
      rw [div_lt_one (by norm_num : (0 : ℚ) < 10)]
      linarith
    obtain ⟨φ₂, h2nn, h2lt, h2val, h2rl⟩ :=
      ih ((φ + ((toUInt64 (m % 10)).toNat : ℚ)) / 10) hφ'_nn hφ'_lt hrl'.1 (Or.inl hrl') hok
    refine ⟨φ₂, h2nn, h2lt, ?_, h2rl⟩
    rw [← h2val]
    have h_decomp : (m.toNat : ℚ) = ((m / 10 : UInt128).toNat : ℚ) * 10
        + ((toUInt64 (m % 10)).toNat : ℚ) := by
      rw [h_div, h_d_toNat]
      have h_nat : m.toNat = m.toNat / 10 * 10 + m.toNat % 10 := by omega
      have h_q : (m.toNat : ℚ) = ((m.toNat / 10 * 10 + m.toNat % 10 : ℕ) : ℚ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) h_nat
      rw [h_q]; push_cast; ring
    rw [h_decomp]
    rw [show (10 : ℚ) ^ (e + 1) = 10 ^ e * 10 from by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp]
    field_simp
    ring
  | case3 m e g hgt =>
    rw [show doNormalize_scaleDown128Spec largeRange.max m e g = .ok (m, e, g) from by
      rw [doNormalize_scaleDown128Spec.eq_def]
      rw [dif_neg hgt]] at hok
    obtain rfl := (Except.ok.inj hok).symm
    exact ⟨φ, hφ0, hφ1, rfl, hrl.resolve_right hgt⟩

/-- `doNormalize_capAtMaxRep` keeps the value with the exact fraction `φ` and keeps a guard that rounds it like
exact rounding. -/
private lemma doNormalize_capAtMaxRep_roundsLike (m : UInt64) (e : Int) (g : Guard) (φ : ℚ)
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hrl : g.RoundsLike φ)
    (out : UInt64 × Int × Guard) (hok : doNormalize_capAtMaxRep m e g = .ok out) :
    ∃ φ₂ : ℚ, 0 ≤ φ₂ ∧ φ₂ < 1 ∧
      ((m.toNat : ℚ) + φ) * 10 ^ e = ((out.1.toNat : ℚ) + φ₂) * 10 ^ out.2.1 ∧
      out.2.2.RoundsLike φ₂ := by
  unfold doNormalize_capAtMaxRep at hok
  by_cases h_gt : m > maxRepUp
  · rw [if_pos h_gt] at hok
    by_cases h_ge : e ≥ maxExponent
    · rw [if_pos h_ge] at hok
      exact absurd hok (by intro h; cases h)
    · rw [if_neg h_ge] at hok
      unfold divu10 at hok
      simp only [] at hok
      obtain rfl := (Except.ok.inj hok).symm
      have h10 : (10 : UInt64).toNat = 10 := uint64_ten_toNat
      have h_div : (m / 10).toNat = m.toNat / 10 := by rw [UInt64.toNat_div, h10]
      have h_mod : (m % 10).toNat = m.toNat % 10 := by rw [UInt64.toNat_mod, h10]
      have h_d_lt : (m % 10).toNat < 10 := by rw [h_mod]; exact Nat.mod_lt _ (by norm_num)
      have hd_nn : (0 : ℚ) ≤ ((m % 10).toNat : ℚ) := Nat.cast_nonneg _
      have hd9 : ((m % 10).toNat : ℚ) ≤ 9 := by exact_mod_cast Nat.lt_succ_iff.mp h_d_lt
      refine ⟨(φ + ((m % 10).toNat : ℚ)) / 10, div_nonneg (by linarith) (by norm_num), ?_, ?_,
        Guard.roundsLike_push hrl.1 hφ0 hφ1 h_d_lt⟩
      · rw [div_lt_one (by norm_num : (0 : ℚ) < 10)]
        linarith
      · have h_decomp : (m.toNat : ℚ) = ((m / 10).toNat : ℚ) * 10 + ((m % 10).toNat : ℚ) := by
          rw [h_div, h_mod]
          have h_nat : m.toNat = m.toNat / 10 * 10 + m.toNat % 10 := by omega
          have h_q : (m.toNat : ℚ) = ((m.toNat / 10 * 10 + m.toNat % 10 : ℕ) : ℚ) := by
            exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) h_nat
          rw [h_q]; push_cast; ring
        rw [h_decomp]
        rw [show (10 : ℚ) ^ (e + 1) = 10 ^ e * 10 from by
          rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp]
        field_simp
        ring
  · rw [if_neg h_gt] at hok
    obtain rfl := (Except.ok.inj hok).symm
    exact ⟨φ, hφ0, hφ1, rfl, hrl⟩

/-- `doNormalize128_algorithmic_facts` for `.to_nearest`, with the final guard rounding the exact dropped fraction
`f` like exact rounding. -/
lemma doNormalize128_nearest_facts
    (zn : Bool) (M : UInt128) (e : Int) (δ : ℚ) (sticky : Bool)
    (hδ_low : 0 ≤ δ) (hδ_lt : δ < 1)
    (hsticky_zero : sticky = false → δ = 0)
    (hsticky_pos : sticky = true → 0 < δ)
    (hM_pos : 1 ≤ M.toNat) (hM_lt : M.toNat < 10 ^ 23)
    (hδM : sticky = true → δ * 10 ^ 20 ≤ (M.toNat : ℚ))
    (result : Number)
    (hok : doNormalize128 zn M e largeRange.min largeRange.max .to_nearest sticky = .ok result)
    (hres : result.mantissa_ ≠ 0) :
    ∃ (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult),
      mantissaFloorSucc ≤ zm.toNat ∧
      zm.toNat ≤ maxRepUp.toNat ∧
      0 ≤ f ∧ f < 1 ∧
      ((M.toNat : ℚ) + δ) * 10 ^ e = ((zm.toNat : ℚ) + f) * 10 ^ ze' ∧
      g.doRoundUp false zm ze' largeRange.min largeRange.max .to_nearest .normalize2 = .ok res_pos ∧
      |result.toRat| = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ ∧
      res_pos.mantissa_ ≠ 0 ∧
      result.negative_ = zn ∧
      g.RoundsLike f := by
  have hminM_v : largeRange.min.toNat = 1000000000000000000 := largeRange_min_val
  have hmaxM_v : largeRange.max.toNat = 9999999999999999999 := largeRange_max_val
  have hM_ne : ¬ (M == 0) = true := by
    intro h
    have : M = 0 := by exact_mod_cast beq_iff_eq.mp h
    rw [this] at hM_pos
    simp at hM_pos
  rw [doNormalize128_eq_spec] at hok
  unfold doNormalize128Spec at hok
  rw [if_neg hM_ne] at hok
  simp only [] at hok
  rcases hsu : doNormalize128_scaleUpSpec largeRange.min M e with ⟨M₁, e₁⟩
  rw [hsu] at hok
  simp only [] at hok
  obtain ⟨hval_su, hM₁_pos, hM₁_lt, he₁_le, hM₁_size⟩ :
      ((M₁.toNat : ℚ) * 10 ^ e₁ = (M.toNat : ℚ) * 10 ^ e)
      ∧ 1 ≤ M₁.toNat ∧ M₁.toNat < 10 ^ 23 ∧ e₁ ≤ e
      ∧ (M₁ = M ∧ e₁ = e ∨ M₁.toNat < 10 ^ 19) := by
    have hfacts := doNormalize128_scaleUp_facts largeRange.min M e hminM_v hM_pos hM_lt
    rw [hsu] at hfacts
    exact hfacts
  have h10e_pos : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  have h10e₁_pos : (0 : ℚ) < (10 : ℚ) ^ e₁ := zpow_pos (by norm_num) _
  set δ₁ : ℚ := δ * 10 ^ (e - e₁) with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ :=
    mul_nonneg hδ_low (le_of_lt (zpow_pos (by norm_num) _))
  have hδ₁_zero : sticky = false → δ₁ = 0 := by
    intro hst
    rw [hδ₁_def, hsticky_zero hst, zero_mul]
  have hδ₁_pos : sticky = true → 0 < δ₁ := fun hst =>
    mul_pos (hsticky_pos hst) (zpow_pos (by norm_num) _)
  have hval₁ : ((M₁.toNat : ℚ) + δ₁) * 10 ^ e₁ = ((M.toNat : ℚ) + δ) * 10 ^ e := by
    rw [hδ₁_def, add_mul, add_mul, hval_su]
    congr 1
    rw [show δ * 10 ^ (e - e₁) * 10 ^ e₁ = δ * (10 ^ (e - e₁) * 10 ^ e₁) from by ring,
        ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), show e - e₁ + e₁ = e from by omega]
  have hδ₁M : δ₁ * 10 ^ 20 ≤ (M₁.toNat : ℚ) := by
    by_cases hst : sticky = true
    · have h := hδM hst
      have lhs_eq : δ₁ * 10 ^ 20 * 10 ^ e₁ = δ * 10 ^ 20 * 10 ^ e := by
        rw [hδ₁_def,
            show δ * 10 ^ (e - e₁) * 10 ^ 20 * 10 ^ e₁
              = δ * 10 ^ 20 * (10 ^ (e - e₁) * 10 ^ e₁) from by ring,
            ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), show e - e₁ + e₁ = e from by omega]
      have hfin : δ₁ * 10 ^ 20 * 10 ^ e₁ ≤ (M₁.toNat : ℚ) * 10 ^ e₁ := by
        rw [lhs_eq, hval_su]
        exact mul_le_mul_of_nonneg_right h (le_of_lt h10e_pos)
      exact le_of_mul_le_mul_right hfin h10e₁_pos
    · rw [Bool.not_eq_true] at hst
      rw [hδ₁_zero hst, zero_mul]
      exact Nat.cast_nonneg _
  have hδ₁_lt : δ₁ < 1 := by
    rcases hM₁_size with ⟨_, heeq⟩ | hlt19
    · rw [hδ₁_def, heeq, sub_self, zpow_zero, mul_one]
      exact hδ_lt
    · have hM₁q : (M₁.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hlt19
      nlinarith [hδ₁M, hM₁q, hδ₁_nn]
  set g₀ : Guard := (if sticky = true
      then (if zn then Guard.new.set_negative else Guard.new).set_sticky
      else (if zn then Guard.new.set_negative else Guard.new)) with hg₀_def
  set ftilde₀ : ℚ := (if sticky = true then (1 : ℚ) / 10 ^ 17 else 0) with hft₀_def
  have hrep₀ : represents g₀ ftilde₀ := by
    rw [hg₀_def, hft₀_def]
    by_cases hst : sticky = true
    · rw [if_pos hst, if_pos hst]
      exact represents_sticky_initial128 zn
    · rw [if_neg hst, if_neg hst]
      exact g0_represents_zero zn
  -- The starting guard rounds `δ₁` like exact rounding, unless the scale-down pushes a digit.
  have hrl₀ : g₀.RoundsLike ftilde₀ := Guard.roundsLike_of_represents hrep₀
  have hinit : (g₀.empty = true ↔ δ₁ = 0) ∧ (g₀.RoundsLike δ₁ ∨ M₁ > toUInt128 largeRange.max) := by
    by_cases hst : sticky = true
    · have hft : ftilde₀ = 1 / 10 ^ 17 := by rw [hft₀_def, if_pos hst]
      have hpos := hδ₁_pos hst
      refine ⟨hrl₀.1.trans ⟨fun h => by rw [hft] at h; norm_num at h, fun h => by linarith⟩, ?_⟩
      by_cases hgt : M₁ > toUInt128 largeRange.max
      · exact Or.inr hgt
      · left
        have hle : M₁.toNat ≤ 9999999999999999999 := by
          by_contra hc
          push Not at hc
          apply hgt
          change toUInt128 largeRange.max < M₁
          rw [BitVec.lt_def, toNat_toUInt128, hmaxM_v]
          exact hc
        have hM₁q : (M₁.toNat : ℚ) ≤ 9999999999999999999 := by exact_mod_cast hle
        have hsmall : δ₁ < 1 / 2 := by nlinarith [hδ₁M]
        rw [hft] at hrl₀
        refine hrl₀.congr ⟨fun h => by norm_num at h, fun h => by linarith⟩
          ⟨fun h => by norm_num at h, fun h => by linarith⟩ ⟨fun h => by norm_num at h, fun h => by linarith⟩
    · have hft : ftilde₀ = δ₁ := by
        rw [hft₀_def, if_neg hst, hδ₁_zero (Bool.not_eq_true _ |>.mp hst)]
      rw [hft] at hrl₀
      exact ⟨hrl₀.1, Or.inl hrl₀⟩
  cases hsd : doNormalize_scaleDown128Spec largeRange.max M₁ e₁ g₀ with
  | error err =>
    except_clash hsd hok
  | ok sd =>
    rw [hsd] at hok
    simp only [] at hok
    obtain ⟨_, ftilde₂, h2nn, h2le1, h2rep, -, -, h2le, -⟩ :=
      doNormalize_scaleDown128_repr largeRange.max M₁ e₁ g₀ hmaxM_v δ₁ ftilde₀
        hδ₁_nn (le_of_lt hδ₁_lt) hrep₀ hM₁_lt sd hsd
    obtain ⟨φ₂, hφ₂_nn, hφ₂_lt, hφ₂_val, hφ₂_rl⟩ :=
      doNormalize_scaleDown128_roundsLike M₁ e₁ g₀ δ₁ hδ₁_nn hδ₁_lt hinit.1 hinit.2 sd hsd
    by_cases hund : (sd.2.1 < minExponent || sd.1 < toUInt128 largeRange.min) = true
    · rw [if_pos hund] at hok
      exfalso
      apply hres
      have h := Except.ok.inj hok
      rw [← h]
      rfl
    · rw [if_neg hund] at hok
      rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hund
      obtain ⟨hund1, hund2⟩ := hund
      have hM₂_ge : 1000000000000000000 ≤ sd.1.toNat := by
        by_contra h
        push Not at h
        apply absurd (decide_eq_true (show sd.1 < toUInt128 largeRange.min from by
          rw [BitVec.lt_def, toNat_toUInt128, hminM_v]; exact h))
        rw [hund2]; simp
      have hM₂_fit : sd.1.toNat < 2 ^ 64 := by
        rw [hmaxM_v] at h2le
        omega
      have hM₂u_toNat : (toUInt64 sd.1).toNat = sd.1.toNat := toNat_toUInt64 hM₂_fit
      cases hcap : doNormalize_capAtMaxRep (toUInt64 sd.1) sd.2.1 sd.2.2 with
      | error err =>
        except_clash hcap hok
      | ok cp =>
        rw [hcap] at hok
        simp only [] at hok
        obtain ⟨_, _, -, -, -, -, -, h3floor, h3le, -⟩ :=
          doNormalize_capAtMaxRep_repr (toUInt64 sd.1) sd.2.1 sd.2.2
            (by rw [hM₂u_toNat]; exact hM₂_ge)
            (by rw [hM₂u_toNat]; rw [hmaxM_v] at h2le; exact h2le)
            _ ftilde₂ h2nn h2le1 h2rep cp hcap
        obtain ⟨φ₃, hφ₃_nn, hφ₃_lt, hφ₃_val, hφ₃_rl⟩ :=
          doNormalize_capAtMaxRep_roundsLike (toUInt64 sd.1) sd.2.1 sd.2.2 φ₂ hφ₂_nn hφ₂_lt hφ₂_rl cp hcap
        cases hru : cp.2.2.doRoundUp zn cp.1 cp.2.1 largeRange.min largeRange.max
            .to_nearest .normalize2 with
        | error err =>
          except_clash hru hok
        | ok res =>
          rw [hru] at hok
          have h_result : result = res.toNumber := (Except.ok.inj hok).symm
          have hres_mant : res.mantissa_ ≠ 0 := by
            rw [h_result] at hres
            exact hres
          set res_pos : RoundResult :=
            { negative_ := false, mantissa_ := res.mantissa_, exponent_ := res.exponent_ }
            with hres_pos_def
          have h_rup_pos : cp.2.2.doRoundUp false cp.1 cp.2.1 largeRange.min largeRange.max
              .to_nearest .normalize2 = .ok res_pos :=
            doRoundUp_false_from_ok cp.2.2 zn cp.1 cp.2.1 .to_nearest .normalize2 res hru
          have h_value : ((cp.1.toNat : ℚ) + φ₃) * 10 ^ cp.2.1
              = ((M.toNat : ℚ) + δ) * 10 ^ e := by
            rw [← hφ₃_val, hM₂u_toNat, ← hφ₂_val, hval₁]
          have h_abs : |result.toRat|
              = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ := by
            rw [h_result, abs_toRat_eq res.toNumber]
            rfl
          have h_neg : result.negative_ = zn := by
            rw [h_result]
            exact doRoundUp_negative_of_mant_ne cp.2.2 zn cp.1 cp.2.1 _ _ _
              .normalize2 res hru hres_mant
          exact ⟨cp.1, cp.2.1, φ₃, cp.2.2, res_pos, by omega, h3le, hφ₃_nn, hφ₃_lt, h_value.symm,
            h_rup_pos, h_abs, hres_mant, h_neg, hφ₃_rl⟩

end XRPL.Model.Protocol
