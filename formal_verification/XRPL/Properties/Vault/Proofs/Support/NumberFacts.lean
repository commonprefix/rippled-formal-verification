import XRPL.Properties.Protocol.Number.Totality
import XRPL.Properties.Protocol.Number.Normalize.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.Common.RoundMonotoneSatDiv
import XRPL.Properties.Vault.Proofs.Support.Basic
-- Re-exported for the files that import this one
import XRPL.Properties.Protocol.Number.ToRep.Common.Proofs
import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary
import XRPL.Properties.Protocol.STAmount.Common.OfNumberFacts
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality

/-! # `Number` facts

Facts about `Number`: rounding of the arithmetic operators, `to_rep`, `truncate`, signs. -/

namespace XRPL.Model.Protocol

/-- `truncateAux` divides out the negative exponent: the value is the natural quotient by `10 ^ (-e)`, the mantissa
never grows, and a nonzero result lands at exponent `0`. -/
lemma Number.truncateAux_val (m : UInt64) (e : Int) :
    e ≤ 0 →
    ((Number.truncateAux m e).1.toNat : ℚ) * 10 ^ (Number.truncateAux m e).2
        = ((m.toNat / 10 ^ (-e).toNat : ℕ) : ℚ) ∧
      (Number.truncateAux m e).1.toNat ≤ m.toNat ∧
      ((Number.truncateAux m e).1.toNat ≠ 0 → (Number.truncateAux m e).2 = 0) := by
  induction m, e using Number.truncateAux.induct with
  | case1 m e h ih =>
    intro he
    rw [show Number.truncateAux m e = Number.truncateAux (m / 10) (e + 1) from by
      rw [Number.truncateAux, if_pos h]]
    obtain ⟨hval, hle, hzero⟩ := ih (by omega)
    have hdiv10 : (m / 10).toNat = m.toNat / 10 := by
      rw [UInt64.toNat_div]
      rfl
    refine ⟨?_, ?_, hzero⟩
    · rw [hval]
      congr 1
      rw [hdiv10, Nat.div_div_eq_div_mul]
      congr 1
      have hd : (-e).toNat = (-(e + 1)).toNat + 1 := by omega
      rw [hd, pow_succ]
      ring
    · rw [hdiv10] at hle
      exact le_trans hle (Nat.div_le_self _ _)
  | case2 m e h =>
    intro he
    rw [show Number.truncateAux m e = (m, e) from by
      rw [Number.truncateAux, if_neg h]]
    by_cases he0 : e = 0
    · subst he0
      refine ⟨by norm_num, le_refl _, fun _ => rfl⟩
    · have hm : m = 0 := by
        rcases not_and_or.mp h with h1 | h2
        · omega
        · simpa using h2
      subst hm
      refine ⟨by norm_num, le_refl _, fun h0 => absurd rfl h0⟩

/-- `Number.truncate` floors a non-negative normalized value. The result is
the integer part, integer-valued, and normalized whenever nonzero. -/
lemma Number.truncate_floor (n t : Number) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hok : n.truncate = .ok t) :
    t.toRat = (⌊n.toRat⌋ : ℚ) ∧ (t.mantissa_ ≠ 0 → t.isNormalized) := by
  unfold Number.truncate at hok
  by_cases hg : n.exponent_ ≥ 0 ∨ n.mantissa_ = 0
  · rw [if_pos hg] at hok
    have ht : t = n := (Except.ok.inj hok).symm
    subst ht
    by_cases hm : t.mantissa_ = 0
    · have h0 : t.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero t hm
      rw [h0]
      norm_num
      exact fun h => absurd hm h
    · have hexp : 0 ≤ t.exponent_ := by
        rcases hg with h | h
        · exact h
        · exact absurd h hm
      have hval : t.toRat = ((t.mantissa_.toNat * 10 ^ t.exponent_.toNat : ℕ) : ℚ) := by
        rw [Number.toRat_of_nonneg t hneg]
        push_cast
        rw [← zpow_natCast (10 : ℚ) t.exponent_.toNat, Int.toNat_of_nonneg hexp]
      rw [hval, Int.floor_natCast]
      exact ⟨rfl, fun _ => hn⟩
  · rw [if_neg hg] at hok
    push Not at hg
    obtain ⟨hexp_neg', hm_ne⟩ := hg
    have hexp_neg : n.exponent_ < 0 := by omega
    obtain ⟨hval, hle, hzero⟩ := Number.truncateAux_val n.mantissa_ n.exponent_ (le_of_lt hexp_neg)
    cases hp : Number.truncateAux n.mantissa_ n.exponent_ with
    | mk m' e' =>
      rw [hp] at hok hval hle hzero
      simp only [] at hok hval hle hzero
      set K : ℕ := n.mantissa_.toNat / 10 ^ (-n.exponent_).toNat with hK
      -- the input to the final normalize denotes exactly `K`
      have hin_val : (Number.unchecked n.negative_ m' e').toRat = (K : ℚ) := by
        rw [Number.toRat_of_nonneg _
          (show (Number.unchecked n.negative_ m' e').negative_ = false from hneg)]
        exact hval
      have hfloor : ⌊n.toRat⌋ = (K : ℤ) := by
        have hd_pos : 0 < 10 ^ (-n.exponent_).toNat := by positivity
        have hnval : n.toRat = (n.mantissa_.toNat : ℚ) / ((10 ^ (-n.exponent_).toNat : ℕ) : ℚ) := by
          rw [Number.toRat_of_nonneg n hneg]
          push_cast
          rw [← zpow_natCast (10 : ℚ) (-n.exponent_).toNat,
            Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n.exponent_),
            zpow_neg, div_eq_mul_inv, inv_inv]
        rw [hnval, Int.floor_nat_div _ _ hd_pos]
      -- `K` is representable: at most 18 digits
      have hK_lt : K < 2 ^ 63 := by
        have hmb := hn.mantissaBounds hm_ne
        have hmax : n.mantissa_.toNat ≤ largeRange.max.toNat := UInt64.le_iff_toNat_le.mp hmb.2
        have hmaxv : largeRange.max.toNat = 9999999999999999999 := by decide
        have hd_ge : 10 ≤ 10 ^ (-n.exponent_).toNat := by
          have h1 : 1 ≤ (-n.exponent_).toNat := by omega
          calc (10 : ℕ) = 10 ^ 1 := by norm_num
            _ ≤ 10 ^ (-n.exponent_).toNat := Nat.pow_le_pow_right (by norm_num) h1
        have : K ≤ n.mantissa_.toNat / 10 := Nat.div_le_div_left hd_ge (by norm_num)
        have h10 : n.mantissa_.toNat / 10 ≤ 999999999999999999 := by omega
        omega
      -- the final normalize is exact on the representable target
      have hgrid := normalize_rounded_to_nearest (Number.unchecked n.negative_ m' e') t hok
      rw [hin_val] at hgrid
      have hrep : ∃ w : Number, w.isNormalized ∧ w.toRat = (K : ℚ) := by
        rcases Nat.eq_zero_or_pos K with h0 | hpos
        · exact ⟨Number.zero, Or.inl rfl, by rw [Number.toRat_zero, h0]; norm_num⟩
        · obtain ⟨w, hw1, _, hw3⟩ := Number.exists_normalized_of_pos_nat K hpos hK_lt
          exact ⟨w, hw1, hw3⟩
      obtain ⟨w, hw_norm, hw_val⟩ := hrep
      have hexact : t.toRat = (K : ℚ) :=
        Number.RoundsToRepresentable.eq_of_representable t _ hgrid w hw_norm hw_val
      refine ⟨by rw [hexact, hfloor]; norm_cast, ?_⟩
      intro ht_ne
      have hm' : m' ≠ 0 := by
        intro h0
        have hKzero : (K : ℚ) = 0 := by
          rw [← hval, h0]
          norm_num
        have := Number.toRat_ne_zero_of_mantissa_ne_zero t ht_ne
        rw [hexact] at this
        exact this hKzero
      exact normalize_result_isNormalized (Number.unchecked n.negative_ m' e') t .to_nearest
        hm' hok ht_ne

/-- `Number.truncate` is monotone on nonnegative normalized inputs. -/
lemma Number.truncate_toRat_mono (n₁ n₂ t₁ t₂ : Number)
    (hn₁ : n₁.isNormalized) (hn₂ : n₂.isNormalized)
    (hneg₁ : n₁.negative_ = false) (hneg₂ : n₂.negative_ = false)
    (hok₁ : n₁.truncate = .ok t₁) (hok₂ : n₂.truncate = .ok t₂)
    (hle : n₁.toRat ≤ n₂.toRat) : t₁.toRat ≤ t₂.toRat := by
  rw [(Number.truncate_floor n₁ t₁ hn₁ hneg₁ hok₁).1,
      (Number.truncate_floor n₂ t₂ hn₂ hneg₂ hok₂).1]
  exact_mod_cast Int.floor_mono hle

/-- Pricing chain monotone. For fixed positive normalized `k` and `d`, the `.to_nearest` map `a ↦ (k * a) / d`
is monotone in a positive `a`. -/
lemma Number.mul_div_num_mono (k d a₁ a₂ m₁ m₂ q₁ q₂ : Number)
    (hk : k.isNormalized) (hkm : k.mantissa_ ≠ 0) (hkneg : k.negative_ = false)
    (hd : d.isNormalized) (hdm : d.mantissa_ ≠ 0) (hdneg : d.negative_ = false)
    (ha₁ : a₁.isNormalized) (ha₁m : a₁.mantissa_ ≠ 0) (ha₁neg : a₁.negative_ = false)
    (ha₂ : a₂.isNormalized) (ha₂m : a₂.mantissa_ ≠ 0) (ha₂neg : a₂.negative_ = false)
    (hm₁ : k.operator_mul a₁ .to_nearest = .ok m₁) (hm₁m : m₁.mantissa_ ≠ 0)
    (hm₂ : k.operator_mul a₂ .to_nearest = .ok m₂) (hm₂m : m₂.mantissa_ ≠ 0)
    (hq₁ : m₁.operator_div d .to_nearest = .ok q₁) (hq₁m : q₁.mantissa_ ≠ 0)
    (hq₂ : m₂.operator_div d .to_nearest = .ok q₂) (hq₂m : q₂.mantissa_ ≠ 0)
    (hle : a₁.toRat ≤ a₂.toRat) : q₁.toRat ≤ q₂.toRat := by
  have hkpos := Number.toRat_pos_of_not_negative k hkneg hkm
  have hdpos := Number.toRat_pos_of_not_negative d hdneg hdm
  have ha₁pos := Number.toRat_pos_of_not_negative a₁ ha₁neg ha₁m
  have ha₂pos := Number.toRat_pos_of_not_negative a₂ ha₂neg ha₂m
  have hprod₁ : 0 < k.toRat * a₁.toRat := mul_pos hkpos ha₁pos
  have hprod₂ : 0 < k.toRat * a₂.toRat := mul_pos hkpos ha₂pos
  have hcm₁ := operator_mul_roundsCuspAware k a₁ m₁ hk ha₁ hkm ha₁m hm₁ hm₁m hprod₁
  have hcm₂ := operator_mul_roundsCuspAware k a₂ m₂ hk ha₂ hkm ha₂m hm₂ hm₂m hprod₂
  have hm₁neg : m₁.negative_ = false := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_mul_algorithmic_facts_to_nearest k a₁ m₁ hk ha₁ hkm ha₁m hm₁ hm₁m
    rw [hF.result_neg, hkneg, ha₁neg]; rfl
  have hm₂neg : m₂.negative_ = false := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_mul_algorithmic_facts_to_nearest k a₂ m₂ hk ha₂ hkm ha₂m hm₂ hm₂m
    rw [hF.result_neg, hkneg, ha₂neg]; rfl
  have hm₁pos := Number.toRat_pos_of_not_negative m₁ hm₁neg hm₁m
  have hm₂pos := Number.toRat_pos_of_not_negative m₂ hm₂neg hm₂m
  have hm₁norm := operator_mul_result_isNormalized k a₁ m₁ .to_nearest hk ha₁ hkm ha₁m hm₁ hm₁m
  have hm₂norm := operator_mul_result_isNormalized k a₂ m₂ .to_nearest hk ha₂ hkm ha₂m hm₂ hm₂m
  have hmle : m₁.toRat ≤ m₂.toRat :=
    operator_mul_left_mono_of_cuspAware k a₁ a₂ m₁ m₂ ha₁ ha₂ hm₁ hm₂ hcm₁ hcm₂
      hm₁pos hm₂pos hkpos ha₁pos hle
  have hquo₁ : 0 < m₁.toRat / d.toRat := div_pos hm₁pos hdpos
  have hquo₂ : 0 < m₂.toRat / d.toRat := div_pos hm₂pos hdpos
  have hcq₁ := operator_div_roundsCuspAware m₁ d q₁ hm₁norm hd hm₁m hdm hq₁ hq₁m hquo₁
  have hcq₂ := operator_div_roundsCuspAware m₂ d q₂ hm₂norm hd hm₂m hdm hq₂ hq₂m hquo₂
  have hq₁nn : 0 ≤ q₁.toRat := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_div_algorithmic_facts_to_nearest m₁ d q₁ hm₁norm hd hm₁m hdm hq₁ hq₁m
    exact hF.result_nonneg hquo₁
  have hq₂nn : 0 ≤ q₂.toRat := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_div_algorithmic_facts_to_nearest m₂ d q₂ hm₂norm hd hm₂m hdm hq₂ hq₂m
    exact hF.result_nonneg hquo₂
  have hq₁pos : 0 < q₁.toRat :=
    lt_of_le_of_ne hq₁nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero q₁ hq₁m))
  have hq₂pos : 0 < q₂.toRat :=
    lt_of_le_of_ne hq₂nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero q₂ hq₂m))
  exact operator_div_num_mono_of_cuspAware m₁ m₂ d q₁ q₂ hm₁norm hm₂norm hq₁ hq₂ hcq₁ hcq₂
    hq₁pos hq₂pos hdpos hm₁pos hmle

/-- Normalizing a zero mantissa yields the canonical zero, whatever the sign,
exponent, range or rounding mode. -/
lemma Number.normalized_zero_mantissa (neg : Bool) (e : Int) (mn mx : UInt64)
    (mode : rounding_mode) : Number.normalized neg 0 e mn mx mode = .ok Number.zero := by
  unfold Number.normalized Number.normalize doNormalize
  simp [Number.unchecked]

/-- `.downward` addition of two non-negative operands stays inside the exact sum and never goes negative. -/
lemma Number.operator_add_downward_nonneg_le (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxnn : 0 ≤ x.toRat) (hynn : 0 ≤ y.toRat)
    (hok : Number.operator_add x y .downward = .ok result) :
    result.toRat ≤ x.toRat + y.toRat ∧ 0 ≤ result.toRat := by
  have hok0 := hok
  unfold Number.operator_add at hok
  by_cases hy0 : y.operator_eq Number.zero = true
  · rw [if_pos hy0] at hok
    have hym : y.mantissa_ = 0 := by
      by_contra h
      rw [Number.operator_eq_zero_false_of_mantissa_ne y h] at hy0
      exact absurd hy0 (by simp)
    have hy0v : y.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero y hym
    rw [← Except.ok.inj hok, hy0v]
    exact ⟨by linarith, hxnn⟩
  · rw [if_neg hy0] at hok
    by_cases hx0 : x.operator_eq Number.zero = true
    · rw [if_pos hx0] at hok
      have hxm : x.mantissa_ = 0 := by
        by_contra h
        rw [Number.operator_eq_zero_false_of_mantissa_ne x h] at hx0
        exact absurd hx0 (by simp)
      have hx0v : x.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero x hxm
      rw [← Except.ok.inj hok, hx0v]
      exact ⟨by linarith, hynn⟩
    · rw [if_neg hx0] at hok
      by_cases hxy : x.operator_eq (y.operator_neg) = true
      · rw [if_pos hxy] at hok
        rw [← Except.ok.inj hok, Number.toRat_zero]
        exact ⟨by linarith, le_refl _⟩
      · have hxm : x.mantissa_ ≠ 0 := fun h =>
          hx0 (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
        have hym : y.mantissa_ ≠ 0 := fun h =>
          hy0 (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
        have hs : (0:ℚ) ≤ x.toRat + y.toRat := by linarith
        by_cases hrm : result.mantissa_ = 0
        · rw [Number.toRat_eq_zero_of_mantissa_zero result hrm]
          exact ⟨hs, le_refl _⟩
        · have hr := operator_add_rounds_downward x y result hx hy hxm hym
            (by simpa using hxy) hok0 hrm
          have hr' : result.toRat ≤ x.toRat + y.toRat ∧
              (x.toRat + y.toRat) - result.toRat ≤
                |x.toRat + y.toRat| * (11 / (2 ^ 63 - 18 : ℚ)) := hr
          rw [abs_of_nonneg hs] at hr'
          have hmul : (x.toRat + y.toRat) * (11 / (2 ^ 63 - 18 : ℚ)) ≤ x.toRat + y.toRat := by
            nlinarith [hs]
          exact ⟨hr'.1, by linarith [hr'.2, hmul]⟩

/-- A nonzero truncation forces a nonzero input mantissa. -/
lemma Number.truncate_source_ne_zero (n t : Number)
    (hok : n.truncate = .ok t) (ht : t.mantissa_ ≠ 0) : n.mantissa_ ≠ 0 := by
  intro h0
  unfold Number.truncate at hok
  rw [if_pos (Or.inr h0)] at hok
  rw [← Except.ok.inj hok] at ht
  exact ht h0

/-- `to_nearest` addition of two nonnegative normalized operands rounds within relative error `6 / (2^63 - 3)`. A
zero operand returns the other exactly. -/
lemma operator_add_nonneg_rounds (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxnn : 0 ≤ x.toRat) (hynn : 0 ≤ y.toRat)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    RoundsWithin result (x.toRat + y.toRat) .to_nearest (6 / (2 ^ 63 - 3 : ℚ)) := by
  have hε : (0 : ℚ) ≤ 6 / (2 ^ 63 - 3 : ℚ) := by positivity
  by_cases hym : y.mantissa_ = 0
  · have hy0 : y = Number.zero := Number.eq_zero_of_mantissa_zero y hy hym
    have hres : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos (by rw [hy0]; decide)] at hok
      exact (Except.ok.inj hok).symm
    refine RoundsWithin_mono result _ 0 _ _ (RoundsWithin_of_eq result _ _ ?_) hε
    rw [hres, hy0, Number.toRat_zero, add_zero]
    rfl
  by_cases hxm : x.mantissa_ = 0
  · have hx0 : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx hxm
    have hres : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hym),
          if_pos (by rw [hx0]; decide)] at hok
      exact (Except.ok.inj hok).symm
    refine RoundsWithin_mono result _ 0 _ _ (RoundsWithin_of_eq result _ _ ?_) hε
    rw [hres, hx0, Number.toRat_zero, zero_add]
    rfl
  -- both nonzero: same-sign (non-negative) addition
  have hxneg : x.negative_ = false := by
    rcases hb : x.negative_ with _ | _
    · rfl
    · exfalso
      have := Number.toRat_of_neg x hb
      have hxpos : (0 : ℚ) < (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ := by
        have h1 : x.mantissa_.toNat ≠ 0 := by
          intro h0; exact hxm (by rw [← UInt64.toNat_inj] at *; exact h0)
        have h2 : (1 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
        positivity
      rw [this] at hxnn
      linarith
  have hyneg : y.negative_ = false := by
    rcases hb : y.negative_ with _ | _
    · rfl
    · exfalso
      have := Number.toRat_of_neg y hb
      have hypos : (0 : ℚ) < (y.mantissa_.toNat : ℚ) * 10 ^ y.exponent_ := by
        have h1 : y.mantissa_.toNat ≠ 0 := by
          intro h0; exact hym (by rw [← UInt64.toNat_inj] at *; exact h0)
        have h2 : (1 : ℚ) ≤ (y.mantissa_.toNat : ℚ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1
        positivity
      rw [this] at hynn
      linarith
  have hnotz : ¬ x.operator_eq y.operator_neg = true := by
    intro hcon
    have hnegy : y.operator_neg = { y with negative_ := !y.negative_ } := by
      unfold Number.operator_neg
      rw [if_neg (by simpa using hym)]
    unfold Number.operator_eq at hcon
    rw [hnegy] at hcon
    simp only [Bool.and_eq_true, beq_iff_eq] at hcon
    have := hcon.1.1
    rw [hxneg, hyneg] at this
    exact Bool.noConfusion this
  have h := operator_add_rounds_same_sign_to_nearest x y result hx hy hxm hym
    (by rw [hxneg, hyneg]) hnotz hok
  refine RoundsWithin_mono result _ _ _ _ h (by norm_num)

/-- A positive-valued `Number` has a clear sign bit. -/
lemma Number.negative_false_of_pos (n : Number) (h : 0 < n.toRat) :
    n.negative_ = false := by
  rcases hb : n.negative_ with _ | _
  · rfl
  · exact absurd h (not_lt.mpr (Number.toRat_nonpos_of_negative n hb))

/-- Dividing by a whole number floors the same from any value between two integers. -/
private lemma floor_div_of_floor (z : ℚ) (m : ℤ) (n : ℕ) (hn : 0 < n) (h1 : (m : ℚ) ≤ z) (h2 : z < m + 1) :
    ⌊z / n⌋ = m / n := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  rw [Int.floor_eq_iff]
  have hdiv := Int.mul_ediv_add_emod m n
  have hmod0 := Int.emod_nonneg m (by exact_mod_cast hn.ne' : (n : ℤ) ≠ 0)
  have hmodlt := Int.emod_lt_of_pos m (by exact_mod_cast hn : (0 : ℤ) < n)
  constructor
  · rw [le_div_iff₀ hnq]
    have : ((m / n : ℤ) : ℚ) * n ≤ m := by
      have h : (m / n) * (n : ℤ) ≤ m := by nlinarith
      exact_mod_cast h
    linarith
  · rw [div_lt_iff₀ hnq]
    have : (m : ℚ) + 1 ≤ (((m / n : ℤ) : ℚ) + 1) * n := by
      have h : m + 1 ≤ (m / n + 1) * (n : ℤ) := by nlinarith
      exact_mod_cast h
    linarith

/-- Flooring onto a finer grid, then onto a coarser one, is flooring onto the coarser one. -/
lemma floor_grid_floor_of_le (x : ℚ) (g b : ℤ) (hgb : g ≤ b) :
    ⌊(⌊x / 10 ^ g⌋ : ℚ) * 10 ^ g / 10 ^ b⌋ = ⌊x / 10 ^ b⌋ := by
  set n : ℕ := 10 ^ (b - g).toNat with hn_def
  have hn : 0 < n := by positivity
  have hg : (0 : ℚ) < 10 ^ g := zpow_pos (by norm_num) _
  have hpow : (10 : ℚ) ^ b = (n : ℚ) * 10 ^ g := by
    rw [hn_def, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    congr 1
    omega
  have h1 : (⌊x / 10 ^ g⌋ : ℚ) * 10 ^ g / 10 ^ b = (⌊x / 10 ^ g⌋ : ℚ) / n := by
    rw [hpow]; field_simp
  have h2 : x / 10 ^ b = x / 10 ^ g / n := by rw [hpow]; field_simp
  rw [h1, h2, floor_div_of_floor _ ⌊x / 10 ^ g⌋ n hn le_rfl (by linarith),
    floor_div_of_floor _ ⌊x / 10 ^ g⌋ n hn (Int.floor_le _) (Int.lt_floor_add_one _)]

end XRPL.Model.Protocol
