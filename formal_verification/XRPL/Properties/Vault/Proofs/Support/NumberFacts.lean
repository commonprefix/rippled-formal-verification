import XRPL.Properties.Protocol.Number.Totality
import XRPL.Properties.Protocol.Number.Normalize.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.Common.RoundMonotoneSatDiv
import XRPL.Properties.Vault.Common.WitnessSupport
import XRPL.Properties.Vault.Proofs.Support.Basic
-- Re-exported for the files that import this one (these lemmas moved to Protocol)
import XRPL.Properties.Protocol.Number.ToRep.Common.Proofs
import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary
import XRPL.Properties.Protocol.STAmount.Common.OfNumberFacts
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality

/-! # `Number` facts

Facts about `Number`: rounding of the arithmetic operators, `to_rep`, `truncate`, signs. -/

namespace XRPL.Model.Protocol

/-- `truncateAux` divides out the negative exponent: the resulting value is the
natural quotient by `10 ^ (-e)`, the mantissa never grows, and a nonzero result
lands at exponent `0`. -/
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

/-- **`Number.truncate` floors a non-negative normalized value.** The result is
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
    -- expose the truncated pair
    obtain ⟨hval, hle, hzero⟩ := Number.truncateAux_val n.mantissa_ n.exponent_ (le_of_lt hexp_neg)
    cases hp : Number.truncateAux n.mantissa_ n.exponent_ with
    | mk m' e' =>
      rw [hp] at hok hval hle hzero
      simp only [] at hok hval hle hzero
      -- the target integer value
      set K : ℕ := n.mantissa_.toNat / 10 ^ (-n.exponent_).toNat with hK
      -- the input to the final normalize denotes exactly `K`
      have hin_val : (Number.unchecked n.negative_ m' e').toRat = (K : ℚ) := by
        rw [Number.toRat_of_nonneg _
          (show (Number.unchecked n.negative_ m' e').negative_ = false from hneg)]
        exact hval
      -- `K` is the floor of the value
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

/-- **Pricing chain monotone.** For fixed positive `k`, `d` (normalized, nonzero,
nonnegative), the map `a ↦ (k * a) / d` (`.to_nearest` at each stage) is monotone
in the varying positive operand `a`. -/
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

/-- **Upper monotonicity of `operator_sub` under `.to_nearest`.** When the exact
difference `x - y` is at most a representable `z`, so is the rounded result: no
representable lies strictly between the truth and a value above `z`. -/
lemma Number.operator_sub_to_nearest_le (x y z result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hne : ¬ x.operator_eq y)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (hres : result.mantissa_ ≠ 0)
    (hz_ge : x.toRat - y.toRat ≤ z.toRat) :
    result.toRat ≤ z.toRat := by
  by_contra hlt
  push Not at hlt
  have hyneg_norm : (y.operator_neg).isNormalized := Number.operator_neg_isNormalized y hy
  have hyneg_m : (y.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne y hym]; exact hym
  have hnz : ¬ x.operator_eq ((y.operator_neg).operator_neg) := by
    rw [neg_neg_of_mant_ne hym]; exact hne
  have hok' : Number.operator_add x (y.operator_neg) .to_nearest = .ok result := hok
  have hyneg_val : (y.operator_neg).toRat = - y.toRat := Number.toRat_neg y
  have h_ge : x.toRat + (y.operator_neg).toRat ≤ result.toRat := by
    rw [hyneg_val]; linarith [hz_ge, hlt]
  have hcontra := operator_add_no_inbetween_above x (y.operator_neg) result hx hyneg_norm
    hxm hyneg_m hnz hok' hres h_ge
  exact hcontra z hz hlt (by rw [hyneg_val]; linarith [hz_ge])

/-- **`.downward` addition of two non-negative operands stays inside the exact sum
and never goes negative.** All three of `operator_add`'s early exits keep the value,
and the general branch's relative error is far below `1`, so the floored sum cannot
cross zero. -/
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

/-- `to_nearest` `Number` addition of two non-negative normalized operands rounds
within the keystone relative error, with the zero cases exact. -/
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

/-- Subtracting an equal (nonzero) `arn` yields `Number.zero` (`x - x = 0`). -/
lemma Number.operator_sub_eq_zero_of_operator_eq (x arn result : Number)
    (hxm : x.mantissa_ ≠ 0) (harnm : arn.mantissa_ ≠ 0)
    (heq : x.operator_eq arn = true)
    (hok : x.operator_sub arn .to_nearest = .ok result) : result = Number.zero := by
  unfold Number.operator_sub at hok
  unfold Number.operator_add at hok
  have hnegm : (arn.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne arn harnm]; exact harnm
  rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hnegm)] at hok
  rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hxm)] at hok
  have h3 : x.operator_eq ((arn.operator_neg).operator_neg) = true := by
    rw [neg_neg_of_mant_ne harnm]; exact heq
  rw [if_pos h3] at hok
  simp only [pure, Except.pure] at hok
  exact (Except.ok.inj hok).symm

/-- Subtracting a zero-mantissa `arn` is the identity (`operator_add x 0 = x`). -/
lemma Number.operator_sub_zero_right (x arn result : Number) (harn : arn.mantissa_ = 0)
    (hok : x.operator_sub arn .to_nearest = .ok result) : result = x := by
  unfold Number.operator_sub at hok
  have hneg0 : arn.operator_neg = Number.zero := by
    unfold Number.operator_neg; rw [if_pos (by rw [harn]; rfl)]
  rw [hneg0] at hok
  unfold Number.operator_add at hok
  rw [if_pos (by decide : Number.zero.operator_eq Number.zero = true)] at hok
  simp only [pure, Except.pure] at hok
  exact (Except.ok.inj hok).symm

/-- **Subtracting a non-negative operand under `.to_nearest` never overshoots the
minuend.** The rounded difference `x - y` is at most `x`: a zero result is `≤ x`
because `x ≥ 0`, an equal-operand cancellation gives the zero result, and the
generic case is `operator_sub_to_nearest_le` at `z = x` (using `x - y ≤ x`). -/
lemma Number.operator_sub_nonneg_le (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hxnn : 0 ≤ x.toRat) (hynn : 0 ≤ y.toRat)
    (hok : x.operator_sub y .to_nearest = .ok result) :
    result.toRat ≤ x.toRat := by
  by_cases hresm : result.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero result hresm]; exact hxnn
  · have hne : ¬ x.operator_eq y := fun heq => by
      have hres0 := Number.operator_sub_eq_zero_of_operator_eq x y result hxm hym heq hok
      rw [hres0] at hresm; exact hresm rfl
    exact Number.operator_sub_to_nearest_le x y x result hx hy hx hxm hym hne hok hresm
      (by linarith [hynn])

/-- `J·10^ec` is a non-negative normalized `Number` for `1 ≤ J < 10^19` with the
sticky-tail condition and a small exponent window. Scaled generalization of
`Number.exists_normalized_of_pos_nat`. -/
lemma Number.exists_normalized_scaled (J : ℕ) (ec : ℤ)
    (h1 : 1 ≤ J) (h2 : J < 10 ^ 19)
    (h3 : J ≤ maxRep.toNat ∨ J % 10 = 0)
    (hlo : (-18 : ℤ) ≤ ec) (hhi : ec ≤ 0) :
    ∃ w : Number, w.isNormalized ∧ w.negative_ = false ∧
      w.toRat = (J : ℚ) * (10 : ℚ) ^ ec := by
  have hJne : J ≠ 0 := by omega
  have hlog_lo : 10 ^ Nat.log 10 J ≤ J := Nat.pow_log_le_self 10 hJne
  have hlog_hi : J < 10 ^ (Nat.log 10 J + 1) := Nat.lt_pow_succ_log_self (by norm_num) J
  set L := Nat.log 10 J with hL_def
  have hL_le : L ≤ 18 := by
    by_contra hcon
    push Not at hcon
    have : (10 : ℕ) ^ 19 ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set k : ℕ := 18 - L with hk_def
  set M : ℕ := J * 10 ^ k with hM_def
  have hLk : L + k = 18 := by omega
  have hM_lo : 10 ^ 18 ≤ M := by
    calc (10 : ℕ) ^ 18 = 10 ^ L * 10 ^ k := by rw [← pow_add, hLk]
      _ ≤ J * 10 ^ k := mul_le_mul_of_nonneg_right hlog_lo (by positivity)
  have hM_hi : M < 10 ^ 19 := by
    calc M = J * 10 ^ k := rfl
      _ < 10 ^ (L + 1) * 10 ^ k := mul_lt_mul_of_pos_right hlog_hi (by positivity)
      _ = 10 ^ 19 := by rw [← pow_add]; congr 1; omega
  have hM_lt : M < UInt64.size := by rw [uint64_size_val]; omega
  have hM_toNat : (Nat.toUInt64 M).toNat = M :=
    UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hM_lt)
  have hsticky : Nat.toUInt64 M ≤ maxRep ∨ (Nat.toUInt64 M).toNat % 10 = 0 := by
    by_cases hk0 : k = 0
    · rcases h3 with h3 | h3
      · left
        rw [UInt64.le_iff_toNat_le, hM_toNat]
        have hMJ : M = J := by rw [hM_def, hk0, pow_zero, Nat.mul_one]
        rw [hMJ]; exact h3
      · right
        rw [hM_toNat, hM_def, hk0, pow_zero, Nat.mul_one]
        exact h3
    · right
      rw [hM_toNat]
      have hdvd : (10 : ℕ) ∣ M := by
        rw [hM_def]
        exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) J
      omega
  refine ⟨⟨false, Nat.toUInt64 M, ec - (k : ℤ)⟩, ?_, rfl, ?_⟩
  · right
    refine ⟨?_, ?_, hsticky, ?_, ?_⟩
    · rw [UInt64.le_iff_toNat_le, largeRange_min_val, hM_toNat]; omega
    · rw [UInt64.le_iff_toNat_le, largeRange_max_val, hM_toNat]; omega
    · show minExponent ≤ ec - (k : ℤ); unfold minExponent; omega
    · show ec - (k : ℤ) ≤ maxExponent; unfold maxExponent; omega
  · rw [Number.toRat_of_nonneg _ rfl]
    show ((Nat.toUInt64 M).toNat : ℚ) * (10 : ℚ) ^ (ec - (k : ℤ)) = (J : ℚ) * (10 : ℚ) ^ ec
    rw [hM_toNat, hM_def, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
    push_cast
    have h10k : (0 : ℚ) < (10 : ℚ) ^ k := by positivity
    field_simp

/-- **Exact subtraction of an integer within the int64 window.** For a normalized
`x` with `0 ≤ x ≤ 2^63 - 1` and an integer value `0 ≤ k ≤ x` held in a
normalized `aN`, the `to_nearest` subtraction returns exactly `x - k`: the
difference is representable, so the correctly-rounded result equals it.
(`0 ≤ x` is implied by `0 ≤ k ≤ x`.) -/
lemma operator_sub_exact_int_le (x aN result : Number) (k : ℚ)
    (hx : x.isNormalized) (hxle : x.toRat ≤ 2 ^ 63 - 1)
    (haN : aN.isNormalized) (haN_val : aN.toRat = k)
    (hk_int : k.den = 1) (hknn : 0 ≤ k) (hkle : k ≤ x.toRat)
    (hok : x.operator_sub aN .to_nearest = .ok result) :
    result.toRat = x.toRat - k := by
  have hrtr := operator_sub_rounded_to_nearest x aN result hx haN hok
  rw [haN_val] at hrtr
  -- a representable witness for x - k closes the goal
  suffices hwit : ∃ w : Number, w.isNormalized ∧ w.toRat = x.toRat - k by
    obtain ⟨w, hw_norm, hw_val⟩ := hwit
    exact Number.RoundsToRepresentable.eq_of_representable result _ hrtr w hw_norm hw_val
  by_cases hk0 : k = 0
  · exact ⟨x, hx, by rw [hk0, sub_zero]⟩
  have hk1 : 1 ≤ k := by
    have hnum_pos : 0 < k.num := by
      rcases lt_trichotomy k.num 0 with h | h | h
      · exact absurd (Rat.num_nonneg.mpr hknn) (by omega)
      · exact absurd (Rat.zero_iff_num_zero.mpr h) hk0
      · exact h
    have : (1 : ℚ) ≤ (k.num : ℚ) := by exact_mod_cast hnum_pos
    calc (1 : ℚ) ≤ (k.num : ℚ) := this
      _ = k := by
        conv_rhs => rw [← Rat.num_div_den k]
        rw [hk_int]; push_cast; ring
  have hx_mne : x.mantissa_ ≠ 0 := by
    intro h0
    have hx0 : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx h0
    rw [hx0, Number.toRat_zero] at hkle
    linarith
  have hx_neg : x.negative_ = false := by
    by_contra hc
    have hc' : x.negative_ = true := by simpa using hc
    have := Number.toRat_of_neg x hc'
    have hmpos : 0 < (x.mantissa_.toNat : ℚ) := by
      have : 0 < x.mantissa_.toNat := by
        have := (hx.mantissaBounds_nat hx_mne).1; omega
      exact_mod_cast this
    nlinarith [zpow_pos (show (0:ℚ) < 10 from by norm_num) x.exponent_,
      le_trans hknn hkle]
  have hx_val : x.toRat = (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ x.exponent_ :=
    Number.toRat_of_nonneg x hx_neg
  obtain ⟨hmA_lo, hmA_hi⟩ := hx.mantissaBounds_nat hx_mne
  have hexp_range : minExponent ≤ x.exponent_ ∧ x.exponent_ ≤ maxExponent := by
    rcases hx with h_zero | ⟨_, _, _, hlo, hhi⟩
    · exact absurd (show x.mantissa_ = 0 by rw [h_zero]; rfl) hx_mne
    · exact ⟨hlo, hhi⟩
  set eA := x.exponent_ with heA_def
  have heA_le : eA ≤ 0 := by
    by_contra hc
    push Not at hc
    have h10 : (10 : ℚ) ^ (1 : ℤ) ≤ (10 : ℚ) ^ eA := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hm18 : ((10 : ℕ) ^ 18 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by exact_mod_cast hmA_lo
    rw [hx_val] at hxle
    push_cast at hm18
    nlinarith [hxle, h10, hm18]
  have heA_ge : (-18 : ℤ) ≤ eA := by
    by_contra hc
    push Not at hc
    have h10 : (10 : ℚ) ^ eA ≤ (10 : ℚ) ^ (-19 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hm19 : (x.mantissa_.toNat : ℚ) < ((10 : ℕ) ^ 19 : ℚ) := by exact_mod_cast hmA_hi
    have hxlt : x.toRat < 1 := by
      rw [hx_val]
      push_cast at hm19
      calc (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ eA
          < 10 ^ 19 * (10 : ℚ) ^ (-19 : ℤ) := by
            have hmnn : (0 : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by positivity
            have hppos : (0 : ℚ) < (10 : ℚ) ^ eA := zpow_pos (by norm_num) _
            nlinarith [h10, hm19, hppos]
        _ = 1 := by
            rw [show ((10 : ℚ) ^ 19 : ℚ) = (10 : ℚ) ^ (19 : ℤ) from by norm_num,
              ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
            norm_num
    linarith
  -- the integer k scaled onto x's grid
  set K : ℕ := k.num.toNat with hK_def
  have hK_val : (K : ℚ) = k := by
    rw [hK_def]
    have : (k.num.toNat : ℤ) = k.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hknn)
    have hq : ((k.num.toNat : ℤ) : ℚ) = (k.num : ℚ) := by exact_mod_cast this
    push_cast at hq ⊢
    rw [hq]
    conv_rhs => rw [← Rat.num_div_den k]
    rw [hk_int]; push_cast; ring
  set KK : ℕ := K * 10 ^ (-eA).toNat with hKK_def
  have hpow_eq : ((10 : ℚ) ^ (-eA).toNat) * (10 : ℚ) ^ eA = 1 := by
    rw [← zpow_natCast (10 : ℚ) (-eA).toNat, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    rw [show ((-eA).toNat : ℤ) + eA = 0 from by omega]
    norm_num
  have hKK_le : KK ≤ x.mantissa_.toNat := by
    have hcross : (KK : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by
      rw [hKK_def]
      push_cast
      have h1 : (K : ℚ) * ((10 : ℚ) ^ (-eA).toNat) * (10 : ℚ) ^ eA ≤
          (x.mantissa_.toNat : ℚ) * (10 : ℚ) ^ eA := by
        rw [mul_assoc, hpow_eq, mul_one, hK_val, ← hx_val]
        exact hkle
      have hppos : (0 : ℚ) < (10 : ℚ) ^ eA := zpow_pos (by norm_num) _
      exact le_of_mul_le_mul_right (by rw [mul_assoc] at h1 ⊢; exact h1) hppos
    exact_mod_cast hcross
  set J : ℕ := x.mantissa_.toNat - KK with hJ_def
  have hJ_val : (J : ℚ) * (10 : ℚ) ^ eA = x.toRat - k := by
    rw [hJ_def, hx_val]
    push_cast [Nat.cast_sub hKK_le]
    rw [hKK_def]
    push_cast
    rw [sub_mul, mul_assoc, hpow_eq, mul_one, hK_val]
  by_cases hJ0 : J = 0
  · refine ⟨Number.zero, Or.inl rfl, ?_⟩
    rw [Number.toRat_zero, ← hJ_val, hJ0]
    norm_num
  have hsticky : J ≤ maxRep.toNat ∨ J % 10 = 0 := by
    by_cases hJle : J ≤ maxRep.toNat
    · exact Or.inl hJle
    · right
      push Not at hJle
      have hmA_gt : maxRep.toNat < x.mantissa_.toNat := by
        have : J ≤ x.mantissa_.toNat := by rw [hJ_def]; omega
        omega
      have heA_neg : eA ≤ -1 := by
        by_contra hc
        push Not at hc
        have heA0 : eA = 0 := by omega
        have hxq : x.toRat = (x.mantissa_.toNat : ℚ) := by
          rw [hx_val, heA0]; norm_num
        rw [hxq] at hxle
        have hlt : (x.mantissa_.toNat : ℚ) < 2 ^ 63 := by linarith
        have : x.mantissa_.toNat < 2 ^ 63 := by exact_mod_cast hlt
        rw [maxRep_val] at hmA_gt
        omega
      have hmA_mod : x.mantissa_.toNat % 10 = 0 := by
        rcases hx with h_zero | ⟨_, _, hst, _, _⟩
        · exact absurd (show x.mantissa_ = 0 by rw [h_zero]; rfl) hx_mne
        · rcases hst with hst | hst
          · exact absurd (UInt64.le_iff_toNat_le.mp hst) (by omega)
          · exact hst
      have hKK_dvd : (10 : ℕ) ∣ KK := by
        rw [hKK_def]
        exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) K
      have hmA_dvd : (10 : ℕ) ∣ x.mantissa_.toNat := Nat.dvd_of_mod_eq_zero hmA_mod
      rw [hJ_def]
      obtain ⟨a, ha⟩ := hmA_dvd
      obtain ⟨b, hb⟩ := hKK_dvd
      rw [ha, hb]
      omega
  obtain ⟨w, hw_norm, _, hw_val⟩ := Number.exists_normalized_scaled J eA
    (by omega) (by rw [hJ_def]; omega) hsticky heA_ge heA_le
  exact ⟨w, hw_norm, by rw [hw_val, hJ_val]⟩

end XRPL.Model.Protocol
