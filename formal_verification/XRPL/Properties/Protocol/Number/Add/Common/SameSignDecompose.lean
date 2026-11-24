import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Add.Common.Decompose
import XRPL.Properties.Protocol.Number.Common.Helpers
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128Facts
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128Nearest
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap


namespace XRPL.Model.Protocol

/-- The state of a same-sign addition before its final rounding: the sum `|truth|` is `(zm + f)·10^ze'`, the guard `g`
holds a fraction that is positive exactly when `f` is, and rounding `zm` with it gives `result`. -/
structure PostAlignSpec (truth : ℚ) (xn : Bool) (result : Number) (mode : rounding_mode)
    (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult) : Prop where
  zm_ge_floor : mantissaFloor ≤ zm.toNat
  zm_le_maxRepUp : zm.toNat ≤ maxRepUp.toNat
  f_nonneg : 0 ≤ f
  f_lt_one : f < 1
  floor_cusp : zm.toNat = mantissaFloor → (8 : ℚ) / 10 ≤ f
  value_eq : |truth| = ((zm.toNat : ℚ) + f) * 10 ^ ze'
  rounds : g.doRoundUp false zm ze' largeRange.min largeRange.max mode
    .overflow = .ok res_pos
  result_abs : |result.toRat| = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_
  res_mant_ne : res_pos.mantissa_ ≠ 0
  represents_t : ∃ ft : ℚ, represents g ft ∧ (0 < ft → 0 < f) ∧ (ft = 0 → f = 0)
  result_neg : result.negative_ = xn
  sbit : g.sbit_ = xn
  zm_succ : mantissaFloorSucc ≤ zm.toNat
  result_norm : result.isNormalized
  truth_top : |truth| < 10 ^ 19 * (10 : ℚ) ^ ze'
  result_mant_ne : result.mantissa_ ≠ 0

/-- A guard asking for a downward round-up holds a positive fraction, so the exact fraction is positive. -/
lemma represents_t_pos_of_shouldRoundUp_downward {g : Guard} {f : ℚ}
    (h : ∃ ft : ℚ, represents g ft ∧ (0 < ft → 0 < f) ∧ (ft = 0 → f = 0)) (hs : g.shouldRoundUp_downward) :
    0 < f := by
  obtain ⟨ft, hr, hp, -⟩ := h
  exact hp (represents_pos_of_shouldRoundUp_downward g ft hr hs)

/-- A guard asking for an upward round-up holds a positive fraction, so the exact fraction is positive. -/
lemma represents_t_pos_of_shouldRoundUp_upward {g : Guard} {f : ℚ}
    (h : ∃ ft : ℚ, represents g ft ∧ (0 < ft → 0 < f) ∧ (ft = 0 → f = 0)) (hs : g.shouldRoundUp_upward) :
    0 < f := by
  obtain ⟨ft, hr, hp, -⟩ := h
  exact hp (represents_pos_of_shouldRoundUp_upward g ft hr hs)

/-- A guard with no digits and no sticky bit holds nothing, so the exact fraction is zero. -/
lemma represents_t_eq_zero_of_digits_zero_xbit_false {g : Guard} {f : ℚ} (hd : g.digits_ = 0)
    (hx : g.xbit_ = false) (h : ∃ ft : ℚ, represents g ft ∧ (0 < ft → 0 < f) ∧ (ft = 0 → f = 0)) : f = 0 := by
  obtain ⟨ft, hr, -, hz⟩ := h
  exact hz (represents_eq_zero_of_digits_zero_xbit_false hd hx hr)

/-- A bind succeeds exactly when its first step does and the rest succeeds on that value. -/
private lemma bind_eq_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {r : β} :
    (x >>= f) = .ok r ↔ ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x <;> simp [bind, Except.bind]

/-- The location of `doRoundUp` only names the error, so a successful rounding is the same with any location. -/
lemma Guard.doRoundUp_ok_location {g : Guard} {negative : Bool} {m : UInt64} {e : Int} {minM maxM : UInt64}
    {mode : rounding_mode} {l₁ l₂ : Error} {r : RoundResult}
    (h : g.doRoundUp negative m e minM maxM mode l₁ = .ok r) :
    g.doRoundUp negative m e minM maxM mode l₂ = .ok r := by
  unfold Guard.doRoundUp at h ⊢
  obtain ⟨g', hp, h2⟩ := bind_eq_ok_iff.mp h
  refine bind_eq_ok_iff.mpr ⟨g', hp, ?_⟩
  dsimp only at h2 ⊢
  obtain ⟨res, hc, hf⟩ := bind_eq_ok_iff.mp h2
  refine bind_eq_ok_iff.mpr ⟨res, hc, ?_⟩
  split at hf
  · cases hf
  · rw [ite_eq_right (by assumption)]; exact hf

/-- A guard that is not empty holds a positive fraction. -/
lemma represents_pos_of_not_empty {g : Guard} {f : ℚ} (hrep : represents g f) (hne : g.empty = false) : 0 < f := by
  obtain ⟨x, hx_nn, _, hf_eq, hxbit_iff, _⟩ := hrep
  have hdv_nn : (0 : ℚ) ≤ (decimalValue g.digits_ : ℚ) / 10 ^ 16 := by positivity
  by_cases hd : g.digits_ = 0
  · have hxb : g.xbit_ = true := by
      unfold Guard.empty Guard.unrecoverable at hne
      rw [hd] at hne
      cases hx : g.xbit_
      · rw [hx] at hne; exact absurd hne (by decide)
      · rfl
    have hx_pos : x > 0 := hxbit_iff.mp hxb
    rw [hf_eq]; linarith
  · have hdv_pos : 0 < decimalValue g.digits_ := decimalValue_pos_of_ne_zero g.digits_ hd
    have hdv_q : (0 : ℚ) < (decimalValue g.digits_ : ℚ) / 10 ^ 16 := by
      apply div_pos _ (by positivity)
      exact_mod_cast hdv_pos
    rw [hf_eq]; linarith

/-- A same-sign addition is `doNormalize128` on `M` of at least 19 digits with `|x + y| = (M + δ)·10^ze'`, `δ` in
`[0, 1)`, and a sticky tail only with `M` of at least 22 digits. -/
theorem Number.operator_addSpec_same_sign_sum
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_same_sign : x.negative_ = y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg) :
    ∃ (M : UInt128) (ze' : Int) (δ : ℚ) (sticky : Bool),
      0 ≤ δ ∧ δ < 1 ∧ (sticky = false → δ = 0) ∧ (sticky = true → 0 < δ) ∧
      10 ^ 18 ≤ M.toNat ∧ M.toNat < 10 ^ 23 ∧ (sticky = true → 10 ^ 21 ≤ M.toNat) ∧
      |x.toRat + y.toRat| = ((M.toNat : ℚ) + δ) * 10 ^ ze' ∧ minExponent ≤ ze' ∧ ze' ≤ maxExponent ∧
      x.operator_addSpec y mode = doNormalize128 x.negative_ M ze' largeRange.min largeRange.max mode sticky := by
  have hy0 : ¬ y.operator_eq Number.zero = true := by
    simp [Number.operator_eq, Number.zero, hy_mant_ne]
  have hx0 : ¬ x.operator_eq Number.zero = true := by
    simp [Number.operator_eq, Number.zero, hx_mant_ne]
  generalize ha : Number.addAlignSpec x y = a
  obtain ⟨xa, ya, E, g⟩ := a
  obtain ⟨f, hrep, hEmin, hEmax, hxa, hya, hlt, hgt, heq⟩ :=
    Number.addAlignSpec_facts x y hx hy hx_mant_ne hy_mant_ne xa ya E g ha
  have hspec : x.operator_addSpec y mode =
      doNormalize128 x.negative_ (xa + ya) E largeRange.min largeRange.max mode (!g.empty) := by
    unfold Number.operator_addSpec
    rw [ite_eq_right hy0, ite_eq_right hx0, ite_eq_right h_not_zero]
    dsimp only
    rw [ha, show (x.negative_ == y.negative_) = true from by rw [h_same_sign]; exact beq_self_eq_true _,
      ite_eq_left rfl]
  have hsum : (xa + ya).toNat = xa.toNat + ya.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have habs := abs_add_eq_of_same_sign h_same_sign
  have hf0 : 0 ≤ f := represents_nonneg hrep
  have hf1 : f < 1 := represents_lt_one hrep
  refine ⟨xa + ya, E, f, !g.empty, hf0, hf1, fun h => represents_empty_eq_zero (by simpa using h) hrep,
    fun h => represents_pos_of_not_empty hrep (by simpa using h), ?_, by rw [hsum]; omega, ?_, ?_, hEmin, hEmax,
    hspec⟩
  · rw [hsum]
    rcases lt_trichotomy x.exponent_ y.exponent_ with h | h | h
    · have := (hlt h).2.2.2.1; omega
    · have := (heq h).2.2.2.2.1; omega
    · have := (hgt h).2.2.2.1; omega
  · intro hst
    have hne : g.empty = false := by simpa using hst
    rw [hsum]
    rcases lt_trichotomy x.exponent_ y.exponent_ with h | h | h
    · have := (hlt h).2.2.2.2 hne; omega
    · rw [(heq h).2.1] at hne; exact absurd hne (by decide)
    · have := (hgt h).2.2.2.2 hne; omega
  · rw [habs, hsum]
    push_cast
    rcases lt_trichotomy x.exponent_ y.exponent_ with h | h | h
    · rw [(hlt h).1, (hlt h).2.1]; ring
    · obtain ⟨rfl, -, hxv, hyv, -⟩ := heq h
      rw [hxv, hyv]; ring
    · rw [(hgt h).1, (hgt h).2.1]; ring

/-- A successful same-sign addition: `Number.operator_addSpec_same_sign_sum` with the result of the normalization. -/
theorem Number.operator_add_algorithmic_facts_same_sign_represents
    (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_same_sign : x.negative_ = y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y mode = .ok result) :
    ∃ (M : UInt128) (ze' : Int) (δ : ℚ) (sticky : Bool),
      0 ≤ δ ∧ δ < 1 ∧ (sticky = false → δ = 0) ∧ (sticky = true → 0 < δ) ∧
      10 ^ 18 ≤ M.toNat ∧ M.toNat < 10 ^ 23 ∧ (sticky = true → 10 ^ 21 ≤ M.toNat) ∧
      |x.toRat + y.toRat| = ((M.toNat : ℚ) + δ) * 10 ^ ze' ∧ minExponent ≤ ze' ∧ ze' ≤ maxExponent ∧
      doNormalize128 x.negative_ M ze' largeRange.min largeRange.max mode sticky = .ok result := by
  rw [Number.operator_add_eq_spec mode hx hy] at hok
  obtain ⟨M, ze', δ, sticky, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hspec⟩ :=
    Number.operator_addSpec_same_sign_sum x y mode hx hy hx_mant_ne hy_mant_ne h_same_sign h_not_zero
  exact ⟨M, ze', δ, sticky, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hspec ▸ hok⟩

/-- What the same-sign normalization needs: a sticky tail is small against `M`, and a mantissa of 19 digits at an
exponent in range never rounds to zero. -/
private lemma sameSign_normalize_inputs (zn : Bool) (M : UInt128) (ze0 : Int) (δ : ℚ) (sticky : Bool)
    (mode : rounding_mode) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hs0 : sticky = false → δ = 0) (hM18 : 10 ^ 18 ≤ M.toNat)
    (hM23 : M.toNat < 10 ^ 23) (hM21 : sticky = true → 10 ^ 21 ≤ M.toNat) (hEmin : minExponent ≤ ze0)
    (result : Number) (hok128 : doNormalize128 zn M ze0 largeRange.min largeRange.max mode sticky = .ok result) :
    (sticky = true → δ * 10 ^ 20 ≤ (M.toNat : ℚ)) ∧ result.mantissa_ ≠ 0 := by
  have hδM : sticky = true → δ * 10 ^ 20 ≤ (M.toNat : ℚ) := by
    intro hst
    have h21 : ((10 : ℕ) ^ 21 : ℚ) ≤ (M.toNat : ℚ) := by exact_mod_cast hM21 hst
    push_cast at h21
    nlinarith
  refine ⟨hδM, fun h0 => ?_⟩
  have hsmall := doNormalize128_underflow_value_small zn M ze0 δ sticky mode hδ0 hδ1 hs0
    (by omega) hM23 hδM result hok128 h0
  have h18 : ((10 : ℕ) ^ 18 : ℚ) ≤ (M.toNat : ℚ) := by exact_mod_cast hM18
  have hpow : (10 : ℚ) ^ (minExponent : ℤ) ≤ 10 ^ ze0 := zpow_le_zpow_right₀ (by norm_num) hEmin
  push_cast at h18
  have : (10 : ℚ) ^ (18 : ℕ) * 10 ^ (minExponent : ℤ) ≤ ((M.toNat : ℚ) + δ) * 10 ^ ze0 :=
    mul_le_mul (by linarith) hpow (by positivity) (by positivity)
  linarith

/-- `to_nearest` same-sign addition before its final rounding, with a guard that rounds like the exact fraction. -/
theorem Number.operator_add_same_sign_nearest_facts (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_same_sign : x.negative_ = y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .to_nearest = .ok result) :
    ∃ (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult),
      mantissaFloorSucc ≤ zm.toNat ∧ zm.toNat ≤ maxRepUp.toNat ∧ 0 ≤ f ∧ f < 1 ∧
      |x.toRat + y.toRat| = ((zm.toNat : ℚ) + f) * 10 ^ ze' ∧
      g.doRoundUp false zm ze' largeRange.min largeRange.max .to_nearest .normalize2 = .ok res_pos ∧
      |result.toRat| = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ ∧
      res_pos.mantissa_ ≠ 0 ∧ result.negative_ = x.negative_ ∧ g.RoundsLike f := by
  obtain ⟨M, ze0, δ, sticky, hδ0, hδ1, hs0, hs1, hM18, hM23, hM21, htruth, hEmin, -, hok128⟩ :=
    Number.operator_add_algorithmic_facts_same_sign_represents x y result .to_nearest hx hy hx_mant_ne hy_mant_ne
      h_same_sign h_not_zero hok
  obtain ⟨hδM, hres⟩ := sameSign_normalize_inputs x.negative_ M ze0 δ sticky .to_nearest hδ0 hδ1 hs0 hM18 hM23
    hM21 hEmin result hok128
  obtain ⟨zm, ze', f, g, res_pos, hsucc, hle, hf0, hf1, hval, hru, habs, hne, hneg, hrl⟩ :=
    doNormalize128_nearest_facts x.negative_ M ze0 δ sticky hδ0 hδ1 hs0 hs1 (by omega) hM23 hδM result hok128 hres
  exact ⟨zm, ze', f, g, res_pos, hsucc, hle, hf0, hf1, htruth.trans hval, hru, habs, hne, hneg, hrl⟩

/-- The same-sign facts in the form the rounding proofs use: the state before the final rounding. -/
theorem Number.operator_add_algorithmic_facts_same_sign_anyMode (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (h_same_sign : x.negative_ = y.negative_)
    (h_not_zero : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y mode = .ok result) :
    ∃ (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult),
      PostAlignSpec (x.toRat + y.toRat) x.negative_ result mode zm ze' f g res_pos := by
  obtain ⟨M, ze0, δ, sticky, hδ0, hδ1, hs0, hs1, hM18, hM23, hM21, htruth, hEmin, -, hok128⟩ :=
    Number.operator_add_algorithmic_facts_same_sign_represents x y result mode hx hy hx_mant_ne hy_mant_ne
      h_same_sign h_not_zero hok
  obtain ⟨hδM, hres⟩ := sameSign_normalize_inputs x.negative_ M ze0 δ sticky mode hδ0 hδ1 hs0 hM18 hM23 hM21
    hEmin result hok128
  obtain ⟨zm, ze', f, g, res_pos, ftilde, hzm_ge, hzm_le, hf_nn, hf_lt, h_value, h_rup, h_result_abs,
      hres_pos_ne, h_neg, h_sbit, hzm_succ, hrep_t, h_pos, h_zero⟩ :=
    doNormalize128_algorithmic_facts x.negative_ M ze0 δ sticky mode hδ0 hδ1 hs0 hs1 (by omega) hM23 hδM
      result hok128 hres
  have hfloor : mantissaFloor < mantissaFloorSucc := by decide
  refine ⟨zm, ze', f, g, res_pos, ⟨hzm_ge, hzm_le, hf_nn, hf_lt, fun h => absurd h (by omega),
    htruth.trans h_value, Guard.doRoundUp_ok_location h_rup, h_result_abs, hres_pos_ne,
    ⟨ftilde, hrep_t, h_pos, h_zero⟩, h_neg, h_sbit, hzm_succ,
    doNormalize128_result_isNormalized x.negative_ M ze0 sticky mode (by omega) result hok128 hres, ?_, hres⟩⟩
  rw [htruth.trans h_value]
  have hup : (maxRepUp.toNat : ℚ) + 1 ≤ 10 ^ 19 := by
    rw [show maxRepUp.toNat = 2 ^ 63 + 2 from by decide]; norm_num
  have hzq : (zm.toNat : ℚ) ≤ maxRepUp.toNat := by exact_mod_cast hzm_le
  exact mul_lt_mul_of_pos_right (by linarith) (zpow_pos (by norm_num) _)

end XRPL.Model.Protocol
