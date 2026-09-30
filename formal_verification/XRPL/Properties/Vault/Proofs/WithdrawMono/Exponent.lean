import XRPL.Properties.Vault.Proofs.Support.NormalizeFacts

/-! # The exponent of a fractional `.to_nearest` `ofNumber`

For a positive normalized `n = m·10^k` the 16-digit pack has exponent `k+3`, or
`k+4` exactly when `m ≥ 9999999999999999500` (the carry). Hence the stored exponent
is at least `j+4` iff `n ≥ 9999999999999999500·10^j`. -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

/-- The 16-digit carry threshold at scale `j`. -/
def carryPt (j : ℤ) : ℚ := (9999999999999999500 : ℚ) * 10 ^ j

private lemma cusp_eq_tn (g : Guard) (neg : Bool) (e : Int) (loc : Error)
    (hb : (g.round .to_nearest == 1 || (g.round .to_nearest == 0 && cMaxValue % 2 == 1)) = true)
    (hexp_lo : minExponent ≤ e + 1) :
    g.doRoundUp neg cMaxValue e cMinValue cMaxValue .to_nearest loc
      = if maxExponent < e + 1 then (.error loc : Except Error RoundResult)
        else .ok { negative_ := neg, mantissa_ := cMinValue, exponent_ := e + 1 } := by
  have h9 : cMaxValue % 10 = 9 := by decide
  have hdiv : cMaxValue / 10 = 999999999999999 := by decide
  have hdivsucc : (999999999999999 : UInt64) + 1 = cMinValue := by decide
  have hdig9 : 9 * 2 ^ 60 ≤ (g.push 9).digits_.toNat := by
    rw [toNat_push_digits, show (9 : UInt64).toNat % 16 = 9 from by decide]; omega
  have hne0 : (g.push 9).digits_ ≠ 0 := by
    intro h
    have : (g.push 9).digits_.toNat = 0 := by rw [h]; rfl
    omega
  have hpush_ne : (g.push 9).empty = false := by unfold Guard.empty Guard.unrecoverable; simp [hne0]
  have hroundUp' : ((g.push 9).round .to_nearest == 1
      || ((g.push 9).round .to_nearest == 0 && (999999999999999 : UInt64) % 2 == 1)) = true := by
    have htn : (g.push 9).round .to_nearest = 1 := by
      unfold Guard.round
      rw [if_neg (by rw [hpush_ne]; exact Bool.false_ne_true),
          if_pos (show (g.push 9).digits_ > 0x5000000000000000 from by
            rw [gt_iff_lt, UInt64.lt_iff_toNat_lt,
                show (0x5000000000000000 : UInt64).toNat = 5764607523034234880 from by decide]
            omega)]
    rw [htn]; rfl
  unfold Guard.doRoundUp
  simp only []
  rw [pushOverflow_noop_of_lt_maxRep (by rw [maxRep_val, cMaxValue_val]; omega) g .to_nearest, hb]
  simp only [if_true]
  rw [if_neg (show ¬ (cMaxValue < cMaxValue ∧ cMaxValue < maxRep) from
        fun h => absurd (UInt64.lt_iff_toNat_lt.mp h.1) (by omega)),
      if_neg (show ¬ (maxRep < cMaxValue ∧ cMaxValue < maxRepUp) from fun h =>
        absurd (UInt64.lt_iff_toNat_lt.mp h.1) (by rw [maxRep_val, cMaxValue_val]; omega))]
  unfold Guard.doDropDigit
  rw [h9, hdiv]
  simp only []
  rw [if_pos hroundUp', hdivsucc,
      show Guard.bringIntoRange neg cMinValue (e + 1) cMinValue
          = { negative_ := neg, mantissa_ := cMinValue, exponent_ := e + 1 } from by
        rw [bringIntoRange_noscale_result
              (fun h => absurd (UInt64.lt_iff_toNat_lt.mp h.1) (by omega)),
            if_neg (not_or.mpr ⟨by omega, by decide⟩)]]

/-- The `.to_nearest` guard decision read off a dropped 3-digit tail `r/1000`. -/
private lemma guard_round_tn (g : Guard) (r : ℕ) (hr : r < 1000)
    (hg : represents g ((r : ℚ) / 1000)) :
    (g.round .to_nearest = 1 ↔ 500 < r) ∧ (g.round .to_nearest = 0 ↔ r = 500) := by
  by_cases he : g.empty
  · obtain ⟨hd, hx⟩ : g.digits_ = 0 ∧ g.xbit_ = false := by
      have hh : (g.digits_ == 0 && !g.xbit_) = true := he
      rw [Bool.and_eq_true] at hh; exact ⟨beq_iff_eq.mp hh.1, by simpa using hh.2⟩
    have hf0 : ((r : ℚ) / 1000) = 0 := represents_eq_zero_of_digits_zero_xbit_false hd hx hg
    have hr0 : r = 0 := by
      have : (r : ℚ) = 0 := by field_simp at hf0; exact_mod_cast hf0
      exact_mod_cast this
    have hround : g.round .to_nearest = -2 := by unfold Guard.round; rw [if_pos he]
    subst hr0
    constructor
    · rw [hround]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
    · rw [hround]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by omega)⟩
  · obtain ⟨h1, -, h0⟩ := round_correct he hg
    have hhalf : ((r : ℚ) / 1000 > 1 / 2) ↔ 500 < r := by
      rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num) (by norm_num)]
      constructor
      · intro h; have : (500 : ℚ) < (r : ℚ) := by linarith
        exact_mod_cast this
      · intro h; have : (500 : ℚ) < (r : ℚ) := by exact_mod_cast h
        linarith
    have heq : ((r : ℚ) / 1000 = 1 / 2) ↔ r = 500 := by
      rw [div_eq_div_iff (by norm_num) (by norm_num)]
      constructor
      · intro h; have : (r : ℚ) = 500 := by linarith
        exact_mod_cast this
      · intro h; subst h; norm_num
    exact ⟨h1.trans hhalf, h0.trans heq⟩

/-- **Exponent of the `.to_nearest` 16-digit pack.** `k+3`, or `k+4` exactly at the
carry `m ≥ 9999999999999999500`. -/
lemma ntr_tn_exp (n : Number) (mant : Int64) (exp : Int)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3)
    (hok : n.normalizeToRange cMinValue cMaxValue .to_nearest = .ok (mant, exp)) :
    ((exp = n.exponent_ + 3 ∧ n.mantissa_.toNat < 9999999999999999500) ∨
     (exp = n.exponent_ + 4 ∧ 9999999999999999500 ≤ n.mantissa_.toNat)) ∧
    (10 ^ 15 ≤ mant.toInt.natAbs ∧ mant.toInt.natAbs < 10 ^ 16) ∧
    (n.negative_ = false → 0 ≤ mant.toInt) ∧ exp ≤ maxExponent := by
  have he_hi := normalizeToRange_iou_exp_hi n .to_nearest mant exp h_lo h_hi hok
  obtain ⟨g, hrep, _hsbit, _h_empty_of, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ .to_nearest h_lo h_hi he_lo he_hi
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  have hsign : ∀ (X : UInt64), X.toNat < 2 ^ 63 →
      (if n.negative_ then -X.toInt64 else X.toInt64) = mant → n.negative_ = false →
        0 ≤ mant.toInt := by
    intro X hX heq hneg
    rw [← heq, hneg]
    simp only [Bool.false_eq_true, if_false]
    rw [UInt64.toInt64_toInt_of_lt _ hX]; positivity
  obtain ⟨hr1, hr0⟩ :=
    guard_round_tn g (n.mantissa_.toNat % 1000) (Nat.mod_lt _ (by omega)) hrep
  have hpar : ((n.mantissa_ / 10 / 10 / 10) % 2 == 1) = true ↔
      (n.mantissa_.toNat / 1000) % 2 = 1 := by
    have hmod : (n.mantissa_ / 10 / 10 / 10 % 2).toNat = (n.mantissa_.toNat / 1000) % 2 := by
      rw [UInt64.toNat_mod, hm3]; rfl
    rw [beq_iff_eq]
    constructor
    · intro h; rw [← hmod, h]; rfl
    · intro h
      refine UInt64.toNat_inj.mp ?_
      rw [hmod, h]; rfl
  have hcond : (g.round .to_nearest == 1
      || (g.round .to_nearest == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true
      ↔ (500 < n.mantissa_.toNat % 1000 ∨
          (n.mantissa_.toNat % 1000 = 500 ∧ (n.mantissa_.toNat / 1000) % 2 = 1)) := by
    rw [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    constructor
    · rintro (h | ⟨h, hp⟩)
      · exact Or.inl (hr1.mp h)
      · exact Or.inr ⟨hr0.mp h, hpar.mp hp⟩
    · rintro (h | ⟨h, hp⟩)
      · exact Or.inl (hr1.mpr h)
      · exact Or.inr ⟨hr0.mpr h, hpar.mpr hp⟩
  have hdm := Nat.div_add_mod n.mantissa_.toNat 1000
  by_cases hround : (g.round .to_nearest == 1
      || (g.round .to_nearest == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true
  · have hc := hcond.mp hround
    by_cases hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue
    · have hbr : (g.round .to_nearest == 1 ||
          (g.round .to_nearest == 0 && cMaxValue % 2 == 1)) = true := by
        rw [hcusp] at hround; exact hround
      have hcusp_eq := cusp_eq_tn g n.negative_ (n.exponent_ + 3) .normalize2 hbr (by omega)
      have hMk : n.mantissa_.toNat / 1000 = 10 ^ 16 - 1 := by
        have := congrArg UInt64.toNat hcusp; rw [hm3, hcMax] at this; exact this
      by_cases hovf : maxExponent < (n.exponent_ + 3) + 1
      · exfalso
        have h_err : n.normalizeToRange cMinValue cMaxValue .to_nearest = .error .normalize2 := by
          unfold Number.normalizeToRange
          rw [h_red, hcusp, hcusp_eq, if_pos hovf]
        rw [h_err] at hok; exact absurd hok (by simp)
      · have hcompute : n.normalizeToRange cMinValue cMaxValue .to_nearest
            = .ok (if n.negative_ then -cMinValue.toInt64 else cMinValue.toInt64,
                   (n.exponent_ + 3) + 1) := by
          unfold Number.normalizeToRange
          rw [h_red, hcusp, hcusp_eq, if_neg hovf]
          rfl
        rw [hcompute] at hok
        obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
        refine ⟨Or.inr ⟨by omega, by omega⟩, ⟨?_, ?_⟩, hsign cMinValue (by rw [hcMin]; omega) hmant,
          by omega⟩
        · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hcMin]; omega), hcMin]
        · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hcMin]; omega), hcMin]
          omega
    · have hlt : (n.mantissa_ / 10 / 10 / 10).toNat < cMaxValue.toNat := by
        have hne : (n.mantissa_ / 10 / 10 / 10).toNat ≠ cMaxValue.toNat :=
          fun h => hcusp (UInt64.toNat_inj.mp h)
        rw [hcMax, hm3] at hne ⊢; omega
      have hadd : (n.mantissa_ / 10 / 10 / 10 + 1).toNat = n.mantissa_.toNat / 1000 + 1 := by
        rw [UInt64.toNat_add, hm3, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      have hcompute : n.normalizeToRange cMinValue cMaxValue .to_nearest
          = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10 + 1).toInt64
                 else (n.mantissa_ / 10 / 10 / 10 + 1).toInt64, n.exponent_ + 3) := by
        unfold Number.normalizeToRange
        rw [h_red, doRoundUp_small_fire g n.negative_ _ (n.exponent_ + 3) .to_nearest
          .normalize2 hround (by rw [hcMin, hm3]; omega) hlt (by omega) (by omega)]
        rfl
      rw [hcompute] at hok
      obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
      rw [hcMax, hm3] at hlt
      refine ⟨Or.inl ⟨by omega, by omega⟩, ⟨?_, ?_⟩, hsign _ (by rw [hadd]; omega) hmant,
        by omega⟩
      · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hadd]; omega), hadd]
        omega
      · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hadd]; omega), hadd]
        omega
  · have hnc : ¬ (500 < n.mantissa_.toNat % 1000 ∨
        (n.mantissa_.toNat % 1000 = 500 ∧ (n.mantissa_.toNat / 1000) % 2 = 1)) :=
      fun h => hround (hcond.mpr h)
    have hcompute : n.normalizeToRange cMinValue cMaxValue .to_nearest
        = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64
               else (n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
      unfold Number.normalizeToRange
      rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) .to_nearest
        .normalize2 (by simpa using hround) (by rw [hcMin, hm3]; omega)
        (by rw [hcMax, hm3]; omega) (by omega) (by omega)]
      rfl
    rw [hcompute] at hok
    obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
    refine ⟨Or.inl ⟨by omega, by omega⟩, ⟨?_, ?_⟩, hsign _ (by rw [hm3]; omega) hmant, by omega⟩
    · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hm3]; omega), hm3]
      omega
    · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hm3]; omega), hm3]
      omega

/-- A zero fractional `checked` on a 16-digit mantissa comes from an underflowing
exponent and is stored with offset `-100`. -/
lemma checked_frac_zero (mant : UInt64) (exp : Int) (neg : Bool) (mode : rounding_mode)
    (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16)
    (he_lo : minExponent + 3 ≤ exp) (he_hi : exp ≤ maxExponent)
    (result : STAmount)
    (hok : STAmount.checked .fractional mant exp neg mode = .ok result)
    (hz : result.mValue = 0) :
    exp < -96 ∧ result.mOffset = -100 := by
  have h_fit : mant.toNat < 2 ^ 63 := by omega
  have h_int : ¬ (STAmount.unchecked .fractional mant exp neg).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_sd : (STAmount.unchecked .fractional mant exp neg).signedDrops.toInt64
      = if neg then -mant.toInt64 else mant.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant exp neg).mValue.toNat < 10 ^ 16 from h_hi),
        signed_mantissa_toInt neg mant h_fit]
    show (STAmount.unchecked .fractional mant exp neg).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    rcases neg <;> simp
  have hiou : (STAmount.unchecked .fractional mant exp neg).iou mode
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if neg then -mant.toInt64 else mant.toInt64, exp⟩) := by
    unfold STAmount.iou
    rw [if_neg h_int]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant exp neg mode h_lo h_hi he_lo he_hi
  by_cases hhi : exp > cMaxOffset
  · exfalso
    have hb : STAmount.checked .fractional mant exp neg mode = .error .overflow := by
      rw [STAmount.checked]; unfold STAmount.canonicalize
      rw [if_neg h_int, hiou, if_pos hhi]
    rw [hb] at hok; simp at hok
  · by_cases hlo : exp < cMinOffset
    · refine ⟨by unfold cMinOffset at hlo; exact hlo, ?_⟩
      rw [STAmount.checked] at hok
      unfold STAmount.canonicalize at hok
      rw [if_neg h_int, hiou, if_neg hhi, if_pos hlo] at hok
      simp only [] at hok
      rw [← Except.ok.inj hok]
      rfl
    · exfalso
      have hc : (⟨.fractional, mant, exp, neg⟩ : STAmount).IOUCanonical :=
        ⟨rfl, h_lo, h_hi, by show (-96 : ℤ) ≤ exp; unfold cMinOffset at hlo; omega,
          by show exp ≤ 80; unfold cMaxOffset at hhi; omega⟩
      have hcid := STAmount.canonicalize_canonical_id ⟨.fractional, mant, exp, neg⟩ mode hc
      rw [STAmount.checked,
          show STAmount.unchecked .fractional mant exp neg
            = (⟨.fractional, mant, exp, neg⟩ : STAmount) from rfl, hcid] at hok
      have hres : result = ⟨.fractional, mant, exp, neg⟩ := (Except.ok.inj hok).symm
      rw [hres] at hz
      simp only [] at hz
      rw [hz] at h_lo
      simp at h_lo

/-- **Exponent of a positive fractional `.to_nearest` `ofNumber`.** The pack
exponent `exp` is `k+3` or (at the carry) `k+4`; the result is zero with offset
`-100` iff `exp` underflows, and otherwise has offset `exp`. -/
lemma ofNumber_frac_tn_exp (n : Number) (r : STAmount) (hn : n.isNormalized)
    (hneg : n.negative_ = false) (hnz : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok r) :
    ∃ exp : ℤ,
      ((exp = n.exponent_ + 3 ∧ n.mantissa_.toNat < 9999999999999999500) ∨
       (exp = n.exponent_ + 4 ∧ 9999999999999999500 ≤ n.mantissa_.toNat)) ∧
      ((exp < -96 ∧ r.mValue = 0 ∧ r.exponent = -100) ∨
       (-96 ≤ exp ∧ r.mValue ≠ 0 ∧ r.exponent = exp)) := by
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnz
    · exact hlo
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true))] at hok
  rw [hneg_dec] at hok
  simp only [Bool.false_eq_true, if_false] at hok
  cases hnorm : n.normalizeToRange kMinValue kMaxValue .to_nearest with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : n.normalizeToRange cMinValue cMaxValue .to_nearest = .ok (mant, exp) := hnorm
    obtain ⟨hexp, ⟨hmlo, hmhi⟩, hsgn, hexp_le⟩ :=
      ntr_tn_exp n mant exp hr_lo hr_hi (by omega) hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn hneg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by rw [← hmant_natAbs]; exact hmlo
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by rw [← hmant_natAbs]; exact hmhi
    have hexp_lo3 : minExponent + 3 ≤ exp := by rcases hexp with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    refine ⟨exp, hexp, ?_⟩
    by_cases hz : r.mValue = 0
    · obtain ⟨hlt, hoff⟩ := checked_frac_zero mant.toUInt64 exp false .to_nearest hmtu_lo hmtu_hi
        hexp_lo3 hexp_le r hok hz
      exact Or.inl ⟨hlt, hz, hoff⟩
    · obtain ⟨hlo96, _, hres⟩ := STAmount.checked_iou_cases .fractional mant.toUInt64 exp false
        .to_nearest rfl hmtu_lo hmtu_hi hexp_lo3 hexp_le r hok hz
      exact Or.inr ⟨hlo96, hz, by rw [hres]; rfl⟩

private lemma zero_ofNumber_frac (r : STAmount)
    (hok : STAmount.ofNumber .fractional Number.zero .to_nearest = .ok r) : r.exponent = -100 := by
  have h : STAmount.ofNumber .fractional Number.zero .to_nearest
      = .ok ⟨.fractional, 0, -100, false⟩ := by rfl
  rw [h] at hok
  rw [← Except.ok.inj hok]; rfl

/-- **Exponent threshold.** For a non-negative normalized `n`, the stored exponent of
its fractional `.to_nearest` pack reaches `j+4` (with `j ≥ -100`) iff
`n ≥ carryPt j`. -/
lemma exp_ge_iff (n : Number) (r : STAmount) (hn : n.isNormalized) (hnn : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok r) (j : ℤ) (hj : -100 ≤ j) :
    j + 4 ≤ r.exponent ↔ carryPt j ≤ n.toRat := by
  have hj0 : (0 : ℚ) < 10 ^ j := zpow_pos (by norm_num) _
  by_cases hnz : n.mantissa_ = 0
  · have hn0 : n = Number.zero := by
      rcases hn with h0 | ⟨hlo, _⟩
      · exact h0
      · exfalso; rw [hnz] at hlo; exact absurd hlo (by decide)
    subst hn0
    rw [zero_ofNumber_frac r hok, Number.toRat_zero, carryPt]
    constructor
    · intro h; omega
    · intro h; nlinarith
  have hpos : 0 < n.toRat :=
    lt_of_le_of_ne hnn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero n hnz))
  have hneg : n.negative_ = false := by
    by_contra h
    have := Number.toRat_nonpos_of_negative n (by simpa using h)
    linarith
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  obtain ⟨exp, hexp, hres⟩ := ofNumber_frac_tn_exp n r hn hneg hnz hok
  have hv : n.toRat = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ := Number.toRat_of_nonneg n hneg
  set k := n.exponent_ with hk
  set m := n.mantissa_.toNat with hm
  have hmq_lo : (10 : ℚ) ^ 18 ≤ (m : ℚ) := by exact_mod_cast hr_lo
  have hmq_hi : (m : ℚ) < 10 ^ 19 := by exact_mod_cast hr_hi
  have hk0 : (0 : ℚ) < 10 ^ k := zpow_pos (by norm_num) _
  -- `10^k` against `10^j`
  have hpow : ∀ d : ℤ, (10 : ℚ) ^ (j + d) = 10 ^ j * 10 ^ d := fun d => zpow_add₀ (by norm_num) _ _
  rw [carryPt, hv]
  constructor
  · intro hge
    have hexp_ge : j + 4 ≤ exp := by
      rcases hres with ⟨_, _, he⟩ | ⟨_, _, he⟩
      · omega
      · omega
    rcases hexp with ⟨he, _⟩ | ⟨he, hC⟩
    · -- `k ≥ j+1`
      have hk1 : (10 : ℚ) ^ (j + 1) ≤ 10 ^ k := zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [hpow, zpow_one] at hk1
      nlinarith
    · have hkj : (10 : ℚ) ^ j ≤ 10 ^ k := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hCq : (9999999999999999500 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hC
      nlinarith
  · intro hle
    -- `k ≥ j`
    have hkj : j ≤ k := by
      by_contra hlt
      push_neg at hlt
      have h1 : (10 : ℚ) ^ (k + 1) ≤ 10 ^ j := zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add₀ (by norm_num), zpow_one] at h1
      nlinarith
    have hexp_ge : j + 4 ≤ exp := by
      rcases eq_or_lt_of_le hkj with heq | hlt
      · rcases hexp with ⟨_, hmC⟩ | ⟨he, _⟩
        · exfalso
          rw [← heq] at hle
          have hmCq : (m : ℚ) < 9999999999999999500 := by exact_mod_cast hmC
          nlinarith
        · omega
      · rcases hexp with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    rcases hres with ⟨hlt, _, _⟩ | ⟨_, _, he⟩
    · omega
    · omega

/-- The stored exponent of a non-negative fractional pack is `-100` (zero) or in
`[-96, 80]`. -/
lemma exp_cases (n : Number) (r : STAmount)
    (hok : STAmount.ofNumber .fractional n .to_nearest = .ok r) :
    r.exponent = -100 ∨ ((-96 : ℤ) ≤ r.exponent ∧ r.exponent ≤ 80) := by
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ NumericType.fractional.isIntegral = true)] at hok
  cases hnr : (if decide (n.signum < 0) = true then n.operator_neg else n).normalizeToRange
      kMinValue kMaxValue .to_nearest with
  | error e => rw [hnr] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨m', e'⟩ := me
    rw [hnr] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    have hint : ¬ (STAmount.unchecked .fractional m'.toUInt64 e' (decide (n.signum < 0))).integral
        = true := by simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
    unfold STAmount.canonicalize at hok
    rw [if_neg hint] at hok
    unfold STAmount.iou at hok
    rw [if_neg hint] at hok
    cases hone : IOUAmount.ofMantissaExp
        (STAmount.unchecked .fractional m'.toUInt64 e' (decide (n.signum < 0))).signedDrops.toInt64
        (STAmount.unchecked .fractional m'.toUInt64 e' (decide (n.signum < 0))).mOffset
        .to_nearest with
    | error e => rw [hone] at hok; exact absurd hok (by simp)
    | ok i =>
      rw [hone] at hok
      simp only [] at hok
      have hres : r.mOffset = i.exponent_ := by rw [← Except.ok.inj hok]
      show r.mOffset = -100 ∨ ((-96 : ℤ) ≤ r.mOffset ∧ r.mOffset ≤ 80)
      rw [hres]
      exact IOUAmount.ofMantissaExp_exponent_cases _ _ _ i hone

end XRPL.Model.SingleAssetVault.WdMono
