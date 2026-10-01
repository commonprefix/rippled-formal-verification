import XRPL.Properties.Protocol.Common.AmountArith
import XRPL.Properties.Vault.Proofs.Support.NumberFacts

/-! # Normalization facts

Facts about `Number` normalization: `doNormalize`, `normalizeToRange`, the guard, and
`IOUAmount.normalize`. -/

namespace XRPL.Model.Protocol

/-- **Forward totality of `operator_sub` for two normalized capped operands.** Both
stored-total decrements of the withdraw run, `assetsTotal - payout` and
`sharesTotal - sharesBurned`, share this shape: the cap bounds both exponents by `0`, which
leaves the headroom `Number.operator_sub_ok_of_normalized_exp` needs. No ordering (`y ≤ x`) is
needed for totality. -/
lemma Number.operator_sub_ok_of_normalized_cap (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxneg : x.negative_ = false) (hyneg : y.negative_ = false)
    (hxcap : x.toRat ≤ 2 ^ 63 - 1) (hycap : y.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, x.operator_sub y mode = .ok result := by
  have hxe := Number.exponent_fn_le_zero_of_cap x hx hxneg hxcap
  have hye := Number.exponent_fn_le_zero_of_cap y hy hyneg hycap
  unfold Number.exponent at hxe hye
  apply Number.operator_sub_ok_of_normalized_exp x y mode hx hy hxneg hyneg <;>
    unfold maxExponent <;> split at * <;> omega

/-- A `.ok` `normalizeToRange` implies the underlying `doNormalize` succeeded. -/
lemma normalizeToRange_ok_doNormalize_ok (n : Number) (minM maxM : UInt64) (mode : rounding_mode)
    (mant : Int64) (exp : Int)
    (hok : n.normalizeToRange minM maxM mode = .ok (mant, exp)) :
    ∃ res : Number, doNormalize n.negative_ n.mantissa_ n.exponent_ minM maxM mode = .ok res := by
  unfold Number.normalizeToRange at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i res hd; exact ⟨res, hd⟩

/-- One erroring step of `doNormalize_scaleDown`: when the mantissa is still above
`maxMant` and the exponent has reached `maxExponent`, the loop aborts. -/
lemma doNormalize_scaleDown_step_error {maxMant M : UInt64} {e : Int} {g : Guard}
    (hgt : maxMant < M) (he : maxExponent ≤ e) :
    doNormalize_scaleDown maxMant M e g = .error .normalize1 := by
  conv_lhs => unfold doNormalize_scaleDown
  rw [dif_pos hgt, if_pos he]

/-- A 19-digit mantissa needs three `scaleDown` steps to reach the 16-digit range;
if the exponent is within two of `maxExponent` at entry, one of those three
`maxExponent` guards fires and the loop errors. -/
lemma doNormalize_scaleDown_errors_of_ge (M : UInt64) (e : Int) (g : Guard)
    (hM_lo : 10 ^ 18 ≤ M.toNat) (hM_hi : M.toNat < 10 ^ 19)
    (he : maxExponent ≤ e + 2) :
    doNormalize_scaleDown cMaxValue M e g = .error .normalize1 := by
  have h10 : (10 : UInt64).toNat = 10 := uint64_ten_toNat
  have hm1 : (M / 10).toNat = M.toNat / 10 := by rw [UInt64.toNat_div, h10]
  have hm2 : (M / 10 / 10).toNat = M.toNat / 100 := by
    rw [UInt64.toNat_div, hm1, h10, Nat.div_div_eq_div_mul]
  by_cases hc0 : maxExponent ≤ e
  · exact doNormalize_scaleDown_step_error
      (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val]; omega) hc0
  · have hc0' : e < maxExponent := by omega
    rw [doNormalize_scaleDown_step
          (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val]; omega) hc0']
    by_cases hc1 : maxExponent ≤ e + 1
    · exact doNormalize_scaleDown_step_error
        (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val, hm1]; omega) hc1
    · have hc1' : e + 1 < maxExponent := by omega
      rw [doNormalize_scaleDown_step
            (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val, hm1]; omega) hc1']
      exact doNormalize_scaleDown_step_error
        (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val, hm2]; omega) (by omega)

/-- **Success of the 16-digit `doNormalize` bounds the source exponent.** A `.ok`
result of `doNormalize _ M _ cMinValue cMaxValue _` on a 19-digit mantissa forces
`e + 3 ≤ maxExponent` (otherwise the `scaleDown` loop would abort). -/
lemma doNormalize_iou_exp_hi (neg : Bool) (M : UInt64) (e : Int) (mode : rounding_mode)
    (res : Number)
    (hM_lo : 10 ^ 18 ≤ M.toNat) (hM_hi : M.toNat < 10 ^ 19)
    (hok : doNormalize neg M e cMinValue cMaxValue mode = .ok res) :
    e + 3 ≤ maxExponent := by
  by_contra hc
  have hge : maxExponent ≤ e + 2 := by omega
  have hM_ne : ¬ (M == 0) = true := by
    intro h
    have : M = 0 := by exact_mod_cast beq_iff_eq.mp h
    rw [this] at hM_lo; simp at hM_lo
  set g0 : Guard := if neg then Guard.new.set_negative else Guard.new with hg0_def
  have herr := doNormalize_scaleDown_errors_of_ge M e g0 hM_lo hM_hi hge
  rw [doNormalize] at hok
  rw [show (M == 0) = false from Bool.eq_false_iff.mpr (fun h => hM_ne h)] at hok
  simp only [Bool.false_eq_true, if_false] at hok
  rw [doNormalize_scaleUp_id cMinValue M e
        (by rw [UInt64.le_iff_toNat_le, cMinValue_val]; omega)] at hok
  simp only [] at hok
  rw [← hg0_def, herr] at hok
  exact absurd hok (by simp)

/-- A `.ok` 16-digit `normalizeToRange` on a 19-digit input bounds the source
exponent below `maxExponent - 2`. -/
lemma normalizeToRange_iou_exp_hi (n : Number) (mode : rounding_mode) (mant : Int64) (exp : Int)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (hok : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp)) :
    n.exponent_ + 3 ≤ maxExponent := by
  obtain ⟨res, hd⟩ := normalizeToRange_ok_doNormalize_ok n cMinValue cMaxValue mode mant exp hok
  exact doNormalize_iou_exp_hi n.negative_ n.mantissa_ n.exponent_ mode res h_lo h_hi hd

/-- **Combined carry-cusp `doRoundUp` characterization.** Rounding up the top of
the 16-digit range renormalizes to `(cMinValue, e+1)` and then either errors (if
`e+1` overflows `maxExponent`) or returns that record. This unifies
`doRoundUp_small_cusp` (the `.ok` leg) with its erroring leg. -/
lemma doRoundUp_small_cusp_eq (g : Guard) (neg : Bool) (e : Int) (mode : rounding_mode)
    (loc : Error)
    (hb : (g.round mode == 1 || (g.round mode == 0 && cMaxValue % 2 == 1)) = true)
    (hexp_lo : minExponent ≤ e + 1) :
    g.doRoundUp neg cMaxValue e cMinValue cMaxValue mode loc
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
  have hpush_sbit : (g.push 9).sbit_ = g.sbit_ := Guard.push_sbit g 9
  have hroundUp' : ((g.push 9).round mode == 1
      || ((g.push 9).round mode == 0 && (999999999999999 : UInt64) % 2 == 1)) = true := by
    cases mode with
    | to_nearest =>
      have htn : (g.push 9).round .to_nearest = 1 := by
        unfold Guard.round
        rw [if_neg (by rw [hpush_ne]; exact Bool.false_ne_true),
            if_pos (show (g.push 9).digits_ > 0x5000000000000000 from by
              rw [gt_iff_lt, UInt64.lt_iff_toNat_lt,
                  show (0x5000000000000000 : UInt64).toNat = 5764607523034234880 from by decide]
              omega)]
      rw [htn]; rfl
    | towards_zero =>
      exfalso
      have : g.round .towards_zero = -1 ∨ g.round .towards_zero = -2 := by
        unfold Guard.round; by_cases he : g.empty = true
        · rw [if_pos he]; right; rfl
        · rw [if_neg he]; left; rfl
      rcases this with h | h <;> rw [h] at hb <;> simp at hb
    | downward =>
      have hsb : g.sbit_ = true := by
        by_contra hh; rw [Bool.not_eq_true] at hh
        have : g.round .downward = -1 ∨ g.round .downward = -2 := by
          unfold Guard.round; by_cases he : g.empty = true
          · rw [if_pos he]; right; rfl
          · rw [if_neg he, hh]; left; rfl
        rcases this with h | h <;> rw [h] at hb <;> simp at hb
      exact round_bool_downward_neg (g.push 9) 999999999999999 (hpush_sbit.trans hsb) hpush_ne
    | upward =>
      have hsb : g.sbit_ = false := by
        by_contra hh; rw [Bool.not_eq_false] at hh
        have : g.round .upward = -1 ∨ g.round .upward = -2 := by
          unfold Guard.round; by_cases he : g.empty = true
          · rw [if_pos he]; right; rfl
          · rw [if_neg he, hh]; left; rfl
        rcases this with h | h <;> rw [h] at hb <;> simp at hb
      exact round_bool_upward_pos (g.push 9) 999999999999999 (hpush_sbit.trans hsb) hpush_ne
  unfold Guard.doRoundUp
  simp only []
  rw [pushOverflow_noop_of_lt_maxRep (by rw [maxRep_val, cMaxValue_val]; omega) g mode, hb]
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

/-- **Success-keyed 16-digit `normalizeToRange` facts.** A `.ok` result on a
19-digit input, under the *weaker* `n.exponent_ + 3 ≤ maxExponent`, still has a
canonical 16-digit mantissa, an exponent in `[n.exponent_ + 3, maxExponent]`, and
(for a sign-cleared input) a non-negative signed mantissa. The carry-cusp exponent
`n.exponent_ + 4` is admissible only when it does not overflow `maxExponent`
(otherwise the run would have errored). -/
lemma normalizeToRange_iou_ok_facts (n : Number) (mode : rounding_mode)
    (mant : Int64) (exp : Int)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 3 ≤ maxExponent)
    (hok : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp)) :
    (cMinValue.toNat ≤ mant.toInt.natAbs ∧ mant.toInt.natAbs ≤ cMaxValue.toNat) ∧
    (n.exponent_ + 3 ≤ exp ∧ exp ≤ maxExponent) ∧
    ((n.negative_ = false → 0 ≤ mant.toInt) ∧ (n.negative_ = true → mant.toInt ≤ 0)) := by
  obtain ⟨g, _hrep, _hsbit, _h_empty_of, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ mode h_lo h_hi he_lo he_hi
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  -- A sign-cleared `if`-mantissa over a sub-`2^63` magnitude is non-negative.
  have hsign : ∀ (X : UInt64), X.toNat < 2 ^ 63 →
      (if n.negative_ then -X.toInt64 else X.toInt64) = mant →
      (n.negative_ = false → 0 ≤ mant.toInt) ∧ (n.negative_ = true → mant.toInt ≤ 0) := by
    intro X hX heq
    constructor
    · intro hneg
      rw [← heq, hneg]
      simp only [Bool.false_eq_true, if_false]
      rw [UInt64.toInt64_toInt_of_lt _ hX]; positivity
    · intro hneg
      rw [← heq, hneg]
      simp only [if_true]
      have hX' : X.toInt64.toInt = (X.toNat : ℤ) := UInt64.toInt64_toInt_of_lt _ hX
      have hmin : Int64.minValue.toInt = (-9223372036854775808 : ℤ) := by decide
      have hmax : Int64.maxValue.toInt = (9223372036854775807 : ℤ) := by decide
      have h_lo : Int64.minValue.toInt ≤ -X.toInt64.toInt := by rw [hmin, hX']; omega
      have h_hi : -X.toInt64.toInt ≤ Int64.maxValue.toInt := by rw [hmax, hX']; omega
      rw [Int64.toInt_neg, AmountArith.toInt_bmod_self h_lo h_hi]
      omega
  by_cases hround : (g.round mode == 1
      || (g.round mode == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true
  · by_cases hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue
    · -- carry-cusp: admissible only when `(n.exponent_+3)+1 ≤ maxExponent`.
      have hbr : (g.round mode == 1 || (g.round mode == 0 && cMaxValue % 2 == 1)) = true := by
        rw [hcusp] at hround; exact hround
      have hcusp_eq := doRoundUp_small_cusp_eq g n.negative_ (n.exponent_ + 3) mode
        .normalize2 hbr (by omega)
      by_cases hovf : maxExponent < (n.exponent_ + 3) + 1
      · exfalso
        have h_err : n.normalizeToRange cMinValue cMaxValue mode = .error .normalize2 := by
          unfold Number.normalizeToRange
          rw [h_red, hcusp, hcusp_eq, if_pos hovf]
        rw [h_err] at hok; exact absurd hok (by simp)
      · have hcompute : n.normalizeToRange cMinValue cMaxValue mode
            = .ok (if n.negative_ then -cMinValue.toInt64 else cMinValue.toInt64,
                   (n.exponent_ + 3) + 1) := by
          unfold Number.normalizeToRange
          rw [h_red, hcusp, hcusp_eq, if_neg hovf]
          rfl
        rw [hcompute] at hok
        obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
        refine ⟨⟨?_, ?_⟩, ⟨by omega, by omega⟩, hsign cMinValue (by rw [hcMin]; omega) hmant⟩
        · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hcMin]; omega), hcMin]
        · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hcMin]; omega), hcMin, hcMax]
          omega
    · -- fire: increment in place, exponent unchanged.
      have hlt : (n.mantissa_ / 10 / 10 / 10).toNat < cMaxValue.toNat := by
        have hne : (n.mantissa_ / 10 / 10 / 10).toNat ≠ cMaxValue.toNat :=
          fun h => hcusp (UInt64.toNat_inj.mp h)
        rw [hcMax, hm3] at hne ⊢; omega
      have hadd : (n.mantissa_ / 10 / 10 / 10 + 1).toNat = n.mantissa_.toNat / 1000 + 1 := by
        rw [UInt64.toNat_add, hm3, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      have hcompute : n.normalizeToRange cMinValue cMaxValue mode
          = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10 + 1).toInt64
                 else (n.mantissa_ / 10 / 10 / 10 + 1).toInt64, n.exponent_ + 3) := by
        unfold Number.normalizeToRange
        rw [h_red, doRoundUp_small_fire g n.negative_ _ (n.exponent_ + 3) mode
          .normalize2 hround (by rw [hcMin, hm3]; omega) hlt (by omega) (by omega)]
        rfl
      rw [hcompute] at hok
      obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
      refine ⟨⟨?_, ?_⟩, ⟨by omega, by omega⟩, hsign _ (by rw [hadd]; omega) hmant⟩
      · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hadd]; omega), hadd, hcMin]
        omega
      · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hadd]; omega), hadd, hcMax]
        omega
  · -- truncate: keep the 3-digit truncation, exponent unchanged.
    have hcompute : n.normalizeToRange cMinValue cMaxValue mode
        = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64
               else (n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
      unfold Number.normalizeToRange
      rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) mode
        .normalize2 (by simpa using hround) (by rw [hcMin, hm3]; omega)
        (by rw [hcMax, hm3]; omega) (by omega) (by omega)]
      rfl
    rw [hcompute] at hok
    obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
    refine ⟨⟨?_, ?_⟩, ⟨by omega, by omega⟩, hsign _ (by rw [hm3]; omega) hmant⟩
    · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hm3]; omega), hm3, hcMin]
      omega
    · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hm3]; omega), hm3, hcMax]
      omega

lemma IOUAmount.normalize_mantissa_nonpos (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (hm : m.toInt ≤ 0)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok i) :
    i.mantissa_.toInt ≤ 0 := by
  by_cases hi0 : i.mantissa_ = 0
  · rw [hi0]; decide
  unfold IOUAmount.normalize at hok
  by_cases hma : m = 0
  · rw [if_pos (show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = true from beq_iff_eq.mpr hma)] at hok
    rw [← Except.ok.inj hok] at hi0; exact absurd rfl hi0
  · have hm_toInt : m.toInt ≠ 0 := fun h => hma (Int64.toInt_inj.mp (by rw [h]; decide))
    have hmlt : decide (m < 0) = true := by
      rw [decide_eq_true_iff, Int64.lt_iff_toInt_lt]
      have h0 : (0 : Int64).toInt = 0 := by decide
      omega
    rw [show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = false from beq_eq_false_iff_ne.mpr hma] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
    | error err => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      have hofn : IOUAmount.ofNumber v mode = .ok i := hok
      have hv_ne : v.mantissa_ ≠ 0 := IOUAmount.ofNumber_mantissa_ne_zero v mode i hofn hi0
      have hfr' : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).normalize
          largeRange.min largeRange.max mode = .ok v := hfr
      have hun_ne : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).mantissa_ ≠ 0 := by
        show m.toInt.natAbs.toUInt64 ≠ 0
        have hb : m.toInt.natAbs < 2 ^ 64 := by
          have h1 := Int64.le_toInt m
          have h2 := Int64.toInt_lt m
          omega
        have heq : m.toInt.natAbs.toUInt64.toNat = m.toInt.natAbs :=
          UInt64.toNat_ofNat_of_lt hb
        intro h; rw [h] at heq; simp at heq; omega
      have hv_norm : v.isNormalized :=
        normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
      obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv_ne
      have hv_exp_lo : minExponent ≤ v.exponent_ := by
        rcases hv_norm with hz | ⟨_, _, _, hlo', _⟩
        · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
        · exact hlo'
      have hvneg : v.negative_ = true := by
        obtain ⟨m3, e3, g3, res, hrup, hres_eq, -, -, -, -⟩ :=
          normalize_doRoundUp_stage _ v mode hun_ne hfr' hv_ne
        have hres_ne : res.mantissa_ ≠ 0 := by rw [hres_eq] at hv_ne; exact hv_ne
        have hsg := doRoundUp_negative_of_mant_ne g3 _ m3 e3 largeRange.min largeRange.max mode
          .normalize2 res hrup hres_ne
        rw [hres_eq]
        show res.negative_ = true
        rw [hsg]; exact hmlt
      unfold IOUAmount.ofNumber at hofn
      cases hfn : IOUAmount.fromNumber v mode with
      | error err => rw [hfn] at hofn; exact absurd hofn (by simp)
      | ok r =>
        rw [hfn] at hofn
        simp only [] at hofn
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hofn; exact absurd hofn (by simp)
        rw [if_neg hhi] at hofn
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hofn
          rw [← Except.ok.inj hofn] at hi0; exact absurd rfl hi0
        rw [if_neg hlo] at hofn
        have hir : i = r := (Except.ok.inj hofn).symm
        unfold IOUAmount.fromNumber at hfn
        cases hnorm : v.normalizeToRange cMinValue cMaxValue mode with
        | error err => rw [hnorm] at hfn; exact absurd hfn (by simp)
        | ok me' =>
          obtain ⟨mm, ee⟩ := me'
          rw [hnorm] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
            normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnorm
          obtain ⟨-, -, hsign⟩ :=
            normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnorm
          rw [hir, hrmm]
          exact hsign.2 hvneg

/-- Every `IOUAmount.normalize` output is either the zero sentinel (exponent
`-100`) or sits inside the IOU exponent window. -/
lemma IOUAmount.normalize_exp_range (a : IOUAmount) (mode : rounding_mode) (i : IOUAmount)
    (hok : IOUAmount.normalize a mode = .ok i) :
    (i.mantissa_ = 0 ∧ i.exponent_ = -100) ∨
      ((-96 : ℤ) ≤ i.exponent_ ∧ i.exponent_ ≤ 80) := by
  unfold IOUAmount.normalize at hok
  by_cases hz : (a.mantissa_ == 0) = true
  · rw [if_pos hz] at hok
    rw [← Except.ok.inj hok]; exact Or.inl ⟨rfl, rfl⟩
  · rw [if_neg hz] at hok
    cases hfr : Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
    | error e => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      cases hfn : IOUAmount.fromNumber v mode with
      | error e => rw [hfn] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hfn] at hok
        simp only [] at hok
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hok; exact absurd hok (by simp)
        · rw [if_neg hhi] at hok
          by_cases hlo : r.exponent_ < cMinOffset
          · rw [if_pos hlo] at hok
            rw [← Except.ok.inj hok]; exact Or.inl ⟨rfl, rfl⟩
          · rw [if_neg hlo] at hok
            rw [← Except.ok.inj hok]
            refine Or.inr ⟨?_, ?_⟩
            · have : cMinOffset = (-96 : ℤ) := rfl
              omega
            · have : cMaxOffset = (80 : ℤ) := rfl
              omega

/-- A zero-mantissa `IOUAmount.normalize` output is the `-100` zero sentinel: the
only exits that can produce one return `IOUAmount.zero`, and the general exit
lands in the canonical 16-digit window. -/
lemma IOUAmount.normalize_zero_exp (a : IOUAmount) (mode : rounding_mode) (i : IOUAmount)
    (hok : IOUAmount.normalize a mode = .ok i) (hz : i.mantissa_ = 0) : i.exponent_ = -100 := by
  unfold IOUAmount.normalize at hok
  by_cases hma : (a.mantissa_ == 0) = true
  · rw [if_pos hma] at hok; rw [← Except.ok.inj hok]; rfl
  · rw [if_neg hma] at hok
    have hane : a.mantissa_ ≠ 0 := by simpa using hma
    cases hfr : Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
    | error e => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      cases hfn : IOUAmount.fromNumber v mode with
      | error e => rw [hfn] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hfn] at hok
        simp only [] at hok
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hok; exact absurd hok (by simp)
        rw [if_neg hhi] at hok
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hok; rw [← Except.ok.inj hok]; rfl
        rw [if_neg hlo] at hok
        -- the general exit: a nonzero source packs to a nonzero 16-digit mantissa
        exfalso
        have hir : i = r := (Except.ok.inj hok).symm
        rw [hir] at hz
        have hfr' : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
            a.exponent_).normalize largeRange.min largeRange.max mode = .ok v := hfr
        have hun_ne : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
            a.exponent_).mantissa_ ≠ 0 := by
          show a.mantissa_.toInt.natAbs.toUInt64 ≠ 0
          have hb : a.mantissa_.toInt.natAbs < 2 ^ 64 := by
            have h1 := Int64.le_toInt a.mantissa_
            have h2 := Int64.toInt_lt a.mantissa_
            omega
          have heq : a.mantissa_.toInt.natAbs.toUInt64.toNat = a.mantissa_.toInt.natAbs :=
            UInt64.toNat_ofNat_of_lt hb
          have hmi : a.mantissa_.toInt ≠ 0 := fun h =>
            hane (Int64.toInt_inj.mp (by rw [h]; decide))
          intro h; rw [h] at heq; simp at heq; omega
        unfold IOUAmount.fromNumber at hfn
        cases hnr : v.normalizeToRange cMinValue cMaxValue mode with
        | error e => rw [hnr] at hfn; exact absurd hfn (by simp)
        | ok me =>
          obtain ⟨mm, ee⟩ := me
          rw [hnr] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          by_cases hv0 : v.mantissa_ = 0
          · -- the 19-digit lift flushed to zero; its exponent sits far below `cMinOffset`,
            -- so the underflow branch would have fired before this one
            have hnr' : v.normalizeToRange cMinValue cMaxValue mode
                = .ok ((if Number.zero.negative_ then -Number.zero.mantissa_.toInt64
                        else Number.zero.mantissa_.toInt64), Number.zero.exponent_) := by
              unfold Number.normalizeToRange
              rw [show doNormalize v.negative_ v.mantissa_ v.exponent_ cMinValue cMaxValue mode
                    = .ok Number.zero from by
                  unfold doNormalize; rw [if_pos (by simpa using hv0)]]
            have hpair := Except.ok.inj (hnr.symm.trans hnr')
            have hee : ee = Number.zero.exponent_ := congrArg Prod.snd hpair
            apply hlo
            rw [hrmm]
            show ee < cMinOffset
            rw [hee]
            decide
          · have hfr' : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
                a.exponent_).normalize largeRange.min largeRange.max mode = .ok v := hfr
            have hv_norm : v.isNormalized :=
              normalize_result_isNormalized _ v mode hun_ne hfr' hv0
            obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv0
            have hv_exp_lo : minExponent ≤ v.exponent_ := by
              rcases hv_norm with h0 | ⟨_, _, _, hlo', _⟩
              · exact absurd (show v.mantissa_ = 0 by rw [h0]; rfl) hv0
              · exact hlo'
            have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
              normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnr
            obtain ⟨⟨hmlo, -⟩, -, -⟩ :=
              normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnr
            have hcm : cMinValue.toNat = 10 ^ 15 := by decide
            rw [hrmm] at hz
            have hmm0 : mm.toInt.natAbs = 0 := by
              have : mm = 0 := hz
              rw [this]; decide
            omega

/-- **Full-range 16-digit bracketing.** The `normalizeToRange` result magnitude is
either the floor `M/1000` or the ceiling `M/1000 + 1` of the source mantissa, scaled
by `10^(exponent+3)` -- for EVERY rounding mode and over the whole 19-digit range. -/
lemma normalizeToRange_16_bracket (n : Number) (mode : rounding_mode)
    (mant : Int64) (exp : Int)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 4 ≤ maxExponent)
    (hok : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp)) :
    ∃ k : ℕ, (k = n.mantissa_.toNat / 1000 ∨ k = n.mantissa_.toNat / 1000 + 1) ∧
      k < 2 ^ 63 ∧
      (mant.toInt : ℚ) * 10 ^ exp
        = (if n.negative_ then (-1 : ℚ) else 1) * ((k : ℚ) * 10 ^ (n.exponent_ + 3)) := by
  obtain ⟨g, _hrep, _hsbit, _h_empty_of, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ mode h_lo h_hi he_lo (by omega)
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  -- value characterization: the result magnitude is `(M/1000 or M/1000+1)·10^(e+3)`
  by_cases hround : (g.round mode == 1
      || (g.round mode == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true
  · by_cases hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue
    · -- carry-cusp: result `(cMinValue, e+4)`, value `(M/1000+1)·10^(e+3)`
      have hcompute : n.normalizeToRange cMinValue cMaxValue mode
          = .ok (if n.negative_ then -cMinValue.toInt64 else cMinValue.toInt64,
                 (n.exponent_ + 3) + 1) := by
        unfold Number.normalizeToRange
        rw [h_red, hcusp, doRoundUp_small_cusp g n.negative_ (n.exponent_ + 3) mode
          .normalize2 (by rw [hcusp] at hround; exact hround) (by omega) (by omega)]
        rfl
      rw [hcompute] at hok
      obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
      have hMk : n.mantissa_.toNat / 1000 = 10 ^ 16 - 1 := by
        have := congrArg UInt64.toNat hcusp; rw [hm3, hcMax] at this; exact this
      refine ⟨n.mantissa_.toNat / 1000 + 1, Or.inr rfl, by omega, ?_⟩
      rw [← hmant, ← hexp, signed_mantissa_toInt n.negative_ cMinValue (by rw [hcMin]; omega)]
      rw [hcMin, hMk, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0) (n.exponent_ + 3) 1,
          zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0) n.exponent_ 3]
      push_cast; ring
    · -- fire: result `(M/1000+1, e+3)`
      have hlt : (n.mantissa_ / 10 / 10 / 10).toNat < cMaxValue.toNat := by
        have hne : (n.mantissa_ / 10 / 10 / 10).toNat ≠ cMaxValue.toNat :=
          fun h => hcusp (UInt64.toNat_inj.mp h)
        rw [hcMax, hm3] at hne ⊢; omega
      have hadd : (n.mantissa_ / 10 / 10 / 10 + 1).toNat = n.mantissa_.toNat / 1000 + 1 := by
        rw [UInt64.toNat_add, hm3, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      have hcompute : n.normalizeToRange cMinValue cMaxValue mode
          = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10 + 1).toInt64
                 else (n.mantissa_ / 10 / 10 / 10 + 1).toInt64, n.exponent_ + 3) := by
        unfold Number.normalizeToRange
        rw [h_red, doRoundUp_small_fire g n.negative_ _ (n.exponent_ + 3) mode
          .normalize2 hround (by rw [hcMin, hm3]; omega) hlt (by omega) (by omega)]
        rfl
      rw [hcompute] at hok
      obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
      refine ⟨(n.mantissa_ / 10 / 10 / 10 + 1).toNat, Or.inr hadd, by rw [hadd]; omega, ?_⟩
      rw [← hmant, ← hexp, signed_mantissa_toInt n.negative_ _ (by rw [hadd]; omega)]
      push_cast; ring
  · -- truncate: result `(M/1000, e+3)`
    have hcompute : n.normalizeToRange cMinValue cMaxValue mode
        = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64
               else (n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
      unfold Number.normalizeToRange
      rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) mode
        .normalize2 (by simpa using hround) (by rw [hcMin, hm3]; omega)
        (by rw [hcMax, hm3]; omega) (by omega) (by omega)]
      rfl
    rw [hcompute] at hok
    obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
    refine ⟨(n.mantissa_ / 10 / 10 / 10).toNat, Or.inl hm3, by rw [hm3]; omega, ?_⟩
    rw [← hmant, ← hexp, signed_mantissa_toInt n.negative_ _ (by rw [hm3]; omega)]
    push_cast; ring

/-- `pushOverflow` never touches the sign bit. -/
lemma Guard.pushOverflow_sbit (g : Guard) (m : UInt64) (mode : rounding_mode) :
    (g.pushOverflow m mode).sbit_ = g.sbit_ := by
  unfold Guard.pushOverflow
  by_cases h : maxRep ≤ m ∧ m < maxRepUp
  · rw [if_pos h]
    simp only []
    rw [apply_ite Guard.sbit_, Guard.push_sbit, ite_self]
  · rw [if_neg h]

/-- **`.downward` `to_rep` on a sign-cleared `Number` is the integer floor.**
When `sbit_ = false` the `.downward` round decision is `-1`/`-2`, never a bump, so
the shifted magnitude is truncated toward zero: the result brackets the value as
`r ≤ n.toRat < r + 1`. The lower bound gives payout/charge upper bounds. -/
lemma Number.to_rep_downward_floor (n : Number) (r : Int64)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : n.to_rep .downward = .ok r) :
    (r.toInt : ℚ) ≤ n.toRat ∧ n.toRat < (r.toInt : ℚ) + 1 := by
  have hupper : n.toRat < (r.toInt : ℚ) + 1 := by
    have hw := to_rep_within_one n .downward r hn hok
    rw [abs_lt] at hw; linarith [hw.1]
  refine ⟨?_, hupper⟩
  by_cases hexp0 : 0 ≤ n.exponent
  · rw [to_rep_exact_of_exponent_nonneg n .downward r hn hexp0 hok]
  · push_neg at hexp0
    unfold Number.to_rep at hok
    simp only at hok
    by_cases hz : (n.mantissa == 0) = true
    · rw [if_pos hz] at hok
      have hr : r = 0 := by injection hok with h; exact h.symm
      have hmant0 : n.mantissa.toInt = 0 := by rw [beq_iff_eq] at hz; rw [hz]; decide
      have htr : n.toRat = 0 := by rw [← mantissa_mul_exponent_eq_toRat n hn, hmant0]; norm_num
      rw [hr, htr, show (0 : Int64).toInt = 0 from by decide]; norm_num
    · rw [if_neg hz] at hok
      have hmag_nn : 0 ≤ n.mantissa.toInt := (mantissa_sign n).2 hneg
      have hmagM_le : n.mantissa.toInt.natAbs ≤ maxRep.toNat := mantissa_natAbs_le_maxRep n hn
      rw [hneg] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      rw [if_pos hexp0, if_neg (by omega : ¬ n.exponent ≥ 0)] at hok
      simp only at hok
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      set k : ℕ := (-n.exponent).toNat with hkdef
      have hk_cast : (k : ℤ) = -n.exponent := by rw [hkdef]; omega
      have hsp2_sbit : sp.2.sbit_ = false := by
        rw [hspdef, Number.to_rep_shift_sbit n.mantissa n.exponent Guard.new]; rfl
      have hDf : sp.1.toInt = n.mantissa.toInt / 10 ^ k := by
        rw [hspdef]; exact shift_fst_eq n.mantissa n.exponent Guard.new hmag_nn
      have hsp_nn : 0 ≤ sp.1.toInt := by rw [hDf]; exact Int.ediv_nonneg hmag_nn (by positivity)
      have hsp_le : sp.1.toInt ≤ (maxRep.toNat : ℤ) := by
        rw [hDf]
        calc n.mantissa.toInt / 10 ^ k ≤ n.mantissa.toInt := Int.ediv_le_self _ hmag_nn
          _ ≤ (maxRep.toNat : ℤ) := by omega
      -- the `.downward` round decision never bumps (guard sign bit is clear)
      set pof : Guard := sp.2.pushOverflow sp.1.toUInt64 .downward with hpof_def
      have hpof_sbit : pof.sbit_ = false := by rw [hpof_def, Guard.pushOverflow_sbit, hsp2_sbit]
      have hround_val : pof.round .downward = -1 ∨ pof.round .downward = -2 := by
        unfold Guard.round
        by_cases he : pof.empty = true
        · rw [if_pos he]; right; rfl
        · rw [if_neg he, hpof_sbit]; left; rfl
      have hb : (pof.round .downward == 1 || (pof.round .downward == 0 && sp.1 % 2 == 1)) = false := by
        rcases hround_val with h | h <;> rw [h] <;> simp
      rw [hb] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      rw [if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from fun hc => by
        have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
        rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
        omega)] at hok
      have hr : r = sp.1 := by injection hok with h; exact h.symm
      rw [hr]
      -- floor bound: `sp.1 = ⌊n.mantissa / 10^k⌋ ≤ n.toRat`
      have h10k_ne : (10 : ℤ) ^ k ≠ 0 := by positivity
      have hmul_le : sp.1.toInt * 10 ^ k ≤ n.mantissa.toInt := by
        rw [hDf]; exact Int.ediv_mul_le _ h10k_ne
      have hmul_le_q : (sp.1.toInt : ℚ) * 10 ^ k ≤ (n.mantissa.toInt : ℚ) := by exact_mod_cast hmul_le
      rw [← mantissa_mul_exponent_eq_toRat n hn]
      have hexp_pow : (10 : ℚ) ^ n.exponent = ((10 : ℚ) ^ k)⁻¹ := by
        rw [show n.exponent = -(k : ℤ) from by omega, zpow_neg, zpow_natCast]
      rw [hexp_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℚ) < 10 ^ k)]
      exact hmul_le_q

/-- A successful `IOUAmount.normalize` output is either a canonical 16-digit
amount (`InRange16`) or the zero amount. The 19-digit `from_rep` re-lift is
`largeRange`-normalized, so the 16-digit `normalizeToRange` snap lands in
`[cMinValue, cMaxValue]`; the `cMinOffset`/`cMaxOffset` clamps that a `.ok`
passed pin the exponent to `[-96, 80]`. -/
lemma IOUAmount.normalize_InRange16_or_zero (a : IOUAmount) (mode : rounding_mode)
    (i : IOUAmount) (hok : IOUAmount.normalize a mode = .ok i) :
    i.InRange16 ∨ i.mantissa_ = 0 := by
  by_cases hi0 : i.mantissa_ = 0
  · exact Or.inr hi0
  refine Or.inl ?_
  unfold IOUAmount.normalize at hok
  by_cases hma : a.mantissa_ = 0
  · rw [if_pos (beq_iff_eq.mpr hma)] at hok
    rw [← Except.ok.inj hok] at hi0
    exact absurd rfl hi0
  · rw [show (a.mantissa_ == 0) = false from beq_eq_false_iff_ne.mpr hma] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    have ham_toInt : a.mantissa_.toInt ≠ 0 := by
      intro h; exact hma (Int64.toInt_inj.mp (by rw [h]; decide))
    cases hfr : Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
    | error err => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      have hofn : IOUAmount.ofNumber v mode = .ok i := hok
      have hv_ne : v.mantissa_ ≠ 0 := IOUAmount.ofNumber_mantissa_ne_zero v mode i hofn hi0
      have hfr' : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
          a.exponent_).normalize largeRange.min largeRange.max mode = .ok v := hfr
      have hun_ne : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
          a.exponent_).mantissa_ ≠ 0 := by
        show a.mantissa_.toInt.natAbs.toUInt64 ≠ 0
        have hb : a.mantissa_.toInt.natAbs < 2 ^ 64 := by
          have h1 := Int64.le_toInt a.mantissa_
          have h2 := Int64.toInt_lt a.mantissa_
          omega
        have heq : a.mantissa_.toInt.natAbs.toUInt64.toNat = a.mantissa_.toInt.natAbs :=
          UInt64.toNat_ofNat_of_lt hb
        intro h; rw [h] at heq; simp at heq; omega
      have hv_norm : v.isNormalized := normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
      obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv_ne
      have hv_exp_lo : minExponent ≤ v.exponent_ := by
        rcases hv_norm with hz | ⟨_, _, _, hlo', _⟩
        · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
        · exact hlo'
      cases hfn : IOUAmount.fromNumber v mode with
      | error err =>
        unfold IOUAmount.ofNumber at hofn; rw [hfn] at hofn; exact absurd hofn (by simp)
      | ok r =>
        unfold IOUAmount.ofNumber at hofn
        rw [hfn] at hofn
        simp only [] at hofn
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hofn; exact absurd hofn (by simp)
        rw [if_neg hhi] at hofn
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hofn
          rw [← Except.ok.inj hofn] at hi0
          exact absurd rfl hi0
        rw [if_neg hlo] at hofn
        have hir : i = r := (Except.ok.inj hofn).symm
        unfold IOUAmount.fromNumber at hfn
        cases hnorm : v.normalizeToRange cMinValue cMaxValue mode with
        | error err => rw [hnorm] at hfn; exact absurd hfn (by simp)
        | ok me' =>
          obtain ⟨mm, ee⟩ := me'
          rw [hnorm] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          rw [hrmm] at hhi hlo
          have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
            normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnorm
          obtain ⟨⟨hmlo, hmhi⟩, _, _⟩ :=
            normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnorm
          rw [hir, hrmm]
          refine ⟨?_, ?_, ?_, ?_⟩
          · show 10 ^ 15 ≤ mm.toInt.natAbs
            rw [show cMinValue.toNat = 10 ^ 15 from by decide] at hmlo; exact hmlo
          · show mm.toInt.natAbs < 10 ^ 16
            rw [show cMaxValue.toNat = 10 ^ 16 - 1 from by decide] at hmhi; omega
          · show (-96 : ℤ) ≤ ee
            have := not_lt.mp hlo; unfold cMinOffset at this; omega
          · show ee ≤ (80 : ℤ)
            have := not_lt.mp hhi; unfold cMaxOffset at this; omega

/-- `IOUAmount.ofMantissaExp` output exponent: the canonical zero (`-100`) or the
clamped IOU range `[-96, 80]`. -/
lemma IOUAmount.ofMantissaExp_exponent_cases (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (hok : IOUAmount.ofMantissaExp m e mode = .ok i) :
    i.exponent_ = -100 ∨ ((-96 : ℤ) ≤ i.exponent_ ∧ i.exponent_ ≤ 80) := by
  unfold IOUAmount.ofMantissaExp IOUAmount.normalize at hok
  by_cases hm : (m == 0) = true
  · rw [if_pos hm] at hok
    rw [← Except.ok.inj hok]
    exact Or.inl rfl
  · rw [if_neg hm] at hok
    cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
    | error e' => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      cases hfn : IOUAmount.fromNumber v mode with
      | error e' => rw [hfn] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hfn] at hok
        simp only [] at hok
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hok; exact absurd hok (by simp)
        · rw [if_neg hhi] at hok
          by_cases hlo : r.exponent_ < cMinOffset
          · rw [if_pos hlo] at hok
            rw [← Except.ok.inj hok]
            exact Or.inl rfl
          · rw [if_neg hlo] at hok
            rw [← Except.ok.inj hok]
            right
            have h1 := not_lt.mp hlo
            have h2 := not_lt.mp hhi
            unfold cMinOffset at h1
            unfold cMaxOffset at h2
            omega

/-- **Sign preservation of `IOUAmount.normalize`.** A nonnegative signed mantissa
stays nonnegative through the 19-digit re-lift and the 16-digit snap: each stage
carries the cleared sign into its output (`doRoundUp` copies the input sign, and a
flushed-to-zero result is nonnegative trivially). Magnitude-free, unlike the
`RoundsWithin` characterizations, so it applies to sub-`10^16` mantissas. -/
lemma IOUAmount.normalize_mantissa_nonneg (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (hm : 0 ≤ m.toInt)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok i) :
    0 ≤ i.mantissa_.toInt := by
  by_cases hi0 : i.mantissa_ = 0
  · rw [hi0]; decide
  have hmlt : decide (m < 0) = false := by
    rw [decide_eq_false_iff_not, Int64.lt_iff_toInt_lt]
    have h0 : (0 : Int64).toInt = 0 := by decide
    omega
  unfold IOUAmount.normalize at hok
  by_cases hma : m = 0
  · rw [if_pos (show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = true from beq_iff_eq.mpr hma)] at hok
    rw [← Except.ok.inj hok] at hi0; exact absurd rfl hi0
  · have hm_toInt : m.toInt ≠ 0 := fun h => hma (Int64.toInt_inj.mp (by rw [h]; decide))
    rw [show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = false from beq_eq_false_iff_ne.mpr hma] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
    | error err => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      have hofn : IOUAmount.ofNumber v mode = .ok i := hok
      have hv_ne : v.mantissa_ ≠ 0 := IOUAmount.ofNumber_mantissa_ne_zero v mode i hofn hi0
      have hfr' : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).normalize
          largeRange.min largeRange.max mode = .ok v := hfr
      have hun_ne : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).mantissa_ ≠ 0 := by
        show m.toInt.natAbs.toUInt64 ≠ 0
        have hb : m.toInt.natAbs < 2 ^ 64 := by
          have h1 := Int64.le_toInt m
          have h2 := Int64.toInt_lt m
          omega
        have heq : m.toInt.natAbs.toUInt64.toNat = m.toInt.natAbs :=
          UInt64.toNat_ofNat_of_lt hb
        intro h; rw [h] at heq; simp at heq; omega
      have hv_norm : v.isNormalized :=
        normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
      obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv_ne
      have hv_exp_lo : minExponent ≤ v.exponent_ := by
        rcases hv_norm with hz | ⟨_, _, _, hlo', _⟩
        · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
        · exact hlo'
      -- Stage 1: the 19-digit re-lift keeps the cleared sign, so `v.negative_ = false`.
      have hvneg : v.negative_ = false := by
        obtain ⟨m3, e3, g3, res, hrup, hres_eq, -, -, -, -⟩ :=
          normalize_doRoundUp_stage _ v mode hun_ne hfr' hv_ne
        have hres_ne : res.mantissa_ ≠ 0 := by rw [hres_eq] at hv_ne; exact hv_ne
        have hsg := doRoundUp_negative_of_mant_ne g3 _ m3 e3 largeRange.min largeRange.max mode
          .normalize2 res hrup hres_ne
        rw [hres_eq]
        show res.negative_ = false
        rw [hsg]; exact hmlt
      -- Stage 2: the 16-digit snap keeps the cleared sign, giving a nonnegative mantissa.
      unfold IOUAmount.ofNumber at hofn
      cases hfn : IOUAmount.fromNumber v mode with
      | error err => rw [hfn] at hofn; exact absurd hofn (by simp)
      | ok r =>
        rw [hfn] at hofn
        simp only [] at hofn
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hofn; exact absurd hofn (by simp)
        rw [if_neg hhi] at hofn
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hofn
          rw [← Except.ok.inj hofn] at hi0; exact absurd rfl hi0
        rw [if_neg hlo] at hofn
        have hir : i = r := (Except.ok.inj hofn).symm
        unfold IOUAmount.fromNumber at hfn
        cases hnorm : v.normalizeToRange cMinValue cMaxValue mode with
        | error err => rw [hnorm] at hfn; exact absurd hfn (by simp)
        | ok me' =>
          obtain ⟨mm, ee⟩ := me'
          rw [hnorm] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
            normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnorm
          obtain ⟨-, -, hsign⟩ :=
            normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnorm
          rw [hir, hrmm]
          exact hsign.1 hvneg

/-- A zero-mantissa `Number` renormalizes to the zero `IOUAmount`. (The version in
`RoundToScale.Common.Proofs` is `private`, so it is reproven here.) -/
lemma IOUAmount.ofNumber_zero_mant (n : Number) (mode : rounding_mode)
    (h : n.mantissa_ = 0) :
    IOUAmount.ofNumber n mode = .ok IOUAmount.zero := by
  have hd : doNormalize n.negative_ n.mantissa_ n.exponent_ cMinValue cMaxValue mode
      = .ok Number.zero := by
    unfold doNormalize
    rw [show (n.mantissa_ == 0) = true from beq_iff_eq.mpr h, if_pos rfl]
  unfold IOUAmount.ofNumber IOUAmount.fromNumber Number.normalizeToRange
  rw [hd]
  rfl

end XRPL.Model.Protocol
