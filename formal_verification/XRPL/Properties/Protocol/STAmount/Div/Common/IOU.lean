import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec
import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral
import XRPL.Properties.Protocol.Number.Constructors.Constructors
import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts

/-! # 16-digit IOU normalization

Rounding bounds of `IOUAmount.normalize` and the sign and magnitude facts used to pack an `IOUAmount` into an
`STAmount`. -/

namespace XRPL.Model.Protocol

set_option maxRecDepth 10000

lemma from_rep_RoundsWithin_anyMode (m : Int64) (e : Int) (mode : rounding_mode) (v : Number)
    (hok : Number.from_rep m e largeRange.min largeRange.max mode = .ok v) (hv_ne : v.mantissa_ ≠ 0) :
    RoundsWithin v ((m.toInt : ℚ) * 10 ^ e) mode (10 / (2 ^ 63 + 2 : ℚ)) := by
  cases mode with
  | to_nearest =>
    exact RoundsWithin_mono v _ (5 / (2 ^ 63 + 7 : ℚ)) (10 / (2 ^ 63 + 2 : ℚ)) .to_nearest
      (from_rep_rounds_to_nearest m e v hok hv_ne) (by norm_num)
  | downward => exact from_rep_rounds_downward m e v hok hv_ne
  | upward => exact from_rep_rounds_upward m e v hok hv_ne
  | towards_zero => exact from_rep_rounds_towards_zero m e v hok hv_ne

/-- Shared `IOUAmount.normalize` decomposition facts for a 17-to-18-digit signed mantissa: the exact
19-digit re-lift `v` (`from_rep`) and its 16-digit re-round (`ofNumber`). -/
lemma IOUAmount.normalize_vfacts (m : Int64) (e : Int) (mode : rounding_mode) (result : IOUAmount)
    (hm_lo : 10 ^ 16 ≤ m.toInt.natAbs) (hm_hi : m.toInt.natAbs < 10 ^ 18)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok result) (hne : result.mantissa_ ≠ 0) :
    ∃ v : Number, Number.from_rep m e largeRange.min largeRange.max mode = .ok v ∧
      IOUAmount.ofNumber v mode = .ok result ∧ v.mantissa_ ≠ 0 ∧
      10 ^ 18 ≤ v.mantissa_.toNat ∧ v.mantissa_.toNat < 10 ^ 19 ∧
      minExponent ≤ v.exponent_ ∧ v.exponent_ ≤ e := by
  have hm_ne : (⟨m, e⟩ : IOUAmount).mantissa_ ≠ 0 := by
    show m ≠ 0; intro h; rw [h] at hm_lo; simp at hm_lo
  unfold IOUAmount.normalize at hok
  rw [if_neg (by simpa using hm_ne)] at hok
  cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
  | error err => rw [hfr] at hok; simp at hok
  | ok v =>
    rw [hfr] at hok; simp only at hok
    have hv_ne : v.mantissa_ ≠ 0 := IOUAmount.ofNumber_mantissa_ne_zero v mode result hok hne
    have hfr' : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).normalize
        largeRange.min largeRange.max mode = .ok v := hfr
    have hun_ne : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).mantissa_ ≠ 0 := by
      show m.toInt.natAbs.toUInt64 ≠ 0
      have hb : m.toInt.natAbs < 2 ^ 64 := by omega
      have heq : m.toInt.natAbs.toUInt64.toNat = m.toInt.natAbs := UInt64.toNat_ofNat_of_lt hb
      intro h; rw [h] at heq; simp at heq; omega
    have hv_norm : v.isNormalized :=
      normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
    have hv_mant := hv_norm.mantissaBounds_nat hv_ne
    have hv_exp_lo : minExponent ≤ v.exponent_ := by
      rcases hv_norm with hz | ⟨_, _, _, hlo, _⟩
      · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
      · exact hlo
    have hfr_bd := from_rep_RoundsWithin_anyMode m e mode v hfr hv_ne
    -- v.exponent_ ≤ e via the value bound
    have habs := RoundsWithin_abs_le_two v ((m.toInt : ℚ) * 10 ^ e) (10 / (2 ^ 63 + 2 : ℚ)) mode
      hfr_bd (by norm_num)
    rw [show RatValued.toRat v = v.toRat from rfl] at habs
    have hmabs : |(m.toInt : ℚ) * 10 ^ e| = (m.toInt.natAbs : ℚ) * 10 ^ e := by
      rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℚ) < 10) _), Nat.cast_natAbs]; push_cast; ring
    have hvabs : |v.toRat| = (v.mantissa_.toNat : ℚ) * 10 ^ v.exponent_ := _root_.XRPL.Model.Protocol.abs_toRat_eq v
    have hvexp : v.exponent_ ≤ e := by
      by_contra hc; push Not at hc
      have h1 : (10 : ℚ) ^ (e + 1) ≤ 10 ^ v.exponent_ := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hvm18 : (10 : ℚ) ^ (18 : ℕ) ≤ (v.mantissa_.toNat : ℚ) := by exact_mod_cast hv_mant.1
      have hmlt : (m.toInt.natAbs : ℚ) < (10 : ℚ) ^ (18 : ℕ) := by exact_mod_cast hm_hi
      have hpe : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
      rw [hvabs, hmabs] at habs
      have hpow1 : (10 : ℚ) ^ (e + 1) = 10 ^ e * 10 := by
        rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
      nlinarith [habs, h1, hvm18, hmlt, hpe, hpow1]
    exact ⟨v, rfl, hok, hv_ne, hv_mant.1, hv_mant.2, hv_exp_lo, hvexp⟩

/-- `IOUAmount.normalize` rel-error on a 17-to-18-digit signed mantissa. `m·10^e` with `10^16 ≤ |m| < 10^18`
re-rounds within `ε₁ + ε₂ + ε₁·ε₂`, with `ε₁ = 10/(2⁶³+2)` and `ε₂ = 10⁻¹⁵`. -/
lemma IOUAmount.normalize_rounds_within (m : Int64) (e : Int) (mode : rounding_mode) (result : IOUAmount)
    (hm_lo : 10 ^ 16 ≤ m.toInt.natAbs) (hm_hi : m.toInt.natAbs < 10 ^ 18)
    (he_hi : e + 4 ≤ maxExponent)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok result) (hne : result.mantissa_ ≠ 0) :
    RoundsWithin result ((m.toInt : ℚ) * 10 ^ e) mode
      (10 / (2 ^ 63 + 2 : ℚ) + (10 : ℚ) ^ (-15 : ℤ) + 10 / (2 ^ 63 + 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ)) := by
  obtain ⟨v, hfr, hok', hv_ne, hvm_lo, hvm_hi, hv_exp_lo, hvexp⟩ :=
    IOUAmount.normalize_vfacts m e mode result hm_lo hm_hi hok hne
  have hfr_bd := from_rep_RoundsWithin_anyMode m e mode v hfr hv_ne
  have hofn := IOUAmount.ofNumber_rounds_within v mode result hvm_lo hvm_hi
    (by omega) (by omega) hok' hne
  exact RoundsWithin_trans result v ((m.toInt : ℚ) * 10 ^ e) (10 / (2 ^ 63 + 2 : ℚ))
    ((10 : ℚ) ^ (-15 : ℤ)) mode hfr_bd
    (by rw [show RatValued.toRat v = v.toRat from rfl]; exact hofn) (by positivity) (by positivity)

/-- `IOUAmount.normalize` of a 17-to-18-digit mantissa gives a canonical 16-digit amount (`InRange16`). -/
lemma IOUAmount.normalize_InRange16 (m : Int64) (e : Int) (mode : rounding_mode) (result : IOUAmount)
    (hm_lo : 10 ^ 16 ≤ m.toInt.natAbs) (hm_hi : m.toInt.natAbs < 10 ^ 18)
    (he_hi : e + 4 ≤ maxExponent)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok result) (hne : result.mantissa_ ≠ 0) :
    result.InRange16 := by
  obtain ⟨v, hfr, hok', hv_ne, hvm_lo, hvm_hi, hv_exp_lo, hvexp⟩ :=
    IOUAmount.normalize_vfacts m e mode result hm_lo hm_hi hok hne
  exact IOUAmount.ofNumber_InRange16 v mode result hvm_lo hvm_hi (by omega) (by omega) hok' hne

/-- An IOU amount's `signum` is negative exactly when its mantissa is. -/
lemma IOUAmount.signum_neg_iff (i : IOUAmount) : i.signum < 0 ↔ i.mantissa_ < 0 := by
  unfold IOUAmount.signum
  by_cases h_lt : i.mantissa_ < 0
  · rw [if_pos h_lt]; simp [h_lt]
  · rw [if_neg h_lt]; split <;> simp_all

/-- The canonicalize-pack magnitude: `|i.mantissa_|` as a `UInt64` equals the natural
absolute value of the mantissa. -/
lemma IOUAmount.absMant_toNat (i : IOUAmount) (h_fit : i.mantissa_.toInt.natAbs < 2 ^ 63) :
    (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64.toNat
      = i.mantissa_.toInt.natAbs := by
  have h_absToInt : (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toInt
      = (i.mantissa_.toInt.natAbs : ℤ) := by
    by_cases h_lt : i.mantissa_ < 0
    · rw [if_pos ((IOUAmount.signum_neg_iff i).mpr h_lt)]
      have h_lt' : i.mantissa_.toInt < 0 := by simpa using Int64.lt_iff_toInt_lt.mp h_lt
      rw [Int64.toInt_neg, Int.bmod_eq_iff (by norm_num)]
      constructor <;> omega
    · rw [if_neg (fun h => h_lt ((IOUAmount.signum_neg_iff i).mp h))]
      have hge : 0 ≤ i.mantissa_.toInt := by
        rcases lt_or_ge i.mantissa_.toInt 0 with hh | hh
        · exact absurd (Int64.lt_iff_toInt_lt.mpr (by simpa using hh)) h_lt
        · exact hh
      omega
  have h1 := toUInt64_toNat_of_nonneg (if i.signum < 0 then -i.mantissa_ else i.mantissa_)
    (by rw [h_absToInt]; positivity)
  rw [h_absToInt] at h1
  omega

/-- The canonicalize IOU pack preserves value. The `STAmount` record of a canonical `IOUAmount` `i`
(magnitude `|i.mantissa_|`, exponent `i.exponent_`, sign from `i.signum`) has value `i.toRat`. -/
lemma STAmount.iou_pack_toRat (i : IOUAmount) (hr : i.InRange16) :
    (⟨.fractional, (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64,
       i.exponent_, decide (i.signum < 0)⟩ : STAmount).toRat = i.toRat := by
  have h_fit : i.mantissa_.toInt.natAbs < 2 ^ 63 := by have := hr.mant_hi; omega
  have h_absToNat := IOUAmount.absMant_toNat i h_fit
  have h_decsign : decide (i.signum < 0) = decide (i.mantissa_ < 0) := by
    rw [decide_eq_decide]; exact IOUAmount.signum_neg_iff i
  rw [STAmount.toRat_signed]
  show (if decide (i.signum < 0) then (-1 : ℚ) else 1)
      * (((if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64).toNat : ℚ)
        * 10 ^ i.exponent_ = i.toRat
  rw [h_absToNat, h_decsign, IOUAmount.toRat_eq i]
  have hsign : (if decide (i.mantissa_ < 0) then (-1 : ℚ) else 1) * (i.mantissa_.toInt.natAbs : ℚ)
      = (i.mantissa_.toInt : ℚ) := by
    by_cases hlt : i.mantissa_ < 0
    · rw [if_pos (by simpa using hlt)]
      have hlt' : i.mantissa_.toInt < 0 := by simpa using Int64.lt_iff_toInt_lt.mp hlt
      have hc : (i.mantissa_.toInt.natAbs : ℚ) = -(i.mantissa_.toInt : ℚ) := by
        rw [Nat.cast_natAbs]; push_cast; rw [abs_of_neg (by exact_mod_cast hlt')]
      rw [hc]; ring
    · rw [if_neg (by simpa using hlt)]
      have hge : 0 ≤ i.mantissa_.toInt := by
        rcases lt_or_ge i.mantissa_.toInt 0 with hh | hh
        · exact absurd (Int64.lt_iff_toInt_lt.mpr (by simpa using hh)) hlt
        · exact hh
      have hc : (i.mantissa_.toInt.natAbs : ℚ) = (i.mantissa_.toInt : ℚ) := by
        rw [Nat.cast_natAbs]; push_cast; rw [abs_of_nonneg (by exact_mod_cast hge)]
      rw [hc]; ring
  linear_combination (10 : ℚ) ^ i.exponent_ * hsign

end XRPL.Model.Protocol
