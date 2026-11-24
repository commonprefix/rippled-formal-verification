import XRPL.Properties.Protocol.STAmount.Common.IOUWitnessTraces
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRange
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap

/-! # Witnesses for the directed-mode IOU `RoundsWithin` headlines

Concrete canonical operands whose directed rounding error exceeds `|truth|·4/10¹⁶`, for the add and sub
headlines. The inner `Number` op is exact on them, so only the 16-digit re-round errs. -/

namespace XRPL.Model.Protocol

lemma add_lift_trace_g (mode : rounding_mode) :
    Number.operator_add ⟨false, 5000000000000003000, -3⟩ ⟨false, 5000000000000002000, -3⟩ mode
      = .ok ⟨false, 1000000000000000500, -2⟩ := by
  rw [Number.operator_add_eq_spec]
  case hx => decide
  case hy => decide
  cases mode <;> decide +kernel

lemma ofnum_dir (mode : rounding_mode) (m16 : UInt64)
    (hm16 : m16 = (if mode = .upward then 1000000000000001 else 1000000000000000))
    (hmode : mode = .downward ∨ mode = .upward ∨ mode = .towards_zero) :
    IOUAmount.ofNumber ⟨false, 1000000000000000500, -2⟩ mode = .ok ⟨m16.toInt64, 1⟩ := by
  obtain ⟨k, hnorm, _, _, htz, hdown, hup, _⟩ :=
    normalizeToRange_16_per_mode ⟨false, 1000000000000000500, -2⟩ mode (by decide) (by decide) (by decide) (by decide)
  have hk : k = m16 := by
    rcases hmode with h | h | h <;> subst h <;> rw [hm16]
    · have := hdown rfl; apply UInt64.toNat_inj.mp; simpa using this
    · have := hup rfl; apply UInt64.toNat_inj.mp; simpa using this
    · have := htz rfl; apply UInt64.toNat_inj.mp; simpa using this
  subst hk
  unfold IOUAmount.ofNumber IOUAmount.fromNumber
  rw [show (⟨false, 1000000000000000500, -2⟩ : Number).normalizeToRange cMinValue cMaxValue mode
        = .ok (k.toInt64, 1) by rw [hnorm]; norm_num]
  simp only []
  rw [ite_eq_right (by decide : ¬ ((1 : Int) > cMaxOffset)), ite_eq_right (by decide : ¬ ((1 : Int) < cMinOffset))]

lemma operator_add_dir_eq (mode : rounding_mode) (sumI : IOUAmount)
    (hofn : IOUAmount.ofNumber ⟨false, 1000000000000000500, -2⟩ mode = .ok sumI) :
    STAmount.operator_add ⟨.fractional, 5000000000000003, 0, false⟩
        ⟨.fractional, 5000000000000002, 0, false⟩ mode
      = STAmount.ofIOUAmount sumI mode := by
  have hc1 : (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).IOUCanonical :=
    ⟨by decide, by decide, by decide, by decide, by decide⟩
  have hc2 : (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).IOUCanonical :=
    ⟨by decide, by decide, by decide, by decide, by decide⟩
  have hiou1 := STAmount.iou_canonical_id ⟨.fractional, 5000000000000003, 0, false⟩ mode hc1
  have hiou2 := STAmount.iou_canonical_id ⟨.fractional, 5000000000000002, 0, false⟩ mode hc2
  have htn1 : (⟨(⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).signedDrops.toInt64,
      (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).mOffset⟩ : IOUAmount).toNumber mode
      = .ok ⟨false, 5000000000000003000, -3⟩ :=
    STAmount.iou_toNumber_canonical ⟨.fractional, 5000000000000003, 0, false⟩ mode hc1
  have htn2 : (⟨(⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).signedDrops.toInt64,
      (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).mOffset⟩ : IOUAmount).toNumber mode
      = .ok ⟨false, 5000000000000002000, -3⟩ :=
    STAmount.iou_toNumber_canonical ⟨.fractional, 5000000000000002, 0, false⟩ mode hc2
  have hadd_inner : IOUAmount.operator_add
      ⟨(⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).signedDrops.toInt64,
        (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).mOffset⟩
      ⟨(⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).signedDrops.toInt64,
        (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).mOffset⟩ mode = .ok sumI := by
    unfold IOUAmount.operator_add
    rw [ite_eq_right (by decide : ¬ (((⟨(⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).signedDrops.toInt64,
          (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).mOffset⟩ : IOUAmount).mantissa_ == 0) = true)),
        ite_eq_right (by decide : ¬ (((⟨(⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).signedDrops.toInt64,
          (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).mOffset⟩ : IOUAmount).mantissa_ == 0) = true))]
    rw [htn1]; simp only []
    rw [htn2]; simp only []
    rw [add_lift_trace_g mode]; simp only []
    exact hofn
  unfold STAmount.operator_add
  rw [ite_eq_right (by decide : ¬ ((!STAmount.areComparable ⟨.fractional, 5000000000000003, 0, false⟩
        ⟨.fractional, 5000000000000002, 0, false⟩) = true)),
      ite_eq_right (by decide : ¬ (((⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).mValue == 0) = true)),
      ite_eq_right (by decide : ¬ (((⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).mValue == 0) = true)),
      ite_eq_right (by decide : ¬ (((⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).integral) = true))]
  rw [hiou1]; simp only []
  rw [hiou2]; simp only []
  rw [hadd_inner]

-- per-mode add witnesses: downward/towards_zero give m16 = 10^15, upward gives 10^15+1, all err by 5
lemma add_dir_wit_core (mode : rounding_mode) (m16 : UInt64)
    (hm16 : m16 = (if mode = .upward then 1000000000000001 else 1000000000000000))
    (hmode : mode = .downward ∨ mode = .upward ∨ mode = .towards_zero) :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_add v1 v2 mode = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat + v2.toRat) (4 / 10 ^ 16 : ℚ) := by
  have hmv : m16.toNat = (if mode = .upward then 1000000000000001 else 1000000000000000) := by
    rw [hm16]; split <;> decide
  have hofn := ofnum_dir mode m16 hm16 hmode
  have hnat : (m16.toInt64).toInt.natAbs = m16.toNat := by rw [hm16]; split <;> decide
  have hsr : (⟨m16.toInt64, 1⟩ : IOUAmount).InRange16 :=
    ⟨by show 10 ^ 15 ≤ (m16.toInt64).toInt.natAbs; rw [hnat, hmv]; split <;> decide,
     by show (m16.toInt64).toInt.natAbs < 10 ^ 16; rw [hnat, hmv]; split <;> decide,
     by show (-96 : ℤ) ≤ 1; decide, by show (1 : ℤ) ≤ 80; decide⟩
  have hop := operator_add_dir_eq mode ⟨m16.toInt64, 1⟩ hofn
  rw [STAmount.ofIOU_canonical ⟨m16.toInt64, 1⟩ mode hsr] at hop
  have hmv_uint : (m16.toInt64).toInt.natAbs.toUInt64 = m16 := by rw [hm16]; split <;> decide
  have hneg : decide ((m16.toInt64) < 0) = false := by rw [hm16]; split <;> decide
  rw [hmv_uint, hneg] at hop
  have h1 : (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).toRat = 5000000000000003 := by
    rw [STAmount.toRat_signed]; norm_num [show ((5000000000000003 : UInt64).toNat : ℚ) = 5000000000000003 by norm_cast]
  have h2 : (⟨.fractional, 5000000000000002, 0, false⟩ : STAmount).toRat = 5000000000000002 := by
    rw [STAmount.toRat_signed]; norm_num [show ((5000000000000002 : UInt64).toNat : ℚ) = 5000000000000002 by norm_cast]
  have hr : (⟨.fractional, m16, 1, false⟩ : STAmount).toRat = 10 * (m16.toNat : ℚ) := by
    rw [STAmount.toRat_signed]; push_cast; ring
  refine ⟨⟨.fractional, 5000000000000003, 0, false⟩, ⟨.fractional, 5000000000000002, 0, false⟩,
          ⟨.fractional, m16, 1, false⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩, hop, ?_, ?_⟩
  · show m16 ≠ 0; rw [hm16]; split <;> decide
  · unfold RoundsWithinWitness
    rw [show RatValued.toRat (⟨.fractional, m16, 1, false⟩ : STAmount)
          = (⟨.fractional, m16, 1, false⟩ : STAmount).toRat from rfl, hr, h1, h2, hmv]
    split <;> norm_num

/-- Directed-mode IOU subtraction witness core: `v1 − v2 = v1 + (−v2)` with `−v2` the
addition witness operand, so the addition chain applies. -/
theorem sub_dir_wit_core (mode : rounding_mode) (m16 : UInt64)
    (hm16 : m16 = (if mode = .upward then 1000000000000001 else 1000000000000000))
    (hmode : mode = .downward ∨ mode = .upward ∨ mode = .towards_zero) :
    ∃ (v1 v2 result : STAmount),
      v1.IOUCanonical ∧ v2.IOUCanonical ∧
      STAmount.operator_sub v1 v2 mode = .ok result ∧ result.mValue ≠ 0 ∧
      RoundsWithinWitness result (v1.toRat - v2.toRat) (4 / 10 ^ 16 : ℚ) := by
  have hmv : m16.toNat = (if mode = .upward then 1000000000000001 else 1000000000000000) := by
    rw [hm16]; split <;> decide
  have hofn := ofnum_dir mode m16 hm16 hmode
  have hnat : (m16.toInt64).toInt.natAbs = m16.toNat := by rw [hm16]; split <;> decide
  have hsr : (⟨m16.toInt64, 1⟩ : IOUAmount).InRange16 :=
    ⟨by show 10 ^ 15 ≤ (m16.toInt64).toInt.natAbs; rw [hnat, hmv]; split <;> decide,
     by show (m16.toInt64).toInt.natAbs < 10 ^ 16; rw [hnat, hmv]; split <;> decide,
     by show (-96 : ℤ) ≤ 1; decide, by show (1 : ℤ) ≤ 80; decide⟩
  -- operator_sub v1 v2 = operator_add v1 (−v2), and −v2 is the addition witness operand
  have hop : STAmount.operator_sub ⟨.fractional, 5000000000000003, 0, false⟩
      ⟨.fractional, 5000000000000002, 0, true⟩ mode
      = .ok ⟨.fractional, (m16.toInt64).toInt.natAbs.toUInt64, 1, decide ((m16.toInt64) < 0)⟩ := by
    have hadd := operator_add_dir_eq mode ⟨m16.toInt64, 1⟩ hofn
    rw [STAmount.ofIOU_canonical ⟨m16.toInt64, 1⟩ mode hsr] at hadd
    exact hadd
  rw [show (m16.toInt64).toInt.natAbs.toUInt64 = m16 by rw [hm16]; split <;> decide,
      show decide ((m16.toInt64) < 0) = false by rw [hm16]; split <;> decide] at hop
  have h1 : (⟨.fractional, 5000000000000003, 0, false⟩ : STAmount).toRat = 5000000000000003 := by
    rw [STAmount.toRat_signed]; norm_num [show ((5000000000000003 : UInt64).toNat : ℚ) = 5000000000000003 by norm_cast]
  have h2 : (⟨.fractional, 5000000000000002, 0, true⟩ : STAmount).toRat = -5000000000000002 := by
    rw [STAmount.toRat_signed]; norm_num [show ((5000000000000002 : UInt64).toNat : ℚ) = 5000000000000002 by norm_cast]
  have hr : (⟨.fractional, m16, 1, false⟩ : STAmount).toRat = 10 * (m16.toNat : ℚ) := by
    rw [STAmount.toRat_signed]; push_cast; ring
  refine ⟨⟨.fractional, 5000000000000003, 0, false⟩, ⟨.fractional, 5000000000000002, 0, true⟩,
          ⟨.fractional, m16, 1, false⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩, hop, ?_, ?_⟩
  · show m16 ≠ 0; rw [hm16]; split <;> decide
  · unfold RoundsWithinWitness
    rw [show RatValued.toRat (⟨.fractional, m16, 1, false⟩ : STAmount)
          = (⟨.fractional, m16, 1, false⟩ : STAmount).toRat from rfl, hr, h1, h2, hmv]
    split <;> norm_num

end XRPL.Model.Protocol
