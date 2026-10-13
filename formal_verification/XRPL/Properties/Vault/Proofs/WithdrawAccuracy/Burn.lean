import XRPL.Properties.Vault.Common.CmpFaithfulCanonical
import XRPL.Properties.Vault.Proofs.Support.Integral

/-! # Share-side facts for the withdraw accuracy proofs -/

namespace XRPL.Model.SingleAssetVault.WdAcc

open XRPL.Model.Protocol

/-- A successful `ofNumber .int64` of a nonnegative integer fits `Int64`. -/
lemma ofNumber_int64_fit (n : Number) (mode : rounding_mode) (sta : STAmount)
    (hn : n.isNormalized) (hnn : 0 ≤ n.toRat) (hden : n.toRat.den = 1)
    (hok : STAmount.ofNumber .int64 n mode = .ok sta) :
    n.toRat ≤ 2 ^ 63 - 1 := by
  have hnegf : n.negative_ = false := Number.negative_false_of_nonneg n hn hnn
  have hsig : decide (n.signum < 0) = false := by
    unfold Number.signum
    rw [hnegf]
    simp only [Bool.false_eq_true, if_false]
    by_cases hm : (n.mantissa_ != 0) = true
    · rw [if_pos hm]; decide
    · rw [if_neg hm]; decide
  unfold STAmount.ofNumber at hok
  rw [hsig] at hok
  simp only [Bool.false_eq_true, if_false,
    show NumericType.int64.isIntegral = true from rfl, if_true] at hok
  cases hrep : n.to_rep mode with
  | error e => rw [hrep] at hok; simp at hok
  | ok rv =>
    have hexact : (rv.toInt : ℚ) = n.toRat :=
      int_cast_eq_of_abs_lt_one rv.toInt n.toRat hden (to_rep_within_one n mode rv hn hrep)
    rw [← hexact]
    have h := Int64.toInt_le rv
    rw [show Int64.maxValue.toInt = 2 ^ 63 - 1 from by decide] at h
    exact_mod_cast h

/-- For a positive canonical `int64` burn and the packed share total, the
field comparison decides value equality. -/
lemma burn_eq_iff (S : Number) (sb sta : STAmount)
    (hS : S.isNormalized) (hSnn : 0 ≤ S.toRat) (hSden : S.toRat.den = 1)
    (hst : STAmount.ofNumber .int64 S .to_nearest = .ok sta)
    (hpos : 0 < sb.toRat) (hc : sb.Canonical) (hSnt : sb.mNumericType = .int64) :
    sb.operator_eq sta = true ↔ sb.toRat = S.toRat := by
  obtain ⟨hnt, hoff, hneg, hmv, hval⟩ := STAmount.ofNumber_int64_shape S .to_nearest sta hS hSnn
    hSden (ofNumber_int64_fit S .to_nearest sta hS hSnn hSden hst) hst
  have hic : sb.IntegralCanonical := (hc.1 (by show sb.mNumericType.isIntegral = true; rw [hSnt]; rfl)).1
  have hsbneg : sb.mIsNegative = false := by
    rcases h : sb.mIsNegative with _ | _
    · rfl
    · exact absurd (STAmount.toRat_nonpos_of sb h) (not_le.mpr hpos)
  have hsbv := STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sb hic hpos.le
  unfold STAmount.operator_eq STAmount.areComparable
  rw [hSnt, hnt, hsbneg, hneg, hic.offset_zero, hoff, ← hsbv, ← hmv]
  simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq, Nat.cast_inj]
  exact ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.mp h⟩

/-- A nonnegative canonical `int64` amount is an integer below `2 ^ 63`. -/
lemma int64_bounds (sb : STAmount) (hnn : 0 ≤ sb.toRat) (hc : sb.Canonical)
    (hSnt : sb.mNumericType = .int64) :
    sb.toRat.den = 1 ∧ sb.toRat ≤ 2 ^ 63 - 1 := by
  have hic : sb.IntegralCanonical := (hc.1 (by show sb.mNumericType.isIntegral = true; rw [hSnt]; rfl)).1
  refine ⟨STAmount.IntegralCanonical.den_eq_one sb hic, ?_⟩
  rw [← STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sb hic hnn]
  have h := hic.in_range
  rw [hSnt, show NumericType.int64.maxValue.toNat = 9223372036854775807 from by decide] at h
  have h' : ((sb.mValue.toNat : ℕ) : ℚ) ≤ ((9223372036854775807 : ℕ) : ℚ) := by exact_mod_cast h
  norm_num at h' ⊢; exact h'

/-- The share-total update subtracts the burn exactly. -/
lemma sub_burn_exact (S sbn st' : Number) (sb : STAmount)
    (hS : S.isNormalized) (hSnn : 0 ≤ S.toRat) (hSden : S.toRat.den = 1)
    (hfit : S.toRat ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ sb.toRat) (hc : sb.Canonical) (hSnt : sb.mNumericType = .int64)
    (hsbn : sb.toNumber .to_nearest = .ok sbn)
    (hsub : S.operator_sub sbn .to_nearest = .ok st') :
    st'.toRat = S.toRat - sb.toRat := by
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical sb .to_nearest
    (STAmount.Canonical.exactCanonical sb hc)
  obtain rfl : sn = sbn := Except.ok.inj (hsn.symm.trans hsbn)
  obtain ⟨hden, hle⟩ := int64_bounds sb hnn hc hSnt
  rw [← hsnv] at hden hle hnn ⊢
  refine (operator_sub_exact_int S sn st' hS hsnn hSden hden ?_ hsub).1
  rw [rat_sub_eq_num_cast _ _ hSden hden, Rat.num_intCast]
  have h1 := rat_eq_num_cast_of_den_one _ hSden
  have h2 := rat_eq_num_cast_of_den_one _ hden
  have a1 : (0 : ℤ) ≤ S.toRat.num := by exact_mod_cast (h1 ▸ hSnn)
  have a2 : S.toRat.num ≤ 2 ^ 63 - 1 := by
    have : ((S.toRat.num : ℤ) : ℚ) ≤ ((2 ^ 63 - 1 : ℤ) : ℚ) := by rw [h1]; push_cast; linarith
    exact_mod_cast this
  have a3 : (0 : ℤ) ≤ sn.toRat.num := by exact_mod_cast (h2 ▸ hnn)
  have a4 : sn.toRat.num ≤ 2 ^ 63 - 1 := by
    have : ((sn.toRat.num : ℤ) : ℚ) ≤ ((2 ^ 63 - 1 : ℤ) : ℚ) := by rw [h2]; push_cast; linarith
    exact_mod_cast this
  omega

end XRPL.Model.SingleAssetVault.WdAcc
