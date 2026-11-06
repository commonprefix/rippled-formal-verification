import XRPL.Properties.Lending.Loan.Common.PaymentFactor

/-! # Rounding error of a power by squaring

A to-nearest `Number` product is within the relative error `5 / (2^63 + 7)` of the exact product, a little less
than the error of the other operators. A `k`-th power by squaring is within `k − 1` such errors of the exact power. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private Number.power_ge_one rn_ge Number.ofInt64_one_toRat from XRPL.Properties.Lending.Loan.Common.SetLawful

/-- The relative error of a to-nearest `Number` product. -/
def Number.mulError : ℚ := 5 / (2 ^ 63 + 7)

lemma Number.mulError_pos : 0 < Number.mulError := by unfold Number.mulError; norm_num

/-- A nonzero to-nearest product is within the product error of the exact product. -/
lemma Number.mul_within (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (h : x.operator_mul y .to_nearest = .ok r) (hr : r.toRat ≠ 0) :
    |r.toRat - x.toRat * y.toRat| ≤ |x.toRat * y.toRat| * Number.mulError :=
  operator_mul_rounds_to_nearest x y r hx hy h (fun hm => hr (Number.toRat_eq_zero_iff.mpr hm))

/-- A to-nearest product of values at least one is at least one. -/
private lemma Number.mul_ge_one (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (h : x.operator_mul y .to_nearest = .ok r) (hx1 : 1 ≤ x.toRat) (hy1 : 1 ≤ y.toRat) : 1 ≤ r.toRat := by
  have := rn_ge (operator_mul_rounded_to_nearest _ _ _ hx hy h) _ (Number.ofInt64_isNormalized 1)
    (by rw [Number.ofInt64_one_toRat]; nlinarith)
  rwa [Number.ofInt64_one_toRat] at this

/-- A to-nearest product of values at least one is within the product error of the exact product. -/
private lemma Number.mul_bounds (x y r : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (h : x.operator_mul y .to_nearest = .ok r) (hx1 : 1 ≤ x.toRat) (hy1 : 1 ≤ y.toRat) :
    x.toRat * y.toRat * (1 - Number.mulError) ≤ r.toRat ∧ r.toRat ≤ x.toRat * y.toRat * (1 + Number.mulError) := by
  have hr1 := Number.mul_ge_one x y r hx hy h hx1 hy1
  have hw := Number.mul_within x y r hx hy h (by linarith)
  rw [abs_of_nonneg (by nlinarith : (0 : ℚ) ≤ x.toRat * y.toRat)] at hw
  constructor
  · linarith [(abs_le.mp hw).1]
  · linarith [(abs_le.mp hw).2]

/-- A power by squaring of a base at least one is within `k − 1` product errors of the exact power. Each
squaring doubles the error count of the half power and adds one, each multiplication by the base adds one. -/
lemma Number.power_bounds (base : Number) (hb : base.isNormalized) (h1 : 1 ≤ base.toRat) :
    ∀ (k : Nat) (r : Number), 1 ≤ k → base.power k = .ok r →
      base.toRat ^ k * (1 - Number.mulError) ^ (k - 1) ≤ r.toRat ∧
        r.toRat ≤ base.toRat ^ k * (1 + Number.mulError) ^ (k - 1) := by
  have he := Number.mulError_pos
  have he1 : Number.mulError ≤ 1 := by unfold Number.mulError; norm_num
  have hb0 : 0 ≤ base.toRat := by linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r hk h
    match k, ih with
    | 0, _ => omega
    | 1, _ =>
      rw [Number.power] at h
      cases h
      simp
    | j + 2, ih =>
      rw [Number.power] at h
      obtain ⟨half, hh, h⟩ := bind_ok_peel _ _ _ h
      have hhalfN := Number.power_isNormalized base hb _ half hh
      have hhalf1 := Number.power_ge_one base hb h1 _ half hh
      obtain ⟨hlo, hhi⟩ := ih ((j + 2) / 2) (by omega) half (by omega) hh
      obtain ⟨sq, hs, h⟩ := bind_ok_peel _ _ _ h
      have hsqN := Number.operator_mul_isNormalized _ _ sq _ hhalfN hhalfN hs
      have hsq1 := Number.mul_ge_one _ _ _ hhalfN hhalfN hs hhalf1 hhalf1
      obtain ⟨hsqlo, hsqhi⟩ := Number.mul_bounds _ _ _ hhalfN hhalfN hs hhalf1 hhalf1
      obtain ⟨m, hm⟩ : ∃ m, (j + 2) / 2 = m + 1 := ⟨(j + 2) / 2 - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel] at hlo hhi
      have hA : 0 ≤ base.toRat ^ (m + 1) * (1 - Number.mulError) ^ m :=
        mul_nonneg (pow_nonneg hb0 _) (pow_nonneg (by linarith) _)
      have sqlo : base.toRat ^ (2 * m + 2) * (1 - Number.mulError) ^ (2 * m + 1) ≤ sq.toRat := by
        calc base.toRat ^ (2 * m + 2) * (1 - Number.mulError) ^ (2 * m + 1)
            = (base.toRat ^ (m + 1) * (1 - Number.mulError) ^ m) *
                (base.toRat ^ (m + 1) * (1 - Number.mulError) ^ m) * (1 - Number.mulError) := by ring
          _ ≤ half.toRat * half.toRat * (1 - Number.mulError) := by gcongr
          _ ≤ sq.toRat := hsqlo
      have sqhi : sq.toRat ≤ base.toRat ^ (2 * m + 2) * (1 + Number.mulError) ^ (2 * m + 1) := by
        calc sq.toRat ≤ half.toRat * half.toRat * (1 + Number.mulError) := hsqhi
          _ ≤ (base.toRat ^ (m + 1) * (1 + Number.mulError) ^ m) *
                (base.toRat ^ (m + 1) * (1 + Number.mulError) ^ m) * (1 + Number.mulError) := by gcongr
          _ = base.toRat ^ (2 * m + 2) * (1 + Number.mulError) ^ (2 * m + 1) := by ring
      split at h
      · rename_i hodd
        have hk' : j + 2 = 2 * m + 3 := by
          have : (j + 2) % 2 = 1 := by simpa using hodd
          omega
        obtain ⟨hrlo, hrhi⟩ := Number.mul_bounds _ _ _ hsqN hb h hsq1 h1
        rw [hk', show 2 * m + 3 - 1 = 2 * m + 2 from by omega]
        have hB : 0 ≤ base.toRat ^ (2 * m + 2) * (1 - Number.mulError) ^ (2 * m + 1) :=
          mul_nonneg (pow_nonneg hb0 _) (pow_nonneg (by linarith) _)
        constructor
        · calc base.toRat ^ (2 * m + 3) * (1 - Number.mulError) ^ (2 * m + 2)
              = base.toRat ^ (2 * m + 2) * (1 - Number.mulError) ^ (2 * m + 1) * base.toRat *
                  (1 - Number.mulError) := by ring
            _ ≤ sq.toRat * base.toRat * (1 - Number.mulError) := by gcongr
            _ ≤ r.toRat := hrlo
        · calc r.toRat ≤ sq.toRat * base.toRat * (1 + Number.mulError) := hrhi
            _ ≤ base.toRat ^ (2 * m + 2) * (1 + Number.mulError) ^ (2 * m + 1) * base.toRat *
                  (1 + Number.mulError) := by gcongr
            _ = base.toRat ^ (2 * m + 3) * (1 + Number.mulError) ^ (2 * m + 2) := by ring
      · rename_i heven
        have hk' : j + 2 = 2 * m + 2 := by
          have : (j + 2) % 2 ≠ 1 := by simpa using heven
          omega
        cases h
        rw [hk', show 2 * m + 2 - 1 = 2 * m + 1 from by omega]
        exact ⟨sqlo, sqhi⟩

end XRPL.Model.Lending
