import Mathlib.Tactic

/-! # Round-trip loss arithmetic

`J = (S·I + s·c)/(S + s)` is the redeemed shares' exact worth on the updated vault:
a convex combination of the deposit's ideal charge `I` and the recorded charge `c`. -/

namespace XRPL.Model.SingleAssetVault.DilG

lemma J_le_max (S s c I J : ℚ) (hS : 0 ≤ S) (hs : 0 < s) (B : ℚ) (hIB : I ≤ B) (hcB : c ≤ B)
    (hJ : J * (S + s) = S * I + s * c) : J ≤ B := by
  have hSs : 0 < S + s := by linarith
  have : J * (S + s) ≤ B * (S + s) := by
    rw [hJ]; nlinarith
  exact le_of_mul_le_mul_right this hSs

/-- The loss side: the charge overpays by at most `δ·I` plus half a unit of its digit. -/
lemma loss_arith (S s c I J I₂ p hc M : ℚ) (hS : 0 ≤ S) (hs : 0 < s) (hc0 : 0 ≤ c)
    (hI : 0 ≤ I) (hhc : 0 ≤ hc)
    (hover : c - I ≤ I * (2 / 10 ^ 18) + hc)
    (hJ : J * (S + s) = S * I + s * c)
    (hI₂ : (1 - 1 / 10 ^ 18) * J ≤ I₂)
    (hp : I₂ - p ≤ I₂ * (1 / 10 ^ 17) + M) :
    c - p ≤ c * (2 * (1 / 10 ^ 17)) + hc + M := by
  have hSs : 0 < S + s := by linarith
  have hJ0 : 0 ≤ J := by
    have : 0 ≤ J * (S + s) := by rw [hJ]; positivity
    exact nonneg_of_mul_nonneg_left this hSs
  have h1 : c - p ≤ c - (1 - 1 / 10 ^ 17) * ((1 - 1 / 10 ^ 18) * J) + M := by
    have : (1 - 1 / 10 ^ 17) * ((1 - 1 / 10 ^ 18) * J) ≤ (1 - 1 / 10 ^ 17) * I₂ :=
      mul_le_mul_of_nonneg_left hI₂ (by norm_num)
    linarith
  by_cases hcI : c ≤ I
  · have hJc : c ≤ J := by
      have : c * (S + s) ≤ J * (S + s) := by rw [hJ]; nlinarith
      exact le_of_mul_le_mul_right this hSs
    nlinarith
  · have hIc : I < c := lt_of_not_ge hcI
    have hJc : J ≤ c := J_le_max S s c I J hS hs c hIc.le le_rfl hJ
    have hcJ : c - J ≤ c - I := by
      have h2 : (c - J) * (S + s) = S * (c - I) := by linear_combination -hJ
      have : (c - J) * (S + s) ≤ (c - I) * (S + s) := by rw [h2]; nlinarith
      exact le_of_mul_le_mul_right this hSs
    have : I * (2 / 10 ^ 18) ≤ c * (2 / 10 ^ 18) := mul_le_mul_of_nonneg_right hIc.le (by norm_num)
    nlinarith

end XRPL.Model.SingleAssetVault.DilG
