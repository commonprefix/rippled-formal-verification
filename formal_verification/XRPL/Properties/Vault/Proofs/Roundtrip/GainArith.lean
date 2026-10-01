import Mathlib.Tactic

/-! # Round-trip gain arithmetic

The redeemed shares' priced worth `Qw` is within the stage error of
`(S·I + s·c)/(S + s)`. On a fractional asset either it stays below `P + ½u`, or the charge
`c` sits within a fifth of a grid step of `P + ½u`. -/

namespace XRPL.Model.SingleAssetVault.RtT

/-- `Qw·(S + s) ≤ K·(S·I + s·c)` with `K` the product of the two stage factors. -/
lemma qw_bound (S s A c I A₁ Qw K : ℚ) (hs : 0 < s) (hSs : 0 < S + s)
    (hAsI : A * s = S * I) (hK : K = (1 + 1 / 10 ^ 18) * (1 + 1 / 10 ^ 17))
    (hA₁ : A₁ ≤ (1 + 1 / 10 ^ 18) * (A + c))
    (hQw : Qw ≤ A₁ * s / (S + s) * (1 + 1 / 10 ^ 17)) :
    Qw * (S + s) ≤ K * (S * I + s * c) := by
  have h1 : Qw * (S + s) ≤ A₁ * s * (1 + 1 / 10 ^ 17) := by
    have := mul_le_mul_of_nonneg_right hQw hSs.le
    calc Qw * (S + s) ≤ A₁ * s / (S + s) * (1 + 1 / 10 ^ 17) * (S + s) := this
      _ = A₁ * s * (1 + 1 / 10 ^ 17) := by field_simp
  have h2 : A₁ * s * (1 + 1 / 10 ^ 17) ≤ (1 + 1 / 10 ^ 18) * (A + c) * s * (1 + 1 / 10 ^ 17) := by
    have := mul_le_mul_of_nonneg_right hA₁ hs.le
    exact mul_le_mul_of_nonneg_right this (by norm_num)
  have h3 : (1 + 1 / 10 ^ 18) * (A + c) * s * (1 + 1 / 10 ^ 17) = K * (S * I + s * c) := by
    rw [hK]; linear_combination (1 + 1 / 10 ^ 18) * (1 + 1 / 10 ^ 17) * hAsI
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-- If both `I` and `c` are at most `B`, then `Qw ≤ K·B`. -/
lemma qw_le_max (S s I c Qw K B : ℚ) (hS : 0 ≤ S) (hs : 0 < s) (hK0 : 0 ≤ K)
    (hQw : Qw * (S + s) ≤ K * (S * I + s * c)) (hIB : I ≤ B) (hcB : c ≤ B) :
    Qw ≤ K * B := by
  have hSs : 0 < S + s := by linarith
  have h1 : S * I + s * c ≤ B * (S + s) := by
    have := mul_le_mul_of_nonneg_left hIB hS
    have := mul_le_mul_of_nonneg_left hcB hs.le
    linarith
  have h2 : Qw * (S + s) ≤ (K * B) * (S + s) := by
    have := mul_le_mul_of_nonneg_left h1 hK0
    linarith
  exact le_of_mul_le_mul_right h2 hSs

lemma gain_frac_arith (S s A c P u g I Qd A₁ Qw : ℚ)
    (hS : 0 ≤ S) (hs : 0 < s) (hA : 0 ≤ A) (hAsI : A * s = S * I)
    (hQd : |Qd - I| ≤ I * (2 / 10 ^ 18)) (hPQ : |P - Qd| ≤ 1 / 2 * u)
    (hcP : c ≤ P) (hc0 : 0 ≤ c)
    (hA₁ : A₁ ≤ (1 + 1 / 10 ^ 18) * (A + c))
    (hQw : Qw ≤ A₁ * s / (S + s) * (1 + 1 / 10 ^ 17))
    (hsum : A + P < 10 ^ 16 * g) (hu0 : 0 < u)
    (hPu : 10 ^ 15 * u ≤ P) (hPhi : P < 10 ^ 16 * u) :
    Qw < P + 1 / 2 * u ∨ (Qw < P + 3 / 2 * u ∧ P + u ≤ c + g) := by
  obtain ⟨W, hW⟩ : ∃ W : ℚ, W = P + 1 / 2 * u := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℚ, K = (1 + 1 / 10 ^ 18) * (1 + 1 / 10 ^ 17) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℚ, D = 1 - 2 / 10 ^ 18 := ⟨_, rfl⟩
  have hQd1 := abs_le.mp hQd
  have hPQ1 := abs_le.mp hPQ
  have hSs : 0 < S + s := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; norm_num
  have hKhi : K ≤ 1 + 111 / 10 ^ 19 := by rw [hK]; norm_num
  have hD0 : 0 < D := by rw [hD]; norm_num
  have hIpos : 0 < I := by
    by_contra h; replace h := not_lt.mp h
    have : I * (2 / 10 ^ 18) ≤ 0 := by nlinarith
    linarith
  have hIW : I * D ≤ W := by rw [hD, hW]; linarith
  have hQw' := qw_bound S s A c I A₁ Qw K hs hSs hAsI hK hA₁ hQw
  by_cases hcase : Qw < W
  · left; rw [← hW]; exact hcase
  right
  replace hcase := not_lt.mp hcase
  have hW0 : 0 ≤ W := by rw [hW]; linarith
  constructor
  · -- `Qw ≤ K·W/D < W + u`
    have hIB : I ≤ W / D := by rw [le_div_iff₀ hD0]; exact hIW
    have hcB : c ≤ W / D := by
      rw [le_div_iff₀ hD0]
      have : c * D ≤ c := by rw [hD]; nlinarith
      linarith [show c ≤ W by rw [hW]; linarith]
    have h1 := qw_le_max S s I c Qw K (W / D) hS hs hK0 hQw' hIB hcB
    have h2 : K * (W / D) * D = K * W := by field_simp
    have h3 : Qw * D ≤ K * W := by
      have := mul_le_mul_of_nonneg_right h1 hD0.le
      linarith
    have h4 : K * W ≤ (1 + 111 / 10 ^ 19) * W := mul_le_mul_of_nonneg_right hKhi hW0
    have h5 : W ≤ (10 ^ 16 + 1) * u := by rw [hW]; linarith
    have e6 : (P + 3 / 2 * u) * D = (W + u) * (1 - 2 / 10 ^ 18) := by rw [hD, hW]; ring
    have h6 : Qw * D < (P + 3 / 2 * u) * D := by rw [e6]; linarith
    exact lt_of_mul_lt_mul_right h6 hD0.le
  · -- the charge is within `2·10⁻¹⁷·(A + c)` of `W`
    have hmain : W * (S + s) ≤ K * (S * I + s * c) :=
      le_trans (mul_le_mul_of_nonneg_right hcase hSs.le) hQw'
    have hSI : S * I * D ≤ S * W := by
      have := mul_le_mul_of_nonneg_left hIW hS; linarith
    -- `s·(W·D - K·c·D) ≤ S·W·(K - D)`
    have h1 : s * (W * D - K * c * D) ≤ S * W * (K - D) := by
      have e1 : W * (S + s) * D ≤ K * (S * I + s * c) * D :=
        mul_le_mul_of_nonneg_right hmain hD0.le
      have e2 : K * (S * I * D) ≤ K * (S * W) := mul_le_mul_of_nonneg_left hSI hK0
      have e3 : K * (S * I + s * c) * D = K * (S * I * D) + K * s * c * D := by ring
      have e4 : s * (W * D - K * c * D) = W * (S + s) * D - S * W * D - K * s * c * D := by ring
      have e5 : S * W * (K - D) = K * (S * W) - S * W * D := by ring
      rw [e4, e5]; linarith
    have hκ : 0 ≤ K - D := by rw [hK, hD]; norm_num
    -- multiply by `I` and use `S·I = A·s`
    have h2 : W * D - K * c * D ≤ A * W * (K - D) / I := by
      rw [le_div_iff₀ hIpos]
      have e1 : I * (s * (W * D - K * c * D)) ≤ I * (S * W * (K - D)) :=
        mul_le_mul_of_nonneg_left h1 hIpos.le
      have e2 : I * (S * W * (K - D)) = s * (A * W * (K - D)) := by
        linear_combination (W * (K - D)) * hAsI.symm
      have e3 : s * ((W * D - K * c * D) * I) ≤ s * (A * W * (K - D)) := by
        rw [e2] at e1; linarith
      exact le_of_mul_le_mul_left e3 hs
    -- `W ≤ ρ·I`
    have hu : u * (10 ^ 15 - 1 / 2) ≤ I * (1 + 2 / 10 ^ 18) := by linarith
    have hWI : W ≤ I * ((1 + 2 / 10 ^ 18) * (1 + 1 / (10 ^ 15 - 1 / 2))) := by
      have hu' : u ≤ I * (1 + 2 / 10 ^ 18) / (10 ^ 15 - 1 / 2) := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      have e : I * ((1 + 2 / 10 ^ 18) * (1 + 1 / (10 ^ 15 - 1 / 2))) =
          I * (1 + 2 / 10 ^ 18) + I * (1 + 2 / 10 ^ 18) / (10 ^ 15 - 1 / 2) := by ring
      rw [e, hW]; linarith
    have h3 : A * W * (K - D) / I ≤ A * ((1 + 2 / 10 ^ 18) * (1 + 1 / (10 ^ 15 - 1 / 2))) * (K - D) := by
      rw [div_le_iff₀ hIpos]
      have e1 : A * W ≤ A * (I * ((1 + 2 / 10 ^ 18) * (1 + 1 / (10 ^ 15 - 1 / 2)))) :=
        mul_le_mul_of_nonneg_left hWI hA
      have e2 := mul_le_mul_of_nonneg_right e1 hκ
      linarith
    have hρ : ((1 + 2 / 10 ^ 18) * (1 + 1 / (10 ^ 15 - 1 / 2))) * (K - D) ≤ 2 / 10 ^ 17 * D := by
      rw [hK, hD]; norm_num
    have h4 : A * ((1 + 2 / 10 ^ 18) * (1 + 1 / (10 ^ 15 - 1 / 2))) * (K - D) ≤ A * (2 / 10 ^ 17 * D) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hρ hA
    -- `(W - K·c)·D ≤ 2·10⁻¹⁷·A·D`, so `W - c ≤ 2·10⁻¹⁷·(A + c)`
    have h5 : (W - K * c) * D ≤ (A * (2 / 10 ^ 17)) * D := by
      have : (W - K * c) * D = W * D - K * c * D := by ring
      rw [this]; linarith
    have h6 : W - K * c ≤ A * (2 / 10 ^ 17) := le_of_mul_le_mul_right h5 hD0
    have h7 : K * c ≤ (1 + 111 / 10 ^ 19) * c := mul_le_mul_of_nonneg_right hKhi hc0
    have h8 : W - c ≤ 2 / 10 ^ 17 * (A + c) := by linarith
    rw [hW] at h8
    linarith

end XRPL.Model.SingleAssetVault.RtT
