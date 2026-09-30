import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts

/-! # Grid nesting for the downward `roundToExponent`

`roundToExponent p s .downward` is the largest multiple of `10^s` below `p` (or
`p` itself when `p` is already on a coarser grid). A result on a coarse grid lies
on every finer grid, so a coarser grid for the smaller input cannot overtake. -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

private lemma grid_refine (z : ℤ) (e s' : ℤ) (h : s' ≤ e) :
    ∃ z' : ℤ, (z : ℚ) * 10 ^ e = (z' : ℚ) * 10 ^ s' := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, e = s' + n := ⟨(e - s').toNat, by omega⟩
  refine ⟨z * 10 ^ n, ?_⟩
  rw [hn, zpow_add₀ (by norm_num), zpow_natCast]
  push_cast; ring

/-- Shape of a downward `roundToExponent` of a positive canonical IOU amount. -/
lemma rte_facts (value result : STAmount) (s : ℤ) (hc : value.IOUCanonical)
    (hpos : 0 < value.toRat) (hs_hi : s ≤ 80)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    0 ≤ result.toRat ∧ result.toRat ≤ value.toRat ∧
    (∀ s' ≤ s, ∃ z : ℤ, result.toRat = (z : ℚ) * 10 ^ s') ∧
    (result.mValue ≠ 0 → ∀ z : ℤ, (z : ℚ) * 10 ^ s ≤ value.toRat →
      (z : ℚ) * 10 ^ s ≤ result.toRat) := by
  have hint : ¬ value.integral = true := by
    unfold STAmount.integral; rw [hc.is_fractional]; decide
  have hnz : ¬ value.isZero = true := by
    unfold STAmount.isZero
    have := hc.mant_lo
    intro h
    have h0 : value.mValue = 0 := beq_iff_eq.mp h
    rw [h0] at this; simp at this
  have hs10 : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  by_cases hge : value.exponent ≥ s
  · have hres : result = value := by
      unfold STAmount.roundToExponent at hok
      rw [if_neg hint, if_neg hnz, if_pos hge] at hok
      exact (Except.ok.inj hok).symm
    subst hres
    refine ⟨le_of_lt hpos, le_refl _, ?_, fun _ _ h => h⟩
    intro s' hs'
    obtain ⟨z, hz⟩ := STAmount.exists_int_grid result
    obtain ⟨z', hz'⟩ := grid_refine z result.exponent s' (by omega)
    exact ⟨z', hz.trans hz'⟩
  · push_neg at hge
    have hlo : (-96 : ℤ) ≤ s := le_trans hc.exp_lo (le_of_lt hge)
    by_cases hm : result.mValue = 0
    · have h0 : result.toRat = 0 := by rw [STAmount.toRat_signed, hm]; simp
      refine ⟨by rw [h0], by rw [h0]; exact le_of_lt hpos, fun s' _ => ⟨0, by rw [h0]; simp⟩,
        fun h => absurd hm h⟩
    · have hr : result.toRat = (⌊value.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s :=
        STAmount.roundToExponent_rounded value result s .downward hc hlo hs_hi hm hok
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hr]
        have : (0 : ℤ) ≤ ⌊value.toRat / 10 ^ s⌋ := Int.floor_nonneg.mpr (by positivity)
        have : (0 : ℚ) ≤ (⌊value.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast this
        positivity
      · rw [hr]
        have h1 := Int.floor_le (value.toRat / 10 ^ s)
        calc (⌊value.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ value.toRat / 10 ^ s * 10 ^ s :=
              mul_le_mul_of_nonneg_right h1 (le_of_lt hs10)
          _ = value.toRat := by field_simp
      · intro s' hs'
        obtain ⟨z', hz'⟩ := grid_refine ⌊value.toRat / 10 ^ s⌋ s s' hs'
        exact ⟨z', hr.trans hz'⟩
      · intro _ z hz
        rw [hr]
        have hzle : (z : ℚ) ≤ value.toRat / 10 ^ s := by rw [le_div_iff₀ hs10]; exact hz
        have : z ≤ ⌊value.toRat / 10 ^ s⌋ := Int.le_floor.mpr hzle
        have : (z : ℚ) ≤ (⌊value.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast this
        exact mul_le_mul_of_nonneg_right this (le_of_lt hs10)

/-- **Grid nesting.** Rounding the smaller amount down onto a coarser grid never
overtakes rounding the larger one down onto a finer grid. -/
lemma rte_grid_mono (p₁ p₂ a₁ a₂ : STAmount) (s₁ s₂ : ℤ)
    (hc₁ : p₁.IOUCanonical) (hc₂ : p₂.IOUCanonical)
    (hp₁ : 0 < p₁.toRat) (hp₂ : 0 < p₂.toRat) (hle : p₁.toRat ≤ p₂.toRat)
    (hs : s₂ ≤ s₁) (hs₁ : s₁ ≤ 80) (hs₂ : s₂ ≤ 80)
    (h₁ : STAmount.roundToExponent p₁ s₁ .downward = .ok a₁)
    (h₂ : STAmount.roundToExponent p₂ s₂ .downward = .ok a₂)
    (ha₂ : a₂.mValue ≠ 0) : a₁.toRat ≤ a₂.toRat := by
  obtain ⟨_, hle₁, hgrid₁, _⟩ := rte_facts p₁ a₁ s₁ hc₁ hp₁ hs₁ h₁
  obtain ⟨_, _, _, hmax₂⟩ := rte_facts p₂ a₂ s₂ hc₂ hp₂ hs₂ h₂
  obtain ⟨z, hz⟩ := hgrid₁ s₂ hs
  rw [hz]
  exact hmax₂ ha₂ z (by rw [← hz]; linarith)

end XRPL.Model.SingleAssetVault.WdMono
