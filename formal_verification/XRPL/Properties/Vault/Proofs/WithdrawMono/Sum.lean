import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.WithdrawMono.Add
import XRPL.Properties.Vault.Proofs.WithdrawMono.Exponent

/-! # The post-sum exponent is antitone in the subtracted amount

`numberExponent (x + y) ` for `x > 0` and `y < 0`: a more negative `y` never
raises the stored exponent. The only place the rounded sum could invert is a
single Number cell; an exponent jump there needs the carry point inside the cell,
where the sum rounds to nearest. -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

private lemma normalized_of_mant (m : UInt64) (j : ℤ) (hlo : 10 ^ 18 ≤ m.toNat)
    (hhi : m.toNat ≤ 9999999999999999999) (h10 : m.toNat % 10 = 0)
    (hj_lo : minExponent ≤ j) (hj_hi : j ≤ maxExponent) :
    (⟨false, m, j⟩ : Number).isNormalized := by
  right
  refine ⟨?_, ?_, Or.inr h10, hj_lo, hj_hi⟩
  · show largeRange.min ≤ m
    rw [UInt64.le_iff_toNat_le]
    exact le_trans (by decide) hlo
  · show m ≤ largeRange.max
    rw [UInt64.le_iff_toNat_le]
    exact le_trans hhi (by decide)

private lemma toRat_mk (m : UInt64) (j : ℤ) :
    (⟨false, m, j⟩ : Number).toRat = (m.toNat : ℚ) * 10 ^ j :=
  Number.toRat_of_nonneg _ rfl

/-- **Post-sum exponent antitone.** For `x > 0` fixed and `y₂ ≤ y₁ < 0` with
`x + y₂ ≥ 0`, the stored exponent of the rounded `x + y₂` is at most that of
`x + y₁`. -/
lemma sum_exp_anti (x y₁ y₂ s₁ s₂ : Number)
    (hx : x.isNormalized) (hy₁ : y₁.isNormalized) (hy₂ : y₂.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hy₁m : y₁.mantissa_ ≠ 0) (hy₂m : y₂.mantissa_ ≠ 0)
    (hxneg : x.negative_ = false) (hy₁neg : y₁.negative_ = true) (hy₂neg : y₂.negative_ = true)
    (hle : y₂.toRat ≤ y₁.toRat) (hnn : 0 ≤ x.toRat + y₂.toRat)
    (hok₁ : Number.operator_add x y₁ .to_nearest = .ok s₁)
    (hok₂ : Number.operator_add x y₂ .to_nearest = .ok s₂)
    (e₁ e₂ : ℤ) (he₁ : numberExponent s₁ .fractional = .ok e₁)
    (he₂ : numberExponent s₂ .fractional = .ok e₂) :
    e₂ ≤ e₁ := by
  have hpeel : ∀ (s : Number) (e : ℤ), numberExponent s .fractional = .ok e →
      ∃ r : STAmount, STAmount.ofNumber .fractional s .to_nearest = .ok r ∧ r.exponent = e := by
    intro s e he
    unfold numberExponent at he
    cases hr : STAmount.ofNumber .fractional s .to_nearest with
    | error err => rw [hr] at he; exact absurd he (by simp [bind, Except.bind])
    | ok r =>
      rw [hr] at he
      exact ⟨r, rfl, Except.ok.inj he⟩
  obtain ⟨r₁, hr₁, rfl⟩ := hpeel s₁ e₁ he₁
  obtain ⟨r₂, hr₂, rfl⟩ := hpeel s₂ e₂ he₂
  by_contra hlt
  push_neg at hlt
  set t₁ := x.toRat + y₁.toRat with ht₁
  set t₂ := x.toRat + y₂.toRat with ht₂
  have ht : t₂ ≤ t₁ := by rw [ht₁, ht₂]; linarith
  have hs₁n : s₁.isNormalized := operator_add_isNormalized_to_nearest' x y₁ s₁ hx hy₁ hok₁
  have hs₂n : s₂.isNormalized := operator_add_isNormalized_to_nearest' x y₂ s₂ hx hy₂ hok₂
  have hs₁nn : 0 ≤ s₁.toRat := operator_add_nonneg x y₁ s₁ hx hy₁ hok₁ (le_trans hnn ht)
  have hs₂nn : 0 ≤ s₂.toRat := operator_add_nonneg x y₂ s₂ hx hy₂ hok₂ hnn
  have hc₁ := exp_cases s₁ r₁ hr₁
  have hc₂ := exp_cases s₂ r₂ hr₂
  set j := r₂.exponent - 4 with hj
  have hj_lo : -100 ≤ j := by omega
  have hj_hi : j ≤ 76 := by omega
  have hC₂ : carryPt j ≤ s₂.toRat :=
    (exp_ge_iff s₂ r₂ hs₂n hs₂nn hr₂ j hj_lo).mp (by omega)
  have hC₁ : s₁.toRat < carryPt j := by
    by_contra h
    push_neg at h
    have := (exp_ge_iff s₁ r₁ hs₁n hs₁nn hr₁ j hj_lo).mpr h
    omega
  -- the carry point and its lower grid neighbour
  have hmin : minExponent ≤ j := by unfold minExponent; omega
  have hmax : j ≤ maxExponent := by unfold maxExponent; omega
  have hJ := normalized_of_mant 9999999999999999500 j (by decide) (by decide) (by decide) hmin hmax
  have hM := normalized_of_mant 9999999999999999490 j (by decide) (by decide) (by decide) hmin hmax
  have hJv : (⟨false, 9999999999999999500, j⟩ : Number).toRat = carryPt j := by
    rw [toRat_mk, carryPt, show (9999999999999999500 : UInt64).toNat = 9999999999999999500 from rfl]
    norm_num
  have hMv : (⟨false, 9999999999999999490, j⟩ : Number).toRat
      = (9999999999999999490 : ℚ) * 10 ^ j := by
    rw [toRat_mk, show (9999999999999999490 : UInt64).toNat = 9999999999999999490 from rfl]
    norm_num
  have hj0 : (0 : ℚ) < 10 ^ j := zpow_pos (by norm_num) _
  have hMJ : (9999999999999999490 : ℚ) * 10 ^ j < carryPt j := by
    rw [carryPt]; nlinarith
  -- run 1 truth below the carry point, run 2 truth above its neighbour
  have ht₁J : t₁ < carryPt j := by
    by_contra h
    push_neg at h
    have := operator_add_ge_of_ge_normalized x y₁ s₁ _ hx hy₁ hok₁ hJ (by rw [hJv]; exact h)
    rw [hJv] at this
    linarith
  have ht₂M : (9999999999999999490 : ℚ) * 10 ^ j < t₂ := by
    by_contra h
    push_neg at h
    have := operator_add_le_of_le_normalized x y₂ s₂ _ hx hy₂ hok₂ hM (by rw [hMv]; exact h)
    rw [hMv] at this
    linarith
  have hs₁M : (9999999999999999490 : ℚ) * 10 ^ j ≤ s₁.toRat := by
    have := operator_add_ge_of_ge_normalized x y₁ s₁ _ hx hy₁ hok₁ hM
      (by rw [hMv]; linarith)
    rwa [hMv] at this
  have hMpos : (0 : ℚ) < (9999999999999999490 : ℚ) * 10 ^ j := by positivity
  have hmne : ∀ s : Number, 0 < s.toRat → s.mantissa_ ≠ 0 := fun s hs h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero s h0] at hs; exact lt_irrefl _ hs
  have hnz : ∀ y : Number, 0 < x.toRat + y.toRat → ¬ x.operator_eq y.operator_neg := by
    intro y hpos heq
    have hxy : x = y.operator_neg := by
      unfold Number.operator_eq at heq
      simp only [Bool.and_eq_true, beq_iff_eq] at heq
      obtain ⟨⟨h1, h2⟩, h3⟩ := heq
      cases x; cases hyn : y.operator_neg
      rw [hyn] at h1 h2 h3
      simp_all
    rw [hxy, Number.toRat_neg] at hpos
    linarith
  have hdiff₁ : x.negative_ ≠ y₁.negative_ := by rw [hxneg, hy₁neg]; decide
  have hdiff₂ : x.negative_ ≠ y₂.negative_ := by rw [hxneg, hy₂neg]; decide
  have hn₁ := add_nearestTo_below_carry x y₁ s₁ hx hy₁ hxm hy₁m hdiff₁
    (hnz y₁ (by linarith)) hok₁ (hmne s₁ (by linarith)) j (by linarith) (by rw [← carryPt]; exact ht₁J)
  have hn₂ := add_nearestTo_below_carry x y₂ s₂ hx hy₂ hxm hy₂m hdiff₂
    (hnz y₂ (by linarith)) hok₂ (hmne s₂ (by linarith)) j ht₂M (by rw [← carryPt]; linarith)
  have hmono := round_mono_core t₂ t₁ s₂ s₁ hn₂ hn₁ hs₂n hs₁n ht (fun heq => by
    have hyy : y₂.toRat = y₁.toRat := by rw [ht₁, ht₂] at heq; linarith
    have := hy₂.toRat_inj hy₁ hyy
    subst this
    rw [Except.ok.inj (hok₂.symm.trans hok₁)])
  linarith

end XRPL.Model.SingleAssetVault.WdMono
