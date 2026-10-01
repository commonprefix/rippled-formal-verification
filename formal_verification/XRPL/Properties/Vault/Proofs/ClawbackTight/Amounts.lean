import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Vault.Proofs.Support.FracCanon
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Vault.Common.STAmountToNumber
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight

/-! # Amounts whose `toNumber` is value-exact -/

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

/-- Every successful `toNumber` of `s` is normalized and value-exact. -/
def NumExact (s : STAmount) : Prop :=
  ∀ n, s.toNumber .to_nearest = .ok n → n.isNormalized ∧ n.toRat = s.toRat

lemma numExact_of_canonical (s : STAmount) (hc : s.Canonical) : NumExact s := by
  intro n hn
  obtain ⟨sn, h1, h2, h3⟩ := STAmount.toNumber_canonical_exact s .to_nearest hc
  obtain rfl := Except.ok.inj (h1.symm.trans hn)
  exact ⟨h3, h2⟩

lemma numExact_of_fczr (s : STAmount) (h : STAmount.FracCanonZero s) : NumExact s := by
  intro n hn
  rcases h.2 with hc | hz
  · obtain ⟨sn, h1, h2, h3⟩ := STAmount.toNumber_iou_exact s .to_nearest hc
    obtain rfl := Except.ok.inj (h1.symm.trans hn)
    exact ⟨h3, h2⟩
  · rw [STAmount.toNumber_zero_eq s _ n hz hn, Number.toRat_zero,
      (STAmount.toRat_eq_zero_iff s).mpr hz]
    exact ⟨Or.inl rfl, rfl⟩

lemma numExact_of_integral (s : STAmount) (hint : s.mNumericType.isIntegral = true)
    (hoff : s.mOffset = 0) (hval : s.mValue.toNat ≤ maxRep.toNat) : NumExact s := by
  intro n hn
  obtain ⟨sn, h1, h2, h3, -⟩ := STAmount.toNumber_integral_exact' s .to_nearest hint hoff hval
  obtain rfl := Except.ok.inj (h1.symm.trans hn)
  exact ⟨h3, h2⟩

lemma fractional_of_not_integral (nt : NumericType) (h : ¬ nt.isIntegral = true) :
    nt = .fractional := by
  cases nt with
  | fractional => rfl
  | integral => exact absurd rfl h

/-- An `ofNumber` output of a normalized `Number` has a value-exact `toNumber`. -/
lemma numExact_of_ofNumber (nt : NumericType) (n : Number) (mode : rounding_mode) (a : STAmount)
    (hn : n.isNormalized) (h : STAmount.ofNumber nt n mode = .ok a) : NumExact a := by
  by_cases hint : nt.isIntegral = true
  · obtain ⟨h1, h2, h3⟩ := STAmount.ofNumber_integral_facts nt n mode a hint h
    exact numExact_of_integral a (by rw [h1]; exact hint) h2 h3
  · have hfr := fractional_of_not_integral nt hint
    subst hfr
    exact numExact_of_fczr a (STAmount.ofNumber_frac_fczr n mode a (fun _ => hn) h)

/-- `ofNumber` of a non-negative normalized `Number` is non-negative. -/
lemma ofNumber_nonneg (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) : 0 ≤ result.toRat := by
  by_cases hint : nt.isIntegral = true
  · unfold STAmount.ofNumber at hok
    simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hint] at hok
    cases hr : n.to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok intValue =>
      rw [hr] at hok
      simp only [] at hok
      obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n mode intValue hneg hr
      have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep intValue hnn hle
      have hres_val : result.toRat = (intValue.toInt : ℚ) := by
        have hexact := STAmount.canonicalize_integral_toRat
          (STAmount.unchecked nt intValue.toUInt64 0 false) result mode
          (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint) rfl
          hval hok
        rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
        show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
        rw [toUInt64_toNat_of_nonneg intValue hnn]
      rw [hres_val]; exact_mod_cast hnn
  · have hnt_frac := fractional_of_not_integral nt hint
    by_cases hz : result.mValue = 0
    · rw [STAmount.toRat_signed, hz]; simp
    · have hn_ne : n.mantissa_ ≠ 0 :=
        STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result hnt_frac hok hz
      obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
      have hexp_lo : minExponent ≤ n.exponent_ := by
        rcases hn with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
        · exact hlo
      have hok' : STAmount.ofNumber .fractional n mode = .ok result := by rw [← hnt_frac]; exact hok
      have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
        (STAmount.ofNumber_iou_ok_facts n mode result hlo19 hhi19 hexp_lo hok' hz).2
      obtain ⟨mant, exp, -, hval, -, hcast, -, -, -, -⟩ :=
        STAmount.ofNumber_iou_snap_pos nt n mode result hnt_frac hneg
          hlo19 hhi19 hexp_lo hexp_hi hok hz
      rw [hval, hcast]; positivity

end XRPL.Model.SingleAssetVault.ClwTight
