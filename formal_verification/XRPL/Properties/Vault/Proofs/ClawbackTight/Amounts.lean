import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
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
  obtain ⟨sn, h1, h2, h3, -⟩ := STAmount.toNumber_offset_zero_exact s .to_nearest hint hoff hval
  obtain rfl := Except.ok.inj (h1.symm.trans hn)
  exact ⟨h3, h2⟩

lemma fractional_of_not_integral (nt : NumericType) (h : ¬ nt.isIntegral = true) :
    nt = .fractional := by
  cases nt with
  | fractional => rfl
  | integral => exact absurd rfl h

/-- An `ofNumber` output of a normalized `Number` has a value-exact `toNumber`. -/
lemma numExact_of_ofNumber (nt : NumericType) (n : Number) (mode : rounding_mode) (a : STAmount)
    (h : STAmount.ofNumber nt n mode = .ok a) : NumExact a := by
  by_cases hint : nt.isIntegral = true
  · obtain ⟨h1, h2, h3⟩ := STAmount.ofNumber_integral_facts nt n mode a hint h
    exact numExact_of_integral a (by rw [h1]; exact hint) h2 h3
  · have hfr := fractional_of_not_integral nt hint
    subst hfr
    exact numExact_of_fczr a (STAmount.ofNumber_fractional_fczr n mode a h)

end XRPL.Model.SingleAssetVault.ClwTight
