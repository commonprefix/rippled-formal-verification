import XRPL.Properties.Vault.Proofs.ExactUpdates.Clamp
import XRPL.Properties.Vault.Proofs.Support.NumberFacts

/-! # Pricing signs, the integral total bound, and the exact update step -/

namespace XRPL.Model.SingleAssetVault.Exact

open XRPL.Model.Protocol

/-- The withdraw net asset value is normalized and nonnegative. -/
lemma nav_nonneg (v : Vault) (w : Bool) (nav : Number)
    (hsub : v.assetsTotal.operator_sub (match w with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok nav) :
    nav.isNormalized ∧ 0 ≤ nav.toRat := by
  cases w
  · exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm
        v.wf.lossUnrealized_norm hsub,
      Number.RoundsToRepresentable.nonneg_of_nonneg nav _
        (operator_sub_rounded_to_nearest _ _ nav v.wf.assetsTotal_norm v.wf.lossUnrealized_norm hsub)
        (by have := v.exact.withdraw_nav_nonneg; simpa [RawVault.toExact] using this)⟩
  · exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub,
      Number.RoundsToRepresentable.nonneg_of_nonneg nav _
        (operator_sub_rounded_to_nearest _ _ nav v.wf.assetsTotal_norm (Or.inl rfl) hsub)
        (by have := v.exact.assetsTotal_nonneg; simpa [RawVault.toExact, Number.toRat_zero] using this)⟩

/-- `nav_nonneg` with the loss term given explicitly. -/
lemma nav_nonneg' (v : Vault) (L nav : Number) (hL : L = Number.zero ∨ L = v.lossUnrealized)
    (hsub : v.assetsTotal.operator_sub L .to_nearest = .ok nav) :
    nav.isNormalized ∧ 0 ≤ nav.toRat := by
  rcases hL with rfl | rfl
  · exact nav_nonneg v true nav hsub
  · exact nav_nonneg v false nav hsub

/-- The priced payout of nonnegative, exactly-convertible shares: nonnegative, of the
vault's type, canonical when fractional and nonzero, and exactly convertible. -/
lemma price_facts (v : Vault) (w : Bool) (s p : STAmount)
    (hs : ∀ sn, s.toNumber .to_nearest = .ok sn → sn.isNormalized ∧ sn.toRat = s.toRat)
    (hnn : 0 ≤ s.toRat)
    (hok : v.sharesToAssetsWithdraw s w = .ok p) :
    0 ≤ p.toRat ∧ p.mNumericType = v.numericType ∧
    (v.numericType.isIntegral = false → p.mValue ≠ 0 → p.IOUCanonical) ∧
    (∀ pn, p.toNumber .to_nearest = .ok pn → pn.isNormalized ∧ pn.toRat = p.toRat) := by
  obtain ⟨nav, hsub, hcase⟩ := WdMono.price_reduces v s p w hok
  obtain ⟨hnavn, hnav0⟩ := nav_nonneg v w nav hsub
  rcases hcase with ⟨_, rfl⟩ | ⟨_, sn, NV, aN, hsn, hmul, hdiv, hof⟩
  · have hz : (STAmount.zero v.numericType).mValue = 0 := STAmount.zero_mValue _
    have hnt : (STAmount.zero v.numericType).mNumericType = v.numericType :=
      STAmount.zero_mNumericType _
    refine ⟨by rw [STAmount.toRat_eq_zero_of_mValue_zero _ hz], hnt, fun _ h => absurd hz h, ?_⟩
    intro pn hpn
    by_cases hint : v.numericType.isIntegral = true
    · obtain ⟨sn, hsn, hval, hnorm, _⟩ := STAmount.toNumber_offset_zero_exact _ .to_nearest
        (by rw [hnt]; exact hint) (WdAcc.zero_mOffset _ hint) (by rw [hz]; exact Nat.zero_le _)
      rw [Except.ok.inj (hpn.symm.trans hsn)]; exact ⟨hnorm, hval⟩
    · rw [STAmount.toNumber_zero_fractional _ .to_nearest
        (by show (STAmount.zero _).mNumericType.isIntegral = false; rw [hnt]; simpa using hint)
        hz] at hpn
      rw [← Except.ok.inj hpn, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero _ hz]
      exact ⟨Or.inl rfl, rfl⟩
  · obtain ⟨hsnn, hsnv⟩ := hs sn hsn
    have hNVn := WdMono.mul_norm nav sn NV hnavn hsnn hmul
    have hNV0 : 0 ≤ NV.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg NV _
      (operator_mul_rounded_to_nearest nav sn NV hnavn hsnn hmul)
      (mul_nonneg hnav0 (by rw [hsnv]; exact hnn))
    have haNn := WdMono.div_norm NV v.sharesTotal aN hNVn v.wf.sharesTotal_norm hdiv
    have haN0 : 0 ≤ aN.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg aN _
      (operator_div_rounded_to_nearest NV v.sharesTotal aN hNVn v.wf.sharesTotal_norm hdiv)
      (div_nonneg hNV0 v.wf.sharesTotal_nonneg)
    exact WdMono.ofNumber_facts v.numericType aN p haNn haN0 hof

/-- Shares computed from a nonnegative, exactly-convertible asset amount are
nonnegative. -/
lemma shares_nonneg (v : Vault) (X sd : STAmount) (w : Bool)
    (hX : ∀ xn, X.toNumber .to_nearest = .ok xn → xn.isNormalized ∧ 0 ≤ xn.toRat)
    (h : assetsToSharesWithdraw v X true w = .ok sd) : 0 ≤ sd.toRat := by
  cases w <;> simp only [assetsToSharesWithdraw, bind, Except.bind, pure, Except.pure] at h <;>
    walk_ok
  all_goals first
    | (rw [STAmount.toRat_eq_zero_of_mValue_zero _ (STAmount.zero_mValue _)])
    | skip
  all_goals
    have hN := ‹v.assetsTotal.operator_sub _ .to_nearest = .ok _›
    obtain ⟨hnavn, hnav0⟩ := nav_nonneg' v _ _ (by first | exact Or.inl rfl | exact Or.inr rfl) hN
    obtain ⟨hxn, hx0⟩ := hX _ ‹X.toNumber _ = _›
    have hmul := ‹Number.operator_mul v.sharesTotal _ _ = _›
    have hdiv := ‹Number.operator_div _ _ _ = _›
    have hMn := WdMono.mul_norm _ _ _ v.wf.sharesTotal_norm hxn hmul
    have hM0 := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
      (operator_mul_rounded_to_nearest _ _ _ v.wf.sharesTotal_norm hxn hmul)
      (mul_nonneg v.wf.sharesTotal_nonneg hx0)
    have hDn := WdMono.div_norm _ _ _ hMn hnavn hdiv
    have hD0 := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
      (operator_div_rounded_to_nearest _ _ _ hMn hnavn hdiv) (div_nonneg hM0 hnav0)
    obtain ⟨htv, htn⟩ := Number.truncate_floor _ _ hDn
      (Number.negative_false_of_nonneg _ hDn hD0) ‹Number.truncate _ = _›
    rename_i t _ _
    by_cases htm : t.mantissa_ = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero _
        (WdMono.ofNumber_mant0 _ _ _ _ htm ‹STAmount.ofNumber _ t _ = _›)]
    · have ht0 : 0 ≤ t.toRat := by rw [htv]; exact_mod_cast Int.floor_nonneg.mpr hD0
      exact (WdMono.ofNumber_facts _ t sd (htn htm) ht0 ‹STAmount.ofNumber _ t _ = _›).1

/-- An integral pack of a nonnegative total bounds it below `2^63`. -/
lemma total_fit (nt : NumericType) (hint : nt.isIntegral = true) (T : Number) (atr : STAmount)
    (hT : T.isNormalized) (hT0 : 0 ≤ T.toRat)
    (hok : STAmount.ofNumber nt T .to_nearest = .ok atr) : T.toRat < 2 ^ 63 := by
  have hnegf : T.negative_ = false := Number.negative_false_of_nonneg T hT hT0
  have hsig : decide (T.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hnegf
  unfold STAmount.ofNumber at hok
  rw [hsig] at hok
  simp only [Bool.false_eq_true, hint, ↓reduceIte] at hok
  cases hrep : T.to_rep .to_nearest with
  | error e => rw [hrep] at hok; simp at hok
  | ok rv =>
    have h1 := to_rep_within_one T .to_nearest rv hT hrep
    have h2 := (Number.to_rep_nonneg_range T .to_nearest rv hnegf hrep).2
    rw [maxRep_val] at h2
    have h2' : (rv.toInt : ℚ) ≤ 9223372036854775807 := by exact_mod_cast h2
    have := (abs_lt.mp h1).1
    linarith

/-- **The exact update step.** Subtracting a gridded payout `0 ≤ a ≤ A ≤ T` from both
stored totals is exact. -/
lemma updates_exact (T A an at' av' : Number) (a : ℚ)
    (hT : T.isNormalized) (hA : A.isNormalized) (hAT : A.toRat ≤ T.toRat)
    (han : an.isNormalized) (hanv : an.toRat = a) (ha0 : 0 ≤ a) (haA : a ≤ A.toRat)
    (hg : GridNear T a)
    (hat : T.operator_sub an .to_nearest = .ok at')
    (hav : A.operator_sub an .to_nearest = .ok av') :
    at'.toRat = T.toRat - a ∧ av'.toRat = A.toRat - a := by
  obtain ⟨s, j, hs1, hs2, hj, hnear⟩ := hg
  have hs : minExponent + 37 ≤ s := by unfold minExponent; omega
  have hs' : s ≤ maxExponent := by unfold maxExponent; omega
  subst hanv
  refine ⟨sub_exact_grid T an at' s j hT han ha0 (le_trans haA hAT) hj hs hs'
      (fun _ h => hnear h) hat,
    sub_exact_grid A an av' s j hA han ha0 haA hj hs hs' (fun hpos h => ?_) hav⟩
  have hAe := exponent_le_of_le A T hA hT (lt_of_lt_of_le hpos haA) hAT
  have := hnear (le_trans h hAe)
  linarith

end XRPL.Model.SingleAssetVault.Exact
