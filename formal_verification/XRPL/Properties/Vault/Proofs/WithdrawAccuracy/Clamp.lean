import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Price

/-! # Shape of the fractional `clampToSumExponent` output -/

namespace XRPL.Model.SingleAssetVault.WdAcc

open XRPL.Model.Protocol

/-- `toNumber` of a fractional canonical-or-zero amount is normalized. -/
lemma toNumber_fczr_norm (s : STAmount) (mode : rounding_mode) (n : Number)
    (h : STAmount.FracCanonZero s) (hok : s.toNumber mode = .ok n) : n.isNormalized := by
  rcases h.2 with hc | hz
  · obtain ⟨sn, hsn, -, hsnn⟩ := STAmount.toNumber_iou_exact s mode hc
    rw [show n = sn from Except.ok.inj (hok.symm.trans hsn)]; exact hsnn
  · rw [STAmount.toNumber_zero_eq s mode n hz hok]; exact Or.inl rfl

open private sumAndRoundToExponent from XRPL.Model.Protocol.Rounding in
/-- The fractional clamp keeps a canonical-or-zero amount canonical-or-zero. -/
lemma clamp_frac_shape (amount : Number) (d r : STAmount)
    (hd : STAmount.FracCanonZero d) (hok : clampToSumExponent amount d = .ok r) : STAmount.FracCanonZero r := by
  have hint : d.integral = false := by show d.mNumericType.isIntegral = false; rw [hd.1]; rfl
  unfold clampToSumExponent at hok
  simp only [hint, sumAndRoundToExponent, bind, Except.bind, pure, Except.pure] at hok
  have hnt : d.numericType = .fractional := hd.1
  walk_ok
  · exact absurd ‹false = true› (by decide)
  · exact STAmount.roundToExponent_fczr _ _ _ _ (STAmount.operator_neg_fczr d hd) ‹_›
  · have hdn := toNumber_fczr_norm d _ _ hd ‹d.toNumber _ = _›
    have hs2 := STAmount.ofNumber_fractional_fczr _ _ _
      (hnt ▸ ‹STAmount.ofNumber d.numericType _ .downward = _›)
    have hs3 := STAmount.roundToExponent_fczr _ _ _ _ hs2 ‹STAmount.roundToExponent _ _ _ = _›
    have hsumn := toNumber_fczr_norm _ _ _ hs3 ‹STAmount.toNumber _ .downward = _›
    exact STAmount.ofNumber_fractional_fczr _ _ r
      (hnt ▸ ‹STAmount.ofNumber d.numericType _ .to_nearest = _›)

/-- On a fractional vault the priced payout of canonical shares is canonical-or-zero. -/
lemma price_fczr (v : Vault) (sh p : STAmount) (w : Bool)
    (hfr : v.numericType = .fractional) (hc : sh.Canonical)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) : STAmount.FracCanonZero p := by
  obtain ⟨sn0, hsn0, -, hsnn⟩ := STAmount.toNumber_exact_canonical sh .to_nearest
    (STAmount.Canonical.exactCanonical sh hc)
  have hlu : (match w with
      | true => Number.zero
      | false => v.lossUnrealized).isNormalized := by
    cases w
    · exact v.wf.lossUnrealized_norm
    · exact Or.inl rfl
  cases w <;> simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at hok
    <;> walk_ok
  all_goals first
    | exact ⟨by rw [STAmount.zero_mNumericType, hfr], Or.inr (STAmount.zero_mValue _)⟩
    | skip
  all_goals
    have hnavn := operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm hlu
      ‹v.assetsTotal.operator_sub _ _ = _›
    obtain rfl := Except.ok.inj (hsn0.symm.trans ‹sh.toNumber _ = _›)
    have hmul := ‹Number.operator_mul _ sn0 _ = _›
    have hdiv := ‹Number.operator_div _ v.sharesTotal _ = _›
    exact STAmount.ofNumber_fractional_fczr _ _ p (hfr ▸ ‹STAmount.ofNumber v.numericType _ _ = _›)

/-- `toNumber` is value-exact and normalized on the clamped payout. -/
lemma payout_toNumber (v : Vault) (sh p b : STAmount) (w : Bool) (n : Number)
    (hc : sh.Canonical) (hp : v.sharesToAssetsWithdraw sh w = .ok p)
    (hcl : clampToSumExponent v.assetsTotal p.operator_neg = .ok b)
    (hn : b.toNumber .to_nearest = .ok n) : n.isNormalized ∧ n.toRat = b.toRat := by
  by_cases hint : v.numericType.isIntegral = true
  · obtain ⟨hpnt, hpoff, hpmv⟩ := price_integral_shape v _ _ _ hint hp
    have hcint : p.integral = true := by
      show p.mNumericType.isIntegral = true; rw [hpnt]; exact hint
    obtain ⟨hbnt, hboff, hbmv, -⟩ := clamp_integral _ _ _ hcint hcl
    obtain ⟨sn, hsn, hsnv, hsnn, -⟩ := STAmount.toNumber_offset_zero_exact b .to_nearest
      (by rw [hbnt, hpnt]; exact hint) (by rw [hboff, hpoff]) (by rw [hbmv]; exact hpmv)
    obtain rfl := Except.ok.inj (hsn.symm.trans hn)
    exact ⟨hsnn, hsnv⟩
  · have hfr : v.numericType = .fractional := by
      cases h : v.numericType with
      | fractional => rfl
      | integral => rw [h] at hint; exact absurd rfl hint
    have hb := clamp_frac_shape _ _ _
      (STAmount.operator_neg_fczr _ (price_fczr v sh p w hfr hc hp)) hcl
    rcases hb.2 with hbc | hbz
    · obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact b .to_nearest hbc
      obtain rfl := Except.ok.inj (hsn.symm.trans hn)
      exact ⟨hsnn, hsnv⟩
    · rw [STAmount.toNumber_zero_eq b _ n hbz hn, Number.toRat_zero,
        (STAmount.toRat_eq_zero_iff b).mpr hbz]
      exact ⟨Or.inl rfl, rfl⟩

end XRPL.Model.SingleAssetVault.WdAcc
