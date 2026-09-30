import XRPL.Properties.Vault.Proofs.Support.ComputeWithdraw
import XRPL.Properties.Vault.Proofs.WithdrawMono.Price
import XRPL.Properties.Vault.Proofs.WithdrawMono.Sum
import XRPL.Properties.Vault.Proofs.WithdrawMono.Zero

/-! # Withdraw payout monotonicity

The recorded payout is `clampToSumExponent assetsTotal (−priced)`. Pricing is
monotone in the burned shares; on an integral asset the clamp is the identity; on a
fractional one it rounds `priced` down onto the grid of the post-sum total, whose
exponent only drops as `priced` grows (`WdMono.sum_exp_anti`), and a coarser grid
for the smaller payout cannot overtake (`WdMono.rte_grid_mono`). -/

namespace XRPL.Model.SingleAssetVault.WdMono

open XRPL.Model.Protocol

/-- The successful paths of `Vault.withdraw`, final or not. -/
lemma withdraw_ok_cases (v : Vault) (amount : WithdrawAmount) (w : Bool) (r : WithdrawResult)
    (hpos : 0 < amount.amount.toRat) (hok : v.withdraw amount w hpos = .ok r)
    (herr : r.error = none) :
    ∃ cw an sta,
      (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets w
        | .vaultShares shares => computeWithdrawByShares v shares w) = .ok cw ∧
      cw.error = none ∧ cw.assets'.toNumber .to_nearest = .ok an ∧
      v.assetsAvailable.operator_lt an = false ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sta ∧
      r.sharesBurned = cw.sharesRedeemed ∧
      (cw.sharesRedeemed.operator_eq sta = true ∨
       (∃ atr, clampToSumExponent v.assetsTotal cw.assets'.operator_neg = .ok r.assets' ∧
          r.assets'.isFractionalNonPositive = .ok false ∧
          STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok atr)) := by
  simp only [Vault.withdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals try (simp [WithdrawResult.rejected] at herr; done)
  all_goals try (have h := ‹Option.isSome _ = true›; simp at herr; simp [herr] at h)
  all_goals refine ⟨_, _, _, ‹_›, by simp_all, ‹_›, by simp_all, ‹_›, rfl, ?_⟩
  all_goals first
    | (right; exact ⟨_, ‹_›, by simp_all, ‹_›⟩)
    | (left; simp_all)

/-- A successful non-final withdrawal records the clamp of the burned shares' price. -/
lemma reduce (v : Vault) (amount : WithdrawAmount) (w : Bool) (sta : STAmount)
    (r : WithdrawResult) (hpos : 0 < amount.amount.toRat) (hok : v.withdraw amount w hpos = .ok r)
    (herr : r.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sta)
    (hfin : r.sharesBurned.operator_eq sta = false) :
    ∃ p pn atr, v.sharesToAssetsWithdraw r.sharesBurned w = .ok p ∧
      p.toNumber .to_nearest = .ok pn ∧ v.assetsAvailable.operator_lt pn = false ∧
      clampToSumExponent v.assetsTotal p.operator_neg = .ok r.assets' ∧
      r.assets'.isFractionalNonPositive = .ok false ∧
      STAmount.ofNumber v.numericType v.assetsTotal .to_nearest = .ok atr := by
  obtain ⟨cw, an, sta', hcomp, hcerr, han, hlt, hsta', hsb, hcase⟩ :=
    withdraw_ok_cases v amount w r hpos hok herr
  have hsta : sta' = sta := Except.ok.inj (hsta'.symm.trans hst)
  subst hsta
  rcases hcase with hfin' | ⟨atr, hcl, hfnp, hatr⟩
  · rw [hsb, hfin'] at hfin; exact absurd hfin (by decide)
  · refine ⟨cw.assets', an, atr, ?_, han, hlt, hcl, hfnp, hatr⟩
    rw [hsb]; exact computeWithdraw_ok_priced v amount w cw hcomp hcerr

/-- Exact `Number` form of the negated canonical price. -/
lemma neg_toNumber (p : STAmount) (hc : p.IOUCanonical) (hpos : 0 < p.toRat) (dn : Number)
    (hdn : p.operator_neg.toNumber .to_nearest = .ok dn) :
    dn.isNormalized ∧ dn.toRat = -p.toRat ∧ dn.mantissa_ ≠ 0 ∧ dn.negative_ = true := by
  obtain ⟨sn, hsn, hval, hnorm⟩ := STAmount.toNumber_iou_exact p.operator_neg .to_nearest
    hc.operator_neg
  have hds : dn = sn := Except.ok.inj (hdn.symm.trans hsn)
  subst hds
  rw [STAmount.operator_neg_toRat] at hval
  refine ⟨hnorm, hval, fun h => ?_, ?_⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hval; linarith
  · by_contra h
    have := Number.toRat_nonneg_of_nonnegative dn (by simpa using h)
    linarith

end XRPL.Model.SingleAssetVault.WdMono

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- More shares burned never pays less from the same vault. -/
lemma Vault.withdraw_payout_monotone_proof (v : Vault) (amount₁ amount₂ : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (sharesTotalAmount : STAmount) (r₁ r₂ : WithdrawResult)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hcb₁ : r₁.sharesBurned.Canonical) (hcb₂ : r₂.sharesBurned.Canonical)
    (hnnb₁ : 0 ≤ r₁.sharesBurned.toRat) (hnnb₂ : 0 ≤ r₂.sharesBurned.toRat)
    (hpos₁ : 0 < amount₁.amount.toRat)
    (hok₁ : v.withdraw amount₁ waiveUnrealizedLoss hpos₁ = .ok r₁) (herr₁ : r₁.error = none)
    (hpos₂ : 0 < amount₂.amount.toRat)
    (hok₂ : v.withdraw amount₂ waiveUnrealizedLoss hpos₂ = .ok r₂) (herr₂ : r₂.error = none)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin₁ : r₁.sharesBurned.operator_eq sharesTotalAmount = false)
    (hfin₂ : r₂.sharesBurned.operator_eq sharesTotalAmount = false)
    (hle : r₁.sharesBurned.toRat ≤ r₂.sharesBurned.toRat) :
    r₁.assets'.toRat ≤ r₂.assets'.toRat := by
  obtain ⟨p₁, pn₁, atr, hp₁, hpn₁, hav₁, hcl₁, hfnp₁, hatr⟩ :=
    WdMono.reduce v amount₁ waiveUnrealizedLoss sharesTotalAmount r₁ hpos₁ hok₁ herr₁ hst hfin₁
  obtain ⟨p₂, pn₂, _, hp₂, hpn₂, hav₂, hcl₂, hfnp₂, _⟩ :=
    WdMono.reduce v amount₂ waiveUnrealizedLoss sharesTotalAmount r₂ hpos₂ hok₂ herr₂ hst hfin₂
  obtain ⟨hp₁nn, hp₁nt, hp₁c, hp₁n⟩ :=
    WdMono.price_facts v waiveUnrealizedLoss _ p₁ hcb₁ hnnb₁ hnav hp₁
  obtain ⟨hp₂nn, hp₂nt, hp₂c, hp₂n⟩ :=
    WdMono.price_facts v waiveUnrealizedLoss _ p₂ hcb₂ hnnb₂ hnav hp₂
  have hmono : p₁.mValue ≠ 0 → p₁.toRat ≤ p₂.toRat :=
    WdMono.price_mono v waiveUnrealizedLoss _ _ p₁ p₂ hcb₁ hcb₂ hnnb₁ hnnb₂ hnav hp₁ hp₂ hle
  by_cases hint : v.numericType.isIntegral = true
  · have hpi : ∀ p : STAmount, p.mNumericType = v.numericType → p.integral = true :=
      fun p h => by unfold STAmount.integral; rw [h]; exact hint
    rw [WdMono.clampToSumExponent_neg_int_toRat _ _ _ (hpi p₁ hp₁nt) hp₁nn hcl₁,
      WdMono.clampToSumExponent_neg_int_toRat _ _ _ (hpi p₂ hp₂nt) hp₂nn hcl₂]
    by_cases hz : p₁.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero p₁ hz]; exact hp₂nn
    · exact hmono hz
  · have hnt : v.numericType = .fractional := by
      cases h : v.numericType with
      | fractional => rfl
      | integral mv mo ms msh => rw [h] at hint; simp [NumericType.isIntegral] at hint
    have hint' : v.numericType.isIntegral = false := by simpa using hint
    rw [hnt] at hatr
    have hTn : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
    have hT0 : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
    -- a zero price is reported non-positive, which the run rejects
    have hnz : ∀ (p a : STAmount), p.mNumericType = v.numericType →
        clampToSumExponent v.assetsTotal p.operator_neg = .ok a →
        a.isFractionalNonPositive = .ok false → p.mValue ≠ 0 := by
      intro p a hpt hcl hf hz
      have := WdMono.clamp_zero_frac _ p a atr hTn hT0 (hpt.trans hnt) hz hatr hcl
      rw [hf] at this; exact absurd (Except.ok.inj this) (by decide)
    have hz₁ := hnz p₁ _ hp₁nt hcl₁ hfnp₁
    have hz₂ := hnz p₂ _ hp₂nt hcl₂ hfnp₂
    have hc₁ := hp₁c hint' hz₁
    have hc₂ := hp₂c hint' hz₂
    have hpos₁ := WdMono.pos_of_nonneg p₁ hp₁nn hz₁
    have hpos₂ := WdMono.pos_of_nonneg p₂ hp₂nn hz₂
    have hple := hmono hz₁
    obtain ⟨dn₁, s₁, pe₁, hdn₁, hs₁, hpe₁, hrte₁⟩ :=
      WdMono.clamp_neg_frac _ _ _ hc₁ hpos₁ hcl₁
    obtain ⟨dn₂, s₂, pe₂, hdn₂, hs₂, hpe₂, hrte₂⟩ :=
      WdMono.clamp_neg_frac _ _ _ hc₂ hpos₂ hcl₂
    obtain ⟨hdn₁n, hdn₁v, hdn₁m, hdn₁neg⟩ := WdMono.neg_toNumber p₁ hc₁ hpos₁ dn₁ hdn₁
    obtain ⟨hdn₂n, hdn₂v, hdn₂m, hdn₂neg⟩ := WdMono.neg_toNumber p₂ hc₂ hpos₂ dn₂ hdn₂
    -- the second payout fits under the available assets, hence under the total
    obtain ⟨hpn₂n, hpn₂v⟩ := hp₂n pn₂ hpn₂
    have hav : pn₂.toRat ≤ v.assetsAvailable.toRat := by
      by_contra h
      push_neg at h
      have := (operator_lt_iff _ _ v.wf.assetsAvailable_norm hpn₂n).mpr h
      rw [hav₂] at this; exact absurd this (by decide)
    have haT : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := v.exact.assetsAvailable_le
    have hTpos : 0 < v.assetsTotal.toRat := by linarith
    have hTm : v.assetsTotal.mantissa_ ≠ 0 := fun h => by
      rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hTpos; exact lt_irrefl _ hTpos
    have hTneg : v.assetsTotal.negative_ = false := by
      by_contra h
      have := Number.toRat_nonpos_of_negative _ (by simpa using h)
      linarith
    have hpe : pe₂ ≤ pe₁ :=
      WdMono.sum_exp_anti _ dn₁ dn₂ s₁ s₂ hTn hdn₁n hdn₂n hTm hdn₁m hdn₂m hTneg hdn₁neg hdn₂neg
        (by rw [hdn₁v, hdn₂v]; linarith) (by rw [hdn₂v]; linarith) hs₁ hs₂ pe₁ pe₂ hpe₁ hpe₂
    have ha₂t : r₂.assets'.mNumericType = .fractional :=
      WdMono.roundToExponent_frac_nt _ _ _ _ hc₂.is_fractional hrte₂
    have ha₂ : r₂.assets'.mValue ≠ 0 := fun h => by
      rw [WdMono.fnp_zero _ ha₂t h] at hfnp₂; exact absurd (Except.ok.inj hfnp₂) (by decide)
    exact WdMono.rte_grid_mono p₁ p₂ _ _ pe₁ pe₂ hc₁ hc₂ hpos₁ hpos₂ hple hpe
      (WdMono.pe_le _ _ hpe₁) (WdMono.pe_le _ _ hpe₂) hrte₁ hrte₂ ha₂

end XRPL.Model.SingleAssetVault
