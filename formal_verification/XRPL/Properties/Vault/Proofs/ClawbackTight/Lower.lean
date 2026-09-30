import XRPL.Properties.Vault.Proofs.ClawbackTight.Reduce
import XRPL.Properties.Vault.Proofs.ClawbackTight.Clamp
import XRPL.Properties.Vault.Proofs.WithdrawTight.Payout

/-! # The clamp shortfall of a clawback against the post-clawback total -/

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

/-- A successful `Vault.clawback` records the total less the recovered amount. -/
lemma clawback_total (v : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hnn : 0 ≤ assets.toRat) (hok : v.clawback assets holderShares hnn = .ok r)
    (herr : r.error = none) :
    ∃ an' at' atr', r.assetsRecovered.toNumber .to_nearest = .ok an' ∧
      v.assetsTotal.operator_sub an' .to_nearest = .ok at' ∧
      STAmount.ofNumber v.numericType at' .to_nearest = .ok atr' ∧
      r.vault'.assetsTotal = at' := by
  simp only [Vault.clawback, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | (simp [ClawbackResult.rejected] at herr; done)
    | (simp only at herr; simp [herr] at *; done)
    | skip
  exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, by rw_lawful⟩

/-- A fractional clamp either keeps the priced amount or floors it onto a grid no coarser
than that of the rounded post-clawback total `atr'`. -/
lemma frac_clamp_gap (A : Number) (hA : A.isNormalized) (p rec : STAmount)
    (hpcan : p.IOUCanonical) (hppos : 0 < p.toRat) (hPA : p.toRat ≤ A.toRat)
    (hcl : clampToSumExponent A p.operator_neg = .ok rec) (hrm : rec.mValue ≠ 0)
    (an' at' : Number) (atr' : STAmount) (han' : rec.toNumber .to_nearest = .ok an')
    (hat : A.operator_sub an' .to_nearest = .ok at')
    (hatr' : STAmount.ofNumber .fractional at' .to_nearest = .ok atr') :
    (rec.toRat = p.toRat ∧ rec.exponent = p.exponent) ∨
    (rec.exponent ≤ p.exponent ∧
      p.toRat - rec.toRat ≤ (10 : ℚ) ^ atr'.exponent - 10 ^ p.exponent) := by
  obtain ⟨dn, s, pe, hdn, hs, hpe, hrte⟩ := WdMono.clamp_neg_frac _ _ _ hpcan hppos hcl
  by_cases hge : pe ≤ p.exponent
  · left
    rw [WdTight.rte_ge p _ pe hpcan hge hrte]
    exact ⟨rfl, rfl⟩
  right
  replace hge := not_le.mp hge
  have hpe80 := WdMono.pe_le _ _ hpe
  obtain ⟨ha0, hale, hgrid, hmax⟩ := WdMono.rte_facts p _ pe hpcan hppos hpe80 hrte
  have hacan : rec.IOUCanonical := (clamp_frac A hA p rec hpcan hppos hPA hcl hrm).1
  have hapos := WdMono.pos_of_nonneg _ ha0 hrm
  have hxle : rec.exponent ≤ p.exponent := WdAcc.iou_offset_le _ _ hacan hpcan ha0 hale
  obtain ⟨zp, hzp⟩ := STAmount.exists_int_grid p
  obtain ⟨za, hza⟩ := hgrid p.exponent hge.le
  have h10 : (0 : ℚ) < 10 ^ pe := zpow_pos (by norm_num) _
  have hlt' : p.toRat - rec.toRat < 10 ^ pe := by
    have h1 : (⌊p.toRat / 10 ^ pe⌋ : ℚ) * 10 ^ pe ≤ p.toRat := by
      have := Int.floor_le (p.toRat / 10 ^ pe); rwa [le_div_iff₀ h10] at this
    have h2 := hmax hrm _ h1
    have h3 : p.toRat < ((⌊p.toRat / 10 ^ pe⌋ : ℚ) + 1) * 10 ^ pe := by
      have := Int.lt_floor_add_one (p.toRat / 10 ^ pe); rwa [div_lt_iff₀ h10] at this
    linarith
  have hgap := WdTight.grid_gap p.toRat rec.toRat p.exponent pe hge zp za hzp hza hlt'
  have he1 : numberExponent at' .fractional = .ok atr'.exponent := by
    unfold numberExponent; rw [hatr']; rfl
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact rec .to_nearest hacan
  obtain rfl : an' = sn := Except.ok.inj (han'.symm.trans hsn)
  have hanm' : an'.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsnv]; exact hapos.ne')
  have hy1n := Number.operator_neg_isNormalized an' hsnn
  have hy1m : an'.operator_neg.mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne _ hanm']; exact hanm'
  have hy1neg : an'.operator_neg.negative_ = true := by
    rw [Number.operator_neg_negative_of_ne _ hanm',
      Number.negative_false_of_pos an' (by rw [hsnv]; exact hapos)]; rfl
  have hy1v : an'.operator_neg.toRat = -rec.toRat := by rw [Number.toRat_neg, hsnv]
  obtain ⟨hdnn, hdnv, hdnm, hdnneg⟩ := WdMono.neg_toNumber p hpcan hppos dn hdn
  have hTpos : 0 < A.toRat := by linarith
  have hTm : A.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hTpos; exact lt_irrefl _ hTpos
  have hTneg : A.negative_ = false := Number.negative_false_of_pos _ hTpos
  have hpee : pe ≤ atr'.exponent :=
    WdMono.sum_exp_anti _ _ dn at' s hA hy1n hdnn hTm hy1m hdnm hTneg hy1neg hdnneg
      (by rw [hy1v, hdnv]; linarith) (by rw [hdnv]; linarith) hat hs _ _ he1 hpe
  have hee : (10 : ℚ) ^ pe ≤ 10 ^ atr'.exponent := zpow_le_zpow_right₀ (by norm_num) hpee
  exact ⟨hxle, by linarith⟩

end XRPL.Model.SingleAssetVault.ClwTight
