import XRPL.Properties.Vault.Proofs.Burn
import XRPL.Properties.Vault.Proofs.Support.NumberFacts

/-! # Lawfulness of the records the operations write

Each lemma takes the record an exit writes (as `{ v with … }` over the starting
vault) and shows its `to_lawful` re-check succeeds. They are about records only:
which exit writes which record is left to the callers. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The record with only `sharesTotal` reduced passes the `to_lawful` re-check
(no `notLawful`). -/
lemma Vault.burnShares_record_never_notLawful (v : Vault)
    (sharesDestroyed sharesTotalAmount : STAmount) (sdn st' : Number)
    (hcan : v.canBurnShares = .ok (.assets sharesTotalAmount))
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sdn)
    (hst : v.sharesTotal.operator_sub sdn .to_nearest = .ok st') :
    ∃ v' : Vault, ({ v.toRawVault with sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st' } := by
  have hwf := v.wf
  have hvalid := v.exact
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault hwf
  have hsta_val : sharesTotalAmount.toRat = (v.toExact.sharesTotal : ℚ) :=
    Vault.canBurnShares_assets_exact_proof v sharesTotalAmount hcan hfit
  have hle' : sharesDestroyed.toRat ≤ v.sharesTotal.toRat := by rw [← hST, ← hsta_val]; exact hle
  have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
  have hsd_nn : 0 ≤ sharesDestroyed.toRat := STAmount.toRat_nonneg_of sharesDestroyed hnn
  have hsd_den : sharesDestroyed.toRat.den = 1 :=
    STAmount.IntegralCanonical.den_eq_one sharesDestroyed hcanon
  -- guard components: shares outstanding, both asset totals zero
  have hguard : v.sharesTotal.mantissa_ ≠ 0 ∧ v.assetsTotal.mantissa_ = 0 ∧
      v.assetsAvailable.mantissa_ = 0 := by
    unfold Vault.canBurnShares at hcan
    simp only [] at hcan
    by_cases hg : (v.sharesTotal.mantissa_ == 0 ||
        (v.assetsTotal.mantissa_ != 0 || v.assetsAvailable.mantissa_ != 0)) = true
    · rw [if_pos hg, pure_eq] at hcan
      exact absurd (Except.ok.inj hcan) (fun h => CanBurnSharesResult.noConfusion h)
    · rw [Bool.or_eq_true, Bool.or_eq_true] at hg
      push Not at hg
      obtain ⟨h1, h2, h3⟩ := hg
      exact ⟨fun h => h1 (by rw [h]; rfl), by by_contra h; exact h2 (by simpa using h),
        by by_contra h; exact h3 (by simpa using h)⟩
  obtain ⟨hshares_ne, hAT_m0, hAV_m0⟩ := hguard
  have hAT0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAT_m0
  have hAV0 : v.assetsAvailable.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAV_m0
  have hLU0 : v.lossUnrealized.toRat = 0 :=
    le_antisymm (by
      have h1 := hvalid.lossUnrealized_le
      have h2 : v.toExact.assetsTotal - v.toExact.assetsAvailable = 0 := by
        show v.assetsTotal.toRat - v.assetsAvailable.toRat = 0
        rw [hAT0, hAV0]; ring
      rw [h2] at h1; exact h1) hvalid.lossUnrealized_nonneg
  have hsz : sharesDestroyed.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have hmval : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) = sharesDestroyed.toRat :=
      STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sharesDestroyed hcanon hsd_nn
    have h1 : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
      rw [hmval]
      calc sharesDestroyed.toRat ≤ v.sharesTotal.toRat := hle'
        _ ≤ 2 ^ 63 - 1 := hfit'
        _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
    exact_mod_cast h1
  obtain ⟨sdn0, hsdn0_ok, hsdn_val, hsdn_norm⟩ :=
    STAmount.toNumber_integral_small_exact sharesDestroyed .to_nearest hcanon hsz
  have hsdn_eq : sdn = sdn0 := by rw [hsdn0_ok] at hnum; exact (Except.ok.inj hnum).symm
  rw [hsdn_eq] at hst
  -- the subtraction is exact
  have hsdn_den : sdn0.toRat.den = 1 := by rw [hsdn_val]; exact hsd_den
  have hdiff_den : (v.sharesTotal.toRat - sdn0.toRat).den = 1 := by
    rw [rat_sub_eq_num_cast _ _ hwf.sharesTotal_int hsdn_den]; exact Rat.den_intCast _
  have hdiff_nn : 0 ≤ v.sharesTotal.toRat - sdn0.toRat := by rw [hsdn_val]; linarith
  have hdiff_le : v.sharesTotal.toRat - sdn0.toRat ≤ 2 ^ 63 - 1 := by rw [hsdn_val]; linarith
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal sdn0 st'
    hwf.sharesTotal_norm hsdn_norm hwf.sharesTotal_int hsdn_den
    (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hdiff_nn
  have hst_norm : st'.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz _ _ _ hwf.sharesTotal_norm hsdn_norm hst
  have hwfE : ({ v with sharesTotal := st' } : RawVault).WF :=
    ⟨hwf.assetsTotal_norm, hwf.assetsAvailable_norm, hwf.assetsMaximum_norm,
      hst_norm, hwf.lossUnrealized_norm, hst_nn, hst_den,
      hwf.scale_integral, hwf.scale_le, hwf.assetsTotal_sub_ok⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨hvalid.assetsTotal_nonneg, hvalid.assetsAvailable_nonneg,
      hvalid.assetsAvailable_le, hvalid.assetsMaximum_pos, ?_, hvalid.cap, ?_, ?_, ?_⟩)
  · intro _; exact ⟨hAT0, hAV0⟩
  · exact le_of_eq hLU0.symm
  · show v.lossUnrealized.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat
    rw [hLU0, hAT0, hAV0]; linarith
  · show 0 ≤ v.assetsTotal.toRat - v.lossUnrealized.toRat
    rw [hLU0, hAT0]; linarith

/-- The record subtracting one payout from both asset totals and one burn from
`sharesTotal` passes the `to_lawful` re-check (no `notLawful`). `hempty`: dropping to zero shares must also zero the assets. -/
lemma Vault.subtract_record_never_notLawful (v : Vault)
    (payout burned at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hp_norm : payout.isNormalized) (hp_nn : 0 ≤ payout.toRat)
    (hp_le : payout.toRat ≤ v.assetsTotal.toRat)
    (hb_norm : burned.isNormalized) (hb_nn : 0 ≤ burned.toRat)
    (hb_den : burned.toRat.den = 1) (hb_le : burned.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hat : v.assetsTotal.operator_sub payout .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_sub payout .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_sub burned .to_nearest = .ok st')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  -- new asset total: normalized, nonnegative, and at or below the starting total
  have hat_norm : at'.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm hp_norm hat
  have hat_nn : 0 ≤ at'.toRat :=
    operator_sub_nonneg _ _ _ v.wf.assetsTotal_norm hp_norm hat (by linarith)
  have hat_le : at'.toRat ≤ v.assetsTotal.toRat := by
    by_cases hpm : payout.mantissa_ = 0
    · exact le_of_eq (congrArg Number.toRat
        (Number.operator_sub_zero_right v.assetsTotal payout at' hpm hat))
    · by_cases hAm : v.assetsTotal.mantissa_ = 0
      · exfalso
        have hA0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAm
        have hp0 : payout.toRat = 0 := le_antisymm (by rw [← hA0]; exact hp_le) hp_nn
        exact Number.toRat_ne_zero_of_mantissa_ne_zero payout hpm hp0
      · exact Number.operator_sub_nonneg_le v.assetsTotal payout at' v.wf.assetsTotal_norm
          hp_norm hAm hpm v.exact.assetsTotal_nonneg hp_nn hat
  -- parity: the same payout leaves `assetsAvailable` at the total's new value
  rw [hAV, hat] at hav
  have hae : at' = av' := Except.ok.inj hav
  subst hae
  -- new share total: exact integer decrement, normalized, nonnegative
  have hdiff_den : (v.sharesTotal.toRat - burned.toRat).den = 1 := by
    rw [rat_sub_eq_num_cast _ _ v.wf.sharesTotal_int hb_den]; exact Rat.den_intCast _
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal burned st'
    v.wf.sharesTotal_norm hb_norm v.wf.sharesTotal_int hb_den
    (rat_num_natAbs_lt_of_le _ hdiff_den (by linarith) (by linarith)) hst
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; linarith
  have hst_norm : st'.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.sharesTotal_norm hb_norm hst
  -- the decremented record is well-formed and exactly valid, so `to_lawful` succeeds
  have hwfE : ({ v with assetsTotal := at', assetsAvailable := at', sharesTotal := st' } : RawVault).WF :=
    ⟨hat_norm, hat_norm, v.wf.assetsMaximum_norm, hst_norm,
      v.wf.lossUnrealized_norm, hst_nn, hst_den,
      v.wf.scale_integral, v.wf.scale_le, Number.operator_sub_self_ok at' .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨hat_nn, hat_nn, le_refl _, v.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩)
  · -- empty_shares: a zero new share total forces zero assets
    intro h0
    have h0' : st'.toRat.num.toNat = 0 := h0
    have hcast := rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn
    rw [h0'] at hcast
    have hst0 : st'.toRat = 0 := by exact_mod_cast hcast.symm
    have hat0 := hempty hst0
    exact ⟨hat0, hat0⟩
  · -- cap: the new total is at or below the starting total, which respects the cap
    intro m hm
    exact le_trans hat_le (v.exact.cap m hm)
  · exact le_of_eq hL.symm
  · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
    rw [show v.lossUnrealized.toRat = 0 from hL]; linarith
  · show 0 ≤ at'.toRat - v.lossUnrealized.toRat
    rw [show v.lossUnrealized.toRat = 0 from hL]; linarith

/-- The all-zero record (both asset totals and `sharesTotal` zeroed) passes the
`to_lawful` re-check (no `notLawful`), like a freshly created vault. -/
lemma Vault.zero_record_never_notLawful (v : Vault)
    (hL : v.toExact.lossUnrealized = 0) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  set w : RawVault := { v with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } with hw_def
  have hz : Number.zero.isNormalized := Or.inl rfl
  -- the exact projections of the zeroed record (loss carries over from `v`)
  have hAT : w.toExact.assetsTotal = 0 := by simp only [hw_def, RawVault.toExact, Number.toRat_zero]
  have hAV0 : w.toExact.assetsAvailable = 0 := by simp only [hw_def, RawVault.toExact, Number.toRat_zero]
  have hST : w.toExact.sharesTotal = 0 := by
    simp only [hw_def, RawVault.toExact, Number.toRat_zero, Rat.num_zero, Int.toNat_zero]
  have hLU : w.toExact.lossUnrealized = 0 := hL
  have hwfE : w.WF :=
    ⟨hz, hz, v.wf.assetsMaximum_norm, hz, v.wf.lossUnrealized_norm,
      by simp only [hw_def, Number.toRat_zero, le_refl],
      by simp only [hw_def, Number.toRat_zero]; rfl,
      v.wf.scale_integral, v.wf.scale_le, Number.operator_sub_self_ok Number.zero .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact w hwfE).mpr ?_)
  refine ⟨?_, ?_, ?_, v.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAT]
  · rw [hAV0]
  · rw [hAV0, hAT]
  · rw [hST, hAT, hAV0]; intro _; exact ⟨rfl, rfl⟩
  · intro m hm; rw [hAT]; exact le_of_lt (v.exact.assetsMaximum_pos m hm)
  · rw [hLU]
  · rw [hLU, hAT, hAV0]; norm_num
  · rw [hAT, hLU]; norm_num

end XRPL.Model.SingleAssetVault
