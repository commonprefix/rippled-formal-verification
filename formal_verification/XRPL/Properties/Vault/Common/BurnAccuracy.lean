import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Vault.Common.LawfulSupport

/-! # `LawfulVault.burnShares` accuracy proofs

Proof bodies behind the accuracy headlines in `VaultBurn.lean`. Both statements
are exact, so this file has no error bounds and no witness theorems. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **Proof body of `canBurnShares_assets_exact`.** -/
theorem LawfulVault.canBurnShares_assets_exact_proof (lv : LawfulVault) (sharesTotalAmount : STAmount)
    (hok : lv.canBurnShares = .ok (.assets sharesTotalAmount))
    (hfit : (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    sharesTotalAmount.toRat = (lv.toExact.sharesTotal : ℚ) := by
  have hST : ((lv.toExact.sharesTotal : ℕ) : ℚ) = lv.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal lv.toRawVault lv.wf
  have hfit' : lv.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
  unfold LawfulVault.canBurnShares at hok
  simp only [] at hok
  by_cases hg : (lv.sharesTotal.mantissa_ == 0 ||
      (lv.assetsTotal.mantissa_ != 0 || lv.assetsAvailable.mantissa_ != 0)) = true
  · rw [if_pos hg, epure] at hok
    exact CanBurnSharesResult.noConfusion (Except.ok.inj hok)
  · rw [if_neg hg] at hok
    simp only [pure_bind] at hok
    obtain ⟨sta, hofn, hok⟩ := bind_ok_peel _ _ _ hok
    rw [epure] at hok
    have hsta : sta = sharesTotalAmount := CanBurnSharesResult.assets.inj (Except.ok.inj hok)
    obtain ⟨_, _, _, _, hval⟩ := STAmount.ofNumber_int64_shape lv.sharesTotal .to_nearest sta
      lv.wf.sharesTotal_norm lv.wf.sharesTotal_nonneg lv.wf.sharesTotal_int hfit' hofn
    rw [← hsta, hval, ← hST]

/-- **Proof body of `burnShares_sharesTotal_exact`.** -/
theorem LawfulVault.burnShares_sharesTotal_exact_proof (lv : LawfulVault) (sharesDestroyed : STAmount)
    (lv' : LawfulVault)
    (hok : lv.burnShares sharesDestroyed = .ok lv')
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ (lv.toExact.sharesTotal : ℚ))
    (hfit : (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    (lv'.toExact.sharesTotal : ℚ) =
      (lv.toExact.sharesTotal : ℚ) - sharesDestroyed.toRat := by
  have hST : ((lv.toExact.sharesTotal : ℕ) : ℚ) = lv.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal lv.toRawVault lv.wf
  have hsd_nn : 0 ≤ sharesDestroyed.toRat := STAmount.toRat_nonneg_of sharesDestroyed hnn
  have hsd_den : sharesDestroyed.toRat.den = 1 :=
    STAmount.IntegralCanonical.den_eq_one sharesDestroyed hcanon
  -- the stored magnitude is small
  have hsz : sharesDestroyed.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have hsd_val : sharesDestroyed.toRat = ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) := by
      rw [STAmount.IntegralCanonical.toRat_eq_signedDrops sharesDestroyed hcanon]
      unfold STAmount.signedDrops
      rw [show sharesDestroyed.mIsNegative = false from hnn]
      simp only [Bool.false_eq_true, if_false]
      norm_cast
    have h1 : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
      rw [← hsd_val]
      exact le_trans hle (le_trans hfit (by norm_num))
    exact_mod_cast h1
  obtain ⟨sdn, hsdn_ok, hsdn_val, hsdn_norm⟩ :=
    STAmount.toNumber_integral_small_exact sharesDestroyed .to_nearest hcanon hsz
  -- walk the burn
  unfold LawfulVault.burnShares at hok
  simp only [] at hok
  obtain ⟨sdn', hsdn', hok⟩ := bind_ok_peel _ _ _ hok
  have hsdn'_eq : sdn' = sdn := by rw [hsdn_ok] at hsdn'; exact (Except.ok.inj hsdn').symm
  rw [hsdn'_eq] at hok
  obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
  -- the in-op `to_lawful` re-check pins `lv'.toRawVault` to the updated record
  have hv' : lv'.toRawVault = { lv with sharesTotal := st' } := (RawVault.to_lawful_ok hok).1
  -- the subtraction is exact
  have hxq := rat_eq_num_cast_of_den_one lv.sharesTotal.toRat lv.wf.sharesTotal_int
  have hyq := rat_eq_num_cast_of_den_one sdn.toRat (by rw [hsdn_val]; exact hsd_den)
  have hdiff : lv.sharesTotal.toRat - sdn.toRat
      = ((lv.sharesTotal.toRat.num - sdn.toRat.num : ℤ) : ℚ) := by
    conv_lhs => rw [← hxq, ← hyq]
    push_cast; ring
  have hdiff_den : (lv.sharesTotal.toRat - sdn.toRat).den = 1 := by
    rw [hdiff]; exact Rat.den_intCast _
  have hdiff_nn : 0 ≤ lv.sharesTotal.toRat - sdn.toRat := by
    rw [hsdn_val]
    have : sharesDestroyed.toRat ≤ lv.sharesTotal.toRat := by rw [← hST]; exact hle
    linarith
  have hdiff_le : lv.sharesTotal.toRat - sdn.toRat ≤ 2 ^ 63 - 1 := by
    have h1 : lv.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
    rw [hsdn_val]
    linarith
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int lv.sharesTotal sdn st'
    lv.wf.sharesTotal_norm hsdn_norm lv.wf.sharesTotal_int
    (by rw [hsdn_val]; exact hsd_den)
    (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
  -- read the new stored total back
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hdiff_nn
  have hproj : (lv'.toExact.sharesTotal : ℚ) = ((st'.toRat.num.toNat : ℕ) : ℚ) := by
    rw [hv']; rfl
  rw [hproj, rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn, hst_val, hsdn_val, ← hST]

end XRPL.Model.SingleAssetVault
