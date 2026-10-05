import XRPL.Properties.Vault.Proofs.Lawful
import XRPL.Properties.Vault.Proofs.DepositAccuracy.Pricing
import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit
import XRPL.Properties.Vault.Common.CmpFaithfulCanonical
import XRPL.Properties.Vault.Common.WitnessSupport

/-! # Lawfulness of the deposit record

The record a successful deposit writes (both asset totals and `sharesTotal` raised
by the clamped charge and the issued shares) re-validates. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DepAcc

lemma Vault.deposit_lawful (v : Vault) (amount : STAmount) (isDonation : Bool)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanon : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (am aD sC : STAmount) (cN sN at' av' st' : Number)
    (hround : roundToVaultExponent amount v.assetsTotal = .ok am)
    (hamz : am.isZero = false)
    (hsh_don : isDonation = true → v.sharesTotal.mantissa_ ≠ 0)
    (hdon_eq : isDonation = true → aD = am ∧ sC = STAmount.zero .int64)
    (hcomp : isDonation = false → ∃ priced : STAmount,
      computeDeposit v am = .ok (.success priced sC) ∧
      clampToSumExponent v.assetsTotal priced = .ok aD ∧
      aD.isFractionalNonPositive = .ok false)
    (hcN : aD.toNumber .to_nearest = .ok cN) (hsN : sC.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + sC.toRat ≤ 2 ^ 63 - 1) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  have hfacts : cN.toRat = aD.toRat ∧ cN.isNormalized ∧ 0 ≤ aD.toRat ∧
      sC.IntegralCanonical ∧ 0 ≤ sC.toRat := by
    have hamCanon : am.Canonical := by
      rcases roundToVaultExponent_canonical_or_isZero amount am v.assetsTotal hcanon hround
        with hc | hz
      · exact hc
      · rw [hz] at hamz; exact absurd hamz (by decide)
    have ham_nn : 0 ≤ am.toRat :=
      RawVault.roundToVaultExponent_nonneg amount am v.assetsTotal hcanon hnn hround
    have ham_ne : am.mValue ≠ 0 := by unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
    have ham_pos : 0 < am.toRat :=
      lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
    by_cases hd : isDonation = true
    · obtain ⟨haD, hsC⟩ := hdon_eq hd
      have hDc' : aD.ExactCanonical := by
        rw [haD]; exact STAmount.Canonical.exactCanonical am hamCanon
      obtain ⟨cN0, hcN0, hval0, hnorm0⟩ := STAmount.toNumber_exact_canonical aD .to_nearest hDc'
      have hcNeq : cN = cN0 := by rw [hcN0] at hcN; exact (Except.ok.inj hcN).symm
      exact ⟨by rw [hcNeq]; exact hval0, by rw [hcNeq]; exact hnorm0, by rw [haD]; exact ham_nn,
        by rw [hsC]; exact zero_int64_IntegralCanonical, by rw [hsC, STAmount.zero_int64_toRat]⟩
    · have hd' : isDonation = false := by simpa using hd
      obtain ⟨priced, hcdp, hclamp, hfnp⟩ := hcomp hd'
      obtain ⟨shares, hats, hshz, hsad, -, hseq⟩ :=
        computeDeposit_success_reduces v am priced sC hcdp
      obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
      have hshpos : 0 < shares.toRat :=
        assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
      obtain ⟨hcN_val, hcN_norm⟩ :=
        Vault.deposit_charge_toNumber_facts v shares priced aD cN hshc hshnt hshpos hsad
          hclamp hcN
      exact ⟨hcN_val, hcN_norm,
        Vault.deposit_charge_nonneg v shares priced aD hshc hshnt hshpos hsad hclamp hfnp,
        hseq ▸ hshc, by rw [hseq]; exact le_of_lt hshpos⟩
  obtain ⟨hcN_val, hcN_norm, hDnn', hSc', hSnn'⟩ := hfacts
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSsz' : v.sharesTotal.toRat + sC.toRat ≤ 2 ^ 63 - 1 := by
    rw [← hST]; exact hSsz
  have hST_nn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
  have hAT_nn : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hcN_nn : 0 ≤ cN.toRat := by rw [hcN_val]; exact hDnn'
  -- asset field updates
  have hat_norm : at'.isNormalized :=
    operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm hcN_norm hat
  have hat_nn : 0 ≤ at'.toRat :=
    operator_add_nonneg _ _ _ v.wf.assetsTotal_norm hcN_norm hat (by linarith)
  rw [hAV, hat] at hav
  have hae : at' = av' := Except.ok.inj hav
  subst hae
  -- share field update
  have hshares : st'.isNormalized ∧ 0 ≤ st'.toRat ∧ st'.toRat.den = 1 ∧ st'.toRat ≠ 0 := by
    by_cases hd : isDonation = true
    · obtain ⟨haD, hsC⟩ := hdon_eq hd
      have hsN_zero : sN = Number.zero := by
        rw [hsC, zero_int64_toNumber] at hsN
        exact (Except.ok.inj hsN).symm
      rw [hsN_zero, Number.operator_add_zero_right] at hst
      have hst_eq : st' = v.sharesTotal := (Except.ok.inj hst).symm
      have hmant := hsh_don hd
      refine ⟨hst_eq ▸ v.wf.sharesTotal_norm, hst_eq ▸ hST_nn,
        hst_eq ▸ v.wf.sharesTotal_int, ?_⟩
      rw [hst_eq]
      exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hmant
    · have hd' : isDonation = false := by simpa using hd
      obtain ⟨priced', hcdp', -, -⟩ := hcomp hd'
      obtain ⟨shares, _, hshz, _, _, hsh_eq⟩ :=
        computeDeposit_success_reduces v am priced' sC hcdp'
      have hsC_ne : sC.toRat ≠ 0 := by
        rw [hsh_eq]
        exact STAmount.toRat_ne_zero shares (ne_of_beq_false hshz)
      have hsC_pos : 0 < sC.toRat := lt_of_le_of_ne hSnn' (Ne.symm hsC_ne)
      have hsC_den : sC.toRat.den = 1 := STAmount.IntegralCanonical.den_eq_one sC hSc'
      -- the stored magnitude is small
      have hsC_mval : ((sC.mValue.toNat : ℕ) : ℚ) = sC.toRat :=
        STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sC hSc' hSnn'
      have hsz : sC.mValue.toNat ≤ 2 ^ 63 - 1 := by
        have h1 : ((sC.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
          rw [hsC_mval]
          calc sC.toRat ≤ v.sharesTotal.toRat + sC.toRat := by linarith
            _ ≤ 2 ^ 63 - 1 := hSsz'
            _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
        exact_mod_cast h1
      obtain ⟨sN0, hsN0, hsN_val0, hsN_norm0⟩ :=
        STAmount.toNumber_integral_small_exact sC .to_nearest hSc' hsz
      have hsN_eq : sN = sN0 := by rw [hsN0] at hsN; exact (Except.ok.inj hsN).symm
      have hsN_val : sN.toRat = sC.toRat := by rw [hsN_eq]; exact hsN_val0
      have hsN_norm : sN.isNormalized := by rw [hsN_eq]; exact hsN_norm0
      have hsN_den : sN.toRat.den = 1 := by rw [hsN_val]; exact hsC_den
      have hsum_den : (v.sharesTotal.toRat + sN.toRat).den = 1 := by
        exact Rat.den_one_add _ _ v.wf.sharesTotal_int hsN_den
      have hsum_nn : 0 ≤ v.sharesTotal.toRat + sN.toRat := by
        rw [hsN_val]; linarith
      have hsum_le : v.sharesTotal.toRat + sN.toRat ≤ 2 ^ 63 - 1 := by
        rw [hsN_val]; exact hSsz'
      obtain ⟨hst_val, hst_den⟩ := operator_add_exact_int v.sharesTotal sN st'
        v.wf.sharesTotal_norm hsN_norm v.wf.sharesTotal_int hsN_den
        (rat_num_natAbs_lt_of_le _ hsum_den hsum_nn hsum_le) hst
      refine ⟨operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.sharesTotal_norm
        hsN_norm hst, by rw [hst_val]; exact hsum_nn, hst_den, ?_⟩
      rw [hst_val, hsN_val]
      have : 0 < v.sharesTotal.toRat + sC.toRat := by linarith
      exact ne_of_gt this
  obtain ⟨hst_norm, hst_nn, hst_den, hst_ne⟩ := hshares
  -- the updated record is well-formed and exactly valid, so `to_lawful` succeeds
  have hwfE : ({ v with assetsTotal := at', assetsAvailable := at', sharesTotal := st' } : RawVault).WF :=
    ⟨hat_norm, hat_norm, v.wf.assetsMaximum_norm, hst_norm,
      v.wf.lossUnrealized_norm, hst_nn, hst_den,
      v.wf.scale_integral, v.wf.scale_le, Number.operator_sub_self_ok at' .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨hat_nn, hat_nn, le_refl _, v.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩)
  · -- empty_shares: the new share total is nonzero
    intro h0
    exfalso
    have h0' : st'.toRat.num.toNat = 0 := h0
    have := rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn
    rw [h0'] at this
    exact hst_ne (by exact_mod_cast this.symm)
  · -- cap
    intro mq hm
    have hm' : mq ∈ v.assetsMaximum.map Number.toRat := hm
    rw [Option.mem_map] at hm'
    obtain ⟨n, hn, rfl⟩ := hm'
    have hn' : v.assetsMaximum = some n := hn
    rw [hn'] at hmax
    have hnpos : 0 < n.toRat :=
      v.exact.assetsMaximum_pos n.toRat (Option.mem_map.mpr ⟨n, hn, rfl⟩)
    have hne0 : n.operator_ne Number.zero = true :=
      (operator_ne_iff n Number.zero (v.wf.assetsMaximum_norm n hn) (Or.inl rfl)).mpr
        (by rw [Number.toRat_zero]; exact ne_of_gt hnpos)
    have hgt : at'.operator_gt n = false := by
      simp only [Option.getD_some, hne0, Bool.true_and] at hmax; exact hmax
    have := (operator_gt_iff at' n hat_norm (v.wf.assetsMaximum_norm n hn)).not.mp
      (by rw [hgt]; simp)
    exact le_of_not_gt (fun hc => this hc)
  · exact le_of_eq hL.symm
  · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
    rw [show v.lossUnrealized.toRat = 0 from hL]
    linarith
  · show 0 ≤ at'.toRat - v.lossUnrealized.toRat
    rw [show v.lossUnrealized.toRat = 0 from hL]
    linarith

end XRPL.Model.SingleAssetVault
