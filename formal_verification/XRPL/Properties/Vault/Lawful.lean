import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.Create
import XRPL.Properties.Vault.Common.Unchanged
import XRPL.Properties.Vault.Common.LawfulSupport
import XRPL.Properties.Vault.VaultBurn
import XRPL.Model.Vault.VaultCreate
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultDelete
import XRPL.Model.Vault.VaultSet

/-! # Every vault operation preserves lawfulness

In each preservation theorem `hok` states the operation ran without a throw. The
result may still carry a TER, and a rejected operation returns the starting vault
unchanged.

The three mutating operations additionally hypothesize the reachability
invariants of the vault-only model (`interestUnrealized = 0`,
`lossUnrealized = 0`, and record-level `assetsAvailable = assetsTotal`: every
vault operation writes both asset fields with the identical update, and lending
is out of scope) together with canonical-storage and sign facts about the
amounts the run reports. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

theorem Vault.create_lawful (nt : NumericType) (scale : UInt8)
    (assetsMaximum : Option Number)
    (hmax_norm : ∀ m ∈ assetsMaximum, m.isNormalized) -- If assetsMaximum is present, it is normalized
    (hmax_pos : ∀ m ∈ assetsMaximum, 0 < m.toRat) -- If assetsMaximum is present, it is positive
    (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) : -- If vault holds an integral type, scale must be 0, otherwise it has to be <= 18
    (Vault.create nt scale assetsMaximum).Lawful :=
  Vault.create_lawful_proof nt scale assetsMaximum hmax_norm hmax_pos hscale_int hscale_le

variable (v : Vault)

theorem Vault.deposit_lawful (amount : STAmount) (isDonation : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    -- no unrealized interest or loss: with lossUnrealized equal to the stored
    -- gap exactly, the two independent additions can shrink the gap and break
    -- Valid, so preservation only holds on states with both fields zero
    (hI : v.toExact.interestUnrealized = 0)
    (hL : v.toExact.lossUnrealized = 0)
    -- vault-only operations keep both asset fields identical (no lending)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (r : DepositResult) (hok : v.deposit amount isDonation = .ok r)
    -- the taken amount is stored canonically and is not negative
    (hDc : r.amountDeposit'.ExactCanonical)
    (hDnn : 0 ≤ r.amountDeposit'.toRat)
    -- the issued shares are a canonical nonnegative integral amount
    (hSc : r.sharesIssued.IntegralCanonical)
    (hSnn : 0 ≤ r.sharesIssued.toRat)
    -- the new share total fits the share domain (int64)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.deposit_error_unchanged_proof v amount isDonation r hok herr]
    exact hv
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, hsh_don, _hins, hdon_eq, hcomp,
      hcN, hsN, hat, hav, hst, hmax, hr⟩ :=
      Vault.deposit_success_reduces v amount isDonation r hok herr'
    subst hr
    have hDc' : aD.ExactCanonical := hDc
    have hDnn' : 0 ≤ aD.toRat := hDnn
    have hSc' : sC.IntegralCanonical := hSc
    have hSnn' : 0 ≤ sC.toRat := hSnn
    have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
      Vault.WF.toExact_sharesTotal v hv.wf
    have hSsz' : v.sharesTotal.toRat + sC.toRat ≤ 2 ^ 63 - 1 := by
      rw [← hST]; exact hSsz
    have hST_nn : 0 ≤ v.sharesTotal.toRat := hv.wf.sharesTotal_nonneg
    have hAT_nn : (0 : ℚ) ≤ v.assetsTotal.toRat := hv.valid.assetsTotal_nonneg
    -- the taken amount converts exactly
    obtain ⟨cN0, hcN0, hcN_val0, hcN_norm0⟩ :=
      STAmount.toNumber_exact_canonical aD .to_nearest hDc'
    have hcN_eq : cN = cN0 := by rw [hcN0] at hcN; exact (Except.ok.inj hcN).symm
    have hcN_val : cN.toRat = aD.toRat := by rw [hcN_eq]; exact hcN_val0
    have hcN_norm : cN.isNormalized := by rw [hcN_eq]; exact hcN_norm0
    have hcN_nn : 0 ≤ cN.toRat := by rw [hcN_val]; exact hDnn'
    -- asset field updates
    have hat_norm : at'.isNormalized :=
      operator_add_isNormalized_to_nearest' _ _ _ hv.wf.assetsTotal_norm hcN_norm hat
    have hat_nn : 0 ≤ at'.toRat :=
      operator_add_nonneg _ _ _ hv.wf.assetsTotal_norm hcN_norm hat (by linarith)
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
        rw [hsN_zero, operator_add_zero_right] at hst
        have hst_eq : st' = v.sharesTotal := (Except.ok.inj hst).symm
        have hmant := hsh_don hd
        refine ⟨hst_eq ▸ hv.wf.sharesTotal_norm, hst_eq ▸ hST_nn,
          hst_eq ▸ hv.wf.sharesTotal_int, ?_⟩
        rw [hst_eq]
        exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hmant
      · have hd' : isDonation = false := by simpa using hd
        obtain ⟨shares, _, hshz, _, _, hsh_eq⟩ :=
          computeDeposit_success_reduces v am aD sC (hcomp hd')
        have hsC_ne : sC.toRat ≠ 0 := by
          rw [hsh_eq]
          exact STAmount.IntegralCanonical.toRat_ne_zero_of_not_isZero shares
            (hsh_eq ▸ hSc') (hsh_eq ▸ hshz)
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
          rw [rat_add_eq_num_cast _ _ hv.wf.sharesTotal_int hsN_den]
          exact Rat.den_intCast _
        have hsum_nn : 0 ≤ v.sharesTotal.toRat + sN.toRat := by
          rw [hsN_val]; linarith
        have hsum_le : v.sharesTotal.toRat + sN.toRat ≤ 2 ^ 63 - 1 := by
          rw [hsN_val]; exact hSsz'
        obtain ⟨hst_val, hst_den⟩ := operator_add_exact_int v.sharesTotal sN st'
          hv.wf.sharesTotal_norm hsN_norm hv.wf.sharesTotal_int hsN_den
          (rat_num_natAbs_lt_of_le _ hsum_den hsum_nn hsum_le) hst
        refine ⟨operator_add_isNormalized_to_nearest' _ _ _ hv.wf.sharesTotal_norm
          hsN_norm hst, by rw [hst_val]; exact hsum_nn, hst_den, ?_⟩
        rw [hst_val, hsN_val]
        have : 0 < v.sharesTotal.toRat + sC.toRat := by linarith
        exact ne_of_gt this
    obtain ⟨hst_norm, hst_nn, hst_den, hst_ne⟩ := hshares
    -- assemble lawfulness of the updated record
    show ({ v with assetsTotal := at', assetsAvailable := at', sharesTotal := st' }
      : Vault).Lawful
    refine ⟨⟨hat_norm, hat_norm, hv.wf.assetsMaximum_norm, hst_norm,
      hv.wf.interestUnrealized_norm, hv.wf.lossUnrealized_norm, hst_nn, hst_den,
      hv.wf.scale_integral, hv.wf.scale_le⟩,
      ⟨hat_nn, hat_nn, le_refl _, hv.valid.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
      have hgt : at'.operator_gt n = false := by simpa using hmax
      have := (operator_gt_iff at' n hat_norm (hv.wf.assetsMaximum_norm n hn)).not.mp
        (by rw [hgt]; simp)
      exact le_of_not_gt (fun hc => this hc)
    · exact le_of_eq hL.symm
    · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]
      linarith
    · exact le_of_eq hI.symm
    · show v.interestUnrealized.toRat ≤ at'.toRat - at'.toRat
      rw [show v.interestUnrealized.toRat = 0 from hI]
      linarith
    · intro h
      have h' : (0 : ℚ) < at'.toRat := h
      show v.interestUnrealized.toRat < at'.toRat
      rw [show v.interestUnrealized.toRat = 0 from hI]
      exact h'
    · show 0 ≤ at'.toRat - v.interestUnrealized.toRat - v.lossUnrealized.toRat
      rw [show v.interestUnrealized.toRat = 0 from hI,
        show v.lossUnrealized.toRat = 0 from hL]
      linarith
    · intro h
      exfalso
      have h' : (0 : ℚ) < v.interestUnrealized.toRat := h
      rw [show v.interestUnrealized.toRat = 0 from hI] at h'
      exact absurd h' (lt_irrefl 0)

theorem Vault.withdraw_lawful (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    -- no unrealized interest or loss: with lossUnrealized equal to the stored
    -- gap exactly, the two independent additions can shrink the gap and break
    -- Valid, so preservation only holds on states with both fields zero
    (hI : v.toExact.interestUnrealized = 0)
    (hL : v.toExact.lossUnrealized = 0)
    -- vault-only operations keep both asset fields identical (no lending)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (r : WithdrawResult) (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    -- the paid amount is stored canonically and is not negative
    (hDc : r.assets'.ExactCanonical)
    (hDnn : 0 ≤ r.assets'.toRat)
    -- the burned shares are a canonical nonnegative int64 amount
    (hSc : r.sharesBurned.IntegralCanonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hSnn : r.sharesBurned.negative = false)
    -- a holder cannot burn more shares than exist
    (hsle : r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ))
    -- the share total fits the share domain (int64)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.withdraw_error_unchanged_proof v amount waiveUnrealizedLoss r hok herr]
    exact hv
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨result, hres, aN, sta, haN, hlt, hsta, hbranch⟩ :=
      Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr'
    have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
      Vault.WF.toExact_sharesTotal v hv.wf
    have hST_nn : 0 ≤ v.sharesTotal.toRat := hv.wf.sharesTotal_nonneg
    have hAVval : v.assetsAvailable.toRat = v.assetsTotal.toRat := by rw [hAV]
    have hAT_nn : (0 : ℚ) ≤ v.assetsTotal.toRat := hv.valid.assetsTotal_nonneg
    rcases hbranch with ⟨_, allAvail, _, hr⟩ | ⟨hne, sN, at', av', st', hsN, hat, hav, hst, hr⟩
    · -- final withdrawal: all three totals zeroed
      subst hr
      show ({ v with assetsAvailable := Number.zero,
                      assetsTotal := Number.zero,
                      sharesTotal := Number.zero } : Vault).Lawful
      have hz : Number.zero.isNormalized := Or.inl rfl
      have hLU0 : v.lossUnrealized.toRat = 0 := hL
      have hIU0 : v.interestUnrealized.toRat = 0 := hI
      refine ⟨⟨hz, hz, hv.wf.assetsMaximum_norm, hz,
        hv.wf.interestUnrealized_norm, hv.wf.lossUnrealized_norm,
        ?_, ?_, hv.wf.scale_integral, hv.wf.scale_le⟩,
        ⟨?_, ?_, ?_, hv.valid.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp only [Number.toRat_zero, le_refl]
      · simp only [Number.toRat_zero]; rfl
      · simp only [Vault.toExact, Number.toRat_zero, le_refl]
      · simp only [Vault.toExact, Number.toRat_zero, le_refl]
      · simp only [Vault.toExact, Number.toRat_zero, le_refl]
      · intro _
        simp only [Vault.toExact, Number.toRat_zero]
        exact ⟨trivial, trivial⟩
      · intro mq hm
        have hm' : mq ∈ v.assetsMaximum.map Number.toRat := hm
        rw [Option.mem_map] at hm'
        obtain ⟨n, hn, rfl⟩ := hm'
        simp only [Vault.toExact, Number.toRat_zero]
        exact le_of_lt (hv.valid.assetsMaximum_pos n.toRat
          (Option.mem_map.mpr ⟨n, hn, rfl⟩))
      · simp only [Vault.toExact]
        rw [hLU0]
      · simp only [Vault.toExact, Number.toRat_zero]
        rw [hLU0]
        linarith
      · simp only [Vault.toExact]
        rw [hIU0]
      · simp only [Vault.toExact, Number.toRat_zero]
        rw [hIU0]
        linarith
      · simp only [Vault.toExact, Number.toRat_zero]
        intro h
        exact absurd h (lt_irrefl 0)
      · simp only [Vault.toExact, Number.toRat_zero]
        rw [hIU0, hLU0]
        linarith
      · simp only [Vault.toExact]
        intro h
        rw [hIU0] at h
        exact absurd h (lt_irrefl 0)
    · -- partial withdrawal
      subst hr
      have hDc' : result.assets'.ExactCanonical := hDc
      have hDnn' : 0 ≤ result.assets'.toRat := hDnn
      have hSc' : result.sharesRedeemed.IntegralCanonical := hSc
      have hSnt' : result.sharesRedeemed.mNumericType = .int64 := hSnt
      have hSnn' : result.sharesRedeemed.mIsNegative = false := hSnn
      have hsle' : result.sharesRedeemed.toRat ≤ v.sharesTotal.toRat := by
        rw [← hST]; exact hsle
      have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
      have hSnn_val : 0 ≤ result.sharesRedeemed.toRat :=
        STAmount.toRat_nonneg_of _ hSnn'
      -- the paid amount converts exactly
      obtain ⟨aN0, haN0, haN_val0, haN_norm0⟩ :=
        STAmount.toNumber_exact_canonical result.assets' .to_nearest hDc'
      have haN_eq : aN = aN0 := by rw [haN0] at haN; exact (Except.ok.inj haN).symm
      have haN_val : aN.toRat = result.assets'.toRat := by rw [haN_eq]; exact haN_val0
      have haN_norm : aN.isNormalized := by rw [haN_eq]; exact haN_norm0
      have haN_nn : 0 ≤ aN.toRat := by rw [haN_val]; exact hDnn'
      -- funds guard: the paid amount is at most the available balance
      have hle_a : aN.toRat ≤ v.assetsTotal.toRat := by
        have h1 := (operator_lt_iff v.assetsAvailable aN
          hv.wf.assetsAvailable_norm haN_norm).not.mp (by rw [hlt]; simp)
        rw [hAVval] at h1
        exact le_of_not_gt (fun hc => h1 hc)
      -- asset field updates
      have hat_norm : at'.isNormalized :=
        operator_sub_isNormalized_to_nearest' _ _ _ hv.wf.assetsTotal_norm haN_norm hat
      have hat_nn : 0 ≤ at'.toRat :=
        operator_sub_nonneg _ _ _ hv.wf.assetsTotal_norm haN_norm hat (by linarith)
      rw [hAV, hat] at hav
      have hae : at' = av' := Except.ok.inj hav
      subst hae
      -- share field update, exact
      have hS_den : result.sharesRedeemed.toRat.den = 1 :=
        STAmount.IntegralCanonical.den_eq_one _ hSc'
      have hS_mval : ((result.sharesRedeemed.mValue.toNat : ℕ) : ℚ)
          = result.sharesRedeemed.toRat :=
        STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg _ hSc' hSnn_val
      have hsz : result.sharesRedeemed.mValue.toNat ≤ 2 ^ 63 - 1 := by
        have h1 : ((result.sharesRedeemed.mValue.toNat : ℕ) : ℚ)
            ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
          rw [hS_mval]
          calc result.sharesRedeemed.toRat ≤ v.sharesTotal.toRat := hsle'
            _ ≤ 2 ^ 63 - 1 := hfit'
            _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
        exact_mod_cast h1
      obtain ⟨sN0, hsN0, hsN_val0, hsN_norm0⟩ :=
        STAmount.toNumber_integral_small_exact result.sharesRedeemed .to_nearest hSc' hsz
      have hsN_eq : sN = sN0 := by rw [hsN0] at hsN; exact (Except.ok.inj hsN).symm
      have hsN_val : sN.toRat = result.sharesRedeemed.toRat := by
        rw [hsN_eq]; exact hsN_val0
      have hsN_norm : sN.isNormalized := by rw [hsN_eq]; exact hsN_norm0
      have hsN_den : sN.toRat.den = 1 := by rw [hsN_val]; exact hS_den
      have hdiff_den : (v.sharesTotal.toRat - sN.toRat).den = 1 := by
        rw [rat_sub_eq_num_cast _ _ hv.wf.sharesTotal_int hsN_den]
        exact Rat.den_intCast _
      have hdiff_nn : 0 ≤ v.sharesTotal.toRat - sN.toRat := by
        rw [hsN_val]; linarith
      have hdiff_le : v.sharesTotal.toRat - sN.toRat ≤ 2 ^ 63 - 1 := by
        rw [hsN_val]; linarith [hSnn_val]
      obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal sN st'
        hv.wf.sharesTotal_norm hsN_norm hv.wf.sharesTotal_int hsN_den
        (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
      have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hdiff_nn
      have hst_norm : st'.isNormalized :=
        operator_sub_isNormalized_to_nearest' _ _ _ hv.wf.sharesTotal_norm hsN_norm hst
      -- the non-final guard forces a strict share remainder or an empty vault
      have hkey : st'.toRat = 0 → at'.toRat = 0 := by
        intro h0
        rw [hst_val, hsN_val] at h0
        by_cases hst0 : v.sharesTotal.toRat = 0
        · -- empty vault: nothing can be paid, both subtractions are exact zero
          have hAT0 : v.assetsTotal.toRat = 0 := by
            have h1 := (hv.valid.empty_shares (by
              have h2 : ((v.toExact.sharesTotal : ℕ) : ℚ) = 0 := by rw [hST]; exact hst0
              exact_mod_cast h2)).1
            exact h1
          have haN0 : aN.toRat = 0 := le_antisymm (by rw [hAT0] at hle_a; exact hle_a) haN_nn
          have hexact := Number.RoundsToRepresentable.eq_of_representable at'
            (v.assetsTotal.toRat - aN.toRat)
            (operator_sub_rounded_to_nearest v.assetsTotal aN at'
              hv.wf.assetsTotal_norm haN_norm hat)
            Number.zero (Or.inl rfl)
            (by rw [Number.toRat_zero, hAT0, haN0]; ring)
          rw [hexact, hAT0, haN0]
          ring
        · -- shares remain: the redeemed amount is strictly below the total,
          -- contradicting the zero remainder
          exfalso
          have hslt : result.sharesRedeemed.toRat < v.sharesTotal.toRat := by
            rcases lt_or_eq_of_le hsle' with h | h
            · exact h
            · -- equal values force record equality, tripping the final guard
              exfalso
              obtain ⟨hsta_nt, hsta_off, hsta_neg, hsta_val, _⟩ :=
                STAmount.ofNumber_int64_shape v.sharesTotal .to_nearest sta
                  hv.wf.sharesTotal_norm hST_nn hv.wf.sharesTotal_int hfit' hsta
              have hmv : result.sharesRedeemed.mValue = sta.mValue := by
                have h1 : ((result.sharesRedeemed.mValue.toNat : ℕ) : ℚ)
                    = ((sta.mValue.toNat : ℕ) : ℚ) := by
                  rw [hS_mval, hsta_val, h]
                have h2 : result.sharesRedeemed.mValue.toNat = sta.mValue.toNat := by
                  exact_mod_cast h1
                exact UInt64.toNat_inj.mp h2
              have heq : result.sharesRedeemed.operator_eq sta = true := by
                unfold STAmount.operator_eq STAmount.areComparable
                rw [hSnt', hsta_nt, hSnn', hsta_neg, hSc'.offset_zero, hsta_off, hmv]
                simp
              rw [heq] at hne
              simp at hne
          have hge1 : 1 ≤ v.sharesTotal.toRat - result.sharesRedeemed.toRat :=
            rat_one_le_sub_of_lt _ _ hv.wf.sharesTotal_int hS_den hslt
          linarith
      show ({ v with assetsAvailable := at', assetsTotal := at', sharesTotal := st' }
        : Vault).Lawful
      refine ⟨⟨hat_norm, hat_norm, hv.wf.assetsMaximum_norm, hst_norm,
        hv.wf.interestUnrealized_norm, hv.wf.lossUnrealized_norm, hst_nn, hst_den,
        hv.wf.scale_integral, hv.wf.scale_le⟩,
        ⟨hat_nn, hat_nn, le_refl _, hv.valid.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩⟩
      · -- empty_shares
        intro h0
        have h0' : st'.toRat.num.toNat = 0 := h0
        have hcast := rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn
        rw [h0'] at hcast
        have hz : at'.toRat = 0 := hkey (by exact_mod_cast hcast.symm)
        exact ⟨hz, hz⟩
      · -- cap
        intro mq hm
        have hm' : mq ∈ v.assetsMaximum.map Number.toRat := hm
        rw [Option.mem_map] at hm'
        obtain ⟨n, hn, rfl⟩ := hm'
        have hcapn : v.assetsTotal.toRat ≤ n.toRat :=
          hv.valid.cap n.toRat (Option.mem_map.mpr ⟨n, hn, rfl⟩)
        exact operator_sub_le_of_le_normalized _ _ _ _ hv.wf.assetsTotal_norm haN_norm
          hat (hv.wf.assetsMaximum_norm n hn) (by linarith)
      · exact le_of_eq hL.symm
      · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
        rw [show v.lossUnrealized.toRat = 0 from hL]
        linarith
      · exact le_of_eq hI.symm
      · show v.interestUnrealized.toRat ≤ at'.toRat - at'.toRat
        rw [show v.interestUnrealized.toRat = 0 from hI]
        linarith
      · intro h
        have h' : (0 : ℚ) < at'.toRat := h
        show v.interestUnrealized.toRat < at'.toRat
        rw [show v.interestUnrealized.toRat = 0 from hI]
        exact h'
      · show 0 ≤ at'.toRat - v.interestUnrealized.toRat - v.lossUnrealized.toRat
        rw [show v.interestUnrealized.toRat = 0 from hI,
          show v.lossUnrealized.toRat = 0 from hL]
        linarith
      · intro h
        exfalso
        have h' : (0 : ℚ) < v.interestUnrealized.toRat := h
        rw [show v.interestUnrealized.toRat = 0 from hI] at h'
        exact absurd h' (lt_irrefl 0)

theorem Vault.clawback_lawful (assets : STAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    -- no unrealized interest or loss: with lossUnrealized equal to the stored
    -- gap exactly, the two independent additions can shrink the gap and break
    -- Valid, so preservation only holds on states with both fields zero
    (hI : v.toExact.interestUnrealized = 0)
    (hL : v.toExact.lossUnrealized = 0)
    -- vault-only operations keep both asset fields identical (no lending)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (r : ClawbackResult) (hok : v.clawback assets = .ok r)
    -- the recovered amount is stored canonically, is not negative, and is
    -- covered by the available balance (checked inside `computeClawback`)
    (hDc : r.assetsRecovered.ExactCanonical)
    (hDnn : 0 ≤ r.assetsRecovered.toRat)
    (hDle : r.assetsRecovered.toRat ≤ v.toExact.assetsAvailable)
    -- the destroyed shares are a canonical nonnegative integral amount
    -- strictly below the share total (a full clawback can leave asset dust
    -- with zero shares outstanding, which `Valid.empty_shares` forbids)
    (hSc : r.sharesDestroyed.IntegralCanonical)
    (hSnn : r.sharesDestroyed.negative = false)
    (hslt : r.sharesDestroyed.toRat < (v.toExact.sharesTotal : ℚ))
    -- the share total fits the share domain (int64)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.clawback_error_unchanged_proof v assets r hok herr]
    exact hv
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨result, hres, hshz, sdn, arn, at', st', av', hsdn, harn, hat, hst, hav, hr⟩ :=
      Vault.clawback_success_reduces v assets r hok herr'
    subst hr
    have hDc' : result.assetsRecovered.ExactCanonical := hDc
    have hDnn' : 0 ≤ result.assetsRecovered.toRat := hDnn
    have hDle' : result.assetsRecovered.toRat ≤ v.assetsAvailable.toRat := hDle
    have hSc' : result.sharesDestroyed.IntegralCanonical := hSc
    have hSnn' : result.sharesDestroyed.mIsNegative = false := hSnn
    have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
      Vault.WF.toExact_sharesTotal v hv.wf
    have hST_nn : 0 ≤ v.sharesTotal.toRat := hv.wf.sharesTotal_nonneg
    have hslt' : result.sharesDestroyed.toRat < v.sharesTotal.toRat := by
      rw [← hST]; exact hslt
    have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
    have hSnn_val : 0 ≤ result.sharesDestroyed.toRat := STAmount.toRat_nonneg_of _ hSnn'
    have hAVval : v.assetsAvailable.toRat = v.assetsTotal.toRat := by rw [hAV]
    -- the recovered amount converts exactly
    obtain ⟨arn0, harn0, harn_val0, harn_norm0⟩ :=
      STAmount.toNumber_exact_canonical result.assetsRecovered .to_nearest hDc'
    have harn_eq : arn = arn0 := by rw [harn0] at harn; exact (Except.ok.inj harn).symm
    have harn_val : arn.toRat = result.assetsRecovered.toRat := by
      rw [harn_eq]; exact harn_val0
    have harn_norm : arn.isNormalized := by rw [harn_eq]; exact harn_norm0
    have harn_nn : 0 ≤ arn.toRat := by rw [harn_val]; exact hDnn'
    have hle_a : arn.toRat ≤ v.assetsTotal.toRat := by
      rw [harn_val, ← hAVval]; exact hDle'
    -- asset field updates
    have hat_norm : at'.isNormalized :=
      operator_sub_isNormalized_to_nearest' _ _ _ hv.wf.assetsTotal_norm harn_norm hat
    have hat_nn : 0 ≤ at'.toRat :=
      operator_sub_nonneg _ _ _ hv.wf.assetsTotal_norm harn_norm hat (by linarith)
    rw [hAV, hat] at hav
    have hae : at' = av' := Except.ok.inj hav
    subst hae
    -- share field update, exact
    have hS_den : result.sharesDestroyed.toRat.den = 1 :=
      STAmount.IntegralCanonical.den_eq_one _ hSc'
    have hS_mval : ((result.sharesDestroyed.mValue.toNat : ℕ) : ℚ)
        = result.sharesDestroyed.toRat :=
      STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg _ hSc' hSnn_val
    have hsz : result.sharesDestroyed.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 : ((result.sharesDestroyed.mValue.toNat : ℕ) : ℚ)
          ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
        rw [hS_mval]
        calc result.sharesDestroyed.toRat ≤ v.sharesTotal.toRat := le_of_lt hslt'
          _ ≤ 2 ^ 63 - 1 := hfit'
          _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
      exact_mod_cast h1
    obtain ⟨sdn0, hsdn0, hsdn_val0, hsdn_norm0⟩ :=
      STAmount.toNumber_integral_small_exact result.sharesDestroyed .to_nearest hSc' hsz
    have hsdn_eq : sdn = sdn0 := by rw [hsdn0] at hsdn; exact (Except.ok.inj hsdn).symm
    have hsdn_val : sdn.toRat = result.sharesDestroyed.toRat := by
      rw [hsdn_eq]; exact hsdn_val0
    have hsdn_norm : sdn.isNormalized := by rw [hsdn_eq]; exact hsdn_norm0
    have hsdn_den : sdn.toRat.den = 1 := by rw [hsdn_val]; exact hS_den
    have hdiff_den : (v.sharesTotal.toRat - sdn.toRat).den = 1 := by
      rw [rat_sub_eq_num_cast _ _ hv.wf.sharesTotal_int hsdn_den]
      exact Rat.den_intCast _
    have hdiff_nn : 0 ≤ v.sharesTotal.toRat - sdn.toRat := by
      rw [hsdn_val]; linarith
    have hdiff_le : v.sharesTotal.toRat - sdn.toRat ≤ 2 ^ 63 - 1 := by
      rw [hsdn_val]; linarith
    obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal sdn st'
      hv.wf.sharesTotal_norm hsdn_norm hv.wf.sharesTotal_int hsdn_den
      (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
    have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hdiff_nn
    have hst_norm : st'.isNormalized :=
      operator_sub_isNormalized_to_nearest' _ _ _ hv.wf.sharesTotal_norm hsdn_norm hst
    have hst_ne : st'.toRat ≠ 0 := by
      rw [hst_val, hsdn_val]
      have hge1 : 1 ≤ v.sharesTotal.toRat - result.sharesDestroyed.toRat :=
        rat_one_le_sub_of_lt _ _ hv.wf.sharesTotal_int hS_den hslt'
      intro hc
      linarith
    show ({ v with sharesTotal := st', assetsAvailable := at', assetsTotal := at' }
      : Vault).Lawful
    refine ⟨⟨hat_norm, hat_norm, hv.wf.assetsMaximum_norm, hst_norm,
      hv.wf.interestUnrealized_norm, hv.wf.lossUnrealized_norm, hst_nn, hst_den,
      hv.wf.scale_integral, hv.wf.scale_le⟩,
      ⟨hat_nn, hat_nn, le_refl _, hv.valid.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩⟩
    · -- empty_shares: the strict share bound keeps the remainder positive
      intro h0
      exfalso
      have h0' : st'.toRat.num.toNat = 0 := h0
      have hcast := rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn
      rw [h0'] at hcast
      exact hst_ne (by exact_mod_cast hcast.symm)
    · -- cap
      intro mq hm
      have hm' : mq ∈ v.assetsMaximum.map Number.toRat := hm
      rw [Option.mem_map] at hm'
      obtain ⟨n, hn, rfl⟩ := hm'
      have hcapn : v.assetsTotal.toRat ≤ n.toRat :=
        hv.valid.cap n.toRat (Option.mem_map.mpr ⟨n, hn, rfl⟩)
      exact operator_sub_le_of_le_normalized _ _ _ _ hv.wf.assetsTotal_norm harn_norm
        hat (hv.wf.assetsMaximum_norm n hn) (by linarith)
    · exact le_of_eq hL.symm
    · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]
      linarith
    · exact le_of_eq hI.symm
    · show v.interestUnrealized.toRat ≤ at'.toRat - at'.toRat
      rw [show v.interestUnrealized.toRat = 0 from hI]
      linarith
    · intro h
      have h' : (0 : ℚ) < at'.toRat := h
      show v.interestUnrealized.toRat < at'.toRat
      rw [show v.interestUnrealized.toRat = 0 from hI]
      exact h'
    · show 0 ≤ at'.toRat - v.interestUnrealized.toRat - v.lossUnrealized.toRat
      rw [show v.interestUnrealized.toRat = 0 from hI,
        show v.lossUnrealized.toRat = 0 from hL]
      linarith
    · intro h
      exfalso
      have h' : (0 : ℚ) < v.interestUnrealized.toRat := h
      rw [show v.interestUnrealized.toRat = 0 from hI] at h'
      exact absurd h' (lt_irrefl 0)

theorem Vault.burnShares_lawful (sharesDestroyed sharesTotalAmount : STAmount) (v' : Vault)
    (hv : v.Lawful) -- the starting vault is lawful
    (hcan : v.canBurnShares = .ok (.assets sharesTotalAmount)) -- the burn permission guard passed
    (hcanon : sharesDestroyed.IntegralCanonical) -- stored as a plain integral amount
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat) -- a holder cannot burn more than exists
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) -- the share total fits int64
    (hok : v.burnShares sharesDestroyed = .ok v') :
    v'.Lawful := by
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    Vault.WF.toExact_sharesTotal v hv.wf
  have hsta_val : sharesTotalAmount.toRat = (v.toExact.sharesTotal : ℚ) :=
    Vault.canBurnShares_assets_exact v sharesTotalAmount hv hcan hfit
  have hle' : sharesDestroyed.toRat ≤ v.sharesTotal.toRat := by
    rw [← hST, ← hsta_val]; exact hle
  have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
  have hsd_nn : 0 ≤ sharesDestroyed.toRat := STAmount.toRat_nonneg_of sharesDestroyed hnn
  have hsd_den : sharesDestroyed.toRat.den = 1 :=
    STAmount.IntegralCanonical.den_eq_one sharesDestroyed hcanon
  -- guard components: shares outstanding, both asset totals zero
  have hguard : v.sharesTotal.mantissa_ ≠ 0 ∧ v.assetsTotal.mantissa_ = 0 ∧
      v.assetsAvailable.mantissa_ = 0 := by
    unfold Vault.canBurnShares at hcan
    by_cases hg : (v.sharesTotal.mantissa_ == 0 ||
        (v.assetsTotal.mantissa_ != 0 || v.assetsAvailable.mantissa_ != 0)) = true
    · rw [if_pos hg, epure] at hcan
      exact absurd (Except.ok.inj hcan) (fun h => CanBurnSharesResult.noConfusion h)
    · rw [Bool.or_eq_true, Bool.or_eq_true] at hg
      push_neg at hg
      obtain ⟨h1, h2, h3⟩ := hg
      refine ⟨?_, ?_, ?_⟩
      · intro h; exact h1 (by rw [h]; rfl)
      · by_contra h
        exact h2 (by simpa using h)
      · by_contra h
        exact h3 (by simpa using h)
  obtain ⟨hshares_ne, hAT_m0, hAV_m0⟩ := hguard
  have hAT0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAT_m0
  have hAV0 : v.assetsAvailable.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAV_m0
  -- both unrealized fields are zero on this state
  have hIU0 : v.interestUnrealized.toRat = 0 :=
    le_antisymm (by
      have h1 := hv.valid.interestUnrealized_le
      have h2 : v.toExact.assetsTotal - v.toExact.assetsAvailable = 0 := by
        show v.assetsTotal.toRat - v.assetsAvailable.toRat = 0
        rw [hAT0, hAV0]; ring
      rw [h2] at h1
      exact h1) hv.valid.interestUnrealized_nonneg
  have hLU0 : v.lossUnrealized.toRat = 0 :=
    le_antisymm (by
      have h1 := hv.valid.lossUnrealized_le
      have h2 : v.toExact.assetsTotal - v.toExact.assetsAvailable = 0 := by
        show v.assetsTotal.toRat - v.assetsAvailable.toRat = 0
        rw [hAT0, hAV0]; ring
      rw [h2] at h1
      exact h1) hv.valid.lossUnrealized_nonneg
  -- the destroyed amount converts exactly
  have hsz : sharesDestroyed.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have hmval : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) = sharesDestroyed.toRat :=
      STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sharesDestroyed hcanon hsd_nn
    have h1 : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
      rw [hmval]
      calc sharesDestroyed.toRat ≤ v.sharesTotal.toRat := hle'
        _ ≤ 2 ^ 63 - 1 := hfit'
        _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
    exact_mod_cast h1
  obtain ⟨sdn, hsdn_ok, hsdn_val, hsdn_norm⟩ :=
    STAmount.toNumber_integral_small_exact sharesDestroyed .to_nearest hcanon hsz
  -- walk the burn
  unfold Vault.burnShares at hok
  obtain ⟨sdn', hsdn', hok⟩ := bind_ok_peel _ _ _ hok
  have hsdn'_eq : sdn' = sdn := by rw [hsdn_ok] at hsdn'; exact (Except.ok.inj hsdn').symm
  rw [hsdn'_eq] at hok
  obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
  have hv' : v' = { v with sharesTotal := st' } :=
    (Except.ok.inj (show Except.ok ({ v with sharesTotal := st' } : Vault)
      = Except.ok v' from hok)).symm
  subst hv'
  -- the subtraction is exact
  have hsdn_den : sdn.toRat.den = 1 := by rw [hsdn_val]; exact hsd_den
  have hdiff_den : (v.sharesTotal.toRat - sdn.toRat).den = 1 := by
    rw [rat_sub_eq_num_cast _ _ hv.wf.sharesTotal_int hsdn_den]
    exact Rat.den_intCast _
  have hdiff_nn : 0 ≤ v.sharesTotal.toRat - sdn.toRat := by rw [hsdn_val]; linarith
  have hdiff_le : v.sharesTotal.toRat - sdn.toRat ≤ 2 ^ 63 - 1 := by
    rw [hsdn_val]; linarith
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal sdn st'
    hv.wf.sharesTotal_norm hsdn_norm hv.wf.sharesTotal_int hsdn_den
    (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hdiff_nn
  have hst_norm : st'.isNormalized :=
    operator_sub_isNormalized_to_nearest' _ _ _ hv.wf.sharesTotal_norm hsdn_norm hst
  refine ⟨⟨hv.wf.assetsTotal_norm, hv.wf.assetsAvailable_norm, hv.wf.assetsMaximum_norm,
    hst_norm, hv.wf.interestUnrealized_norm, hv.wf.lossUnrealized_norm, hst_nn, hst_den,
    hv.wf.scale_integral, hv.wf.scale_le⟩,
    ⟨hv.valid.assetsTotal_nonneg, hv.valid.assetsAvailable_nonneg,
    hv.valid.assetsAvailable_le, hv.valid.assetsMaximum_pos, ?_, hv.valid.cap, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- empty_shares: both totals are zero on a burnable state
    intro _
    exact ⟨hAT0, hAV0⟩
  · exact le_of_eq hLU0.symm
  · show v.lossUnrealized.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat
    rw [hLU0, hAT0, hAV0]
    linarith
  · exact le_of_eq hIU0.symm
  · show v.interestUnrealized.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat
    rw [hIU0, hAT0, hAV0]
    linarith
  · intro h
    exfalso
    have h' : (0 : ℚ) < v.assetsTotal.toRat := h
    rw [hAT0] at h'
    exact absurd h' (lt_irrefl 0)
  · show 0 ≤ v.assetsTotal.toRat - v.interestUnrealized.toRat - v.lossUnrealized.toRat
    rw [hIU0, hLU0, hAT0]
    linarith
  · intro h
    exfalso
    have h' : (0 : ℚ) < v.interestUnrealized.toRat := h
    rw [hIU0] at h'
    exact absurd h' (lt_irrefl 0)

end XRPL.Model.SingleAssetVault
