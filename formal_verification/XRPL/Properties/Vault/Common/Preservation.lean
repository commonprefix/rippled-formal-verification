import XRPL.Properties.Vault.Common.Unchanged
import XRPL.Properties.Vault.Common.LawfulSupport
import XRPL.Properties.Vault.LawfulVaultValid
import XRPL.Properties.Vault.Common.DepositWiring
import XRPL.Properties.Vault.Common.ClawbackAccuracy
import XRPL.Properties.Vault.VaultBurn
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultBurn

/-! # No operation writes `lossUnrealized`

Each operation's do-block updates only `assetsTotal`, `assetsAvailable`, and
`sharesTotal` on success, and returns the starting vault on rejection, so
`lossUnrealized` is unchanged in `r.vault'` on every exit. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A deposit keeps both unrealized fields at their starting values. -/
theorem LawfulVault.deposit_preserves_unrealized (lv : LawfulVault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : lv.deposit amountDeposit isDonation = .ok r) :
    r.vault'.lossUnrealized = lv.lossUnrealized := by
  by_cases herr : r.error.isSome = true
  · rw [LawfulVault.deposit_error_unchanged_proof lv amountDeposit isDonation r hok herr]
  · -- success: the reduction pins `r.vault'` to a record that keeps `lossUnrealized`
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrv⟩ :=
      LawfulVault.deposit_success_reduces lv amountDeposit isDonation r hok
        (Option.not_isSome_iff_eq_none.mp herr)
    rw [hrv]

/-- A withdrawal keeps both unrealized fields at their starting values. -/
theorem LawfulVault.withdraw_preserves_unrealized (lv : LawfulVault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.vault'.lossUnrealized = lv.lossUnrealized := by
  by_cases herr : r.error.isSome = true
  · rw [LawfulVault.withdraw_error_unchanged_proof lv amount waiveUnrealizedLoss r hok herr]
  · -- success: both exit records keep `lossUnrealized`
    obtain ⟨cw, aN, sta, _, _, _, _, _, _, hdisj⟩ :=
      LawfulVault.withdraw_success_reduces lv amount waiveUnrealizedLoss r hok
        (Option.not_isSome_iff_eq_none.mp herr)
    rcases hdisj with ⟨_, _, _, _, _, hrv⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrv⟩
    · rw [hrv]
    · rw [hrv]

/-- A clawback keeps both unrealized fields at their starting values. -/
theorem LawfulVault.clawback_preserves_unrealized (lv : LawfulVault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : lv.clawback assets holderShares = .ok r) :
    r.vault'.lossUnrealized = lv.lossUnrealized := by
  by_cases herr : r.error.isSome = true
  · rw [LawfulVault.clawback_error_unchanged_proof lv assets holderShares r hok herr]
  · -- success: the reduction pins `r.vault'` to a record that keeps `lossUnrealized`
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrv⟩ :=
      LawfulVault.clawback_success_reduces lv assets holderShares r hok
        (Option.not_isSome_iff_eq_none.mp herr)
    rw [hrv]

/-- `burnShares` writes only `sharesTotal`, so both unrealized fields carry
over unchanged. -/
theorem LawfulVault.burnShares_preserves_unrealized (lv : LawfulVault) (sharesDestroyed : STAmount)
    (lv' : LawfulVault) (hok : lv.burnShares sharesDestroyed = .ok lv') :
    lv'.lossUnrealized = lv.lossUnrealized := by
  unfold LawfulVault.burnShares at hok
  simp only [] at hok
  obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
  rw [(RawVault.to_lawful_ok hok).1]

/-- On a vault with no unrealized loss, the withdrawal pricing subtraction returns
exactly the net asset value, discharging the `WithdrawNavExact` hypothesis. -/
theorem LawfulVault.withdrawNavExact_of_zero (lv : LawfulVault) (waiveUnrealizedLoss : Bool)
    (hL : lv.toExact.lossUnrealized = 0) :
    lv.WithdrawNavExact waiveUnrealizedLoss := by
  have hL0 : lv.lossUnrealized = Number.zero := by
    have hmz : lv.lossUnrealized.mantissa_ = 0 := by
      by_contra h; exact (Number.toRat_ne_zero_of_mantissa_ne_zero lv.lossUnrealized h) hL
    exact Number.eq_zero_of_mantissa_zero lv.lossUnrealized lv.wf.lossUnrealized_norm hmz
  refine ⟨lv.assetsTotal, ?_, ?_⟩
  · cases waiveUnrealizedLoss with
    | true => exact operator_sub_zero_right _ _
    | false => rw [hL0]; exact operator_sub_zero_right _ _
  · split
    · simp only [RawVault.depositNav, RawVault.toExact]
    · simp only [RawVault.withdrawNav, RawVault.toExact]
      rw [show lv.lossUnrealized.toRat = 0 from hL]; ring

/-- The amount taken and the shares issued by a deposit are both nonnegative,
whether the run succeeds or is rejected (a rejection reports zero amounts). -/
theorem LawfulVault.deposit_result_nonneg (lv : LawfulVault) (amount : STAmount) (isDonation : Bool)
    (hcanon : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (r : DepositResult) (hok : lv.deposit amount isDonation = .ok r) :
    0 ≤ r.amountDeposit'.toRat ∧ 0 ≤ r.sharesIssued.toRat := by
  by_cases herr : r.error.isSome = true
  · obtain ⟨-, haz, hsz⟩ := LawfulVault.deposit_error_rejected_proof lv amount isDonation r hok herr
    rw [haz, hsz, STAmount.zero_toRat, STAmount.zero_int64_toRat]
    exact ⟨le_refl 0, le_refl 0⟩
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, _hsh_don, _hins, hdon_eq, hcomp,
      _hcN, _hsN, _hat, _hav, _hst, _hmax, hamt, hshr, _⟩ :=
      LawfulVault.deposit_success_reduces lv amount isDonation r hok herr'
    rw [hamt, hshr]
    have hamCanon : am.Canonical := by
      rcases roundToVaultExponent_canonical_or_isZero amount am lv.assetsTotal hcanon hround
        with hc | hz
      · exact hc
      · rw [hz] at hamz; exact absurd hamz (by decide)
    have ham_nn : 0 ≤ am.toRat :=
      RawVault.roundToVaultExponent_nonneg amount am lv.assetsTotal hcanon hnn hround
    have ham_ne : am.mValue ≠ 0 := by unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
    have ham_pos : 0 < am.toRat :=
      lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
    by_cases hd : isDonation = true
    · obtain ⟨haD, hsC⟩ := hdon_eq hd
      refine ⟨?_, ?_⟩
      · show 0 ≤ aD.toRat; rw [haD]; exact ham_nn
      · show 0 ≤ sC.toRat; rw [hsC, STAmount.zero_int64_toRat]
    · have hd' : isDonation = false := by simpa using hd
      obtain ⟨shares, hats, hshz, hsad, -, hseq⟩ :=
        computeDeposit_success_reduces lv am aD sC (hcomp hd')
      obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical lv am shares hats
      have hshpos : 0 < shares.toRat :=
        assetsToSharesDeposit_pos lv am shares hamCanon ham_pos hats hshz
      refine ⟨?_, ?_⟩
      · show 0 ≤ aD.toRat
        exact sharesToAssetsDeposit_nonneg lv shares aD hshc hshnt hshpos hsad
      · show 0 ≤ sC.toRat; rw [hseq]; exact le_of_lt hshpos

/-- The amount paid by a withdrawal is nonnegative, whether the run succeeds or is
rejected. On a rejection the payout is zero; on the final withdrawal it is the
`ofNumber` snap of the nonnegative `assetsAvailable`; on a partial withdrawal it is
the `sharesToAssetsWithdraw` payout of the (nonnegative canonical) burned shares. -/
theorem LawfulVault.withdraw_assets_nonneg (lv : LawfulVault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool)
    (hL : lv.toExact.lossUnrealized = 0)
    (r : WithdrawResult) (hok : lv.withdraw amount waiveUnrealizedLoss = .ok r)
    (hSc : r.sharesBurned.IntegralCanonical) (hSnt : r.sharesBurned.mNumericType = .int64)
    (hSnn : r.sharesBurned.negative = false) :
    0 ≤ r.assets'.toRat := by
  by_cases herr : r.error.isSome = true
  · obtain ⟨-, haz, -⟩ := LawfulVault.withdraw_error_rejected_proof lv amount waiveUnrealizedLoss r hok herr
    rw [haz, STAmount.zero_toRat]
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨result, aN, sta, _hres, _hcw_err, _haN, _hlt, hsta, hsb, hbranch⟩ :=
      LawfulVault.withdraw_success_reduces lv amount waiveUnrealizedLoss r hok herr'
    rcases hbranch with ⟨_, _, allAvail, hallAvail, hras, _⟩ |
        ⟨hne, sN, at', av', st', _, _, _hsN, _hat, _, _, _, _hav, _hst, _, _⟩
    · rw [hras]
      have hAA_neg : lv.assetsAvailable.negative_ = false :=
        Number.negative_false_of_norm_nonneg lv.assetsAvailable lv.wf.assetsAvailable_norm
          lv.exact.assetsAvailable_nonneg
      exact STAmount.ofNumber_signfalse_nonneg lv.numericType lv.assetsAvailable .to_nearest allAvail
        lv.wf.assetsAvailable_norm hAA_neg hallAvail
    · have hfin : r.sharesBurned.operator_eq sta = false := by rw [hsb]; exact hne
      have hprice : lv.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok r.assets' :=
        LawfulVault.withdraw_payout_priced lv amount waiveUnrealizedLoss sta r hok herr' hsta hfin
      have hSnn_val : 0 ≤ r.sharesBurned.toRat := STAmount.toRat_nonneg_of _ hSnn
      have hSC_canon : r.sharesBurned.Canonical := by
        refine ⟨fun _ => ⟨hSc, ?_⟩, fun hf => ?_⟩
        · rw [hSnt]; decide
        · rw [show r.sharesBurned.integral = r.sharesBurned.mNumericType.isIntegral
            from rfl, hSnt] at hf
          exact absurd hf (by decide)
      have hnavE : lv.WithdrawNavExact waiveUnrealizedLoss :=
        LawfulVault.withdrawNavExact_of_zero lv waiveUnrealizedLoss hL
      exact (LawfulVault.sharesToAssetsWithdraw_spec lv r.sharesBurned r.assets'
        waiveUnrealizedLoss hSnn_val hSC_canon hnavE hprice).1
/-- **Post-state lawfulness for `deposit`.** A successful deposit's computed record
re-validates: its in-op `to_lawful` re-check returns `.ok lv'`. -/
theorem LawfulVault.deposit_poststate_lawful (lv : LawfulVault) (amount : STAmount) (isDonation : Bool)
    (hL : lv.toExact.lossUnrealized = 0)
    (hAV : lv.assetsAvailable = lv.assetsTotal)
    (hcanon : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (am aD sC : STAmount) (cN sN at' av' st' : Number)
    (hround : roundToVaultExponent amount lv.assetsTotal = .ok am)
    (hamz : am.isZero = false)
    (hsh_don : isDonation = true → lv.sharesTotal.mantissa_ ≠ 0)
    (hdon_eq : isDonation = true → aD = am ∧ sC = STAmount.zero .int64)
    (hcomp : isDonation = false → computeDeposit lv am = .ok (.success aD sC))
    (hcN : aD.toNumber .to_nearest = .ok cN) (hsN : sC.toNumber .to_nearest = .ok sN)
    (hat : lv.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : lv.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : lv.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((lv.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (lv.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (lv.toExact.sharesTotal : ℚ) + sC.toRat ≤ 2 ^ 63 - 1) :
    ∃ lv' : LawfulVault,
      ({ lv.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok lv' ∧
      lv'.toRawVault = { lv.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
    -- storage-canonicity and sign facts for the run's outputs: the taken amount
    -- from `roundToVaultExponent` / `sharesToAssetsDeposit`, shares from `assetsToSharesDeposit`
    have hfacts : cN.toRat = aD.toRat ∧ cN.isNormalized ∧ 0 ≤ aD.toRat ∧
        sC.IntegralCanonical ∧ 0 ≤ sC.toRat := by
      have hamCanon : am.Canonical := by
        rcases roundToVaultExponent_canonical_or_isZero amount am lv.assetsTotal hcanon hround
          with hc | hz
        · exact hc
        · rw [hz] at hamz; exact absurd hamz (by decide)
      have ham_nn : 0 ≤ am.toRat :=
        RawVault.roundToVaultExponent_nonneg amount am lv.assetsTotal hcanon hnn hround
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
        obtain ⟨shares, hats, hshz, hsad, -, hseq⟩ :=
          computeDeposit_success_reduces lv am aD sC (hcomp hd')
        obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical lv am shares hats
        have hshpos : 0 < shares.toRat :=
          assetsToSharesDeposit_pos lv am shares hamCanon ham_pos hats hshz
        obtain ⟨hcN_val, hcN_norm⟩ :=
          sharesToAssetsDeposit_toNumber_exact lv shares aD cN hshc hshnt hsad hcN
        exact ⟨hcN_val, hcN_norm,
          sharesToAssetsDeposit_nonneg lv shares aD hshc hshnt hshpos hsad,
          hseq ▸ hshc, by rw [hseq]; exact le_of_lt hshpos⟩
    obtain ⟨hcN_val, hcN_norm, hDnn', hSc', hSnn'⟩ := hfacts
    have hST : ((lv.toExact.sharesTotal : ℕ) : ℚ) = lv.sharesTotal.toRat :=
      RawVault.WF.toExact_sharesTotal lv.toRawVault lv.wf
    have hSsz' : lv.sharesTotal.toRat + sC.toRat ≤ 2 ^ 63 - 1 := by
      rw [← hST]; exact hSsz
    have hST_nn : 0 ≤ lv.sharesTotal.toRat := lv.wf.sharesTotal_nonneg
    have hAT_nn : (0 : ℚ) ≤ lv.assetsTotal.toRat := lv.exact.assetsTotal_nonneg
    have hcN_nn : 0 ≤ cN.toRat := by rw [hcN_val]; exact hDnn'
    -- asset field updates
    have hat_norm : at'.isNormalized :=
      operator_add_isNormalized_to_nearest' _ _ _ lv.wf.assetsTotal_norm hcN_norm hat
    have hat_nn : 0 ≤ at'.toRat :=
      operator_add_nonneg _ _ _ lv.wf.assetsTotal_norm hcN_norm hat (by linarith)
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
        have hst_eq : st' = lv.sharesTotal := (Except.ok.inj hst).symm
        have hmant := hsh_don hd
        refine ⟨hst_eq ▸ lv.wf.sharesTotal_norm, hst_eq ▸ hST_nn,
          hst_eq ▸ lv.wf.sharesTotal_int, ?_⟩
        rw [hst_eq]
        exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hmant
      · have hd' : isDonation = false := by simpa using hd
        obtain ⟨shares, _, hshz, _, _, hsh_eq⟩ :=
          computeDeposit_success_reduces lv am aD sC (hcomp hd')
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
            calc sC.toRat ≤ lv.sharesTotal.toRat + sC.toRat := by linarith
              _ ≤ 2 ^ 63 - 1 := hSsz'
              _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
          exact_mod_cast h1
        obtain ⟨sN0, hsN0, hsN_val0, hsN_norm0⟩ :=
          STAmount.toNumber_integral_small_exact sC .to_nearest hSc' hsz
        have hsN_eq : sN = sN0 := by rw [hsN0] at hsN; exact (Except.ok.inj hsN).symm
        have hsN_val : sN.toRat = sC.toRat := by rw [hsN_eq]; exact hsN_val0
        have hsN_norm : sN.isNormalized := by rw [hsN_eq]; exact hsN_norm0
        have hsN_den : sN.toRat.den = 1 := by rw [hsN_val]; exact hsC_den
        have hsum_den : (lv.sharesTotal.toRat + sN.toRat).den = 1 := by
          rw [rat_add_eq_num_cast _ _ lv.wf.sharesTotal_int hsN_den]
          exact Rat.den_intCast _
        have hsum_nn : 0 ≤ lv.sharesTotal.toRat + sN.toRat := by
          rw [hsN_val]; linarith
        have hsum_le : lv.sharesTotal.toRat + sN.toRat ≤ 2 ^ 63 - 1 := by
          rw [hsN_val]; exact hSsz'
        obtain ⟨hst_val, hst_den⟩ := operator_add_exact_int lv.sharesTotal sN st'
          lv.wf.sharesTotal_norm hsN_norm lv.wf.sharesTotal_int hsN_den
          (rat_num_natAbs_lt_of_le _ hsum_den hsum_nn hsum_le) hst
        refine ⟨operator_add_isNormalized_to_nearest' _ _ _ lv.wf.sharesTotal_norm
          hsN_norm hst, by rw [hst_val]; exact hsum_nn, hst_den, ?_⟩
        rw [hst_val, hsN_val]
        have : 0 < lv.sharesTotal.toRat + sC.toRat := by linarith
        exact ne_of_gt this
    obtain ⟨hst_norm, hst_nn, hst_den, hst_ne⟩ := hshares
    -- the updated record is well-formed and exactly valid, so `to_lawful` succeeds
    have hwfE : ({ lv with assetsTotal := at', assetsAvailable := at', sharesTotal := st' } : RawVault).WF :=
      ⟨hat_norm, hat_norm, lv.wf.assetsMaximum_norm, hst_norm,
        lv.wf.lossUnrealized_norm, hst_nn, hst_den,
        lv.wf.scale_integral, lv.wf.scale_le, Number.operator_sub_self_ok at' .downward⟩
    refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
      ⟨hat_nn, hat_nn, le_refl _, lv.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩)
    · -- empty_shares: the new share total is nonzero
      intro h0
      exfalso
      have h0' : st'.toRat.num.toNat = 0 := h0
      have := rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn
      rw [h0'] at this
      exact hst_ne (by exact_mod_cast this.symm)
    · -- cap
      intro mq hm
      have hm' : mq ∈ lv.assetsMaximum.map Number.toRat := hm
      rw [Option.mem_map] at hm'
      obtain ⟨n, hn, rfl⟩ := hm'
      have hn' : lv.assetsMaximum = some n := hn
      rw [hn'] at hmax
      have hnpos : 0 < n.toRat :=
        lv.exact.assetsMaximum_pos n.toRat (Option.mem_map.mpr ⟨n, hn, rfl⟩)
      have hne0 : n.operator_ne Number.zero = true :=
        (operator_ne_iff n Number.zero (lv.wf.assetsMaximum_norm n hn) (Or.inl rfl)).mpr
          (by rw [Number.toRat_zero]; exact ne_of_gt hnpos)
      have hgt : at'.operator_gt n = false := by
        simp only [Option.getD_some, hne0, Bool.true_and] at hmax; exact hmax
      have := (operator_gt_iff at' n hat_norm (lv.wf.assetsMaximum_norm n hn)).not.mp
        (by rw [hgt]; simp)
      exact le_of_not_gt (fun hc => this hc)
    · exact le_of_eq hL.symm
    · show lv.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
      rw [show lv.lossUnrealized.toRat = 0 from hL]
      linarith
    · show 0 ≤ at'.toRat - lv.lossUnrealized.toRat
      rw [show lv.lossUnrealized.toRat = 0 from hL]
      linarith

/-- **Post-state lawfulness for `burnShares`.** The record with only `sharesTotal`
reduced re-validates: its in-op `to_lawful` re-check returns `.ok lv'`. -/
theorem LawfulVault.burnShares_poststate_lawful (lv : LawfulVault)
    (sharesDestroyed sharesTotalAmount : STAmount) (sdn st' : Number)
    (hcan : lv.canBurnShares = .ok (.assets sharesTotalAmount))
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat)
    (hfit : (lv.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sdn)
    (hst : lv.sharesTotal.operator_sub sdn .to_nearest = .ok st') :
    ∃ lv' : LawfulVault, ({ lv.toRawVault with sharesTotal := st' } : RawVault).to_lawful = .ok lv' ∧
      lv'.toRawVault = { lv.toRawVault with sharesTotal := st' } := by
  have hwf := lv.wf
  have hvalid := lv.exact
  have hST : ((lv.toExact.sharesTotal : ℕ) : ℚ) = lv.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal lv.toRawVault hwf
  have hsta_val : sharesTotalAmount.toRat = (lv.toExact.sharesTotal : ℚ) :=
    LawfulVault.canBurnShares_assets_exact lv sharesTotalAmount hcan hfit
  have hle' : sharesDestroyed.toRat ≤ lv.sharesTotal.toRat := by rw [← hST, ← hsta_val]; exact hle
  have hfit' : lv.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
  have hsd_nn : 0 ≤ sharesDestroyed.toRat := STAmount.toRat_nonneg_of sharesDestroyed hnn
  have hsd_den : sharesDestroyed.toRat.den = 1 :=
    STAmount.IntegralCanonical.den_eq_one sharesDestroyed hcanon
  -- guard components: shares outstanding, both asset totals zero
  have hguard : lv.sharesTotal.mantissa_ ≠ 0 ∧ lv.assetsTotal.mantissa_ = 0 ∧
      lv.assetsAvailable.mantissa_ = 0 := by
    unfold LawfulVault.canBurnShares at hcan
    simp only [] at hcan
    by_cases hg : (lv.sharesTotal.mantissa_ == 0 ||
        (lv.assetsTotal.mantissa_ != 0 || lv.assetsAvailable.mantissa_ != 0)) = true
    · rw [if_pos hg, epure] at hcan
      exact absurd (Except.ok.inj hcan) (fun h => CanBurnSharesResult.noConfusion h)
    · rw [Bool.or_eq_true, Bool.or_eq_true] at hg
      push_neg at hg
      obtain ⟨h1, h2, h3⟩ := hg
      exact ⟨fun h => h1 (by rw [h]; rfl), by by_contra h; exact h2 (by simpa using h),
        by by_contra h; exact h3 (by simpa using h)⟩
  obtain ⟨hshares_ne, hAT_m0, hAV_m0⟩ := hguard
  have hAT0 : lv.assetsTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAT_m0
  have hAV0 : lv.assetsAvailable.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAV_m0
  have hLU0 : lv.lossUnrealized.toRat = 0 :=
    le_antisymm (by
      have h1 := hvalid.lossUnrealized_le
      have h2 : lv.toExact.assetsTotal - lv.toExact.assetsAvailable = 0 := by
        show lv.assetsTotal.toRat - lv.assetsAvailable.toRat = 0
        rw [hAT0, hAV0]; ring
      rw [h2] at h1; exact h1) hvalid.lossUnrealized_nonneg
  have hsz : sharesDestroyed.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have hmval : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) = sharesDestroyed.toRat :=
      STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sharesDestroyed hcanon hsd_nn
    have h1 : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
      rw [hmval]
      calc sharesDestroyed.toRat ≤ lv.sharesTotal.toRat := hle'
        _ ≤ 2 ^ 63 - 1 := hfit'
        _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
    exact_mod_cast h1
  obtain ⟨sdn0, hsdn0_ok, hsdn_val, hsdn_norm⟩ :=
    STAmount.toNumber_integral_small_exact sharesDestroyed .to_nearest hcanon hsz
  have hsdn_eq : sdn = sdn0 := by rw [hsdn0_ok] at hnum; exact (Except.ok.inj hnum).symm
  rw [hsdn_eq] at hst
  -- the subtraction is exact
  have hsdn_den : sdn0.toRat.den = 1 := by rw [hsdn_val]; exact hsd_den
  have hdiff_den : (lv.sharesTotal.toRat - sdn0.toRat).den = 1 := by
    rw [rat_sub_eq_num_cast _ _ hwf.sharesTotal_int hsdn_den]; exact Rat.den_intCast _
  have hdiff_nn : 0 ≤ lv.sharesTotal.toRat - sdn0.toRat := by rw [hsdn_val]; linarith
  have hdiff_le : lv.sharesTotal.toRat - sdn0.toRat ≤ 2 ^ 63 - 1 := by rw [hsdn_val]; linarith
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int lv.sharesTotal sdn0 st'
    hwf.sharesTotal_norm hsdn_norm hwf.sharesTotal_int hsdn_den
    (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hdiff_nn
  have hst_norm : st'.isNormalized :=
    operator_sub_isNormalized_to_nearest' _ _ _ hwf.sharesTotal_norm hsdn_norm hst
  have hwfE : ({ lv with sharesTotal := st' } : RawVault).WF :=
    ⟨hwf.assetsTotal_norm, hwf.assetsAvailable_norm, hwf.assetsMaximum_norm,
      hst_norm, hwf.lossUnrealized_norm, hst_nn, hst_den,
      hwf.scale_integral, hwf.scale_le, hwf.assetsTotal_sub_ok⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨hvalid.assetsTotal_nonneg, hvalid.assetsAvailable_nonneg,
      hvalid.assetsAvailable_le, hvalid.assetsMaximum_pos, ?_, hvalid.cap, ?_, ?_, ?_⟩)
  · intro _; exact ⟨hAT0, hAV0⟩
  · exact le_of_eq hLU0.symm
  · show lv.lossUnrealized.toRat ≤ lv.assetsTotal.toRat - lv.assetsAvailable.toRat
    rw [hLU0, hAT0, hAV0]; linarith
  · show 0 ≤ lv.assetsTotal.toRat - lv.lossUnrealized.toRat
    rw [hLU0, hAT0]; linarith

/-- **Post-state lawfulness for a subtracting exit (withdraw non-final / clawback).**
Subtracting one payout from both asset totals and one burn from `sharesTotal`
re-validates. `hempty`: dropping to zero shares must also zero the assets. -/
theorem LawfulVault.withdraw_poststate_lawful (lv : LawfulVault)
    (payout burned at' av' st' : Number)
    (hL : lv.toExact.lossUnrealized = 0)
    (hAV : lv.assetsAvailable = lv.assetsTotal)
    (hp_norm : payout.isNormalized) (hp_nn : 0 ≤ payout.toRat)
    (hp_le : payout.toRat ≤ lv.assetsTotal.toRat)
    (hb_norm : burned.isNormalized) (hb_nn : 0 ≤ burned.toRat)
    (hb_den : burned.toRat.den = 1) (hb_le : burned.toRat ≤ lv.sharesTotal.toRat)
    (hfit : lv.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hat : lv.assetsTotal.operator_sub payout .to_nearest = .ok at')
    (hav : lv.assetsAvailable.operator_sub payout .to_nearest = .ok av')
    (hst : lv.sharesTotal.operator_sub burned .to_nearest = .ok st')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ lv' : LawfulVault,
      ({ lv.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok lv' ∧
      lv'.toRawVault = { lv.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  -- new asset total: normalized, nonnegative, and at or below the starting total
  have hat_norm : at'.isNormalized :=
    operator_sub_isNormalized_to_nearest' _ _ _ lv.wf.assetsTotal_norm hp_norm hat
  have hat_nn : 0 ≤ at'.toRat :=
    operator_sub_nonneg _ _ _ lv.wf.assetsTotal_norm hp_norm hat (by linarith)
  have hat_le : at'.toRat ≤ lv.assetsTotal.toRat := by
    by_cases hpm : payout.mantissa_ = 0
    · exact le_of_eq (congrArg Number.toRat
        (Number.operator_sub_zero_right lv.assetsTotal payout at' hpm hat))
    · by_cases hAm : lv.assetsTotal.mantissa_ = 0
      · exfalso
        have hA0 : lv.assetsTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAm
        have hp0 : payout.toRat = 0 := le_antisymm (by rw [← hA0]; exact hp_le) hp_nn
        exact Number.toRat_ne_zero_of_mantissa_ne_zero payout hpm hp0
      · exact Number.operator_sub_nonneg_le lv.assetsTotal payout at' lv.wf.assetsTotal_norm
          hp_norm hAm hpm lv.exact.assetsTotal_nonneg hp_nn hat
  -- parity: the same payout leaves `assetsAvailable` at the total's new value
  rw [hAV, hat] at hav
  have hae : at' = av' := Except.ok.inj hav
  subst hae
  -- new share total: exact integer decrement, normalized, nonnegative
  have hdiff_den : (lv.sharesTotal.toRat - burned.toRat).den = 1 := by
    rw [rat_sub_eq_num_cast _ _ lv.wf.sharesTotal_int hb_den]; exact Rat.den_intCast _
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int lv.sharesTotal burned st'
    lv.wf.sharesTotal_norm hb_norm lv.wf.sharesTotal_int hb_den
    (rat_num_natAbs_lt_of_le _ hdiff_den (by linarith) (by linarith)) hst
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; linarith
  have hst_norm : st'.isNormalized :=
    operator_sub_isNormalized_to_nearest' _ _ _ lv.wf.sharesTotal_norm hb_norm hst
  -- the decremented record is well-formed and exactly valid, so `to_lawful` succeeds
  have hwfE : ({ lv with assetsTotal := at', assetsAvailable := at', sharesTotal := st' } : RawVault).WF :=
    ⟨hat_norm, hat_norm, lv.wf.assetsMaximum_norm, hst_norm,
      lv.wf.lossUnrealized_norm, hst_nn, hst_den,
      lv.wf.scale_integral, lv.wf.scale_le, Number.operator_sub_self_ok at' .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨hat_nn, hat_nn, le_refl _, lv.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩)
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
    exact le_trans hat_le (lv.exact.cap m hm)
  · exact le_of_eq hL.symm
  · show lv.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
    rw [show lv.lossUnrealized.toRat = 0 from hL]; linarith
  · show 0 ≤ at'.toRat - lv.lossUnrealized.toRat
    rw [show lv.lossUnrealized.toRat = 0 from hL]; linarith

/-- **Post-state lawfulness for the final withdrawal.** The all-zero record (both
asset totals and `sharesTotal` zeroed) re-validates like a freshly created vault. -/
theorem LawfulVault.withdraw_final_poststate_lawful (lv : LawfulVault)
    (hL : lv.toExact.lossUnrealized = 0) :
    ∃ lv' : LawfulVault,
      ({ lv.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } : RawVault).to_lawful = .ok lv' ∧
      lv'.toRawVault = { lv.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  set w : RawVault := { lv with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } with hw_def
  have hz : Number.zero.isNormalized := Or.inl rfl
  -- the exact projections of the zeroed record (loss carries over from `lv`)
  have hAT : w.toExact.assetsTotal = 0 := by simp only [hw_def, RawVault.toExact, Number.toRat_zero]
  have hAV0 : w.toExact.assetsAvailable = 0 := by simp only [hw_def, RawVault.toExact, Number.toRat_zero]
  have hST : w.toExact.sharesTotal = 0 := by
    simp only [hw_def, RawVault.toExact, Number.toRat_zero, Rat.num_zero, Int.toNat_zero]
  have hLU : w.toExact.lossUnrealized = 0 := hL
  have hwfE : w.WF :=
    ⟨hz, hz, lv.wf.assetsMaximum_norm, hz, lv.wf.lossUnrealized_norm,
      by simp only [hw_def, Number.toRat_zero, le_refl],
      by simp only [hw_def, Number.toRat_zero]; rfl,
      lv.wf.scale_integral, lv.wf.scale_le, Number.operator_sub_self_ok Number.zero .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact w hwfE).mpr ?_)
  refine ⟨?_, ?_, ?_, lv.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAT]
  · rw [hAV0]
  · rw [hAV0, hAT]
  · rw [hST, hAT, hAV0]; intro _; exact ⟨rfl, rfl⟩
  · intro m hm; rw [hAT]; exact le_of_lt (lv.exact.assetsMaximum_pos m hm)
  · rw [hLU]
  · rw [hLU, hAT, hAV0]; norm_num
  · rw [hAT, hLU]; norm_num

/-- **Post-state lawfulness for `clawback`.** Delegates to the subtracting-exit
assembly. `hempty`: a recovery that empties the shares must also empty the assets. -/
theorem LawfulVault.clawback_poststate_lawful (lv : LawfulVault)
    (assetsRecoveredNumber sharesDestroyedNumber at' av' st' : Number)
    (hL : lv.toExact.lossUnrealized = 0)
    (hAV : lv.assetsAvailable = lv.assetsTotal)
    (hr_norm : assetsRecoveredNumber.isNormalized) (hr_nn : 0 ≤ assetsRecoveredNumber.toRat)
    (hr_le : assetsRecoveredNumber.toRat ≤ lv.assetsTotal.toRat)
    (hd_norm : sharesDestroyedNumber.isNormalized) (hd_nn : 0 ≤ sharesDestroyedNumber.toRat)
    (hd_den : sharesDestroyedNumber.toRat.den = 1)
    (hd_le : sharesDestroyedNumber.toRat ≤ lv.sharesTotal.toRat)
    (hfit : lv.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hat : lv.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hav : lv.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok av')
    (hst : lv.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ lv' : LawfulVault,
      ({ lv.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } : RawVault).to_lawful = .ok lv' ∧
      lv'.toRawVault = { lv.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } :=
  lv.withdraw_poststate_lawful assetsRecoveredNumber sharesDestroyedNumber at' av' st'
    hL hAV hr_norm hr_nn hr_le hd_norm hd_nn hd_den hd_le hfit hat hav hst hempty

end XRPL.Model.SingleAssetVault
