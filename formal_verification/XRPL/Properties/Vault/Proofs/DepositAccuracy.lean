import XRPL.Properties.Vault.Proofs.DepositAccuracy.Pricing
import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit

/-! # `Vault.deposit` accuracy proofs -/

namespace XRPL.Model.SingleAssetVault.DepAcc

open XRPL.Model.Protocol

/-- The successful deposit paths, step by step. -/
lemma Vault.deposit_success_reduces (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (r : DepositResult) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit isDonation hpos = .ok r)
    (herr : r.error = none) :
    ∃ (amount assetDeposited sharesCreated : STAmount) (cN sN at' av' st' : Number),
      roundToVaultExponent amountDeposit v.assetsTotal = .ok amount ∧
      amount.isZero = false ∧
      (isDonation = true → v.sharesTotal.mantissa_ ≠ 0) ∧
      (isDonation = false → v.isInsolvent = false) ∧
      (isDonation = true → assetDeposited = amount ∧ sharesCreated = STAmount.zero .int64) ∧
      (isDonation = false → ∃ priced,
        computeDeposit v amount = .ok (.success priced sharesCreated) ∧
        clampToSumExponent v.assetsTotal priced = .ok assetDeposited ∧
        assetDeposited.isFractionalNonPositive = .ok false) ∧
      assetDeposited.toNumber .to_nearest = .ok cN ∧
      sharesCreated.toNumber .to_nearest = .ok sN ∧
      v.assetsTotal.operator_add cN .to_nearest = .ok at' ∧
      v.assetsAvailable.operator_add cN .to_nearest = .ok av' ∧
      v.sharesTotal.operator_add sN .to_nearest = .ok st' ∧
      ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
        at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false ∧
      r.amountDeposit' = assetDeposited ∧ r.sharesIssued = sharesCreated ∧
      r.vault'.toRawVault =
        { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  unfold Vault.deposit at hok
  simp only [] at hok
  have hcontra : ∀ ter, DepositResult.rejected v ter = r → False := by
    intro ter h; rw [← h] at herr; simp [DepositResult.rejected] at herr
  obtain ⟨amount, hround, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
      · rw [if_neg h3] at hok
        simp only [pure_bind] at hok
        by_cases hd : isDonation = true
        · -- donation: the charge is the rounded amount, no shares, no clamp
          rw [if_neg (by simp [hd])] at hok
          obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨n3, hn3, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
            at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
          · rw [if_pos hm] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
          · rw [if_neg hm] at hok
            have hsh : v.sharesTotal.mantissa_ ≠ 0 := by
              intro h0
              rw [h0] at h2; simp [hd] at h2
            obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
            obtain rfl := Except.ok.inj hok
            exact ⟨amount, amount, STAmount.zero .int64, n1, n3, at', av', st',
              hround, by simpa using h1, fun _ => hsh, fun h => absurd h (by rw [hd]; decide),
              fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by rw [hd]; decide),
              hn1, hn3, hat, hav, hst, by simpa using hm,
              rfl, rfl, (RawVault.to_lawful_ok htl).1⟩
        · -- real deposit: price with `computeDeposit`, then snap to the sum grid
          rw [if_pos (by simpa using hd)] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          cases cres with
          | error e =>
            simp only [] at hok
            exact absurd (Except.ok.inj hok) (hcontra _)
          | success a s =>
            simp only [] at hok
            obtain ⟨c, hclamp, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨fnp, hfnp, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hf : fnp = true
            · rw [if_pos hf] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
            · rw [if_neg hf] at hok
              obtain rfl : fnp = false := by simpa using hf
              obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨at', hat, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨av', hav, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨n3, hn3, hok⟩ := bind_ok_peel _ _ _ hok
              obtain ⟨st', hst, hok⟩ := bind_ok_peel _ _ _ hok
              by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
                at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
              · rw [if_pos hm] at hok; exact absurd (Except.ok.inj hok) (hcontra _)
              · rw [if_neg hm] at hok
                have hins : v.isInsolvent = false := by
                  have hnd : isDonation = false := by simpa using hd
                  rw [hnd] at h3; simpa using h3
                obtain ⟨v', htl, hok⟩ := bind_ok_peel _ _ _ hok
                obtain rfl := Except.ok.inj hok
                exact ⟨amount, c, s, n1, n3, at', av', st',
                  hround, by simpa using h1,
                  fun h => absurd h (by simp [hd]),
                  fun _ => hins,
                  fun h => absurd h (by simp [hd]),
                  fun _ => ⟨a, hcd, hclamp, hfnp⟩, hn1, hn3, hat, hav, hst, by simpa using hm,
                  rfl, rfl, (RawVault.to_lawful_ok htl).1⟩

end XRPL.Model.SingleAssetVault.DepAcc

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc

/-- Proof body of `Vault.deposit_charge_integral`. The rounded amount equals the
integral input (identity pass), the issued shares are a positive `int64` count,
and the proven `sharesToAssetsDeposit_charge_integral_bound` bounds the overcharge. -/
lemma Vault.deposit_charge_integral_proof (v : Vault) (amountDeposit : STAmount)
    (r : DepositResult) (hcanon : amountDeposit.Canonical)
    (hint : v.numericType.isIntegral = true) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    r.amountDeposit'.toRat - v.idealChargeDeposit r.sharesIssued.toRat ≤
      1 + v.idealChargeDeposit r.sharesIssued.toRat * depositε := by
  obtain ⟨amount, c, sh, cN, sN, at', av', st', hround, hanz, _, _, _, hcd, _, _, _, _, _, _, hamt, hshr, _⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit false r hpos hok herr
  obtain ⟨priced, hcdp, hclamp, -⟩ := hcd rfl
  obtain ⟨shares, hats, hsz, hsad, hgt, hsheq⟩ :=
    computeDeposit_success_reduces v amount priced sh hcdp
  -- the charge is the vault's integral type, and it is comparable to `amount`
  have hcty : priced.mNumericType = v.numericType :=
    (sharesToAssetsDeposit_integral_canonical v shares priced hint hsad).2
  have hcmp : STAmount.areComparable amount priced = true := by
    rw [STAmount.operator_gt, STAmount.operator_lt] at hgt
    split at hgt
    · exact absurd hgt (by simp)
    · rename_i hcond; simpa using hcond
  have hamt_int : amount.integral = true := by
    have htyeq : amount.mNumericType = priced.mNumericType := by
      have := hcmp; unfold STAmount.areComparable at this
      exact beq_iff_eq.mp this
    unfold STAmount.integral; rw [htyeq, hcty]; exact hint
  -- so the input is integral, `roundToVaultExponent` was the identity
  have hameq : amount = amountDeposit := by
    have htype := roundToVaultExponent_mNumericType amountDeposit v.assetsTotal amount hcanon hround
    have hadint : amountDeposit.integral = true := by
      unfold STAmount.integral at hamt_int ⊢; rw [← htype]; exact hamt_int
    rw [roundToVaultExponent_integral amountDeposit v.assetsTotal hadint] at hround
    exact (Except.ok.inj hround).symm
  rw [hameq] at hats
  -- issued shares: positive `int64` canonical count
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amountDeposit shares hats
  have hshpos : 0 < shares.toRat :=
    assetsToSharesDeposit_pos v amountDeposit shares hcanon hpos hats hsz
  -- apply the proven charge bound
  obtain ⟨_, hbound⟩ :=
    sharesToAssetsDeposit_charge_integral_bound v amountDeposit shares priced hint hshc hshnt hshpos
      hsad
  -- on an integral vault the clamp hands the charge straight back
  have hcp : c = priced :=
    clampToSumExponent_integral_nonneg v.assetsTotal priced c
      (by show priced.mNumericType.isIntegral = true; rw [hcty]; exact hint)
      (sharesToAssetsDeposit_nonneg v shares priced hshc hshnt hshpos hsad) hclamp
  have hcr : r.amountDeposit' = c := hamt
  have hsr : r.sharesIssued = shares := by rw [hshr, hsheq]
  rw [hcr, hcp, hsr]
  exact hbound

/-- Proof body of `Vault.deposit_vault_updates`. Both stored asset totals round
`old + taken` within `depositε` (the taken amount is nonnegative, so the `Number`
addition never cancels), and the share total is stored exactly whenever the sum
fits the `int64` domain. -/
lemma Vault.deposit_vault_updates_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (hcanon : amountDeposit.Canonical)
    (hpos : 0 < amountDeposit.toRat) (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation hpos = .ok r) (herr : r.error = none) :
    RoundsWithin r.vault'.assetsTotal
      (v.toExact.assetsTotal + r.amountDeposit'.toRat) .to_nearest depositε ∧
    RoundsWithin r.vault'.assetsAvailable
      (v.toExact.assetsAvailable + r.amountDeposit'.toRat) .to_nearest depositε ∧
    ((v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) =
        (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat) := by
  obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, hsh_don, _hins, hdon_eq, hcomp,
    hcN, hsN, hat, hav, hst, hmax, hamt, hshr, hrv⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit isDonation r hpos hok herr
  rw [hamt, hshr, hrv]
  -- the rounded amount is canonical and positive
  have hamCanon : am.Canonical := by
    rcases roundToVaultExponent_canonical_or_isZero amountDeposit am v.assetsTotal hcanon hround
      with hc | hz
    · exact hc
    · rw [hz] at hamz; exact absurd hamz (by decide)
  have ham_nn : 0 ≤ am.toRat :=
    RawVault.roundToVaultExponent_nonneg amountDeposit am v.assetsTotal hcanon (le_of_lt hpos) hround
  have ham_ne : am.mValue ≠ 0 := by
    unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
  have ham_pos : 0 < am.toRat :=
    lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
  -- the taken amount converts exactly through `to_nearest`, is normalized, nonnegative
  have hcN_facts : cN.toRat = aD.toRat ∧ cN.isNormalized ∧ 0 ≤ cN.toRat := by
    by_cases hd : isDonation = true
    · obtain ⟨haD, _⟩ := hdon_eq hd
      have hExact : aD.ExactCanonical := by
        rw [haD]; exact STAmount.Canonical.exactCanonical am hamCanon
      obtain ⟨cN0, hcN0, hval0, hnorm0⟩ := STAmount.toNumber_exact_canonical aD .to_nearest hExact
      have hcNeq : cN0 = cN := by rw [hcN0] at hcN; exact Except.ok.inj hcN
      have hval : cN.toRat = aD.toRat := hcNeq ▸ hval0
      have hnorm : cN.isNormalized := hcNeq ▸ hnorm0
      exact ⟨hval, hnorm, by rw [hval, haD]; exact ham_nn⟩
    · have hd' : isDonation = false := by simpa using hd
      obtain ⟨pr, hcp, hclamp, hfnp⟩ := hcomp hd'
      obtain ⟨shares, hats, hshz, hsad, _, hseq⟩ :=
        computeDeposit_success_reduces v am pr sC hcp
      obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
      have hshpos : 0 < shares.toRat :=
        assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
      obtain ⟨hval, hnorm⟩ :=
        Vault.deposit_charge_toNumber_facts v shares pr aD cN hshc hshnt hshpos hsad hclamp hcN
      exact ⟨hval, hnorm, by
        rw [hval]
        exact Vault.deposit_charge_nonneg v shares pr aD hshc hshnt hshpos hsad hclamp hfnp⟩
  obtain ⟨hcNv, hcNn, hcN_nn⟩ := hcN_facts
  have hε_mono : (6 : ℚ) / (2 ^ 63 - 3) ≤ depositε := by rw [depositε_eq]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · -- assetsTotal
    have h := operator_add_nonneg_rounds v.assetsTotal cN at'
      v.wf.assetsTotal_norm hcNn v.exact.assetsTotal_nonneg hcN_nn hat
    rw [hcNv] at h
    exact RoundsWithin_mono at' (v.toExact.assetsTotal + aD.toRat) _ _ .to_nearest h hε_mono
  · -- assetsAvailable
    have h := operator_add_nonneg_rounds v.assetsAvailable cN av'
      v.wf.assetsAvailable_norm hcNn v.exact.assetsAvailable_nonneg hcN_nn hav
    rw [hcNv] at h
    exact RoundsWithin_mono av' (v.toExact.assetsAvailable + aD.toRat) _ _ .to_nearest h hε_mono
  · -- sharesTotal, exact whenever in domain
    intro hSsz
    have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
      RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have hSsz' : v.sharesTotal.toRat + sC.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hSsz
    have hST_nn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
    -- the issued shares are a nonnegative int64 canonical count
    have hSfacts : sC.IntegralCanonical ∧ sC.mNumericType = .int64 ∧ 0 ≤ sC.toRat := by
      by_cases hd : isDonation = true
      · obtain ⟨_, hsC⟩ := hdon_eq hd
        rw [hsC]
        exact ⟨zero_int64_IntegralCanonical, STAmount.zero_int64_mNumericType,
          le_of_eq STAmount.zero_int64_toRat.symm⟩
      · have hd' : isDonation = false := by simpa using hd
        obtain ⟨pr, hcp, -, -⟩ := hcomp hd'
        obtain ⟨shares, hats, hshz, _, _, hseq⟩ :=
          computeDeposit_success_reduces v am pr sC hcp
        obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
        have hpos_sh : 0 < shares.toRat :=
          assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
        refine ⟨?_, ?_, ?_⟩
        · rw [hseq]; exact hshc
        · rw [hseq]; exact hshnt
        · rw [hseq]; exact le_of_lt hpos_sh
    obtain ⟨hSc, hSnt, hSnn⟩ := hSfacts
    have hsz : sC.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have hr := hSc.in_range; rw [hSnt] at hr
      calc sC.mValue.toNat ≤ NumericType.int64.maxValue.toNat := hr
        _ ≤ 2 ^ 63 - 1 := by decide
    obtain ⟨sN0, hsN0, hsN_val0, hsN_norm0⟩ :=
      STAmount.toNumber_integral_small_exact sC .to_nearest hSc hsz
    have hsN_eq : sN0 = sN := by rw [hsN0] at hsN; exact Except.ok.inj hsN
    have hsN_val : sN.toRat = sC.toRat := by rw [← hsN_eq]; exact hsN_val0
    have hsN_norm : sN.isNormalized := by rw [← hsN_eq]; exact hsN_norm0
    have hsC_den : sC.toRat.den = 1 := STAmount.IntegralCanonical.den_eq_one sC hSc
    have hsN_den : sN.toRat.den = 1 := by rw [hsN_val]; exact hsC_den
    have hsum_den : (v.sharesTotal.toRat + sN.toRat).den = 1 :=
      Rat.den_one_add _ _ v.wf.sharesTotal_int hsN_den
    have hsum_nn : 0 ≤ v.sharesTotal.toRat + sN.toRat := by rw [hsN_val]; linarith
    have hsum_le : v.sharesTotal.toRat + sN.toRat ≤ 2 ^ 63 - 1 := by rw [hsN_val]; exact hSsz'
    have hsum_bound : (v.sharesTotal.toRat + sN.toRat).num.natAbs < 2 ^ 63 :=
      Rat.num_natAbs_lt_of_abs_le _ hsum_den (by rw [abs_of_nonneg hsum_nn]; exact hsum_le)
    obtain ⟨hst_val, hst_den⟩ := operator_add_exact_int v.sharesTotal sN st'
      v.wf.sharesTotal_norm hsN_norm v.wf.sharesTotal_int hsN_den hsum_bound hst
    have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hsum_nn
    -- reconstruct the ℕ shares total from the exact rational
    have hcast : ((st'.toRat.num.toNat : ℕ) : ℚ) = st'.toRat := by
      have hnum_nn : 0 ≤ st'.toRat.num := Rat.num_nonneg.mpr hst_nn
      have hnd := Rat.num_div_den st'.toRat
      rw [hst_den] at hnd
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum_nn]
      simpa using hnd
    show ((st'.toRat.num.toNat : ℕ) : ℚ) = (v.toExact.sharesTotal : ℚ) + sC.toRat
    rw [hcast, hst_val, hsN_val, ← hST]

/-- Proof body of `Vault.deposit_vault_updates_integral`: in-domain integer sums
are stored exactly. -/
lemma Vault.deposit_vault_updates_integral_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hnt : v.numericType = .int64 ∨ v.numericType = .native)
    (hcanon : amountDeposit.IntegralCanonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (hdenA : v.assetsTotal.toRat.den = 1)
    (hdenAv : v.assetsAvailable.toRat.den = 1)
    (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit isDonation hpos = .ok r) (herr : r.error = none)
    (hsz : v.toExact.assetsTotal + r.amountDeposit'.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal + r.amountDeposit'.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable + r.amountDeposit'.toRat := by
  obtain ⟨amount, c, sh, cN, sN, at', av', st', hround, hanz, _, _, hdon, hcd,
    hcN, hsN, hat, hav, hst, hmaxg, hamt, _, hr⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit isDonation r hpos hok herr
  have hvint : v.numericType.isIntegral = true := by
    rcases hnt with h | h <;> rw [h] <;> decide
  -- the amount passes through `roundToVaultExponent` unchanged
  have hameq : amount = amountDeposit := by
    rw [roundToVaultExponent_integral amountDeposit v.assetsTotal hcanon.is_integral] at hround
    exact (Except.ok.inj hround).symm
  -- the taken amount is a canonical integral record of the vault's type
  have hcfacts : c.IntegralCanonical ∧ c.mNumericType = v.numericType := by
    by_cases hd : isDonation = true
    · obtain ⟨hceq, _⟩ := hdon hd
      rw [hceq, hameq]
      exact ⟨hcanon, hty⟩
    · obtain ⟨priced, hcd0, hcl, -⟩ := hcd (by simpa using hd)
      obtain ⟨shares, _, _, hsta, _, _⟩ :=
        computeDeposit_success_reduces v amount priced sh hcd0
      obtain ⟨hpc, hpty⟩ := sharesToAssetsDeposit_integral_canonical v shares priced hvint hsta
      -- the recorded charge is `priced` snapped to the sum grid; on an integral vault
      -- the snap is inert, so type, offset and mantissa all carry over
      obtain ⟨hnt', hoff', hval'⟩ :=
        clampToSumExponent_integral_fields v.assetsTotal priced c
          (by unfold STAmount.integral; rw [hpty]; exact hvint) hcl
      refine ⟨⟨?_, ?_, ?_⟩, by rw [hnt', hpty]⟩
      · rw [hnt']; exact hpc.is_integral
      · rw [hoff']; exact hpc.offset_zero
      · rw [hval', hnt']; exact hpc.in_range
  obtain ⟨hcc, hcty⟩ := hcfacts
  have hcmax : c.mNumericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hcty]; exact NumericType.maxValue_le_maxRep_of_real v.numericType hnt
  -- `toNumber` of the taken amount is exact, normalized, integer-valued
  obtain ⟨cN', hcN', hcNval, hcNnorm, hcden⟩ :=
    STAmount.toNumber_integral_exact c .to_nearest hcc hcmax
  have hcNeq : cN' = cN := by rw [hcN'] at hcN; exact Except.ok.inj hcN
  rw [hcNeq] at hcNval hcNnorm
  -- magnitude bound on the taken amount
  have habs_c : |c.toRat| ≤ (2 : ℚ) ^ 63 - 1 := by
    refine le_trans (STAmount.IntegralCanonical.abs_toRat_le c hcc) ?_
    rw [hcty]
    rcases hnt with h | h <;> rw [h]
    · rw [show (NumericType.int64.maxValue).toNat = 9223372036854775807 from by decide]
      norm_num
    · rw [show (NumericType.native.maxValue).toNat = 100000000000000000 from by decide]
      norm_num
  have hc_r : r.amountDeposit' = c := hamt
  have hsz' : v.assetsTotal.toRat + c.toRat ≤ 2 ^ 63 - 1 := by
    rw [hc_r] at hsz; exact hsz
  have hA0 : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hAv0 : (0 : ℚ) ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAvA : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat := v.exact.assetsAvailable_le
  have hcden' : cN.toRat.den = 1 := by rw [hcNval]; exact hcden
  -- exact stored total
  have hboundA : (v.assetsTotal.toRat + cN.toRat).num.natAbs < 2 ^ 63 := by
    refine Rat.num_natAbs_lt_of_abs_le _ (Rat.den_one_add _ _ hdenA hcden') ?_
    rw [hcNval, abs_le]
    have hclo := (abs_le.mp habs_c).1
    constructor
    · linarith
    · linarith
  obtain ⟨hatval, _⟩ := operator_add_exact_int v.assetsTotal cN at'
    v.wf.assetsTotal_norm hcNnorm hdenA hcden' hboundA hat
  -- exact stored available
  have hboundAv : (v.assetsAvailable.toRat + cN.toRat).num.natAbs < 2 ^ 63 := by
    refine Rat.num_natAbs_lt_of_abs_le _ (Rat.den_one_add _ _ hdenAv hcden') ?_
    rw [hcNval, abs_le]
    have hclo := (abs_le.mp habs_c).1
    constructor
    · linarith
    · linarith
  obtain ⟨havval, _⟩ := operator_add_exact_int v.assetsAvailable cN av'
    v.wf.assetsAvailable_norm hcNnorm hdenAv hcden' hboundAv hav
  constructor
  · show r.vault'.assetsTotal.toRat = v.assetsTotal.toRat + r.amountDeposit'.toRat
    rw [hc_r, hr]
    show at'.toRat = v.assetsTotal.toRat + c.toRat
    rw [hatval, hcNval]
  · show r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.amountDeposit'.toRat
    rw [hc_r, hr]
    show av'.toRat = v.assetsAvailable.toRat + c.toRat
    rw [havval, hcNval]

/-- **Deposit shares are monotone in the rounded amount.** Minimal added inputs over
the headline: `roundedAmount_i.Canonical` and `0 < roundedAmount_i.toRat` (as in the
sibling `deposit_sharesIssued`). Both the nonempty pricing chain and the empty-vault
`Number.normalized` map are monotone. -/
lemma Vault.deposit_shares_monotone_proof (v : Vault)
    (amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ : STAmount)
    (r₁ r₂ : DepositResult)
    (hcanon₁ : roundedAmount₁.Canonical) (hcanon₂ : roundedAmount₂.Canonical)
    (hposR₁ : 0 < roundedAmount₁.toRat) (hposR₂ : 0 < roundedAmount₂.toRat)
    (hrounded₁ : v.roundedDepositAmount amountDeposit₁ = .ok (.rounded roundedAmount₁))
    (hrounded₂ : v.roundedDepositAmount amountDeposit₂ = .ok (.rounded roundedAmount₂))
    (hpos₁ : 0 < amountDeposit₁.toRat)
    (hok₁ : v.deposit amountDeposit₁ false hpos₁ = .ok r₁) (herr₁ : r₁.error = none)
    (hpos₂ : 0 < amountDeposit₂.toRat)
    (hok₂ : v.deposit amountDeposit₂ false hpos₂ = .ok r₂) (herr₂ : r₂.error = none)
    (hle : roundedAmount₁.toRat ≤ roundedAmount₂.toRat) :
    r₁.sharesIssued.toRat ≤ r₂.sharesIssued.toRat := by
  obtain ⟨am₁, aD₁, sC₁, _, _, _, _, _, hround₁, _, _, _, _, hcomp₁, _, _, _, _, _, _, _, hr₁, _⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit₁ false r₁ hpos₁ hok₁ herr₁
  obtain ⟨am₂, aD₂, sC₂, _, _, _, _, _, hround₂, _, _, _, _, hcomp₂, _, _, _, _, _, _, _, hr₂, _⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit₂ false r₂ hpos₂ hok₂ herr₂
  -- amount = roundedAmount
  have haeq₁ : am₁ = roundedAmount₁ :=
    Except.ok.inj (hround₁.symm.trans (roundedDepositAmount_rounded v _ _ hrounded₁).1)
  have haeq₂ : am₂ = roundedAmount₂ :=
    Except.ok.inj (hround₂.symm.trans (roundedDepositAmount_rounded v _ _ hrounded₂).1)
  -- computeDeposit success → assetsToSharesDeposit + shares; the clamp only touches
  -- the recorded charge, never the share count
  obtain ⟨priced₁, hcdp₁, _, _⟩ := hcomp₁ rfl
  obtain ⟨priced₂, hcdp₂, _, _⟩ := hcomp₂ rfl
  obtain ⟨sh₁, hats₁, hshz₁, _, _, hseq₁⟩ :=
    computeDeposit_success_reduces v am₁ priced₁ sC₁ hcdp₁
  obtain ⟨sh₂, hats₂, hshz₂, _, _, hseq₂⟩ :=
    computeDeposit_success_reduces v am₂ priced₂ sC₂ hcdp₂
  have hsi₁ : r₁.sharesIssued = sh₁ := by rw [hr₁]; exact hseq₁
  have hsi₂ : r₂.sharesIssued = sh₂ := by rw [hr₂]; exact hseq₂
  rw [hsi₁, hsi₂]
  exact assetsToSharesDeposit_mono v am₁ am₂ sh₁ sh₂
    (by rw [haeq₁]; exact hcanon₁) (by rw [haeq₁]; exact hposR₁)
    (by rw [haeq₂]; exact hcanon₂) (by rw [haeq₂]; exact hposR₂)
    hats₁ hshz₁ hats₂ hshz₂ (by rw [haeq₁, haeq₂]; exact hle)

end XRPL.Model.SingleAssetVault
