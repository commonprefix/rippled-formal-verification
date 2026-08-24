import XRPL.Properties.Vault.Common.Unchanged
import XRPL.Properties.Vault.Common.LawfulSupport
import XRPL.Properties.Vault.Common.DepositWiring
import XRPL.Properties.Vault.Common.ClawbackAccuracy
import XRPL.Properties.Vault.VaultBurn
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultBurn

/-! # No operation writes `interestUnrealized` or `lossUnrealized`

Each operation's do-block updates only `assetsTotal`, `assetsAvailable`, and
`sharesTotal` on success, and returns the starting vault on rejection. So the two
unrealized fields are the same in `r.vault'` as in `v` on every exit. Walked with
the same reduction toolkit as `Unchanged.lean`; every leaf closes by `rfl` because
both a bare `v` and a `{v with assetsTotal, assetsAvailable, sharesTotal := …}`
record carry `v`'s unrealized fields unchanged. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A deposit keeps both unrealized fields at their starting values. -/
theorem Vault.deposit_preserves_unrealized (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  unfold Vault.deposit at hok
  obtain ⟨amount, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h]; rfl
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h]; rfl
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h]; rfl
      · rw [if_neg h3] at hok
        simp only [pure_bind] at hok
        by_cases hd : isDonation = true
        · rw [if_pos hd] at hok
          obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
          · rw [if_pos hm] at hok; injection hok with h; rw [← h]; rfl
          · rw [if_neg hm] at hok; injection hok with h; rw [← h]
        · rw [if_neg hd] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          cases cres with
          | error e => injection hok with h; rw [← h]; rfl
          | success a s =>
            simp only [] at hok
            obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨n3, _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
            by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
            · rw [if_pos hm] at hok; injection hok with h; rw [← h]; rfl
            · rw [if_neg hm] at hok; injection hok with h; rw [← h]

/-- A withdrawal keeps both unrealized fields at their starting values. -/
theorem Vault.withdraw_preserves_unrealized (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  unfold Vault.withdraw at hok
  cases amount
  all_goals {
    simp only [] at hok
    obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
    by_cases h1 : result.error.isSome = true
    · rw [if_pos h1] at hok; injection hok with h; rw [← h]
    · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
      obtain ⟨assetsNumber', _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h2 : v.assetsAvailable.operator_lt assetsNumber' = true
      · rw [if_pos h2] at hok; injection hok with h; rw [← h]; rfl
      · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
        obtain ⟨sta, _, hok⟩ := bind_ok_peel _ _ _ hok
        by_cases h3 : result.sharesRedeemed.operator_eq sta = true
        · rw [if_pos h3] at hok
          by_cases h4 : v.lossUnrealized.operator_ne Number.zero = true
          · rw [if_pos h4] at hok; injection hok with h; rw [← h]; rfl
          · rw [if_neg h4] at hok; try simp only [pure_bind] at hok
            obtain ⟨allAvail, _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]
        · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
          obtain ⟨sbn, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases h5 : (assetsNumber'.mantissa_ != 0 && atr.operator_eq atr') = true
          · rw [if_pos h5] at hok; injection hok with h; rw [← h]; rfl
          · rw [if_neg h5] at hok; try simp only [pure_bind] at hok
            obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
            obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]
  }

/-- A clawback keeps both unrealized fields at their starting values. -/
theorem Vault.clawback_preserves_unrealized (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : v.clawback assets holderShares = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  unfold Vault.clawback at hok
  obtain ⟨result, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : result.error.isSome = true
  · rw [if_pos h1] at hok; injection hok with h; rw [← h]
  · rw [if_neg h1] at hok; try simp only [pure_bind] at hok
    by_cases h2 : result.sharesDestroyed.isZero = true
    · rw [if_pos h2] at hok; injection hok with h; rw [← h]; rfl
    · rw [if_neg h2] at hok; try simp only [pure_bind] at hok
      obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨arn, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr, _, hok⟩ := bind_ok_peel _ _ _ hok
      obtain ⟨atr', _, hok⟩ := bind_ok_peel _ _ _ hok
      by_cases h3 : (arn.mantissa_ != 0 && atr.operator_eq atr') = true
      · rw [if_pos h3] at hok; injection hok with h; rw [← h]; rfl
      · rw [if_neg h3] at hok; try simp only [pure_bind] at hok
        obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
        obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
        injection hok with h; rw [← h]

/-- `burnShares` writes only `sharesTotal`, so both unrealized fields carry
over unchanged. -/
theorem Vault.burnShares_preserves_unrealized (v : Vault) (sharesDestroyed : STAmount)
    (v' : Vault) (hok : v.burnShares sharesDestroyed = .ok v') :
    v'.lossUnrealized = v.lossUnrealized := by
  unfold Vault.burnShares at hok
  obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
  injection hok with h; rw [← h]

/-- On a vault with no unrealized interest or loss, both withdrawal pricing
subtractions return exactly the net asset value: the first subtracts the zero
`interestUnrealized`, the second subtracts either the zero `lossUnrealized`
(`waiveUnrealizedLoss = false`) or the literal zero (`true`). Discharges the
`WithdrawNavExact` hypothesis the payout accuracy lemmas take, from the
`interest = loss = 0` state every modeled operation preserves. -/
theorem Vault.withdrawNavExact_of_zero (v : Vault) (hv : v.Lawful) (waiveUnrealizedLoss : Bool)
    (hL : v.lossUnrealized.toRat = 0) :
    v.WithdrawNavExact waiveUnrealizedLoss := by
  have hL0 : v.lossUnrealized = Number.zero := by
    have hmz : v.lossUnrealized.mantissa_ = 0 := by
      by_contra h; exact (Number.toRat_ne_zero_of_mantissa_ne_zero v.lossUnrealized h) hL
    exact Number.eq_zero_of_mantissa_zero v.lossUnrealized hv.wf.lossUnrealized_norm hmz
  refine ⟨v.assetsTotal, ?_, ?_⟩
  · cases waiveUnrealizedLoss with
    | true => exact operator_sub_zero_right _ _
    | false => rw [hL0]; exact operator_sub_zero_right _ _
  · split
    · simp only [Vault.depositNav]
    · simp only [Vault.withdrawNav]
      rw [show v.lossUnrealized.toRat = 0 from hL]; ring

/-- The amount taken and the shares issued by a deposit are both nonnegative,
whether the run succeeds or is rejected (a rejection reports zero amounts). On the
success path the taken amount is `roundToVaultExponent`'s output on a donation and
`sharesToAssetsDeposit`'s upward charge on a real deposit, and the issued shares
are `assetsToSharesDeposit`'s int64 output. -/
theorem Vault.deposit_result_nonneg (v : Vault) (amount : STAmount) (isDonation : Bool)
    (hv : v.Lawful) (hcanon : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (r : DepositResult) (hok : v.deposit amount isDonation = .ok r) :
    0 ≤ r.amountDeposit'.toRat ∧ 0 ≤ r.sharesIssued.toRat := by
  by_cases herr : r.error.isSome = true
  · obtain ⟨-, haz, hsz⟩ := Vault.deposit_error_rejected_proof v amount isDonation r hok herr
    rw [haz, hsz, STAmount.zero_toRat, STAmount.zero_int64_toRat]
    exact ⟨le_refl 0, le_refl 0⟩
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, _hsh_don, _hins, hdon_eq, hcomp,
      _hcN, _hsN, _hat, _hav, _hst, _hmax, hr⟩ :=
      Vault.deposit_success_reduces v amount isDonation r hok herr'
    subst hr
    have hamCanon : am.Canonical := by
      rcases roundToVaultExponent_canonical_or_isZero amount am v.assetsTotal hcanon hround
        with hc | hz
      · exact hc
      · rw [hz] at hamz; exact absurd hamz (by decide)
    have ham_nn : 0 ≤ am.toRat :=
      Vault.roundToVaultExponent_nonneg amount am v.assetsTotal hcanon hnn hround
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
        computeDeposit_success_reduces v am aD sC (hcomp hd')
      obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
      have hshpos : 0 < shares.toRat :=
        assetsToSharesDeposit_pos v hv am shares hamCanon ham_pos hats hshz
      refine ⟨?_, ?_⟩
      · show 0 ≤ aD.toRat
        exact sharesToAssetsDeposit_nonneg v hv shares aD hshc hshnt hshpos hsad
      · show 0 ≤ sC.toRat; rw [hseq]; exact le_of_lt hshpos

/-- The amount paid by a withdrawal is nonnegative, whether the run succeeds or is
rejected. On a rejection the payout is zero; on the final withdrawal it is the
`ofNumber` snap of the nonnegative `assetsAvailable`; on a partial withdrawal it is
the `sharesToAssetsWithdraw` payout of the (nonnegative canonical) burned shares. -/
theorem Vault.withdraw_assets_nonneg (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (hv : v.Lawful)
    (hL : v.lossUnrealized.toRat = 0)
    (r : WithdrawResult) (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    (hSc : r.sharesBurned.IntegralCanonical) (hSnt : r.sharesBurned.mNumericType = .int64)
    (hSnn : r.sharesBurned.negative = false) :
    0 ≤ r.assets'.toRat := by
  by_cases herr : r.error.isSome = true
  · obtain ⟨-, haz, -⟩ := Vault.withdraw_error_rejected_proof v amount waiveUnrealizedLoss r hok herr
    rw [haz, STAmount.zero_toRat]
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨result, aN, sta, _hres, _hcw_err, _haN, _hlt, hsta, _hsb, hbranch⟩ :=
      Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr'
    rcases hbranch with ⟨_, _, allAvail, hallAvail, hr⟩ |
        ⟨hne, sN, at', av', st', _, _, _hsN, _hat, _, _, _, _hav, _hst, hr⟩
    · subst hr
      show 0 ≤ allAvail.toRat
      have hAA_neg : v.assetsAvailable.negative_ = false :=
        Number.negative_false_of_norm_nonneg v.assetsAvailable hv.wf.assetsAvailable_norm
          hv.valid.assetsAvailable_nonneg
      exact STAmount.ofNumber_signfalse_nonneg v.numericType v.assetsAvailable .to_nearest allAvail
        hv.wf.assetsAvailable_norm hAA_neg hallAvail
    · have hfin : r.sharesBurned.operator_eq sta = false := by rw [hr]; exact hne
      have hprice : v.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok r.assets' :=
        Vault.withdraw_payout_priced v amount waiveUnrealizedLoss sta r hok herr' hsta hfin
      subst hr
      have hSc' : result.sharesRedeemed.IntegralCanonical := hSc
      have hSnt' : result.sharesRedeemed.mNumericType = .int64 := hSnt
      have hSnn_val : 0 ≤ result.sharesRedeemed.toRat := STAmount.toRat_nonneg_of _ hSnn
      have hSC_canon : result.sharesRedeemed.Canonical := by
        refine ⟨fun _ => ⟨hSc', ?_⟩, fun hf => ?_⟩
        · rw [hSnt']; decide
        · rw [show result.sharesRedeemed.integral = result.sharesRedeemed.mNumericType.isIntegral
            from rfl, hSnt'] at hf
          exact absurd hf (by decide)
      have hnavE : v.WithdrawNavExact waiveUnrealizedLoss :=
        Vault.withdrawNavExact_of_zero v hv waiveUnrealizedLoss hL
      exact (Vault.sharesToAssetsWithdraw_spec v hv result.sharesRedeemed result.assets'
        waiveUnrealizedLoss hSnn_val hSC_canon hnavE hprice).1

theorem Vault.deposit_lawful_proof (v : Vault) (amount : STAmount) (isDonation : Bool)
    (hv : v.Lawful)
    (hL : v.lossUnrealized.toRat = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanon : amount.Canonical)
    (hnn : 0 ≤ amount.toRat)
    (r : DepositResult) (hok : v.deposit amount isDonation = .ok r)
    (hSsz : v.sharesTotal.toRat + r.sharesIssued.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.deposit_error_unchanged_proof v amount isDonation r hok herr]
    exact hv
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, hsh_don, _hins, hdon_eq, hcomp,
      hcN, hsN, hat, hav, hst, hmax, hr⟩ :=
      Vault.deposit_success_reduces v amount isDonation r hok herr'
    subst hr
    -- derive the storage-canonicity and sign facts about the run's own outputs
    -- (formerly hypothesized): the taken amount is `roundToVaultExponent`'s output
    -- on a donation and `sharesToAssetsDeposit`'s upward charge on a real deposit,
    -- and the issued shares are `assetsToSharesDeposit`'s int64 output
    have hfacts : cN.toRat = aD.toRat ∧ cN.isNormalized ∧ 0 ≤ aD.toRat ∧
        sC.IntegralCanonical ∧ 0 ≤ sC.toRat := by
      have hamCanon : am.Canonical := by
        rcases roundToVaultExponent_canonical_or_isZero amount am v.assetsTotal hcanon hround
          with hc | hz
        · exact hc
        · rw [hz] at hamz; exact absurd hamz (by decide)
      have ham_nn : 0 ≤ am.toRat :=
        Vault.roundToVaultExponent_nonneg amount am v.assetsTotal hcanon hnn hround
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
          computeDeposit_success_reduces v am aD sC (hcomp hd')
        obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
        have hshpos : 0 < shares.toRat :=
          assetsToSharesDeposit_pos v hv am shares hamCanon ham_pos hats hshz
        obtain ⟨hcN_val, hcN_norm⟩ :=
          sharesToAssetsDeposit_toNumber_exact v hv shares aD cN hshc hshnt hsad hcN
        exact ⟨hcN_val, hcN_norm,
          sharesToAssetsDeposit_nonneg v hv shares aD hshc hshnt hshpos hsad,
          hseq ▸ hshc, by rw [hseq]; exact le_of_lt hshpos⟩
    obtain ⟨hcN_val, hcN_norm, hDnn', hSc', hSnn'⟩ := hfacts
    have hSsz' : v.sharesTotal.toRat + sC.toRat ≤ 2 ^ 63 - 1 := hSsz
    have hST_nn : 0 ≤ v.sharesTotal.toRat := hv.wf.sharesTotal_nonneg
    have hAT_nn : (0 : ℚ) ≤ v.assetsTotal.toRat := hv.valid.assetsTotal_nonneg
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
      hv.wf.lossUnrealized_norm, hst_nn, hst_den,
      hv.wf.scale_integral, hv.wf.scale_le⟩,
      ⟨hat_nn, hat_nn, le_refl _, hv.valid.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩⟩
    · -- empty_shares: the new share total is nonzero
      intro h0
      exact absurd (show st'.toRat = 0 from h0) hst_ne
    · -- cap
      intro n hn
      have hn' : v.assetsMaximum = some n := hn
      rw [hn'] at hmax
      have hnpos : 0 < n.toRat := hv.valid.assetsMaximum_pos n hn
      have hne0 : n.operator_ne Number.zero = true :=
        (operator_ne_iff n Number.zero (hv.wf.assetsMaximum_norm n hn) (Or.inl rfl)).mpr
          (by rw [Number.toRat_zero]; exact ne_of_gt hnpos)
      have hgt : at'.operator_gt n = false := by
        simp only [Option.getD_some, hne0, Bool.true_and] at hmax; exact hmax
      have := (operator_gt_iff at' n hat_norm (hv.wf.assetsMaximum_norm n hn)).not.mp
        (by rw [hgt]; simp)
      exact le_of_not_gt (fun hc => this hc)
    · exact le_of_eq hL.symm
    · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]
      linarith
    · show 0 ≤ at'.toRat - v.lossUnrealized.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]
      linarith

theorem Vault.withdraw_lawful_proof (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful)
    (hL : v.lossUnrealized.toRat = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (r : WithdrawResult) (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    (hSc : r.sharesBurned.IntegralCanonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hSnn : r.sharesBurned.negative = false)
    (hsle : r.sharesBurned.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.withdraw_error_unchanged_proof v amount waiveUnrealizedLoss r hok herr]
    exact hv
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨result, aN, sta, hres, _, haN, hlt, hsta, _, hbranch⟩ :=
      Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok herr'
    have hST_nn : 0 ≤ v.sharesTotal.toRat := hv.wf.sharesTotal_nonneg
    have hAVval : v.assetsAvailable.toRat = v.assetsTotal.toRat := by rw [hAV]
    have hAT_nn : (0 : ℚ) ≤ v.assetsTotal.toRat := hv.valid.assetsTotal_nonneg
    rcases hbranch with ⟨_, _, allAvail, _, hr⟩ |
      ⟨hne, sN, at', av', st', _, _, hsN, hat, _, _, _, hav, hst, hr⟩
    · -- final withdrawal: all three totals zeroed
      subst hr
      show ({ v with assetsAvailable := Number.zero,
                      assetsTotal := Number.zero,
                      sharesTotal := Number.zero } : Vault).Lawful
      have hz : Number.zero.isNormalized := Or.inl rfl
      have hLU0 : v.lossUnrealized.toRat = 0 := hL
      refine ⟨⟨hz, hz, hv.wf.assetsMaximum_norm, hz,
        hv.wf.lossUnrealized_norm,
        ?_, ?_, hv.wf.scale_integral, hv.wf.scale_le⟩,
        ⟨?_, ?_, ?_, hv.valid.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp only [Number.toRat_zero, le_refl]
      · simp only [Number.toRat_zero]; rfl
      · simp only [Number.toRat_zero, le_refl]
      · simp only [Number.toRat_zero, le_refl]
      · simp only [Number.toRat_zero, le_refl]
      · intro _
        simp only [Number.toRat_zero]
        exact ⟨trivial, trivial⟩
      · intro n hn
        simp only [Number.toRat_zero]
        exact le_of_lt (hv.valid.assetsMaximum_pos n hn)
      · show (0 : ℚ) ≤ v.lossUnrealized.toRat
        rw [hLU0]
      · simp only [Number.toRat_zero]
        rw [hLU0]
        linarith
      · simp only [Number.toRat_zero]
        rw [hLU0]
        linarith
    · -- partial withdrawal
      -- the payout is priced from the burned shares (the non-final guard `hne`)
      have hfin : r.sharesBurned.operator_eq sta = false := by rw [hr]; exact hne
      have hprice : v.sharesToAssetsWithdraw r.sharesBurned waiveUnrealizedLoss = .ok r.assets' :=
        Vault.withdraw_payout_priced v amount waiveUnrealizedLoss sta r hok herr' hsta hfin
      subst hr
      have hSc' : result.sharesRedeemed.IntegralCanonical := hSc
      have hSnt' : result.sharesRedeemed.mNumericType = .int64 := hSnt
      have hSnn' : result.sharesRedeemed.mIsNegative = false := hSnn
      have hsle' : result.sharesRedeemed.toRat ≤ v.sharesTotal.toRat := hsle
      have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := hfit
      have hSnn_val : 0 ≤ result.sharesRedeemed.toRat :=
        STAmount.toRat_nonneg_of _ hSnn'
      -- burned shares are canonical (int64 integral), so the payout is derivable
      have hSC_canon : result.sharesRedeemed.Canonical := by
        refine ⟨fun _ => ⟨hSc', ?_⟩, fun hf => ?_⟩
        · rw [hSnt']; decide
        · rw [show result.sharesRedeemed.integral = result.sharesRedeemed.mNumericType.isIntegral
            from rfl, hSnt'] at hf
          exact absurd hf (by decide)
      -- the paid amount is a nonnegative payout (formerly hypothesized)
      have hnavE : v.WithdrawNavExact waiveUnrealizedLoss :=
        Vault.withdrawNavExact_of_zero v hv waiveUnrealizedLoss hL
      have hDnn' : 0 ≤ result.assets'.toRat :=
        (Vault.sharesToAssetsWithdraw_spec v hv result.sharesRedeemed result.assets'
          waiveUnrealizedLoss hSnn_val hSC_canon hnavE hprice).1
      -- and it converts exactly through `toNumber`
      obtain ⟨haN_val, haN_norm⟩ :=
        Vault.sharesToAssetsWithdraw_toNumber_facts v hv result.sharesRedeemed result.assets'
          waiveUnrealizedLoss aN hSC_canon hprice haN
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
            have h1 := (hv.valid.empty_shares hst0).1
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
        hv.wf.lossUnrealized_norm, hst_nn, hst_den,
        hv.wf.scale_integral, hv.wf.scale_le⟩,
        ⟨hat_nn, hat_nn, le_refl _, hv.valid.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩⟩
      · -- empty_shares
        intro h0
        have hz : at'.toRat = 0 := hkey (show st'.toRat = 0 from h0)
        exact ⟨hz, hz⟩
      · -- cap
        intro n hn
        have hcapn : v.assetsTotal.toRat ≤ n.toRat := hv.valid.cap n hn
        exact operator_sub_le_of_le_normalized _ _ _ _ hv.wf.assetsTotal_norm haN_norm
          hat (hv.wf.assetsMaximum_norm n hn) (by linarith)
      · exact le_of_eq hL.symm
      · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
        rw [show v.lossUnrealized.toRat = 0 from hL]
        linarith
      · show 0 ≤ at'.toRat - v.lossUnrealized.toRat
        rw [show v.lossUnrealized.toRat = 0 from hL]
        linarith

theorem Vault.clawback_lawful_proof (v : Vault) (assets holderShares : STAmount)
    (hv : v.Lawful)
    (hL : v.lossUnrealized.toRat = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanon : assets.Canonical)
    (r : ClawbackResult)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hok : v.clawback assets holderShares = .ok r)
    (hslt : r.sharesDestroyed.toRat < v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.clawback_error_unchanged_proof v assets holderShares r hok herr]
    exact hv
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    -- derive the recovery/destroyed-shares canonicity, sign, and coverage facts
    -- (formerly hypothesized) from the run: the recovery prices the destroyed
    -- shares through `sharesToAssetsWithdraw` and the guard already forced it
    -- under `assetsAvailable`
    have hnavE : v.WithdrawNavExact false := Vault.withdrawNavExact_of_zero v hv false hL
    obtain ⟨hSnn_r, hcanon_sd_r, hprice_r, hDle_r, -⟩ :=
      Vault.clawback_recovery_priced' v assets holderShares r hv hnavE hcanon hSc hSnn hok herr'
    have hSc_r : r.sharesDestroyed.IntegralCanonical :=
      Vault.clawback_shares_intCanonical' v assets holderShares r hSic hok herr'
    have hDnn_r : 0 ≤ r.assetsRecovered.toRat :=
      (Vault.sharesToAssetsWithdraw_spec v hv r.sharesDestroyed r.assetsRecovered false
        hSnn_r hcanon_sd_r hnavE hprice_r).1
    obtain ⟨result, hres, -, hshz, -, -, sdn, arn, at', st', av', -, -, hsdn, harn, hat, -, -, -,
        hst, hav, hr⟩ :=
      Vault.clawback_success_reduces v assets holderShares r hok herr'
    subst hr
    have hSc' : result.sharesDestroyed.IntegralCanonical := hSc_r
    have hSnn_val : 0 ≤ result.sharesDestroyed.toRat := hSnn_r
    have hDnn' : 0 ≤ result.assetsRecovered.toRat := hDnn_r
    have hDle' : result.assetsRecovered.toRat ≤ v.assetsAvailable.toRat := hDle_r
    have hST_nn : 0 ≤ v.sharesTotal.toRat := hv.wf.sharesTotal_nonneg
    have hslt' : result.sharesDestroyed.toRat < v.sharesTotal.toRat := hslt
    have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := hfit
    have hAVval : v.assetsAvailable.toRat = v.assetsTotal.toRat := by rw [hAV]
    -- the recovered amount converts exactly
    obtain ⟨harn_val, harn_norm⟩ :=
      Vault.sharesToAssetsWithdraw_toNumber_facts v hv result.sharesDestroyed result.assetsRecovered
        false arn hcanon_sd_r hprice_r harn
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
      hv.wf.lossUnrealized_norm, hst_nn, hst_den,
      hv.wf.scale_integral, hv.wf.scale_le⟩,
      ⟨hat_nn, hat_nn, le_refl _, hv.valid.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩⟩
    · -- empty_shares: the strict share bound keeps the remainder positive
      intro h0
      exact absurd (show st'.toRat = 0 from h0) hst_ne
    · -- cap
      intro n hn
      have hcapn : v.assetsTotal.toRat ≤ n.toRat := hv.valid.cap n hn
      exact operator_sub_le_of_le_normalized _ _ _ _ hv.wf.assetsTotal_norm harn_norm
        hat (hv.wf.assetsMaximum_norm n hn) (by linarith)
    · exact le_of_eq hL.symm
    · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]
      linarith
    · show 0 ≤ at'.toRat - v.lossUnrealized.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]
      linarith

theorem Vault.burnShares_lawful_proof (v : Vault)
    (sharesDestroyed sharesTotalAmount : STAmount) (v' : Vault)
    (hv : v.Lawful)
    (hcan : v.canBurnShares = .ok (.assets sharesTotalAmount))
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hok : v.burnShares sharesDestroyed = .ok v') :
    v'.Lawful := by
  have hsta_val : sharesTotalAmount.toRat = v.sharesTotal.toRat :=
    Vault.canBurnShares_assets_exact v sharesTotalAmount hv hcan hfit
  have hle' : sharesDestroyed.toRat ≤ v.sharesTotal.toRat := by
    rw [← hsta_val]; exact hle
  have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := hfit
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
  have hLU0 : v.lossUnrealized.toRat = 0 :=
    le_antisymm (by
      have h1 := hv.valid.lossUnrealized_le
      have h2 : v.assetsTotal.toRat - v.assetsAvailable.toRat = 0 := by
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
    hst_norm, hv.wf.lossUnrealized_norm, hst_nn, hst_den,
    hv.wf.scale_integral, hv.wf.scale_le⟩,
    ⟨hv.valid.assetsTotal_nonneg, hv.valid.assetsAvailable_nonneg,
    hv.valid.assetsAvailable_le, hv.valid.assetsMaximum_pos, ?_, hv.valid.cap, ?_, ?_,
    ?_⟩⟩
  · -- empty_shares: both totals are zero on a burnable state
    intro _
    exact ⟨hAT0, hAV0⟩
  · exact le_of_eq hLU0.symm
  · show v.lossUnrealized.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat
    rw [hLU0, hAT0, hAV0]
    linarith
  · show 0 ≤ v.assetsTotal.toRat - v.lossUnrealized.toRat
    rw [hLU0, hAT0]
    linarith

end XRPL.Model.SingleAssetVault
