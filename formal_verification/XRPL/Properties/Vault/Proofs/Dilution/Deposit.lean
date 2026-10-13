import XRPL.Properties.Vault.Proofs.Dilution.Charge
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # A deposit dilutes by at most `depositε` plus `3/2` steps of the post-deposit grid -/

namespace XRPL.Model.SingleAssetVault.DilG

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

/-- The stored fields after a successful deposit: the total is the correctly rounded sum,
the loss is untouched, the vault was solvent, and the issued shares are a positive `int64`
count, added exactly when in range. -/
lemma deposit_totals (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    |r.vault'.toExact.assetsTotal - (v.toExact.assetsTotal + r.amountDeposit'.toRat)| ≤
      (v.toExact.assetsTotal + r.amountDeposit'.toRat) * (6 / (2 ^ 63 - 3)) ∧
    r.vault'.toExact.lossUnrealized = v.toExact.lossUnrealized ∧
    r.vault'.toRawVault.numericType = v.toRawVault.numericType ∧
    v.isInsolvent = false ∧
    r.sharesIssued.IntegralCanonical ∧ r.sharesIssued.mNumericType = .int64 ∧
    0 < r.sharesIssued.toRat ∧
    ((v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1 →
      (r.vault'.toExact.sharesTotal : ℚ) = (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat) := by
  obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, -, hins, -, hcomp,
    hcN, -, hat, -, -, -, hamt, hshr, hrv⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit false r hpos hok herr
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
  obtain ⟨pr, hcp, hclamp, hfnp⟩ := hcomp rfl
  obtain ⟨shares, hats, hshz, hsad, _, hseq⟩ := computeDeposit_success_reduces v am pr sC hcp
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
  have hshpos : 0 < shares.toRat := assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
  obtain ⟨hval, hnorm⟩ :=
    Vault.deposit_charge_toNumber_facts v shares pr aD cN hshc hshnt hshpos hsad hclamp hcN
  have haD0 : 0 ≤ aD.toRat := Vault.deposit_charge_nonneg v shares pr aD hshc hshnt hshpos hsad hclamp hfnp
  have h := operator_add_nonneg_rounds v.assetsTotal cN at'
    v.wf.assetsTotal_norm hnorm v.exact.assetsTotal_nonneg (by rw [hval]; exact haD0) hat
  rw [hval] at h
  have hS := (Vault.deposit_vault_updates_proof v amountDeposit false hcanon hpos r hok herr).2.2
  have hTeq : r.vault'.assetsTotal = at' := congrArg RawVault.assetsTotal hrv
  have hLeq : r.vault'.toRawVault.lossUnrealized = v.toRawVault.lossUnrealized := by rw [hrv]
  have hNeq : r.vault'.toRawVault.numericType = v.toRawVault.numericType := by rw [hrv]
  have hsum0 : 0 ≤ v.toExact.assetsTotal + r.amountDeposit'.toRat := by
    rw [hamt]; exact add_nonneg v.exact.assetsTotal_nonneg haD0
  refine ⟨?_, ?_, hNeq, hins rfl, ?_, ?_, ?_, hS⟩
  · have h' : |at'.toRat - (v.assetsTotal.toRat + aD.toRat)| ≤
        |v.assetsTotal.toRat + aD.toRat| * (6 / (2 ^ 63 - 3)) := h
    have hsum1 : 0 ≤ v.assetsTotal.toRat + aD.toRat := by rw [hamt] at hsum0; exact hsum0
    show |r.vault'.assetsTotal.toRat - (v.assetsTotal.toRat + r.amountDeposit'.toRat)| ≤
      (v.assetsTotal.toRat + r.amountDeposit'.toRat) * _
    rw [hTeq, hamt]
    rwa [abs_of_nonneg hsum1] at h'
  · show r.vault'.toRawVault.lossUnrealized.toRat = v.toRawVault.lossUnrealized.toRat
    rw [hLeq]
  · rw [hshr, hseq]; exact hshc
  · rw [hshr, hseq]; exact hshnt
  · rw [hshr, hseq]; exact hshpos

/-- The stored available total after a successful deposit is the `Number` sum of the old one
and the exact charge. -/
lemma deposit_avail (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    ∃ cN, cN.toRat = r.amountDeposit'.toRat ∧ cN.isNormalized ∧
      v.assetsAvailable.operator_add cN .to_nearest = .ok r.vault'.assetsAvailable := by
  obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, hamz, -, -, -, hcomp,
    hcN, -, -, hav, -, -, hamt, -, hrv⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit false r hpos hok herr
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
  obtain ⟨pr, hcp, hclamp, -⟩ := hcomp rfl
  obtain ⟨shares, hats, hshz, hsad, _, -⟩ := computeDeposit_success_reduces v am pr sC hcp
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
  have hshpos : 0 < shares.toRat := assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
  obtain ⟨hval, hnorm⟩ :=
    Vault.deposit_charge_toNumber_facts v shares pr aD cN hshc hshnt hshpos hsad hclamp hcN
  have hAeq : r.vault'.toRawVault.assetsAvailable = av' := by rw [hrv]
  refine ⟨cN, by rw [hamt]; exact hval, hnorm, ?_⟩
  show v.assetsAvailable.operator_add cN .to_nearest = .ok r.vault'.toRawVault.assetsAvailable
  rw [hAeq]; exact hav

/-- A positive total forces a positive share count. -/
lemma shares_pos_of_total (v : Vault) (hA : 0 < v.toExact.assetsTotal) :
    0 < (v.toExact.sharesTotal : ℚ) := by
  have hne : v.toExact.sharesTotal ≠ 0 := fun h0 =>
    absurd (v.exact.empty_shares h0).1 (ne_of_gt hA)
  exact_mod_cast Nat.pos_of_ne_zero hne

end XRPL.Model.SingleAssetVault.DilG

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DilG

/-- **Deposit dilution.** Per-share value drops by at most `3·10⁻¹⁸` relatively (the charge
pricing stages and the total's sum) plus `3/2` steps of the post-deposit grid `10^e` per
existing share. -/
lemma Vault.deposit_no_dilution_proof (v : Vault) (amountDeposit : STAmount) (r : DepositResult)
    (hcanon : amountDeposit.Canonical) (hpos : 0 < amountDeposit.toRat)
    (hL : v.toExact.lossUnrealized = 0)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok : v.deposit amountDeposit false hpos = .ok r) (herr : r.error = none) :
    ∀ e, postSumExponent v.assetsTotal amountDeposit = .ok e →
      r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
        v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - 3 / 10 ^ 18) -
          3 / 2 * (10 : ℚ) ^ e * (v.toExact.sharesTotal : ℚ) := by
  intro e he
  obtain ⟨hA', hL', -, -, -, -, hspos, hS'⟩ := deposit_totals v amountDeposit r hcanon hpos hok herr
  obtain ⟨hc0, hI0, -, -, ep, hep, G, hG0, hG, -, hlow⟩ :=
    charge_sharp v amountDeposit r hcanon hpos hok herr
  set A := v.toExact.assetsTotal with hAdef
  set S : ℚ := (v.toExact.sharesTotal : ℚ) with hSdef
  set s := r.sharesIssued.toRat with hsdef
  set c := r.amountDeposit'.toRat with hcdef
  set A' := r.vault'.toExact.assetsTotal with hA'def
  have hnav : v.withdrawNav = A := by
    show v.toExact.assetsTotal - v.toExact.lossUnrealized = A; rw [hL]; ring
  have hnav' : r.vault'.withdrawNav = A' := by
    show r.vault'.toExact.assetsTotal - r.vault'.toExact.lossUnrealized = A'; rw [hL', hL]; ring
  rw [hnav, hnav', hS' hSsz]
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hge : (10 : ℚ) ^ ep ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) (hep e he)
  have hA0 : 0 ≤ A := v.exact.assetsTotal_nonneg
  rcases lt_or_eq_of_le hA0 with hApos | hAz
  · have hSpos : 0 < S := shares_pos_of_total v hApos
    have hI : v.idealChargeDeposit s * S = A * s := by
      unfold RawVault.idealChargeDeposit
      rw [if_neg (ne_of_gt hApos)]
      show v.toExact.assetsTotal * s / S * S = A * s
      rw [div_mul_cancel₀ _ (ne_of_gt hSpos)]
    have hA'lo := (abs_le.mp hA').1
    have hsum : 0 ≤ A + c := add_nonneg hA0 hc0
    have hdel : (6 : ℚ) / (2 ^ 63 - 3) ≤ 1 / 10 ^ 18 := by norm_num
    -- A' ≥ (A + c)(1 - δa)
    have h1 : (A + c) * (1 - 1 / 10 ^ 18) ≤ A' := by nlinarith
    -- c·S ≥ A·s·(1-δc) - G·S
    have h2 : A * s * (1 - 2 / 10 ^ 18) - G * S ≤ c * S := by
      have := mul_le_mul_of_nonneg_right hlow hS0
      nlinarith
    have hs0 : 0 ≤ s := le_of_lt hspos
    have hAs : 0 ≤ A * s := mul_nonneg hA0 hs0
    have hAS : 0 ≤ A * S := mul_nonneg hA0 hS0
    have hGS : 0 ≤ G * S := mul_nonneg hG0 hS0
    have hgS : G * S ≤ 3 / 2 * 10 ^ e * S := mul_le_mul_of_nonneg_right (by linarith) hS0
    have key : (A + c) * S * (1 - 1 / 10 ^ 18) ≤ A' * S := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℚ) ≤ 1 - 1 / 10 ^ 18)
    nlinarith
  · rw [← hAz]
    have : 0 ≤ A' := by
      have := r.vault'.exact.withdraw_nav_nonneg
      have h0 : r.vault'.toExact.lossUnrealized = 0 := by rw [hL', hL]
      rw [h0] at this; linarith
    have : (0 : ℚ) ≤ 3 / 2 * 10 ^ e * S := by positivity
    nlinarith

end XRPL.Model.SingleAssetVault
