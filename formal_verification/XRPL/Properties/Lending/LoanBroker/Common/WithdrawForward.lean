import XRPL.Properties.Lending.LoanBroker.Common.WithdrawFloor
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Lending.Loan.Common.RoundTotal

/-! # A withdrawal of whole base units passes its checks

On a broker in the Open zone, withdrawing a nonzero whole number of base units of the vault that
leaves at least the minimum cover passes every check of `canCoverWithdraw`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- Withdrawing a nonzero whole number of base units that leaves at least the minimum cover passes
the checks. -/
lemma LoanBroker.canCoverWithdraw_of_units (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (minimumCover : Number) (hz : lb.OpenZone v.baseExponent) (hc : amount.Canonical)
    (hk : ∃ k : ℕ, 0 < k ∧ amount.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent =
      .ok minimumCover)
    (hle : minimumCover.toRat + amount.toRat ≤ lb.toExact.coverAvailable) :
    lb.canCoverWithdraw v amount = .ok .tesSUCCESS := by
  obtain ⟨hblo, hbhi, -⟩ := v.baseExponent_bounds
  obtain ⟨k, hk0, hkv⟩ := hk
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hpos : 0 < amount.toRat := by
    rw [hkv]; have : (0 : ℚ) < k := by exact_mod_cast hk0
    positivity
  have hm0 : 0 ≤ minimumCover.toRat := LoanBroker.minimumCover_nonneg lb _ _ (by omega) hmin
  have hmn : minimumCover.isNormalized := minimumBrokerCover_isNormalized _ _ _ _ _ hmin
  have hAn := lb.wf.coverAvailable_norm
  have hle' : minimumCover.toRat + amount.toRat ≤ lb.coverAvailable.toRat := hle
  have hA0 : 0 ≤ lb.coverAvailable.toRat := by linarith
  have hA9 := LoanBroker.OpenZone.cover_le lb _ hz hbhi
  have hA96 : lb.coverAvailable.toRat < 10 ^ 96 := by linarith

  -- the clamp keeps the amount: an XRP or MPT amount passes whole
  have habs := STAmount.abs_operator_neg_of_pos amount hpos
  have hcl : clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent v) =
      .ok amount := by
    by_cases hint : amount.integral = true
    · rw [clampToSumExponent_integral _ _ _ ((STAmount.operator_neg_integral amount).trans hint), habs]
    have hfr : amount.integral = false := by simpa using hint
    have hiou : amount.IOUCanonical := hc.2 hfr
    have hniou := hiou.operator_neg
    have hfr' : amount.operator_neg.integral = false := (STAmount.operator_neg_integral amount).trans hfr

    -- an IOU amount converts exactly, and its nearest sum with the cover lies between zero and the cover
    obtain ⟨nN, hnN, hnNv, hnNn, hnNe⟩ : ∃ nN : Number, amount.operator_neg.toNumber .to_nearest = .ok nN ∧
        nN.toRat = -amount.toRat ∧ nN.isNormalized ∧ nN.exponent_ + 22 ≤ maxExponent :=
      ⟨_, STAmount.toNumber_iou_canonical _ _ hniou,
        by rw [STAmount.toNumber_iou_canonical_toRat _ hniou, STAmount.operator_neg_toRat],
        STAmount.toNumber_iou_canonical_isNormalized _ hniou,
        by show amount.operator_neg.mOffset - 3 + 22 ≤ maxExponent; have := hniou.exp_hi; unfold maxExponent; omega⟩
    obtain ⟨sum, hsum⟩ := Number.operator_add_ok_of_exp lb.coverAvailable nN .to_nearest hAn hnNn
      (Number.exponent_headroom_of_lt _ hAn hA0 hA96) hnNe
    have hR := operator_add_rounded_to_nearest _ _ _ hAn hnNn hsum
    have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ hAn hnNn hsum
    have hs0 : 0 ≤ sum.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg sum _ hR (by rw [hnNv]; linarith)
    have hsA : sum.toRat ≤ lb.coverAvailable.toRat :=
      Number.RoundsToRepresentable.le_of_le_normalized sum _ hR _ hAn (by rw [hnNv]; linarith)

    -- so the sum has an exponent, and it is the base exponent as the sum stays below `10^(16 + b)`
    have hne : ∃ e, numberExponent sum v.baseExponent .fractional = .ok e := by
      unfold numberExponent
      by_cases hz0 : sum.operator_eq Number.zero = true
      · rw [if_pos hz0]; exact ⟨_, rfl⟩
      rw [if_neg hz0]
      have hsm : sum.mantissa_ ≠ 0 := fun hm => hz0 (by rw [Number.eq_zero_of_mantissa_zero sum hsn hm]; decide)
      obtain ⟨hlo, hhi⟩ := hsn.mantissaBounds_nat hsm
      have hse : sum.exponent_ ≤ 0 := Number.exponent_le_of_toRat_lt sum 0 hsn
        (Number.negative_false_of_nonneg sum hsn hs0) (by unfold minExponent; norm_num) (by norm_num; linarith)
      obtain ⟨r, hr⟩ := STAmount.ofNumber_fractional_ok sum .downward hlo hhi (Number.exponent_ge_min sum hsn hsm)
        (by unfold cMaxOffset; omega)
      rw [hr]
      exact ⟨_, rfl⟩
    obtain ⟨e, he⟩ := hne
    have heb : e = v.baseExponent := numberExponent_at_base sum _ .fractional e hsn hs0 (by omega)
      (fun h => absurd h (by decide)) (LoanBroker.OpenZone.lt_pow_sixteen lb _ hz _ hsA) he
    rw [heb] at he
    have hps : postSumExponent lb.coverAvailable nN v.baseExponent .fractional = .ok v.baseExponent := by
      unfold postSumExponent; rw [hsum, ok_bind]; exact he

    -- a whole number of base units is already on that grid, so rounding toward zero keeps it
    have hround : STAmount.roundToExponent amount v.baseExponent .towards_zero = .ok amount := by
      obtain ⟨r, hr⟩ := STAmount.roundToExponent_ok_any amount v.baseExponent .towards_zero hiou
        (STAmount.mIsNegative_false_of_pos amount hpos) (by omega) (by omega)
      have hrnd := STAmount.roundToExponent_rounded_of_scale amount r _ _ hiou (by omega) (by omega) hr
      simp only [RoundsToRepresentableAt] at hrnd
      change r.toRat = _ at hrnd
      rw [if_pos hpos.le, hkv, mul_div_assoc, div_self hp.ne', mul_one] at hrnd
      have hrv : r.toRat = amount.toRat := by rw [hrnd, hkv]; simp
      have hr0 : r.mValue ≠ 0 := fun h0 => hpos.ne' (hrv ▸ (STAmount.toRat_eq_zero_iff r).mpr h0)
      have hrF := STAmount.roundToExponent_fczr amount r _ _ ⟨hiou.is_fractional, Or.inl hiou⟩ hr
      have hra := STAmount.eq_of_exactCanonical r amount (Or.inl (hrF.2.resolve_right hr0)) (Or.inl hiou)
        (hrF.1.trans hiou.is_fractional.symm) hr0 hrv
      rw [hr, hra]
    have hps' : postSumExponent lb.coverAvailable nN (AssetPool.baseExponent v) amount.operator_neg.numericType =
        .ok v.baseExponent := by
      rw [show amount.operator_neg.numericType = .fractional from hniou.is_fractional]; exact hps
    unfold clampToSumExponent
    simp only [hfr', Bool.false_eq_true, if_false, hnN, ok_bind, habs, hps', pure_bind, hround]

  -- the amount is not zero, converts exactly and fits in the cover
  obtain ⟨aN, haN, haNv, haNn⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
  have hlt : lb.coverAvailable.operator_lt aN = false :=
    (operator_lt_eq_false_iff _ _ hAn haNn).mpr (by rw [haNv]; linarith)
  have hz0 : amount.isZero = false := (STAmount.isZero_eq_false_iff_pos amount hpos.le).mpr hpos

  -- the cover left after the withdrawal is still at least the minimum cover
  obtain ⟨c', hsub⟩ := Number.operator_sub_ok_of_lt lb.coverAvailable aN .to_nearest hAn haNn hA0 hA96
    (by rw [haNv]; exact hpos.le) (by rw [haNv]; linarith)
  have hc'n := operator_sub_isNormalized_to_nearest_sz _ _ _ hAn haNn hsub
  have hc'm : minimumCover.toRat ≤ c'.toRat :=
    (operator_sub_rounded_to_nearest _ _ _ hAn haNn hsub).ge_of_le (Or.inl rfl) _ hmn (by rw [haNv]; linarith)
  have hmc : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover
      (AssetPool.baseExponent v) = .ok true := by
    have hmin' : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent v) =
        .ok minimumCover := hmin
    unfold RawLoanBroker.hasMinimumCover
    rw [hmin', ok_bind, (operator_le_iff _ _ hmn hc'n).mpr hc'm]
    rfl
  unfold LoanBroker.canCoverWithdraw
  simp only [hcl, ok_bind, hz0, haN, hlt, hsub, hmc, Bool.false_eq_true, if_false, Bool.not_true, pure_bind]
  rfl

end XRPL.Model.Lending
