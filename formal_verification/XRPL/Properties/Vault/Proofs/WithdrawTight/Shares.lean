import XRPL.Properties.Vault.Proofs.WithdrawAccuracy
import XRPL.Properties.Vault.Proofs.WithdrawMono
import XRPL.Properties.Vault.Proofs.DepositTight.DivSharp

/-! # Shares burned by an asset-denominated withdrawal

The shares are `⌊round(round(sharesTotal · assets) / nav)⌋`, so they sit at most the
`Number` stage error above the ideal and less than one share plus that error below. -/

namespace XRPL.Model.SingleAssetVault.WdTight

open XRPL.Model.Protocol

/-- The pricing steps of the truncating `assetsToSharesWithdraw`. -/
lemma shares_reduces (v : Vault) (a s : STAmount) (w : Bool)
    (hok : assetsToSharesWithdraw v a true w = .ok s) :
    ∃ nav, v.assetsTotal.operator_sub (match w with
        | true => Number.zero
        | false => v.lossUnrealized) .to_nearest = .ok nav ∧
      ((nav.mantissa_ = 0 ∧ s = STAmount.zero .int64) ∨
       (nav.mantissa_ ≠ 0 ∧ ∃ an SA SN t, a.toNumber .to_nearest = .ok an ∧
          v.sharesTotal.operator_mul an .to_nearest = .ok SA ∧
          SA.operator_div nav .to_nearest = .ok SN ∧ SN.truncate = .ok t ∧
          STAmount.ofNumber .int64 t .to_nearest = .ok s)) := by
  simp only [assetsToSharesWithdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | exact ⟨_, ‹_›, Or.inl ⟨beq_iff_eq.mp ‹_›, rfl⟩⟩
    | exact ⟨_, ‹_›, Or.inr ⟨by simp_all, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩⟩

/-- A successful error-free withdrawal by assets burns the nonzero truncated shares. -/
lemma burned_of_assets (v : Vault) (a : STAmount) (w : Bool) (r : WithdrawResult)
    (hpos : 0 < a.toRat) (hok : v.withdraw (.vaultAssets a) w hpos = .ok r)
    (herr : r.error = none) :
    assetsToSharesWithdraw v a true w = .ok r.sharesBurned ∧ r.sharesBurned.isZero = false := by
  obtain ⟨cw, -, -, hcomp, hcerr, -, -, -, hsb, -⟩ :=
    WdAcc.withdraw_ok_cases v (.vaultAssets a) w r hpos hok herr
  rw [hsb]
  simp only [computeWithdrawByAssets, bind, Except.bind, pure, Except.pure, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at hcomp
  walk_ok
  all_goals first
    | (simp at hcerr; done)
    | exact ⟨‹_›, by simpa using ‹¬ _ = true›⟩

lemma pipe_up : ((1 : ℚ) + 5 / (2 ^ 63 + 7)) * (1 + 6 / (2 ^ 63 - 3)) ≤ 1 + depositε := by
  rw [WdAcc.depositε_val]; norm_num

lemma pipe_lo : (1 : ℚ) - depositε ≤ (1 - 5 / (2 ^ 63 + 7)) * (1 - 6 / (2 ^ 63 - 3)) := by
  rw [WdAcc.depositε_val]; norm_num

lemma pipe_up_sharp :
    ((1 : ℚ) + 5 / (2 ^ 63 + 7)) * (1 + DepTight.divSharpε) ≤ 1 + sharesε := by
  unfold DepTight.divSharpε sharesε; norm_num

lemma pipe_lo_sharp :
    (1 : ℚ) - sharesε ≤ (1 - 5 / (2 ^ 63 + 7)) * (1 - DepTight.divSharpε) := by
  unfold DepTight.divSharpε sharesε; norm_num

/-- Bounds of the truncated shares against `idealSharesWithdraw`. -/
lemma shares_bounds (v : Vault) (a s : STAmount) (w : Bool)
    (hnav : v.WithdrawNavExact w) (hpos : 0 < a.toRat) (hc : a.Canonical)
    (hok : assetsToSharesWithdraw v a true w = .ok s) (hnz : s.isZero = false) :
    s.toRat.den = 1 ∧ 0 < s.toRat ∧
    s.toRat ≤ v.idealSharesWithdraw w a.toRat * (1 + sharesε) ∧
    v.idealSharesWithdraw w a.toRat * (1 - sharesε) - 1 < s.toRat := by
  have hmv : s.mValue ≠ 0 := ne_of_beq_false (show (s.mValue == 0) = false from hnz)
  obtain ⟨nav, hsub, hcase⟩ := shares_reduces v a s w hok
  obtain ⟨hnavn, hnav0, hnavq⟩ := WdMono.nav_facts v w nav hsub hnav
  rcases hcase with ⟨-, rfl⟩ | ⟨hnm, an, SA, SN, t, han, hmul, hdiv, htr, hof⟩
  · exact absurd rfl hmv
  obtain ⟨an0, han0, hanv, hann⟩ := STAmount.toNumber_exact_canonical a .to_nearest
    (STAmount.Canonical.exactCanonical a hc)
  obtain rfl : an = an0 := Except.ok.inj (han.symm.trans han0)
  have htm : t.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 t .to_nearest s (by decide) hof hmv
  have hSNm : SN.mantissa_ ≠ 0 := Number.truncate_source_ne_zero SN t htr htm
  have hSAm : SA.mantissa_ ≠ 0 := operator_div_numerator_ne_zero_sz SA nav SN .to_nearest
    (Number.not_operator_eq_zero_of_mantissa_ne hnm) hdiv hSNm
  obtain ⟨hSm, hanm⟩ := operator_mul_operands_ne_zero v.wf.sharesTotal_norm hann hmul hSAm
  have hSAn := operator_mul_result_isNormalized _ _ _ _ v.wf.sharesTotal_norm hann hSm hanm hmul hSAm
  have hSNn := operator_div_result_isNormalized _ _ _ _ hSAn hnavn hSAm hnm hdiv hSNm
  set ST := v.sharesTotal.toRat with hST
  set N := nav.toRat with hN
  have hST0 : 0 ≤ ST := v.wf.sharesTotal_nonneg
  have hSTpos : 0 < ST := lt_of_le_of_ne hST0
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSm))
  have hNpos : 0 < N := lt_of_le_of_ne hnav0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hnm))
  set T0 := ST * a.toRat with hT0
  have hT0pos : 0 < T0 := mul_pos hSTpos hpos
  have hmulb : |SA.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
    have := operator_mul_rounds_to_nearest _ _ _ v.wf.sharesTotal_norm hann hmul hSAm
    change |SA.toRat - v.sharesTotal.toRat * an.toRat| ≤
      |v.sharesTotal.toRat * an.toRat| * (5 / (2 ^ 63 + 7)) at this
    rwa [hanv, ← hST, ← hT0, abs_of_pos hT0pos] at this
  obtain ⟨hm1, hm2⟩ := abs_le.mp hmulb
  have hSApos : 0 < SA.toRat := by nlinarith
  have hQpos : 0 < SA.toRat / N := div_pos hSApos hNpos
  have hdivb : |SN.toRat - SA.toRat / N| ≤ SA.toRat / N * (DepTight.divSharpε) := by
    have := DepTight.operator_div_rounds_to_nearest_sharp _ _ _ hSAn hnavn hdiv hSNm
    rwa [← hN, abs_of_pos hQpos] at this
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdivb
  have hSNpos : 0 < SN.toRat := by
    have : SA.toRat / N * DepTight.divSharpε < SA.toRat / N :=
      mul_lt_of_lt_one_right hQpos (by unfold DepTight.divSharpε; norm_num)
    linarith
  obtain ⟨hfl, htn⟩ := Number.truncate_floor SN t hSNn (Number.negative_false_of_pos SN hSNpos) htr
  have htnn : 0 ≤ t.toRat := by rw [hfl]; exact_mod_cast Int.floor_nonneg.mpr hSNpos.le
  obtain ⟨z, hz, -, hzh, -⟩ := WdMono.int_pack .int64 (by decide) t s (htn htm) htnn hof
  have hzt : (z : ℚ) = t.toRat := by
    rw [hfl] at hzh ⊢
    have h1 : |((z - ⌊SN.toRat⌋ : ℤ) : ℚ)| ≤ 1 / 2 := by push_cast; exact hzh
    have h2 : z - ⌊SN.toRat⌋ = 0 := by
      by_contra hne
      have : (1 : ℚ) ≤ |((z - ⌊SN.toRat⌋ : ℤ) : ℚ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
      linarith
    have : z = ⌊SN.toRat⌋ := by omega
    rw [this]
  have hst : s.toRat = (⌊SN.toRat⌋ : ℚ) := by rw [hz, hzt, hfl]
  have hideal : v.idealSharesWithdraw w a.toRat = T0 / N := by
    unfold RawVault.idealSharesWithdraw
    rw [← hnavq, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  have hfle : (⌊SN.toRat⌋ : ℚ) ≤ SN.toRat := Int.floor_le _
  have hflt : SN.toRat - 1 < (⌊SN.toRat⌋ : ℚ) := Int.sub_one_lt_floor _
  have hs0 : s.toRat ≠ 0 := STAmount.toRat_ne_zero s hmv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hz]; exact Rat.den_intCast z
  · rw [hst] at hs0 ⊢
    have : (0 : ℚ) ≤ (⌊SN.toRat⌋ : ℚ) := by exact_mod_cast Int.floor_nonneg.mpr hSNpos.le
    exact lt_of_le_of_ne this (Ne.symm hs0)
  · rw [hst, hideal]
    have hq : SA.toRat / N ≤ T0 / N * (1 + 5 / (2 ^ 63 + 7)) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNpos]; linarith
    have hc1 := pipe_up_sharp
    have hTN : 0 < T0 / N := div_pos hT0pos hNpos
    calc (⌊SN.toRat⌋ : ℚ) ≤ SN.toRat := hfle
      _ ≤ SA.toRat / N * (1 + DepTight.divSharpε) := by linarith
      _ ≤ T0 / N * (1 + 5 / (2 ^ 63 + 7)) * (1 + DepTight.divSharpε) :=
          mul_le_mul_of_nonneg_right hq (by unfold DepTight.divSharpε; norm_num)
      _ ≤ T0 / N * (1 + sharesε) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hc1 hTN.le
  · rw [hst, hideal]
    have hq : T0 / N * (1 - 5 / (2 ^ 63 + 7)) ≤ SA.toRat / N := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNpos]; linarith
    have hc1 := pipe_lo_sharp
    have hTN : 0 < T0 / N := div_pos hT0pos hNpos
    have : T0 / N * (1 - sharesε) ≤ SN.toRat :=
      calc T0 / N * (1 - sharesε)
          ≤ T0 / N * ((1 - 5 / (2 ^ 63 + 7)) * (1 - DepTight.divSharpε)) :=
            mul_le_mul_of_nonneg_left hc1 hTN.le
        _ = T0 / N * (1 - 5 / (2 ^ 63 + 7)) * (1 - DepTight.divSharpε) := by ring
        _ ≤ SA.toRat / N * (1 - DepTight.divSharpε) :=
            mul_le_mul_of_nonneg_right hq (by unfold DepTight.divSharpε; norm_num)
        _ ≤ SN.toRat := by linarith
    linarith

end XRPL.Model.SingleAssetVault.WdTight
