import XRPL.Properties.Vault.Proofs.ClawbackTight.Pipe
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Vault.Proofs.ClawbackTight.Amounts

/-! # Truncated share pricing of a clawback -/

namespace XRPL.Model.SingleAssetVault.ClwTight

open XRPL.Model.Protocol

/-- The pricing `nav` of a lawful vault with exact withdraw NAV. -/
lemma nav_facts (v : Vault) (hnav : v.WithdrawNavExact false) (nav : Number)
    (h : v.assetsTotal.operator_sub v.lossUnrealized .to_nearest = .ok nav) :
    nav.isNormalized ∧ nav.toRat = v.withdrawNav ∧ 0 ≤ nav.toRat := by
  obtain ⟨n', hn', hv⟩ := hnav
  obtain rfl : n' = nav := Except.ok.inj (hn'.symm.trans h)
  simp only [Bool.false_eq_true, if_false] at hv
  refine ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm
    v.wf.lossUnrealized_norm h, hv, ?_⟩
  rw [hv]; exact v.exact.withdraw_nav_nonneg

lemma sharesTotal_eq (v : Vault) : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
  RawVault.WF.toExact_sharesTotal v.toRawVault v.wf

/-- A nonzero truncated share count prices `X` within one share below and `sharesε`
above the ideal. -/
lemma shares_core (v : Vault) (hnav : v.WithdrawNavExact false) (X d : STAmount) (hX : NumExact X)
    (hX0 : 0 ≤ X.toRat) (h : assetsToSharesWithdraw v X true false = .ok d) (hd : d.mValue ≠ 0) :
    d.toRat.den = 1 ∧ 0 ≤ d.toRat ∧
      v.idealSharesClawback X.toRat * (1 - sharesε) - 1 < d.toRat ∧
      d.toRat ≤ v.idealSharesClawback X.toRat * (1 + sharesε) := by
  simp only [assetsToSharesWithdraw, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  · exact absurd (STAmount.zero_mValue _) hd
  obtain ⟨nav, xn, sa, sn, tr, hsub, hnz, hx', hmul, hdiv, htr, hof⟩ : ∃ nav xn sa sn tr : Number,
      v.assetsTotal.operator_sub v.lossUnrealized .to_nearest = .ok nav ∧
      ¬ (nav.mantissa_ == 0) = true ∧ X.toNumber .to_nearest = .ok xn ∧
      v.sharesTotal.operator_mul xn .to_nearest = .ok sa ∧ sa.operator_div nav .to_nearest = .ok sn ∧
      sn.truncate = .ok tr ∧ STAmount.ofNumber .int64 tr .to_nearest = .ok d :=
    ⟨_, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
  obtain ⟨hxnn, hxv⟩ := hX xn hx'
  replace hnz : nav.mantissa_ ≠ 0 := by simpa using hnz
  obtain ⟨hnavn, hnavv, hnav0⟩ := nav_facts v hnav nav hsub
  have htrm := STAmount.ofNumber_integral_source_ne_zero _ _ _ _ rfl hof hd
  have hsnm := Number.truncate_source_ne_zero _ _ htr htrm
  have hnavpos : 0 < nav.toRat :=
    lt_of_le_of_ne hnav0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hnz))
  obtain ⟨hsnn, hI, hsnb⟩ := pipe_sharp _ _ _ _ _ v.wf.sharesTotal_norm hxnn hnavn v.wf.sharesTotal_nonneg
    (by rw [hxv]; exact hX0) hnavpos hmul hdiv hsnm
  have hideal : v.sharesTotal.toRat * xn.toRat / nav.toRat = v.idealSharesClawback X.toRat := by
    unfold RawVault.idealSharesClawback; rw [sharesTotal_eq, hxv, hnavv]
  rw [hideal] at hI hsnb
  set I := v.idealSharesClawback X.toRat
  have hε : (0 : ℚ) ≤ sharesε ∧ sharesε ≤ 1 / 2 := by unfold sharesε; norm_num
  have hsnlo := (abs_le.mp hsnb).1
  have hsnhi := (abs_le.mp hsnb).2
  have hsnpos : 0 < sn.toRat := by
    have : I * sharesε ≤ I * (1 / 2) := mul_le_mul_of_nonneg_left hε.2 hI.le
    linarith
  obtain ⟨htrv, htrn⟩ := Number.truncate_floor sn tr hsnn (Number.negative_false_of_pos sn hsnpos) htr
  have hdv : d.toRat = tr.toRat :=
    STAmount.ofNumber_integral_exact _ _ _ _ rfl (htrn htrm) (by rw [htrv]; exact Rat.den_intCast _)
      hof
  rw [hdv, htrv]
  refine ⟨Rat.den_intCast _, by exact_mod_cast Int.floor_nonneg.mpr hsnpos.le, ?_, ?_⟩
  · have := Int.sub_one_lt_floor sn.toRat
    linarith
  · have := Int.floor_le sn.toRat
    linarith

/-- `shares_core` with the coarser `depositε`. -/
lemma shares_core_weak (v : Vault) (hnav : v.WithdrawNavExact false) (X d : STAmount)
    (hX : NumExact X) (hX0 : 0 ≤ X.toRat) (h : assetsToSharesWithdraw v X true false = .ok d)
    (hd : d.mValue ≠ 0) :
    d.toRat.den = 1 ∧ 0 ≤ d.toRat ∧
      v.idealSharesClawback X.toRat * (1 - depositε) - 1 < d.toRat ∧
      d.toRat ≤ v.idealSharesClawback X.toRat * (1 + depositε) := by
  obtain ⟨h1, h2, h3, h4⟩ := shares_core v hnav X d hX hX0 h hd
  have hle : sharesε ≤ depositε := by unfold sharesε depositε; norm_num
  have hs0 : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  have hI : 0 ≤ v.idealSharesClawback X.toRat := by
    by_contra hn; replace hn := not_le.mp hn; nlinarith
  refine ⟨h1, h2, ?_, ?_⟩ <;> nlinarith

end XRPL.Model.SingleAssetVault.ClwTight
