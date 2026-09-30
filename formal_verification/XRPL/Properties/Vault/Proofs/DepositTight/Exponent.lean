import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.SameSign
import XRPL.Properties.Vault.Proofs.DepositTight.Clamp
import XRPL.Properties.Vault.Common.MonotoneCore

/-! # The post-sum exponent is monotone in the delta -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol

/-- A same-sign positive `to_nearest` sum whose truth lies in
`(9999999999999999490·10^j, 9999999999999999500·10^j)` is a nearest representable. -/
lemma add_nearestTo_window (x y s : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hxn : x.negative_ = false) (hyn : y.negative_ = false)
    (hnz : ¬ x.operator_eq y.operator_neg)
    (hok : Number.operator_add x y .to_nearest = .ok s) (j : ℤ)
    (hlo : (9999999999999999490 : ℚ) * 10 ^ j < x.toRat + y.toRat)
    (hhi : x.toRat + y.toRat < (9999999999999999500 : ℚ) * 10 ^ j) :
    s.NearestTo (x.toRat + y.toRat) := by
  obtain ⟨zm, ze', f, g, res_pos, hzm_lo, hzm_hi, hf_nn, hf_lt, -, hval, hrup, habs, hres_ne,
      hrep, hsneg, -, -, -⟩ :=
    operator_add_algorithmic_facts_same_sign_to_nearest x y s hx hy hxm hym (by rw [hxn, hyn]) hnz hok
  set t := x.toRat + y.toRat with ht_def
  have hj : (0 : ℚ) < 10 ^ j := zpow_pos (by norm_num) _
  have hpos : 0 < t := lt_trans (by positivity) hlo
  have htv : t = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by rw [← abs_of_pos hpos, hval]
  have hze : (0 : ℚ) < 10 ^ ze' := zpow_pos (by norm_num) _
  have hmaxUp : maxRepUp.toNat = 9223372036854775810 := by decide
  have hzmq_hi : (zm.toNat : ℚ) ≤ 9223372036854775810 := by exact_mod_cast (hmaxUp ▸ hzm_hi)
  have hzmq_lo : (922337203685477580 : ℚ) ≤ (zm.toNat : ℚ) := by exact_mod_cast hzm_lo
  have htlo : (zm.toNat : ℚ) * 10 ^ ze' ≤ t := by rw [htv]; nlinarith
  have hthi : t < ((zm.toNat : ℚ) + 1) * 10 ^ ze' := by rw [htv]; nlinarith
  -- the cell sits at `ze' = j + 1` with `zm = 999999999999999949`
  have hze_eq : ze' = j + 1 := by
    rcases lt_trichotomy ze' (j + 1) with h | h | h
    · exfalso
      have h1 : (10 : ℚ) ^ ze' ≤ 10 ^ j := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : t < 9223372036854775811 * 10 ^ j := by nlinarith
      linarith
    · exact h
    · exfalso
      have h1 : (10 : ℚ) ^ (j + 2) ≤ 10 ^ ze' := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h2 : (10 : ℚ) ^ (j + 2) = 10 ^ j * 10 ^ 2 := p10 j 2
      have : (92233720368547758000 : ℚ) * 10 ^ j ≤ t := by nlinarith
      linarith
  subst hze_eq
  have h1 : (10 : ℚ) ^ (j + 1) = 10 ^ j * 10 ^ 1 := p10 j 1
  have hzm_eq : zm.toNat = 999999999999999949 := by
    have ha : (zm.toNat : ℚ) < 999999999999999950 := by nlinarith
    have hb : (999999999999999948 : ℚ) < (zm.toNat : ℚ) := by nlinarith
    have ha' : zm.toNat < 999999999999999950 := by exact_mod_cast ha
    have hb' : 999999999999999948 < zm.toNat := by exact_mod_cast hb
    omega
  have hmax : maxRep.toNat = 9223372036854775807 := by decide
  have hclean : zm.toNat + 1 ≤ maxRep.toNat := by omega
  have hs_nn : 0 ≤ s.toRat := Number.toRat_nonneg_of_nonnegative s (hsneg.trans hxn)
  have hs_abs : s.toRat = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ := by
    rw [← abs_of_nonneg hs_nn]; exact habs
  have hcase := doRoundUp_clean_down_up g zm (j + 1) f res_pos s _ hrep hrup hs_abs hres_ne hclean
  exact Number.nearestTo_of_gap t f zm (j + 1) s hpos htv hf_nn hf_lt (by omega) (by omega) hcase

/-- The post-sum pieces of a positive canonical delta on a nonnegative total. -/
lemma post_sum_parts (A : Number) (p : STAmount) (e : ℤ)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat)
    (hp : p.IOUCanonical) (hpneg : p.mIsNegative = false)
    (he : postSumExponent A p = .ok e) :
    ∃ (pn sum : Number) (a : STAmount),
      pn.isNormalized ∧ pn.toRat = p.toRat ∧ pn.mantissa_ ≠ 0 ∧ pn.negative_ = false ∧
      p.toNumber .to_nearest = .ok pn ∧
      A.operator_add pn .to_nearest = .ok sum ∧
      sum.RoundsToRepresentable (A.toRat + p.toRat) .to_nearest ∧
      sum.isNormalized ∧ 0 ≤ sum.toRat ∧
      STAmount.ofNumber .fractional sum .to_nearest = .ok a ∧ a.exponent = e := by
  obtain ⟨dn, sum, a, hdn, hsum, ha, hae⟩ := postSumExponent_reduces A p e he
  rw [show p.numericType = .fractional from hp.is_fractional] at ha
  obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact p .to_nearest hp
  rw [show dn = sn from Except.ok.inj (hdn.symm.trans hsn)] at hsum
  have hp0 : 0 < p.toRat :=
    STAmount.toRat_pos_of p hpneg (by have := hp.mant_lo; intro h; rw [h] at this; simp at this)
  have hsm : sn.mantissa_ ≠ 0 := by
    intro h; rw [Number.toRat_eq_zero_of_mantissa_zero sn h] at hsnv; linarith
  have hrsum := operator_add_rounded_to_nearest A sn sum hA hsnn hsum
  rw [hsnv] at hrsum
  have hsum_norm : sum.isNormalized := operator_add_isNormalized_to_nearest' A sn sum hA hsnn hsum
  have hsum_nn : 0 ≤ sum.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg sum _ hrsum (by linarith)
  exact ⟨sn, sum, a, hsnn, hsnv, hsm,
    Number.negative_false_of_normalized_nonneg sn hsnn (by linarith), hsn, hsum, hrsum,
    hsum_norm, hsum_nn, ha, hae⟩

/-- **The post-sum exponent is monotone in the delta.** -/
lemma postSumExponent_mono (A : Number) (p x : STAmount) (ep ex : ℤ)
    (hA : A.isNormalized) (hA0 : 0 ≤ A.toRat)
    (hp : p.IOUCanonical) (hpneg : p.mIsNegative = false)
    (hx : x.IOUCanonical) (hxneg : x.mIsNegative = false)
    (hle : p.toRat ≤ x.toRat)
    (hep : postSumExponent A p = .ok ep) (hex : postSumExponent A x = .ok ex) :
    ep ≤ ex := by
  obtain ⟨-, hep_lo, -, -, hsum_lo⟩ := post_exp_facts A p ep hA hA0 hp hpneg hep
  obtain ⟨pn, sp, ap, hpnn, hpnv, hpnm, hpnneg, hpn, hsp, hrsp, hspn, hspnn, hap, hape⟩ :=
    post_sum_parts A p ep hA hA0 hp hpneg hep
  obtain ⟨xn, sx, ax, hxnn, hxnv, hxnm, hxnneg, hxn, hsx, hrsx, hsxn, hsxnn, hax, haxe⟩ :=
    post_sum_parts A x ex hA hA0 hx hxneg hex
  have hj : (-100 : ℤ) ≤ ep - 4 := by omega
  have hsp_ge : WdMono.carryPt (ep - 4) ≤ sp.toRat :=
    (WdMono.exp_ge_iff sp ap hspn hspnn hap (ep - 4) hj).mp (by rw [hape]; omega)
  have key : WdMono.carryPt (ep - 4) ≤ sx.toRat := by
    by_cases hbig : WdMono.carryPt (ep - 4) ≤ A.toRat + x.toRat
    · obtain ⟨w, hw, -, hwv⟩ := exists_normalized_scaled 999999999999999950 (ep - 3) (by norm_num)
        (by norm_num) (by omega) (by have := post_exp_facts A p ep hA hA0 hp hpneg hep; omega)
      have hwv' : w.toRat = WdMono.carryPt (ep - 4) := by
        rw [hwv]; unfold WdMono.carryPt
        rw [show ep - 3 = (ep - 4) + ((1 : ℕ) : ℤ) by push_cast; ring, p10]; push_cast; ring
      rw [← hwv']
      exact Number.RoundsToRepresentable.ge_of_ge_normalized sx _ hrsx w hw (by rw [hwv']; exact hbig)
    · push_neg at hbig
      have hmono : sp.toRat ≤ sx.toRat := by
        by_cases hAm : A.mantissa_ = 0
        · -- a zero total: both sums are exact
          have hA0' : A.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero A hAm
          have h1 := Number.RoundsToRepresentable.eq_of_representable sp _ hrsp pn hpnn
            (by rw [hpnv, hA0']; ring)
          have h2 := Number.RoundsToRepresentable.eq_of_representable sx _ hrsx xn hxnn
            (by rw [hxnv, hA0']; ring)
          rw [h1, h2]; linarith
        · have hAn : A.negative_ = false := Number.negative_false_of_normalized_nonneg A hA hA0
          have hnz : ∀ y : Number, y.mantissa_ ≠ 0 → y.negative_ = false →
              ¬ A.operator_eq y.operator_neg = true := by
            intro y hym hyn h
            unfold Number.operator_eq Number.operator_neg at h
            simp [hym, hAn, hyn] at h
          have hcp : WdMono.carryPt (ep - 4) = (9999999999999999500 : ℚ) * 10 ^ (ep - 4) := rfl
          have hn1 := add_nearestTo_window A pn sp hA hpnn hAm hpnm hAn hpnneg (hnz pn hpnm hpnneg)
            hsp (ep - 4) (by rw [hpnv]; exact hsum_lo) (by rw [hpnv, ← hcp]; linarith)
          have hn2 := add_nearestTo_window A xn sx hA hxnn hAm hxnm hAn hxnneg (hnz xn hxnm hxnneg)
            hsx (ep - 4) (by rw [hxnv]; linarith) (by rw [hxnv, ← hcp]; exact hbig)
          refine round_mono_core _ _ sp sx hn1 hn2 hspn hsxn (by rw [hpnv, hxnv]; linarith) ?_
          intro heq
          have hpx : pn = xn := Number.isNormalized.toRat_inj hpnn hxnn (by linarith)
          rw [hpx] at hsp
          rw [Except.ok.inj (hsp.symm.trans hsx)]
      linarith
  rw [← haxe]
  have := (WdMono.exp_ge_iff sx ax hsxn hsxnn hax (ep - 4) hj).mpr key
  omega

end XRPL.Model.SingleAssetVault.DepTight
