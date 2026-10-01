import XRPL.Properties.Protocol.Number.Sub.RoundsWithin
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Pipe
import XRPL.Properties.Vault.Proofs.WithdrawAccuracy.Clamp
import XRPL.Properties.Vault.Proofs.Support.NumberFacts

/-! # Rounding facts for the `sharesToAssetsWithdraw` pricing -/

namespace XRPL.Model.SingleAssetVault.WdPrice

open XRPL.Model.Protocol

/-- `.to_nearest` `ofNumber` of a sign-cleared normalized `Number` lands within half a
ULP of the result and stays nonnegative. -/
lemma ofNumber_half (nt : NumericType) (n : Number)
    (result : STAmount) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) (hres : result.mValue ≠ 0) :
    |result.toRat - n.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ result.exponent ∧
    0 ≤ result.toRat := by
  by_cases hint : nt.isIntegral = true
  · unfold STAmount.ofNumber at hok
    simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, ↓reduceIte, hint] at hok
    cases hr : n.to_rep .to_nearest with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok intValue =>
      rw [hr] at hok
      simp only [] at hok
      obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n .to_nearest intValue hneg hr
      have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep intValue hnn hle
      obtain ⟨-, hres_exp, -, hexact⟩ := STAmount.canonicalize_integral_facts
        (STAmount.unchecked nt intValue.toUInt64 0 false) result .to_nearest
        (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint)
        rfl hval hok
      have hres_val : result.toRat = (intValue.toInt : ℚ) := by
        rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
        show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
        rw [toUInt64_toNat_of_nonneg intValue hnn]
      refine ⟨?_, by rw [hres_val]; exact_mod_cast hnn⟩
      rw [hres_val, show result.exponent = 0 from hres_exp, zpow_zero, mul_one]
      exact Number.to_rep_to_nearest_within_half n intValue hn hneg hr
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    have hn_ne : n.mantissa_ ≠ 0 :=
      STAmount.ofNumber_iou_mantissa_ne_zero nt n .to_nearest result hnt_frac hok hres
    obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
    have hexp_lo : minExponent ≤ n.exponent_ := by
      rcases hn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
      · exact hlo
    have hok' : STAmount.ofNumber .fractional n .to_nearest = .ok result := by
      rw [← hnt_frac]; exact hok
    have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
      STAmount.ofNumber_iou_success_exp_range n .to_nearest result hlo19 hhi19 hexp_lo hok' hres
    obtain ⟨hulp, hexp_ge⟩ := STAmount.ofNumber_iou_within_half_ulp nt n result hnt_frac
      hlo19 hhi19 hexp_lo hexp_hi hok hres
    have hnonneg : 0 ≤ result.toRat := by
      obtain ⟨mant, exp, -, hval, -, hcast, -⟩ :=
        STAmount.ofNumber_iou_snap_pos nt n .to_nearest result hnt_frac hneg
          hlo19 hhi19 hexp_lo hexp_hi hok hres
      rw [hval, hcast]; positivity
    refine ⟨le_trans hulp ?_, hnonneg⟩
    have hmono : (10 : ℚ) ^ (n.exponent_ + 3) ≤ (10 : ℚ) ^ result.exponent :=
      zpow_le_zpow_right₀ (by norm_num) hexp_ge
    linarith

/-- The `mul`/`div` pricing stages of a nonzero result stay within `12 / (2 ^ 63 - 3)`
of the exact quotient, and the result is positive and normalized. -/
lemma pipe (nav sn NS an ST : Number) (hnav : nav.isNormalized) (hN0 : 0 ≤ nav.toRat)
    (hsn : sn.isNormalized) (hs0 : 0 ≤ sn.toRat) (hST : ST.isNormalized) (hSTpos : 0 < ST.toRat)
    (hmul : nav.operator_mul sn .to_nearest = .ok NS)
    (hdiv : NS.operator_div ST .to_nearest = .ok an) (han : an.mantissa_ ≠ 0) :
    an.isNormalized ∧ 0 < an.toRat ∧
    |an.toRat - nav.toRat * sn.toRat / ST.toRat| ≤
      nav.toRat * sn.toRat / ST.toRat * (12 / (2 ^ 63 - 3)) := by
  have hyne : ¬ ST.operator_eq Number.zero = true := fun h => by
    simp [Number.operator_div, h] at hdiv
  have hNSm := operator_div_numerator_ne_zero_sz _ _ _ _ hyne hdiv han
  obtain ⟨hnm, hsm⟩ := operator_mul_operands_ne_zero hnav hsn hmul hNSm
  have hNSn := operator_mul_result_isNormalized _ _ _ _ hnav hsn hnm hsm hmul hNSm
  obtain ⟨-, hSTm⟩ := operator_div_operands_ne_zero hNSn hST hdiv han
  have hann := operator_div_result_isNormalized _ _ _ _ hNSn hST hNSm hSTm hdiv han
  have h1 : |NS.toRat - nav.toRat * sn.toRat| ≤ |nav.toRat * sn.toRat| * (5 / (2 ^ 63 + 7)) :=
    operator_mul_rounds_to_nearest nav sn NS hnav hsn hmul hNSm
  have h2 : |an.toRat - NS.toRat / ST.toRat| ≤ |NS.toRat / ST.toRat| * (6 / (2 ^ 63 - 3)) :=
    operator_div_rounds_to_nearest NS ST an hNSn hST hdiv han
  set T := nav.toRat * sn.toRat with hT
  have hT0 : 0 ≤ T := mul_nonneg hN0 hs0
  rw [abs_of_nonneg hT0] at h1
  set I := T / ST.toRat with hI
  set Q := NS.toRat / ST.toRat with hQ
  have hI0 : 0 ≤ I := div_nonneg hT0 hSTpos.le
  have hQI : |Q - I| ≤ I * (5 / (2 ^ 63 + 7)) := by
    have : Q - I = (NS.toRat - T) / ST.toRat := by rw [hQ, hI]; ring
    rw [this, abs_div, abs_of_pos hSTpos, hI, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right h1 hSTpos.le
  obtain ⟨hq1, hq2⟩ := abs_le.mp hQI
  have hQabs : |Q| ≤ I * (1 + 5 / (2 ^ 63 + 7)) := by
    rw [abs_le]; constructor <;> nlinarith
  have h2' : |an.toRat - Q| ≤ I * (1 + 5 / (2 ^ 63 + 7)) * (6 / (2 ^ 63 - 3)) :=
    le_trans h2 (mul_le_mul_of_nonneg_right hQabs (by norm_num))
  obtain ⟨ha1, ha2⟩ := abs_le.mp h2'
  have hc : (1 + 5 / (2 ^ 63 + 7) : ℚ) * (6 / (2 ^ 63 - 3)) + 5 / (2 ^ 63 + 7) ≤
      12 / (2 ^ 63 - 3) := by norm_num
  have hbound : |an.toRat - I| ≤ I * (12 / (2 ^ 63 - 3)) := by
    rw [abs_le]; constructor <;> nlinarith
  have hIpos : 0 < I := by
    rcases lt_or_eq_of_le hI0 with h | h
    · exact h
    · exfalso
      have hq0 : Q = 0 := by rw [← h] at hq1 hq2; simp at hq1 hq2; linarith
      have : NS.toRat = 0 := by
        rw [hQ] at hq0; rcases div_eq_zero_iff.mp hq0 with h' | h'
        · exact h'
        · linarith
      exact hNSm (Number.toRat_eq_zero_iff.mp this ▸ rfl)
  refine ⟨hann, ?_, hbound⟩
  obtain ⟨hb1, -⟩ := abs_le.mp hbound
  have : (12 / (2 ^ 63 - 3) : ℚ) < 1 := by norm_num
  nlinarith

/-- The loss operand of the pricing subtraction. -/
def lossOp (v : Vault) : Bool → Number
  | true => Number.zero
  | false => v.lossUnrealized

/-- The pricing value backing `idealAssetsWithdraw`. -/
abbrev navQ (v : Vault) (w : Bool) : ℚ := if w then v.depositNav else v.withdrawNav

lemma navQ_nonneg (v : Vault) (w : Bool) : 0 ≤ navQ v w := by
  cases w
  · exact v.exact.withdraw_nav_nonneg
  · exact v.exact.assetsTotal_nonneg

lemma navQ_le (v : Vault) (w : Bool) : navQ v w ≤ v.assetsTotal.toRat := by
  cases w
  · show v.toExact.assetsTotal - v.toExact.lossUnrealized ≤ _
    linarith [v.exact.lossUnrealized_nonneg, show v.toExact.assetsTotal = v.assetsTotal.toRat from rfl]
  · exact le_rfl

/-- The two paths of `sharesToAssetsWithdraw`, exposing the computed pricing value. -/
lemma price_cases (v : Vault) (sh p : STAmount) (w : Bool)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) :
    ∃ nav : Number, v.assetsTotal.operator_sub (lossOp v w) .to_nearest = .ok nav ∧
    nav.isNormalized ∧
    ((nav.mantissa_ = 0 ∧ p = STAmount.zero v.numericType) ∨
     (nav.mantissa_ ≠ 0 ∧ ∃ sn NS an, sh.toNumber .to_nearest = .ok sn ∧
        nav.operator_mul sn .to_nearest = .ok NS ∧
        NS.operator_div v.sharesTotal .to_nearest = .ok an ∧
        STAmount.ofNumber v.numericType an .to_nearest = .ok p)) := by
  cases w <;>
    simp only [Vault.sharesToAssetsWithdraw, lossOp, bind, Except.bind, pure, Except.pure] at hok ⊢ <;>
    walk_ok
  all_goals refine ⟨_, ‹_›, operator_sub_isNormalized_to_nearest' _ _ _ v.wf.assetsTotal_norm
      ?_ ‹_›, ?_⟩
  all_goals first
    | exact v.wf.lossUnrealized_norm
    | exact (Or.inl rfl : Number.zero.isNormalized)
    | exact Or.inl ⟨by simp_all, rfl⟩
    | exact Or.inr ⟨by simp_all, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›⟩

/-- A nonzero computed pricing value sits within the subtraction's rounding of the
exact one. -/
lemma nav_within (v : Vault) (w : Bool) (nav : Number)
    (hsub : v.assetsTotal.operator_sub (lossOp v w) .to_nearest = .ok nav)
    (hgen : nav.mantissa_ ≠ 0) :
    |nav.toRat - navQ v w| ≤ navQ v w * (6 / (2 ^ 63 - 3)) := by
  have hq0 := navQ_nonneg v w
  have hc : (0 : ℚ) ≤ navQ v w * (6 / (2 ^ 63 - 3)) := mul_nonneg hq0 (by norm_num)
  cases w with
  | true =>
    have hz := Number.operator_sub_zero_right v.assetsTotal Number.zero nav rfl hsub
    rw [hz]
    show |v.assetsTotal.toRat - v.assetsTotal.toRat| ≤ _
    rw [sub_self, abs_zero]; exact hc
  | false =>
    simp only [lossOp] at hsub
    by_cases hlm : v.lossUnrealized.mantissa_ = 0
    · have hz := Number.operator_sub_zero_right v.assetsTotal v.lossUnrealized nav hlm hsub
      have hl0 := Number.toRat_eq_zero_of_mantissa_zero v.lossUnrealized hlm
      have : navQ v false = v.assetsTotal.toRat := by
        show v.toExact.assetsTotal - v.toExact.lossUnrealized = _
        rw [show v.toExact.lossUnrealized = v.lossUnrealized.toRat from rfl, hl0, sub_zero]; rfl
      rw [hz, this, sub_self, abs_zero]; rw [this] at hc; exact hc
    · have hlpos : 0 < v.lossUnrealized.toRat := lt_of_le_of_ne v.exact.lossUnrealized_nonneg
        (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hlm))
      have ham : v.assetsTotal.mantissa_ ≠ 0 := by
        intro ha0
        have := Number.toRat_eq_zero_of_mantissa_zero v.assetsTotal ha0
        have := v.exact.withdraw_nav_nonneg
        change 0 ≤ v.assetsTotal.toRat - v.lossUnrealized.toRat at this
        linarith
      have hne : ¬ v.assetsTotal.operator_eq v.lossUnrealized = true := by
        intro heq
        have := Number.operator_sub_eq_zero_of_operator_eq _ _ _ ham hlm heq hsub
        rw [this] at hgen; exact hgen rfl
      have hr := operator_sub_rounds_to_nearest v.assetsTotal v.lossUnrealized nav
        v.wf.assetsTotal_norm v.wf.lossUnrealized_norm ham hlm hne hsub hgen
      have hr' : |nav.toRat - (v.assetsTotal.toRat - v.lossUnrealized.toRat)| ≤
          |v.assetsTotal.toRat - v.lossUnrealized.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) := hr
      have hq : navQ v false = v.assetsTotal.toRat - v.lossUnrealized.toRat := rfl
      rw [hq] at hq0 ⊢
      rwa [abs_of_nonneg hq0] at hr'

/-- Value specification of `sharesToAssetsWithdraw` against the computed pricing value
`nav`: a nonzero result is the half-ULP rounding of a `Number` within
`12 / (2 ^ 63 - 3)` of `nav * shares / sharesTotal`. -/
lemma price_spec (v : Vault) (sh p : STAmount) (w : Bool) (hnn : 0 ≤ sh.toRat)
    (hc : sh.Canonical) (hok : v.sharesToAssetsWithdraw sh w = .ok p) :
    ∃ nav : Number, v.assetsTotal.operator_sub (lossOp v w) .to_nearest = .ok nav ∧
      0 ≤ nav.toRat ∧ 0 ≤ p.toRat ∧
      (p.mValue = 0 ∨
        (nav.mantissa_ ≠ 0 ∧ 0 < v.sharesTotal.toRat ∧ ∃ an : Number, 0 < an.toRat ∧
          |an.toRat - nav.toRat * sh.toRat / v.sharesTotal.toRat| ≤
            nav.toRat * sh.toRat / v.sharesTotal.toRat * (12 / (2 ^ 63 - 3)) ∧
          |p.toRat - an.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ p.exponent)) := by
  obtain ⟨nav, hsub, hnavn, hcase⟩ := price_cases v sh p w hok
  refine ⟨nav, hsub, ?_⟩
  rcases hcase with ⟨hm0, rfl⟩ | ⟨hm, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero nav hm0]
    refine ⟨le_rfl, ?_, Or.inl (STAmount.zero_mValue _)⟩
    rw [(STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)]
  have hnw := nav_within v w nav hsub hm
  have hq0 := navQ_nonneg v w
  have hN0 : 0 ≤ nav.toRat := by
    obtain ⟨h1, -⟩ := abs_le.mp hnw
    have : navQ v w * (6 / (2 ^ 63 - 3)) ≤ navQ v w := by
      have : (6 / (2 ^ 63 - 3) : ℚ) ≤ 1 := by norm_num
      nlinarith
    linarith
  refine ⟨hN0, ?_⟩
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical sh .to_nearest
    (STAmount.Canonical.exactCanonical sh hc)
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  by_cases hp0 : p.mValue = 0
  · exact ⟨by rw [(STAmount.toRat_eq_zero_iff _).mpr hp0], Or.inl hp0⟩
  have han := STAmount.ofNumber_source_ne_zero _ _ _ _ hof hp0
  have hyne : ¬ v.sharesTotal.operator_eq Number.zero = true := fun h => by
    simp [Number.operator_div, h] at hdiv
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := fun h0 => hyne (by
    rw [Number.eq_zero_of_mantissa_zero _ v.wf.sharesTotal_norm h0]; decide)
  have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSTm))
  obtain ⟨hann, hanpos, hb⟩ := pipe nav sn0 NS an v.sharesTotal hnavn hN0 hsnn (hsnv ▸ hnn)
    v.wf.sharesTotal_norm hSTpos hmul hdiv han
  obtain ⟨hh, hpnn⟩ := ofNumber_half v.numericType an p hann
    (Number.negative_false_of_pos an hanpos) hof hp0
  rw [hsnv] at hb
  exact ⟨hpnn, Or.inr ⟨hm, hSTpos, an, hanpos, hb, hh⟩⟩

end XRPL.Model.SingleAssetVault.WdPrice
