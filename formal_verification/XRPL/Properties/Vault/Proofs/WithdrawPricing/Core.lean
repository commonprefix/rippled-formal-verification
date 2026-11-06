import XRPL.Properties.Protocol.Number.Sub.RoundsWithin
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Vault.Proofs.Support.WithdrawExchange
import XRPL.Properties.Vault.Proofs.DepositTight.DivSharp
import XRPL.Properties.Vault.Proofs.WithdrawMono.OfNumber
import XRPL.Properties.Vault.Common.DepositDefs

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
  have hnn : 0 ≤ n.toRat := Number.toRat_nonneg_of_nonnegative n hneg
  by_cases hint : nt.isIntegral = true
  · obtain ⟨z, hz, hz0, hhalf, hoff, -, -⟩ := WdMono.int_pack nt hint n result hn hnn hok
    rw [hz, show result.exponent = 0 from hoff, zpow_zero, mul_one]
    exact ⟨hhalf, by exact_mod_cast hz0⟩
  · have hfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    subst hfr
    have hnz : n.mantissa_ ≠ 0 := by
      intro h; rw [Number.eq_zero_of_mantissa_zero n hn h] at hok
      rw [WdMono.zero_frac_eq result hok] at hres; exact hres rfl
    obtain ⟨-, hrneg, hhalf, -, -⟩ := WdMono.frac_pack n result hn hneg hnz hok hres
    exact ⟨hhalf, by rw [STAmount.toRat_of_nonneg result hrneg]; positivity⟩

/-- The `mul`/`div` pricing stages of a nonzero result stay within `sharesε` of the exact
quotient, and the result is positive and normalized. -/
lemma pipe (nav sn NS an ST : Number) (hnav : nav.isNormalized) (hN0 : 0 ≤ nav.toRat)
    (hsn : sn.isNormalized) (hs0 : 0 ≤ sn.toRat) (hST : ST.isNormalized) (hSTpos : 0 < ST.toRat)
    (hmul : nav.operator_mul sn .to_nearest = .ok NS)
    (hdiv : NS.operator_div ST .to_nearest = .ok an) (han : an.mantissa_ ≠ 0) :
    an.isNormalized ∧ 0 < an.toRat ∧
    |an.toRat - nav.toRat * sn.toRat / ST.toRat| ≤
      nav.toRat * sn.toRat / ST.toRat * sharesε := by
  have hyne : ¬ ST.operator_eq Number.zero = true := fun h => by
    simp [Number.operator_div, h] at hdiv
  have hNSm := operator_div_numerator_ne_zero_sz _ _ _ _ hyne hdiv han
  obtain ⟨hnm, hsm⟩ := operator_mul_operands_ne_zero hnav hsn hmul hNSm
  have hNSn := operator_mul_result_isNormalized _ _ _ _ hnav hsn hnm hsm hmul hNSm
  obtain ⟨-, hSTm⟩ := operator_div_operands_ne_zero hNSn hST hdiv han
  have hann := operator_div_result_isNormalized _ _ _ _ hNSn hST hNSm hSTm hdiv han
  have h1 : |NS.toRat - nav.toRat * sn.toRat| ≤ |nav.toRat * sn.toRat| * (5 / (2 ^ 63 + 7)) :=
    operator_mul_rounds_to_nearest nav sn NS hnav hsn hmul hNSm
  have h2 : |an.toRat - NS.toRat / ST.toRat| ≤ |NS.toRat / ST.toRat| * DepTight.divSharpε :=
    DepTight.operator_div_rounds_to_nearest_sharp NS ST an hNSn hST hdiv han
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
  have h2' : |an.toRat - Q| ≤ I * (1 + 5 / (2 ^ 63 + 7)) * DepTight.divSharpε :=
    le_trans h2 (mul_le_mul_of_nonneg_right hQabs (by unfold DepTight.divSharpε; norm_num))
  obtain ⟨ha1, ha2⟩ := abs_le.mp h2'
  have hc : (1 + 5 / (2 ^ 63 + 7) : ℚ) * DepTight.divSharpε + 5 / (2 ^ 63 + 7) ≤ sharesε := by
    unfold DepTight.divSharpε sharesε; norm_num
  have hbound : |an.toRat - I| ≤ I * sharesε := by
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
  have : (sharesε : ℚ) < 1 := by unfold sharesε; norm_num
  nlinarith

/-- The pricing value backing `idealAssetsWithdraw`. -/
abbrev navQ (v : Vault) (w : Bool) : ℚ := if w then v.depositNav else v.withdrawNav

lemma navQ_nonneg (v : Vault) (w : Bool) : 0 ≤ navQ v w := by
  have hAA := v.exact.assetsAvailable_nonneg
  have hAD := v.exact.assetsDeployed_nonneg
  have hLU := v.exact.lossUnrealized_le
  cases w
  · show 0 ≤ v.toExact.assetsAvailable + v.toExact.assetsDeployed - v.toExact.lossUnrealized
    linarith
  · show 0 ≤ v.toExact.assetsAvailable + v.toExact.assetsDeployed
    linarith

/-- The two paths of `sharesToAssetsWithdraw`, exposing the computed pricing value. -/
lemma price_cases (v : Vault) (sh p : STAmount) (w : Bool)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) :
    ∃ nav : Number, v.assetsTotalForWithdrawal w = .ok nav ∧
    nav.isNormalized ∧
    ((nav.mantissa_ = 0 ∧ p = STAmount.zero v.numericType) ∨
     (nav.mantissa_ ≠ 0 ∧ ∃ sn NS an, sh.toNumber .to_nearest = .ok sn ∧
        nav.operator_mul sn .to_nearest = .ok NS ∧
        NS.operator_div v.sharesTotal .to_nearest = .ok an ∧
        STAmount.ofNumber v.numericType an .to_nearest = .ok p)) := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals refine ⟨_, ‹_›, (Vault.assetsTotalForWithdrawal_nonneg v w _ ‹_›).1, ?_⟩
  all_goals first
    | exact Or.inl ⟨by simp_all, rfl⟩
    | exact Or.inr ⟨by simp_all, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›⟩

/-- Value specification of `sharesToAssetsWithdraw` against the computed pricing value `nav`: a nonzero
result is the half-ULP rounding of a `Number` within `sharesε` of `nav * shares / sharesTotal`. -/
lemma price_spec (v : Vault) (sh p : STAmount) (w : Bool) (hnn : 0 ≤ sh.toRat)
    (hc : sh.Canonical) (hok : v.sharesToAssetsWithdraw sh w = .ok p) :
    ∃ nav : Number, v.assetsTotalForWithdrawal w = .ok nav ∧
      0 ≤ nav.toRat ∧ 0 ≤ p.toRat ∧
      (p.mValue = 0 ∨
        (nav.mantissa_ ≠ 0 ∧ 0 < v.sharesTotal.toRat ∧ ∃ an : Number, 0 < an.toRat ∧
          |an.toRat - nav.toRat * sh.toRat / v.sharesTotal.toRat| ≤
            nav.toRat * sh.toRat / v.sharesTotal.toRat * sharesε ∧
          |p.toRat - an.toRat| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ p.exponent ∧
          an.isNormalized ∧ STAmount.ofNumber v.numericType an .to_nearest = .ok p)) := by
  obtain ⟨nav, hsub, hnavn, hcase⟩ := price_cases v sh p w hok
  refine ⟨nav, hsub, ?_⟩
  rcases hcase with ⟨hm0, rfl⟩ | ⟨hm, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero nav hm0]
    refine ⟨le_rfl, ?_, Or.inl (STAmount.zero_mValue _)⟩
    rw [STAmount.zero_toRat _]
  have hN0 : 0 ≤ nav.toRat := (Vault.assetsTotalForWithdrawal_nonneg v w nav hsub).2
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
  exact ⟨hpnn, Or.inr ⟨hm, hSTpos, an, hanpos, hb, hh, hann, hof⟩⟩

end XRPL.Model.SingleAssetVault.WdPrice
