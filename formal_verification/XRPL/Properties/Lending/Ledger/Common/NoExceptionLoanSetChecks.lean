import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetValue
import XRPL.Properties.Lending.LoanBroker.Common.CoverGrid
import XRPL.Properties.Protocol.STAmount.Common.Representable

/-! # The checks of a new loan compute

The precision check, amortization guards, Open limit check and broker limits of a LoanSet each return a result code
once the loan's values are within the asset's range. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private checkPrecisionFields from XRPL.Model.Lending.Loan.LoanSet
open private STAmount.roundsInRange_of_le_max STAmount.roundToNumericType_integral_of_inRange
  from XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetValue
open private Vault.assetsTotal_ge_available from XRPL.Properties.Lending.Loan.Common.SetScale

local notation "ε" => Number.nearestError

/-- An amount the asset stores, at least zero, rounds into the asset's range in every mode. -/
private lemma STAmount.roundsInRange_of_representable (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (mode : rounding_mode) (x : ℚ)
    (h0 : 0 ≤ x) (h : STAmount.Representable nt x) : STAmount.RoundsInRange nt mode x := by
  rcases hnt with rfl | hnt
  · -- an IOU amount is at most `9999999999999999e80`
    have hx : x ≤ 9999999999999999 * 10 ^ 80 := by
      rcases h with rfl | ⟨m, e, -, hm, -, he, rfl⟩
      · norm_num
      · have hm' : (m : ℚ) ≤ 9999999999999999 := by
          have : m ≤ 9999999999999999 := by omega
          exact_mod_cast this
        have he' : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
        calc (m : ℚ) * 10 ^ e ≤ 9999999999999999 * 10 ^ (80 : ℤ) :=
              mul_le_mul hm' he' (by positivity) (by norm_num)
          _ = 9999999999999999 * 10 ^ 80 := by norm_num
    cases mode <;> simp only [STAmount.RoundsInRange]
    · rw [abs_of_nonneg h0]
      linarith [show (9999999999999999 : ℚ) * 10 ^ 80 < 99999999999999995 * 10 ^ 79 by norm_num]
    · rw [abs_of_nonneg h0]; linarith [show (9999999999999999 : ℚ) * 10 ^ 80 < 10 ^ 96 by norm_num]
    · exact ⟨by linarith, by linarith [show (9999999999999999 : ℚ) * 10 ^ 80 < 10 ^ 96 by norm_num]⟩
    · exact ⟨by linarith, hx⟩
  · -- an XRP or MPT amount is a whole number within the maximum
    refine STAmount.roundsInRange_of_le_max nt hnt mode x h0 ?_
    rcases h with rfl | h
    · positivity
    · rcases hnt with rfl | rfl
      all_goals
        obtain ⟨-, k, hk, -, rfl⟩ := h
        exact_mod_cast hk

/-- An IOU: a nonnegative `Number` that rounds into the IOU range rounds to an IOU amount at a scale in
`[-96, 79]`. -/
private lemma STAmount.roundToNumericType_frac_of_inRange (x : Number) (mode : rounding_mode) (s : Int)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hin : STAmount.RoundsInRange .fractional mode x.toRat)
    (hs : -96 ≤ s ∧ s ≤ 79) : ∃ y, STAmount.roundToNumericType .fractional x mode (some s) = .ok y := by
  obtain ⟨ret, hret⟩ := (STAmount.ofNumber_ok_iff .fractional x mode hx (Or.inl rfl) (Or.inl h0)).mpr hin
  have hretf := STAmount.ofNumber_fractional_fczr x mode ret hret
  have hret0 := STAmount.ofNumber_nonneg .fractional x mode ret hx (Number.negative_false_of_nonneg x hx h0) hret
  have hret_int : ret.integral = false := by unfold STAmount.integral; rw [hretf.1]; rfl
  obtain ⟨rd, hrd⟩ : ∃ rd, STAmount.roundToExponent ret s mode = .ok rd := by
    rcases hretf.2 with hc' | hz
    · exact STAmount.roundToExponent_ok_any ret s mode hc' (STAmount.mIsNegative_false_of_nonneg ret hret0 (by
        intro h0; have := hc'.mant_lo; rw [h0] at this; exact absurd this (by decide))) hs.1 hs.2
    · exact ⟨ret, STAmount.roundToExponent_eq_self ret s _ (Or.inr (Or.inl (by simp [STAmount.isZero, hz])))⟩
  have hrdf := STAmount.roundToExponent_fczr ret rd s mode hretf hrd
  obtain ⟨y, hy, -, -⟩ := hrdf.toNumber_ok mode
  refine ⟨y, ?_⟩
  unfold STAmount.roundToNumericType
  rw [hret]
  simp only [hret_int, Bool.false_eq_true, ↓reduceIte]
  rw [hrd]
  exact hy

/-- A nonnegative `Number` that rounds into the asset's range rounds to an amount of the asset at a scale in
`[-96, 79]`. -/
private lemma STAmount.roundToNumericType_of_inRange (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (x : Number) (mode : rounding_mode)
    (s : Int) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hin : STAmount.RoundsInRange nt mode x.toRat)
    (hs : -96 ≤ s ∧ s ≤ 79) : ∃ y, STAmount.roundToNumericType nt x mode (some s) = .ok y := by
  rcases hnt with rfl | hnt
  · exact STAmount.roundToNumericType_frac_of_inRange x mode s hx h0 hin hs
  · exact STAmount.roundToNumericType_integral_of_inRange nt hnt x mode (some s) hx h0 hin

/-- The check that an amount the asset stores is whole at a scale computes. -/
private lemma isRounded_computes (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (x : Number) (s : Int)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hst : STAmount.isRounded nt x = false) (hs : -96 ≤ s ∧ s ≤ 79) :
    ∃ b, isRounded x s nt = .ok b := by
  have hrep := (STAmount.isRounded_eq_false_iff nt x hx h0).mp hst
  obtain ⟨down, hdown⟩ := STAmount.roundToNumericType_of_inRange nt hnt x .downward s hx h0
    (STAmount.roundsInRange_of_representable nt hnt .downward _ h0 hrep) hs
  obtain ⟨up, hup⟩ := STAmount.roundToNumericType_of_inRange nt hnt x .upward s hx h0
    (STAmount.roundsInRange_of_representable nt hnt .upward _ h0 hrep) hs
  refine ⟨down.operator_eq up, ?_⟩
  unfold isRounded
  rw [hdown, ok_bind, hup, ok_bind]
  rfl

/-- The precision check of a LoanSet computes when its check does on the principal and on each fee. -/
lemma checkPrecisionFields_computes (principal : Number) (fees : LoanFees) (f : Number → Except Error Bool)
    (hf : ∀ x ∈ principal :: fees.amountFields, ∃ b, f x = .ok b) :
    ∃ t, checkPrecisionFields principal fees f = .ok t := by
  obtain ⟨b0, h0⟩ := hf principal (by simp)
  obtain ⟨b1, h1⟩ := hf fees.originationFee (by simp [LoanFees.amountFields])
  obtain ⟨b2, h2⟩ := hf fees.serviceFee (by simp [LoanFees.amountFields])
  obtain ⟨b3, h3⟩ := hf fees.latePaymentFee (by simp [LoanFees.amountFields])
  obtain ⟨b4, h4⟩ := hf fees.closePaymentFee (by simp [LoanFees.amountFields])
  unfold checkPrecisionFields LoanFees.amountFields
  simp only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure, h0, h1, h2, h3, h4]
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> exact ⟨_, rfl⟩

/-- A nonnegative value rounded up to the asset at a scale is zero or at least one unit of the scale. -/
private lemma STAmount.roundToNumericType_upward_unit (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (x T : Number) (s : ℤ)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80) (hsi : nt.isIntegral = true → s = 0)
    (hok : STAmount.roundToNumericType nt x .upward (some s) = .ok T) :
    T.toRat = 0 ∨ (10 : ℚ) ^ s ≤ T.toRat := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hunits : ∀ k : ℕ, T.toRat = (k : ℚ) * 10 ^ s → T.toRat = 0 ∨ (10 : ℚ) ^ s ≤ T.toRat := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · left; rw [hk]; simp
    · right
      rw [hk]
      have : (1 : ℚ) ≤ k := by exact_mod_cast hkpos
      nlinarith
  rcases hnt with rfl | hnt

  · -- an IOU: the amount keeps its exponent or is rounded onto the scale
    unfold STAmount.roundToNumericType at hok
    cases hof : STAmount.ofNumber .fractional x .upward with
    | error e => rw [hof] at hok; exact absurd hok (by simp)
    | ok st =>
      rw [hof] at hok
      simp only at hok
      have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
      have hint : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
      rw [ite_eq_right (by rw [hint]; decide)] at hok
      cases hr : STAmount.roundToExponent st s .upward with
      | error e => rw [hr] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hr] at hok
        simp only at hok
        by_cases hst : st.mValue = 0
        · have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s .upward
            (Or.inr (Or.inl (by unfold STAmount.isZero; simp [hst]))) hr
          subst hrst
          rw [STAmount.toNumber_zero_fractional r .upward hint hst, Except.ok.injEq] at hok
          subst hok
          left; exact Number.toRat_zero
        · obtain ⟨hc, -, -, -, -⟩ :=
            STAmount.ofNumber_frac_stage x .upward st hx h0 (Or.inr (Or.inl rfl)) hof hst
          have hneg := Number.negative_false_of_nonneg x hx h0
          have hst0 : 0 ≤ st.toRat := STAmount.ofNumber_nonneg _ _ _ _ hx hneg hof
          have hsneg := STAmount.mIsNegative_false_of_nonneg st hst0 hst
          by_cases heq : s ≤ st.exponent
          · -- 15 digits or more at an exponent of at least the scale
            have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s .upward (Or.inr (Or.inr heq)) hr
            subst hrst
            obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r .upward hc
            rw [hsn, Except.ok.injEq] at hok
            subst hok
            right
            rw [hv, STAmount.toRat_of_nonneg r hsneg]
            have hm1 : (1 : ℚ) ≤ r.mValue.toNat := by
              have := hc.mant_lo
              have : 1 ≤ r.mValue.toNat := by omega
              exact_mod_cast this
            have hpe : (10 : ℚ) ^ s ≤ 10 ^ r.mOffset := zpow_le_zpow_right₀ (by norm_num) heq
            calc (10 : ℚ) ^ s = 1 * 10 ^ s := by ring
              _ ≤ r.mValue.toNat * 10 ^ r.mOffset := mul_le_mul hm1 hpe hp.le (by positivity)
          · push Not at heq
            obtain ⟨k, hrk, hrty, hrc, -, -, -⟩ :=
              STAmount.roundToExponent_nonneg_units st r s .upward hc hsneg heq hs.1 hs.2 hr
            have hT : T.toRat = r.toRat := by
              rcases hrc with hr0 | hrc
              · have hrint : r.integral = false := by unfold STAmount.integral; rw [hrty]; rfl
                rw [STAmount.toNumber_zero_fractional r .upward hrint hr0, Except.ok.injEq] at hok
                rw [← hok, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero r hr0]
              · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r .upward hrc
                rw [hsn, Except.ok.injEq] at hok
                rw [← hok, hv]
            exact hunits k (by rw [hT, hrk])

  · -- XRP or an MPT: a whole number of units
    have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
    obtain ⟨-, ⟨k, hk⟩, -, -⟩ :=
      STAmount.roundToNumericType_int_grid nt hint x T .upward (some s) hx h0 (Or.inr (Or.inl rfl)) hok
    exact hunits k (by rw [hk, hsi hint]; simp)

/-- The amortization guards and the sanity check of a LoanSet compute on values of the sizes a LoanSet computed. -/
lemma LoanProperties.checkGuards_computes (props : LoanProperties) (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (hsz : props.SetSizes nt)
    (principal : Number) (hp : principal.isNormalized) (hpabs : |principal.toRat| < 10 ^ 200)
    (ir : TenthBips32) (n : UInt32) : ∃ t, props.checkGuards principal ir n nt = .ok t := by
  obtain ⟨k, hk63, hk⟩ := hsz.totalValue_units
  obtain ⟨hlslo, hlshi⟩ := hsz.loanScale_range
  have htvoN := hsz.totalValue_norm
  have htvo0 := hsz.totalValue_nonneg
  have hppN := hsz.periodicPayment_norm
  have hpp0 := hsz.periodicPayment_nonneg
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  have hp10le : (10 : ℚ) ^ props.loanScale ≤ 10 ^ 30 := by
    have := zpow_le_zpow_right₀ (show (1 : ℚ) ≤ 10 by norm_num) hlshi
    norm_num at this ⊢
    exact this
  have hkq : (k : ℚ) ≤ 2 ^ 63 - 1 := by
    have h1 : k + 1 ≤ 2 ^ 63 := hk63
    have h2 : (k : ℚ) + 1 ≤ 2 ^ 63 := by exact_mod_cast h1
    linarith
  have htvoabs : |props.totalValueOutstanding.toRat| < 10 ^ 200 := by
    rw [abs_of_nonneg htvo0, hk]
    calc (k : ℚ) * 10 ^ props.loanScale ≤ (2 ^ 63 - 1) * 10 ^ 30 := by gcongr
      _ < 10 ^ 200 := by norm_num

  -- the interest and the rounded payment
  obtain ⟨ti, hti⟩ := Number.operator_sub_ok_of_abs props.totalValueOutstanding principal .to_nearest htvoN hp
    htvoabs hpabs
  have hppin : STAmount.RoundsInRange nt .upward props.periodicPayment.toRat := by
    rcases hnt with rfl | hnt'
    · simp only [STAmount.RoundsInRange]
      have := hsz.periodicPayment_lt
      exact ⟨by linarith, by linarith [show (10 : ℚ) ^ 36 ≤ 9999999999999999 * 10 ^ 80 by norm_num]⟩
    · exact STAmount.roundsInRange_of_le_max nt hnt' .upward _ hpp0
        (hsz.periodicPayment_max (by rcases hnt' with rfl | rfl <;> rfl))
  obtain ⟨rp, hrp⟩ := STAmount.roundToNumericType_of_inRange nt hnt props.periodicPayment .upward props.loanScale
    hppN hpp0 hppin ⟨by omega, by omega⟩
  have hrpN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hrp
  have hrp0 := STAmount.roundToNumericType_some_nonneg nt _ rp .upward props.loanScale hppN hpp0
    (Or.inr (Or.inl rfl)) ⟨by omega, by omega⟩ hrp

  -- the amortization guards
  obtain ⟨g, hg⟩ : ∃ g, props.amortizationGuards principal (ir != 0) n nt = .ok g := by
    cases hz : rp.operator_eq Number.zero with
    | true =>
      unfold LoanProperties.amortizationGuards
      simp only [bind, Except.bind, pure, Except.pure, hti, hrp, hz]
      split_ifs <;> exact ⟨_, rfl⟩
    | false =>
      -- a payment that is not zero is at least one unit, so the payment count is below `2^63`
      have hrpne : rp.toRat ≠ 0 := fun h0' => by
        have := (Number.operator_eq_iff rp Number.zero hrpN Number.zero_isNormalized).mpr (by
          rw [h0', Number.toRat_zero])
        rw [hz] at this; cases this
      have hunit : (10 : ℚ) ^ props.loanScale ≤ rp.toRat :=
        (STAmount.roundToNumericType_upward_unit nt hnt _ rp props.loanScale hppN hpp0 ⟨by omega, by omega⟩
          hsz.loanScale_integral hrp).resolve_left hrpne
      have hrppos : 0 < rp.toRat := lt_of_lt_of_le hp10 hunit
      obtain ⟨ratio, hratio⟩ := Number.operator_div_ok_of_abs props.totalValueOutstanding rp .upward htvoN hrpN
        htvoabs (by
          rw [abs_of_nonneg hrp0]
          refine le_trans ?_ hunit
          exact zpow_le_zpow_right₀ (by norm_num) (by omega))
      have hratioN := Number.operator_div_isNormalized _ _ ratio _ htvoN hrpN hratio
      have hq0 : 0 ≤ props.totalValueOutstanding.toRat / rp.toRat := div_nonneg htvo0 hrp0
      have hqle : props.totalValueOutstanding.toRat / rp.toRat ≤ 2 ^ 63 - 1 := by
        rw [div_le_iff₀ hrppos, hk]
        calc (k : ℚ) * 10 ^ props.loanScale ≤ (2 ^ 63 - 1) * 10 ^ props.loanScale := by gcongr
          _ ≤ (2 ^ 63 - 1) * rp.toRat := by gcongr
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (2 ^ 63 - 1) 0 (by norm_num)
        (by unfold minExponent maxExponent; norm_num)
      have hwv' : w.toRat = 2 ^ 63 - 1 := by rw [hwv]; norm_num
      have hratio0 : 0 ≤ ratio.toRat ∧ ratio.toRat ≤ 2 ^ 63 - 1 := by
        by_cases hm : ratio.mantissa_ = 0
        · rw [Number.toRat_eq_zero_of_mantissa_zero _ hm]; norm_num
        · have hR := Number.operator_div_rounded_upward _ _ _ htvoN hrpN hratio hm
          refine ⟨?_, ?_⟩
          · have := hR.ge_of_le (Or.inr (Or.inl rfl)) Number.zero Number.zero_isNormalized (by
              rw [Number.toRat_zero]; exact hq0)
            rwa [Number.toRat_zero] at this
          · have := hR.le_of_ge (Or.inr (Or.inl rfl)) w hw (by rw [hwv']; exact hqle)
            rwa [hwv'] at this
      have hneg := Number.negative_false_of_nonneg ratio hratioN hratio0.1
      obtain ⟨c, hc⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos ratio .upward hneg
        (Number.exponent_le_zero_of_cap ratio hratioN hneg hratio0.2)
      unfold LoanProperties.amortizationGuards
      simp only [bind, Except.bind, pure, Except.pure, hti, hrp, hz, hratio, hc]
      split_ifs <;> exact ⟨_, rfl⟩

  unfold LoanProperties.checkGuards
  simp only [bind, Except.bind, pure, Except.pure, hg]
  split_ifs <;> exact ⟨_, rfl⟩

/-- The state of a new loan computes from values below `10^100` in size. Its interest is below `10^102` in size. -/
private lemma LoanState.build_computes (tvo principal mfo : Number) (htN : tvo.isNormalized)
    (hpN : principal.isNormalized) (hmN : mfo.isNormalized) (ht : |tvo.toRat| < 10 ^ 100)
    (hp : |principal.toRat| < 10 ^ 100) (hm : |mfo.toRat| < 10 ^ 100) :
    ∃ st, LoanState.build tvo principal mfo = .ok st ∧ st.interestDue.isNormalized ∧
      |st.interestDue.toRat| < 10 ^ 102 := by
  have he := Number.nearestError_pos
  have he' := Number.nearestError_le
  have h200 : (10 : ℚ) ^ 100 < 10 ^ 200 := by norm_num
  obtain ⟨v1, hv1⟩ := Number.operator_sub_ok_of_abs tvo principal .to_nearest htN hpN (by linarith) (by linarith)
  have hv1N := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ htN hpN hv1
  have hv1abs : |v1.toRat| ≤ 4 * 10 ^ 100 := by
    refine le_trans (Number.sub_near _ _ _ htN hpN hv1).abs_le ?_
    have h1 : |tvo.toRat - principal.toRat| ≤ |tvo.toRat| + |principal.toRat| := abs_sub _ _
    calc |tvo.toRat - principal.toRat| * (1 + ε) ≤ (10 ^ 100 + 10 ^ 100) * 2 := by gcongr <;> linarith
      _ = 4 * 10 ^ 100 := by ring
  obtain ⟨id, hid⟩ := Number.operator_sub_ok_of_abs v1 mfo .to_nearest hv1N hmN
    (by linarith [show (4 : ℚ) * 10 ^ 100 < 10 ^ 200 by norm_num]) (by linarith)
  have hidN := Number.operator_sub_isNormalized_to_nearest_sz _ _ _ hv1N hmN hid
  have hidabs : |id.toRat| < 10 ^ 102 := by
    refine lt_of_le_of_lt (Number.sub_near _ _ _ hv1N hmN hid).abs_le ?_
    have h1 : |v1.toRat - mfo.toRat| ≤ |v1.toRat| + |mfo.toRat| := abs_sub _ _
    calc |v1.toRat - mfo.toRat| * (1 + ε) ≤ (4 * 10 ^ 100 + 10 ^ 100) * 2 := by gcongr <;> linarith
      _ < 10 ^ 102 := by norm_num
  refine ⟨{ valueOutstanding := tvo, principalOutstanding := principal, interestDue := id,
            managementFeeDue := mfo }, ?_, hidN, hidabs⟩
  unfold LoanState.build
  rw [hv1, ok_bind, hid, ok_bind]
  rfl

/-- The Open-limit check computes for an amount below `10^190` in size, on a vault whose balances are below
`10^100`. -/
private lemma Vault.exceedsOpenLimit_computes (v : Vault) (x : Number) (hx : x.isNormalized)
    (hxabs : |x.toRat| < 10 ^ 190)
    (hbal : v.assetsAvailable.toRat + v.assetsDeployed.toRat + v.yieldUnrealized.toRat < 10 ^ 100) :
    ∃ b, v.exceedsOpenLimit x = .ok b := by
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hYN := v.wf.yieldUnrealized_norm
  have h200 : (10 : ℚ) ^ 100 < 10 ^ 200 := by norm_num

  -- the vault total
  obtain ⟨atot, hat⟩ : ∃ atot, v.assetsTotal = .ok atot :=
    Number.operator_add_ok_of_abs _ _ .downward v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm
      (by rw [abs_of_nonneg hAA0]; linarith) (by rw [abs_of_nonneg hAD0]; linarith)
  obtain ⟨hatN, hatge⟩ := Vault.assetsTotal_ge_available v atot hat
  have hat0 : 0 ≤ atot.toRat := le_trans hAA0 hatge
  have hatle : atot.toRat ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat :=
    Vault.assetsTotal_le_exact v atot hat

  -- with the yield
  obtain ⟨s₁, hs₁⟩ := Number.operator_add_ok_of_abs atot v.yieldUnrealized .towards_zero hatN hYN
    (by rw [abs_of_nonneg hat0]; linarith) (by rw [abs_of_nonneg hY0]; linarith)
  obtain ⟨n₁, hlo₁, hs₁v⟩ := Number.operator_add_rounded_towards_zero _ _ _ hatN hYN hs₁
  rw [ite_eq_left (by linarith)] at hlo₁
  have hs₁ge : atot.toRat ≤ s₁.toRat := by
    rw [hs₁v]; exact Number.lower_tight _ n₁ hlo₁ atot hatN (by linarith)
  have hs₁le : s₁.toRat ≤ atot.toRat + v.yieldUnrealized.toRat := by
    rw [hs₁v]; exact Number.lower_le _ n₁ hlo₁
  have hYge : v.yieldUnrealized.toRat ≤ s₁.toRat := by
    rw [hs₁v]; exact Number.lower_tight _ n₁ hlo₁ _ hYN (by linarith)
  have hs₁N : s₁.isNormalized := by
    by_cases hY : v.yieldUnrealized.mantissa_ = 0
    · rw [Number.eq_zero_of_mantissa_zero _ hYN hY, Number.operator_add_zero_right, Except.ok.injEq] at hs₁
      rw [← hs₁]; exact hatN
    · have hYpos : 0 < v.yieldUnrealized.toRat :=
        lt_of_le_of_ne hY0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hY))
      exact Number.operator_add_isNormalized _ _ _ .towards_zero hatN hYN hs₁ (fun h0 => by
        have := Number.toRat_eq_zero_of_mantissa_zero s₁ h0; linarith)

  -- with the amount, against the limit
  obtain ⟨capacity, hcap⟩ := Number.operator_add_ok_of_abs s₁ x .towards_zero hs₁N hx
    (by rw [abs_of_nonneg (le_trans hat0 hs₁ge)]; linarith)
    (by linarith [show (10 : ℚ) ^ 190 < 10 ^ 200 by norm_num])
  obtain ⟨limit, hlim, -, -⟩ := Vault.openLimit_value v
  refine ⟨capacity.operator_gt limit, ?_⟩
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit
  rw [hat, ok_bind, hs₁, ok_bind, hcap, ok_bind, hlim, ok_bind]
  rfl

/-- The minimum cover of a debt from zero up to `K` computes, when the asset stores every amount up to `K`. -/
private lemma minimumBrokerCover_computes (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (d : Number)
    (rate : TenthBips32) (e : Int) (K : ℕ) (hK : K < 2 ^ 63) (hd : d.isNormalized) (hd0 : 0 ≤ d.toRat)
    (hdK : d.toRat ≤ K) (hrate : rate.toNat ≤ 100000)
    (hfit : ∀ v : ℚ, 0 ≤ v → v ≤ K → STAmount.RoundsInRange nt .upward v) (he : -96 ≤ e ∧ e ≤ 79) :
    ∃ m, minimumBrokerCover nt d rate e = .ok m := by
  obtain ⟨hrN, hrv⟩ := TenthBips32.toNumber_facts rate .upward
  obtain ⟨huN, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity .upward
  have hu : (kTenthBipsPerUnity.toNat : ℚ) = 100000 := by decide
  rw [hu] at huv
  have hrq : (rate.toNat : ℚ) ≤ 100000 := by exact_mod_cast hrate
  have hr0 : (0 : ℚ) ≤ rate.toNat := by positivity
  have hKq : (K : ℚ) < 2 ^ 63 := by exact_mod_cast hK
  have hK0 : (0 : ℚ) ≤ K := by positivity
  have hKint : -2 ^ 63 < (K : ℤ) ∧ (K : ℤ) < 2 ^ 63 := by
    refine ⟨?_, by exact_mod_cast hK⟩
    have : (0 : ℤ) ≤ (K : ℤ) := by positivity
    linarith
  obtain ⟨w1, hw1, hw1v⟩ := Number.exists_normalized_int_mul_pow (K : ℤ) 5 hKint
    (by unfold minExponent maxExponent; norm_num)
  obtain ⟨w2, hw2, hw2v⟩ := Number.exists_normalized_int_mul_pow (K : ℤ) 0 hKint
    (by unfold minExponent maxExponent; norm_num)
  have hw1v' : w1.toRat = (K : ℚ) * 100000 := by rw [hw1v]; norm_num
  have hw2v' : w2.toRat = (K : ℚ) := by rw [hw2v]; simp

  -- the debt times the rate, rounded up
  obtain ⟨p, hp⟩ := Number.operator_mul_ok_of_abs d (rate.toNumber .upward) .upward hd hrN
    (by rw [abs_of_nonneg hd0]; linarith [show (2 : ℚ) ^ 63 < 10 ^ 200 by norm_num])
    (by rw [hrv, abs_of_nonneg hr0]; linarith [show (100000 : ℚ) < 10 ^ 200 by norm_num])
  have hpN := Number.operator_mul_isNormalized _ _ p _ hd hrN hp
  have hp0 : 0 ≤ p.toRat ∧ p.toRat ≤ K * 100000 := by
    by_cases hm : p.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ hm]; exact ⟨le_rfl, by positivity⟩
    · have hR := Number.operator_mul_rounded_upward _ _ _ hd hrN hp hm
      rw [hrv] at hR
      refine ⟨?_, ?_⟩
      · have := hR.ge_of_le (Or.inr (Or.inl rfl)) Number.zero Number.zero_isNormalized (by
          rw [Number.toRat_zero]; positivity)
        rwa [Number.toRat_zero] at this
      · have := hR.le_of_ge (Or.inr (Or.inl rfl)) w1 hw1 (by rw [hw1v']; exact mul_le_mul hdK hrq hr0 hK0)
        rwa [hw1v'] at this

  -- over the unity, rounded up
  obtain ⟨m0, hm0⟩ := Number.operator_div_ok_of_abs p (kTenthBipsPerUnity.toNumber .upward) .upward hpN huN
    (by rw [abs_of_nonneg hp0.1]; linarith [show (2 : ℚ) ^ 63 * 100000 < 10 ^ 200 by norm_num])
    (by
      rw [huv, abs_of_nonneg (by norm_num)]
      refine le_trans ?_ (show (1 : ℚ) ≤ 100000 by norm_num)
      rw [zpow_neg]; norm_num)
  have hm0N := Number.operator_div_isNormalized _ _ m0 _ hpN huN hm0
  have hm00 : 0 ≤ m0.toRat ∧ m0.toRat ≤ K := by
    by_cases hm : m0.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ hm]; exact ⟨le_rfl, hK0⟩
    · have hR := Number.operator_div_rounded_upward _ _ _ hpN huN hm0 hm
      rw [huv] at hR
      refine ⟨?_, ?_⟩
      · have := hR.ge_of_le (Or.inr (Or.inl rfl)) Number.zero Number.zero_isNormalized (by
          rw [Number.toRat_zero]; exact div_nonneg hp0.1 (by norm_num))
        rwa [Number.toRat_zero] at this
      · have := hR.le_of_ge (Or.inr (Or.inl rfl)) w2 hw2 (by
          rw [hw2v', div_le_iff₀ (by norm_num)]; exact hp0.2)
        rwa [hw2v'] at this

  -- as an amount of the asset, rounded up
  obtain ⟨m, hm⟩ := STAmount.roundToNumericType_of_inRange nt hnt m0 .upward e hm0N hm00.1
    (hfit _ hm00.1 hm00.2) he
  refine ⟨m, ?_⟩
  have heq : minimumBrokerCover nt d rate e =
      ((d.operator_mul (rate.toNumber .upward) .upward) >>=
        (fun q => q.operator_div (kTenthBipsPerUnity.toNumber .upward) .upward)) >>=
          (fun mc => STAmount.roundToNumericType nt mc .upward (some e)) := rfl
  rw [heq, hp, ok_bind, hm0, ok_bind, hm]

/-- The limits check of a LoanSet computes for a new DebtTotal from zero up to `K`, when the asset stores every
amount up to `K`. -/
lemma LoanBroker.checkLimits_computes (broker : LoanBroker)
    (hnt : broker.numericType = .fractional ∨ broker.numericType = NumericType.native ∨
      broker.numericType = NumericType.int64)
    (d : Number) (e : Int) (K : ℕ) (hK : K < 2 ^ 63) (hd : d.isNormalized) (hd0 : 0 ≤ d.toRat) (hdK : d.toRat ≤ K)
    (hfit : ∀ v : ℚ, 0 ≤ v → v ≤ K → STAmount.RoundsInRange broker.numericType .upward v)
    (he : -96 ≤ e ∧ e ≤ 79) : ∃ t, broker.checkLimits d e = .ok t := by
  have hrate : broker.coverRateMinimum.toNat ≤ 100000 := by
    have := broker.valid.coverRateMinimum_cap
    exact UInt32.le_iff_toNat_le.mp this
  obtain ⟨m, hm⟩ := minimumBrokerCover_computes broker.numericType hnt d broker.coverRateMinimum e K hK hd hd0 hdK
    hrate hfit he
  unfold LoanBroker.checkLimits RawLoanBroker.hasMinimumCover
  simp only [bind, Except.bind, pure, Except.pure, hm]
  split_ifs <;> exact ⟨_, rfl⟩

end XRPL.Model.Lending
