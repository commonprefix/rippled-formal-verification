import XRPL.Properties.Lending.Loan.Common.SetVault

/-! # A create whose checks pass succeeds

When the LoanSet preflight, preclaim and every check of `Loan.create` pass, the vault update succeeds and
the new loan, broker and vault pass their re-checks. The only rejections are the checks themselves. -/

namespace XRPL.Model.Protocol

/-- A nonnegative IOU amount whose STAmount exponent is at most `s` rounds at `s` to fewer than `10^16` units. -/
lemma STAmount.roundToNumericType_frac_le (x T : Number) (mode : rounding_mode) (s : ℤ)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) (hs : -81 ≤ s ∧ s ≤ 80)
    (hexp : ∀ st, STAmount.ofNumber .fractional x mode = .ok st → st.mValue ≠ 0 → st.exponent ≤ s)
    (hok : STAmount.roundToNumericType .fractional x mode (some s) = .ok T) :
    T.toRat ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ s := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber .fractional x mode with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
    have hint : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
    rw [if_neg (by rw [hint]; decide)] at hok
    cases hr : STAmount.roundToExponent st s mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only at hok
      by_cases hst : st.mValue = 0
      · have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s mode
          (Or.inr (Or.inl (by unfold STAmount.isZero; simp [hst]))) hr
        subst hrst
        rw [STAmount.toNumber_zero_fractional r mode hint hst, Except.ok.injEq] at hok
        rw [← hok, Number.toRat_zero]; positivity
      have hc := (STAmount.ofNumber_frac_stage x mode st hx h0 hmode hof hst).1
      have hst0 : 0 ≤ st.toRat :=
        STAmount.ofNumber_nonneg _ _ _ _ hx (Number.negative_false_of_nonneg x hx h0) hof
      have hsneg := STAmount.mIsNegative_false_of_nonneg st hst0 hst
      have hes : st.exponent ≤ s := hexp st hof hst
      have hstle : st.toRat ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ s := by
        rw [STAmount.toRat_of_nonneg st hsneg]
        calc (st.mValue.toNat : ℚ) * 10 ^ st.mOffset ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ st.mOffset :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast (by have := hc.mant_hi; omega)) (by positivity)
          _ ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ s :=
              mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hes) (by positivity)
      by_cases heq : s ≤ st.exponent
      · have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s mode (Or.inr (Or.inr heq)) hr
        subst hrst
        obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hc
        rw [hsn, Except.ok.injEq] at hok
        rw [← hok, hv]; exact hstle
      · push Not at heq
        obtain ⟨k, hrk, hrty, hrc, htn, hdn, hupk⟩ :=
          STAmount.roundToExponent_nonneg_units st r s mode hc hsneg heq hs.1 hs.2 hr
        have hT : T.toRat = r.toRat := by
          rcases hrc with hr0 | hrc
          · have hrint : r.integral = false := by unfold STAmount.integral; rw [hrty]; rfl
            rw [STAmount.toNumber_zero_fractional r mode hrint hr0, Except.ok.injEq] at hok
            rw [← hok, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero r hr0]
          · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hrc
            rw [hsn, Except.ok.injEq] at hok
            rw [← hok, hv]
        -- the ceiling of the amount is at most `10^16 - 1` units
        have hkc : (k : ℤ) ≤ ⌈st.toRat / 10 ^ s⌉ := by
          rcases hmode with rfl | rfl | rfl
          · rcases htn rfl with h | h
            · rw [h]; exact Int.floor_le_ceil _
            · rw [h]
          · rw [hupk rfl]
          · rw [hdn rfl]; exact Int.floor_le_ceil _
        have hcle : ⌈st.toRat / 10 ^ s⌉ ≤ ((10 ^ 16 - 1 : ℕ) : ℤ) :=
          Int.ceil_le.mpr (by rw [div_le_iff₀ hp]; exact_mod_cast hstle)
        rw [hT, hrk]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkc.trans hcle) hp.le

/-- An integral amount fits its type. Rounding to an integral type gives at most the type's
largest value and at most `2^63 - 1`. -/
lemma STAmount.roundToNumericType_int_lt_bound (nt : NumericType) (hnt : nt.isIntegral = true) (x T : Number)
    (mode : rounding_mode) (s : Option ℤ) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hok : STAmount.roundToNumericType nt x mode s = .ok T) : T.toRat < nt.mantissaBound := by
  have hneg := Number.negative_false_of_nonneg x hx h0
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x mode with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
    have hint : st.integral = true := by unfold STAmount.integral; rw [hty]; exact hnt
    have hT : st.toNumber mode = .ok T := by
      cases s with
      | none => exact hok
      | some s => simp only [hint, if_true] at hok; exact hok
    have hic := (STAmount.ofNumber_integral_canonical nt x mode st hnt hof).1
    have hsz : st.mValue.toNat ≤ 2 ^ 63 - 1 := by
      by_cases hz : st.mValue = 0
      · rw [hz]; decide
      · exact ((STAmount.ofNumber_exactCanonical nt x mode st hx h0 hof hz).integralCanonical hint).2
    obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact st mode hic hsz
    rw [hsn, Except.ok.injEq] at hT
    subst hT
    have hst0 : 0 ≤ st.toRat := STAmount.ofNumber_nonneg _ _ _ _ hx hneg hof
    rw [hv]
    have hval := STAmount.IntegralCanonical.toRat_eq_signedDrops st hic
    have habs := STAmount.abs_toRat st
    rw [abs_of_nonneg hst0, hic.offset_zero, zpow_zero, mul_one] at habs
    rw [habs]
    have hin := hic.in_range
    rw [hty] at hin
    cases nt with
    | fractional => exact absurd hnt (by decide)
    | integral mv mo ms msh =>
      show (st.mValue.toNat : ℚ) < ((min mv.toNat maxRep.toNat + 1 : ℕ) : ℚ)
      have hmr : maxRep.toNat = 9223372036854775807 := by decide
      have : st.mValue.toNat < min mv.toNat maxRep.toNat + 1 := by
        have : st.mValue.toNat ≤ mv.toNat := hin
        omega
      exact_mod_cast this

/-- An amount the asset stores exactly rounds back without error. -/
lemma STAmount.roundToNumericType_ok_of_isRounded_false (nt : NumericType) (x : Number)
    (h : STAmount.isRounded nt x = false) :
    ∃ y, STAmount.roundToNumericType nt x .to_nearest = .ok y := by
  unfold STAmount.isRounded at h
  cases hconv : STAmount.equalAfterNumberConvert nt x with
  | error e => rw [hconv] at h; exact absurd h (by simp)
  | ok b =>
    unfold STAmount.equalAfterNumberConvert at hconv
    obtain ⟨st, hst, hconv⟩ := bind_ok_peel _ _ _ hconv
    obtain ⟨n, hnum, -⟩ := bind_ok_peel _ _ _ hconv
    refine ⟨n, ?_⟩
    unfold STAmount.roundToNumericType
    rw [hst]
    exact hnum

/-- A `Number` and its negation have the same exponent field when nonzero. -/
lemma Number.operator_neg_exponent (n : Number) (h : n.mantissa_ ≠ 0) : n.operator_neg.exponent_ = n.exponent_ := by
  unfold Number.operator_neg
  rw [if_neg (by simpa using h)]

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The terms pass the LoanSet preflight and preclaim: PrincipalRequested is positive and an amount the
asset stores, the fees are nonnegative and the rates at most 100%, and the schedule fits. -/
structure Loan.CreatePreflight (broker : LoanBroker) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) : Prop where
  principal_norm : principal.isNormalized
  principal_pos : 0 < principal.toRat
  principal_exact : STAmount.isRounded broker.numericType principal = false
  fees_norm : ∀ fee ∈ fees.amountFields, fee.isNormalized
  fees_nonneg : ∀ fee ∈ fees.amountFields, 0 ≤ fee.toRat
  interestRate_cap : rates.interestRate ≤ maxLoanRate
  lateInterestRate_cap : rates.lateInterestRate ≤ maxLoanRate
  closeInterestRate_cap : rates.closeInterestRate ≤ maxLoanRate
  overpaymentInterestRate_cap : rates.overpaymentInterestRate ≤ maxLoanRate
  overpaymentFee_cap : rates.overpaymentFee ≤ maxLoanRate
  paymentInterval_min : minPaymentInterval ≤ schedule.paymentInterval
  gracePeriod_range : defaultGracePeriod ≤ schedule.gracePeriod ∧ schedule.gracePeriod ≤ schedule.paymentInterval
  fits : schedule.Fits

/-- An IOU, XRP or an MPT stores every whole number below `10^16`. -/
lemma Vault.HoldsAsset.mantissaBound {v : Vault} (h : Vault.HoldsAsset v) :
    10 ^ 16 ≤ v.numericType.mantissaBound := by
  rcases h with h | h | h <;> rw [h] <;> decide

/-- A whole number of base units below `10^16` is an amount the vault's asset stores. -/
lemma Vault.HoldsAsset.isRounded_units {v : Vault} (h : Vault.HoldsAsset v) (x : Number) (k : ℕ)
    (hx : x.isNormalized) (hk : k < 10 ^ 16) (hv : x.toRat = (k : ℚ) * 10 ^ v.baseExponent) :
    STAmount.isRounded v.numericType x = false := by
  have hbase := Vault.baseExponent_scale_range v
  have hx0 : 0 ≤ x.toRat := by rw [hv]; positivity
  rw [STAmount.isRounded_eq_false_iff _ x hx hx0, hv]
  rcases h with h | h | h
  · rw [h]; exact STAmount.representable_fractional_of_units k _ hk (by omega) (by omega)
  · have hb0 : v.baseExponent = 0 := Vault.baseExponent_integral v (by rw [h]; rfl)
    rw [h, hb0, zpow_zero, mul_one]
    have hmv : (100000000000000000 : UInt64).toNat = 100000000000000000 := by decide
    exact Or.inr ⟨by decide, k, by show k ≤ (100000000000000000 : UInt64).toNat; rw [hmv]; omega,
      by omega, rfl⟩
  · have hb0 : v.baseExponent = 0 := Vault.baseExponent_integral v (by rw [h]; rfl)
    rw [h, hb0, zpow_zero, mul_one]
    have hmv : (9223372036854775807 : UInt64).toNat = 9223372036854775807 := by decide
    exact Or.inr ⟨by decide, k, by show k ≤ (9223372036854775807 : UInt64).toNat; rw [hmv]; omega,
      by omega, rfl⟩

/-- What the checks of a create fix about the new loan. In LoanScale units: PrincipalRequested `j ≥ 1`,
the total value `aT ≥ j` in range, the stored principal `j`, the fee `mm ≤ aT - j`, the interest the rest. -/
private lemma Loan.create_checks_facts (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (props : LoanProperties) (loanState : LoanState)
    (debtTotal' : Number) (hpre : Loan.CreatePreflight broker principal rates fees schedule)
    (hgrid : Loan.CreateGrid broker v)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal') :
    ∃ j aT mm : ℕ,
      -10 ≤ props.loanScale ∧ props.loanScale ≤ 80 ∧ v.baseExponent ≤ props.loanScale ∧
      (broker.numericType.isIntegral = true → props.loanScale = 0) ∧
      principal.toRat = (j : ℚ) * 10 ^ props.loanScale ∧ 1 ≤ j ∧ j ≤ aT ∧ j < 10 ^ 16 ∧
      props.totalValueOutstanding.isNormalized ∧
      props.totalValueOutstanding.toRat = (aT : ℚ) * 10 ^ props.loanScale ∧
      aT < broker.numericType.mantissaBound ∧
      props.principalOutstanding.isNormalized ∧ props.principalOutstanding.toRat = principal.toRat ∧
      props.managementFeeOutstanding.isNormalized ∧
      props.managementFeeOutstanding.toRat = (mm : ℚ) * 10 ^ props.loanScale ∧ mm ≤ aT - j ∧
      props.periodicPayment.isNormalized ∧ 0 < props.periodicPayment.toRat ∧
      loanState.interestDue.isNormalized ∧
      loanState.interestDue.toRat = (((aT - j - mm : ℕ) : ℤ) : ℚ) * 10 ^ props.loanScale := by
  have hp := hpre.principal_norm
  have hpos := hpre.principal_pos
  have hst := hpre.principal_exact
  obtain ⟨rate, amount, amountSt, ti, hrt, hpp, hamt, hst', hls, htvo, hpo, hti, hmfo⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hchecks.properties_ok
  have hbase := Vault.baseExponent_scale_range v
  obtain ⟨hlsmin, hls0⟩ := computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hchecks.properties_ok hbase.2
  obtain ⟨ti', hsub, hgt0, hle0, -, hmf0, htv0, hpp0⟩ := LoanProperties.checkGuards_ok_inv _ _ _ _ _ hchecks.guards
  have hrN := loanPeriodicRate_isNormalized _ _ rate hrt
  have hppN := loanPeriodicPayment_isNormalized _ _ _ _ hp hrN hpp
  have hN := Number.ofInt64_isNormalized schedule.paymentTotal.toUInt64.toInt64
  have hNv := Number.ofInt64_count schedule.paymentTotal
  have hamtN := Number.operator_mul_isNormalized _ _ amount _ hppN hN hamt
  have htvN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ htvo
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  have hmfN : props.managementFeeOutstanding.isNormalized := by
    have heq : computeManagementFee broker.numericType ti broker.managementFeeRate props.loanScale =
        (tenthBipsOfValue ti broker.managementFeeRate.toTenthBips32 .to_nearest) >>=
          (fun raw => STAmount.roundToNumericType broker.numericType raw .downward (some props.loanScale)) := rfl
    rw [heq] at hmfo
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ hmfo
    exact STAmount.roundToNumericType_isNormalized _ _ _ _ _ h
  have hpp0' : 0 < props.periodicPayment.toRat := (Number.signum_pos_iff_toRat hppN).mp hpp0
  have htv0' : 0 < props.totalValueOutstanding.toRat := (Number.signum_pos_iff_toRat htvN).mp htv0
  have hmode : valueMode rate = .to_nearest ∨ valueMode rate = .upward ∨ valueMode rate = .downward :=
    (valueMode_cases rate).elim Or.inl (fun h => Or.inr (Or.inl h))
  have hamt0 : 0 ≤ amount.toRat := by
    by_cases h0 : amount.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0]
    · have hR := operator_mul_rounded_valueMode rate _ _ amount hppN hN hamt h0
      have := hR.ge_of_le hmode Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero, hNv]; positivity)
      rwa [Number.toRat_zero] at this
  have hls80 : props.loanScale ≤ 80 := by
    rw [hls]
    refine max_le (le_trans hbase.2 (by norm_num)) ?_
    cases hnt' : broker.numericType with
    | integral mv mo ms msh =>
      rw [hnt'] at hst'
      have := (STAmount.ofNumber_integral_canonical _ _ _ amountSt rfl hst').1.offset_zero
      show amountSt.mOffset ≤ 80; omega
    | fractional =>
      rw [hnt'] at hst'
      by_cases hz : amountSt.mValue = 0
      · -- a zero amount would leave a zero total value
        rw [hnt'] at htvo
        rw [STAmount.roundToNumericType_frac_of_zero _ _ _ _ _ hst' hz htvo] at htv0'
        exact absurd htv0' (lt_irrefl _)
      · exact (STAmount.ofNumber_frac_stage amount _ amountSt hamtN hamt0 hmode hst' hz).1.exp_hi
  have hlo : -10 ≤ props.loanScale := le_trans hbase.1 hlsmin
  have hs : minExponent + 18 ≤ props.loanScale ∧ props.loanScale ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  -- PrincipalRequested is `j ≥ 1` LoanScale units, no more than AssetsAvailable
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal props.loanScale hp hpos.le hst
    ⟨by omega, hls80⟩ hls0 (hchecks.exact principal List.mem_cons_self)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0] at hj; simp at hj; linarith
    · exact h0
  have hfunds : principal.toRat ≤ v.assetsAvailable.toRat := by
    have h1 := hchecks.funds
    by_contra hc'
    push Not at hc'
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hc'] at h1
    exact absurd h1 (by decide)
  obtain ⟨a, ha, hav⟩ := hgrid.assetsAvailable
  have hj16 : j < 10 ^ 16 := by
    have h1 : (j : ℚ) * 10 ^ props.loanScale < (10 ^ 16 : ℕ) * 10 ^ props.loanScale := by
      calc (j : ℚ) * 10 ^ props.loanScale = principal.toRat := hj.symm
        _ ≤ v.assetsAvailable.toRat := hfunds
        _ = (a : ℚ) * 10 ^ v.baseExponent := hav
        _ < (10 ^ 16 : ℕ) * 10 ^ v.baseExponent :=
            mul_lt_mul_of_pos_right (by exact_mod_cast ha) (zpow_pos (by norm_num) _)
        _ ≤ (10 ^ 16 : ℕ) * 10 ^ props.loanScale :=
            mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hlsmin) (by positivity)
    exact_mod_cast lt_of_mul_lt_mul_right h1 hp10.le
  obtain ⟨aT, haTv, haT⟩ : ∃ aT : ℕ, props.totalValueOutstanding.toRat = (aT : ℚ) * 10 ^ props.loanScale ∧
      aT < broker.numericType.mantissaBound := by
    cases hnt' : broker.numericType with
    | fractional =>
      rw [hnt'] at htvo hst'
      have hexp : ∀ st, STAmount.ofNumber .fractional amount (valueMode rate) = .ok st → st.mValue ≠ 0 →
          st.exponent ≤ props.loanScale := fun st hst2 _ => by
        rw [hst', Except.ok.injEq] at hst2
        rw [← hst2, hls]; exact le_max_right _ _
      obtain ⟨-, ⟨k, hk⟩, -, -⟩ := STAmount.roundToNumericType_frac_grid amount _ _ props.loanScale hamtN hamt0
        hmode ⟨by omega, hls80⟩ hexp htvo
      have hle := STAmount.roundToNumericType_frac_le amount _ _ props.loanScale hamtN hamt0 hmode
        ⟨by omega, hls80⟩ hexp htvo
      refine ⟨k, hk, ?_⟩
      rw [hk] at hle
      have : k ≤ 10 ^ 16 - 1 := by exact_mod_cast le_of_mul_le_mul_right hle hp10
      show k < 10 ^ 16
      omega
    | integral mv mo ms msh =>
      rw [hnt'] at htvo
      have hls00 := hls0 (by rw [hnt']; rfl)
      obtain ⟨-, ⟨k, hk⟩, -, -⟩ := STAmount.roundToNumericType_int_grid _ rfl amount _ _ _ hamtN hamt0 hmode htvo
      have hlt := STAmount.roundToNumericType_int_lt_bound _ rfl amount _ _ _ hamtN hamt0 htvo
      refine ⟨k, by rw [hk, hls00, zpow_zero, mul_one], ?_⟩
      rw [hk] at hlt
      exact_mod_cast hlt
  have haT63 : aT < 2 ^ 63 := lt_of_lt_of_le haT (NumericType.mantissaBound_le _)
  have hja : j ≤ aT := by
    by_cases hir : rates.interestRate = 0
    · have hprops := hchecks.properties_ok
      rw [hir] at hprops
      have h1 := (computeLoanProperties_zero_rate_value principal _ _ _ _ _ props hp ⟨hbase.1, hbase.2⟩
        hpre.fits.paymentTotal_pos j hj1 hj (fun _ => by omega) hprops).1
      rw [haTv, hj] at h1
      exact le_of_eq (by exact_mod_cast (mul_right_cancel₀ hp10.ne' h1).symm)
    · have htiN := operator_sub_isNormalized_to_nearest_sz _ _ ti' htvN hp hsub
      have hR := operator_sub_rounded_to_nearest _ _ ti' htvN hp hsub
      by_contra hc'
      push Not at hc'
      have h1 : props.totalValueOutstanding.toRat - principal.toRat ≤ 0 := by
        rw [haTv, hj]
        have : (aT : ℚ) ≤ j := by exact_mod_cast hc'.le
        nlinarith
      have := Number.roundsToRepresentable_nonpos ti' _ hR h1
      have := (Number.signum_pos_iff_toRat htiN).mp (hgt0 hir)
      linarith
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest props.loanScale hp
      hpos.le (Or.inl rfl) ⟨by omega, hls80⟩ hls0 hst j hj (fun _ => hj16) hpo
  have htiv : ti.toRat = ((aT - j : ℕ) : ℚ) * 10 ^ props.loanScale := by
    rw [Number.operator_sub_toRat_of_grid _ _ ti aT j props.loanScale htvN hpoN (by rw [haTv]; norm_cast)
      (by rw [hpov, hj]; norm_cast) (by omega) hs hti]
    push_cast [Nat.cast_sub hja]; ring
  have hR10 : broker.managementFeeRate.toNat ≤ 10000 := broker.managementFeeRate_le
  have hfr : broker.numericType = .fractional → aT - j < 10 ^ 16 := by
    intro hf
    rw [hf] at haT
    exact lt_of_le_of_lt (Nat.sub_le _ _) haT
  obtain ⟨-, hmf_hi, -, ⟨mm, hmm⟩⟩ := computeManagementFee_bounds broker.numericType ti _ (aT - j)
    broker.managementFeeRate props.loanScale (operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti) htiv
    (by omega) hR10 ⟨hlo, hls80⟩ hls0 hfr hmfo
  have hmmK : mm ≤ aT - j := by
    have hC : ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 ≤ aT - j := by
      have : (aT - j) * broker.managementFeeRate.toNat ≤ (aT - j) * 10000 := Nat.mul_le_mul_left _ hR10
      omega
    have h1 : (mm : ℚ) * 10 ^ props.loanScale ≤
        ((((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 : ℕ) : ℚ) * 10 ^ props.loanScale := by
      rw [← hmm]; exact hmf_hi
    have h2 : mm ≤ ((aT - j) * broker.managementFeeRate.toNat + 99999) / 100000 := by
      exact_mod_cast le_of_mul_le_mul_right h1 hp10
    omega
  have hiv := LoanState.build_interestDue_grid _ _ _ props.loanScale aT j mm loanState htvN hp hmfN haTv hj hmm
    haT63 hja (by omega) hs hchecks.state
  refine ⟨j, aT, mm, hlo, hls80, hlsmin, hls0, hj, hj1, hja, hj16, htvN, haTv, haT, hpoN, hpov, hmfN, hmm, hmmK,
    hppN, hpp0', hiv.1, ?_⟩
  rw [hiv.2, haTv, hj, hmm]
  push_cast [Nat.cast_sub hja, Nat.cast_sub hmmK]
  ring

/-- Adding two `Number`s below `10^96` in size never throws. -/
lemma Number.operator_add_ok_of_small (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hx0 : 0 ≤ x.toRat) (hxlt : x.toRat < 10 ^ 96) (hyb : |y.toRat| < 10 ^ 96) :
    ∃ r, x.operator_add y mode = .ok r := by
  by_cases hy0 : y.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero y hy hy0]
    exact ⟨x, Number.operator_add_zero_right x mode⟩
  by_cases hneg : y.negative_ = true
  · -- the negation of `y` has the same exponent and leaves the headroom
    have hyn := Number.operator_neg_isNormalized y hy
    have hyv : 0 ≤ y.operator_neg.toRat := by
      rw [Number.toRat_neg]
      have := Number.toRat_nonpos_of_negative y hneg
      linarith
    have hyl : y.operator_neg.toRat < 10 ^ 96 := by
      rw [Number.toRat_neg]; have := (abs_lt.mp hyb).1; linarith
    have hye := Number.exponent_headroom_of_lt _ hyn hyv hyl
    rw [Number.operator_neg_exponent y hy0] at hye
    exact Number.operator_add_ok_of_exp x y mode hx hy (Number.exponent_headroom_of_lt x hx hx0 hxlt) hye
  · have hy0' : 0 ≤ y.toRat := by
      rw [Number.toRat_of_nonneg y (by simpa using hneg)]; positivity
    exact Number.operator_add_ok_of_exp x y mode hx hy (Number.exponent_headroom_of_lt x hx hx0 hxlt)
      (Number.exponent_headroom_of_lt y hy hy0' (by rw [abs_of_nonneg hy0'] at hyb; exact hyb))

/-- The computed AssetsTotal is at least every `Number` at or below AssetsAvailable plus AssetsDeployed. -/
lemma Vault.assetsTotal_ge_of_le (v : Vault) (atot : Number) (h : v.assetsTotal = .ok atot) (w : Number)
    (hw : w.isNormalized) (hwle : w.toRat ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat) :
    w.toRat ≤ atot.toRat := by
  have hAA := v.wf.assetsAvailable_norm
  have hAD := v.wf.assetsDeployed_norm
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  unfold RawVault.assetsTotal at h
  by_cases hd : v.assetsDeployed.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero _ hAD hd, Number.operator_add_zero_right] at h
    obtain rfl := Except.ok.inj h
    rw [Number.toRat_eq_zero_of_mantissa_zero _ hd, add_zero] at hwle
    exact hwle
  by_cases ha : v.assetsAvailable.mantissa_ = 0
  · have h' := h
    unfold Number.operator_add at h'
    rw [Number.operator_eq_zero_false_of_mantissa_ne _ hd, if_neg Bool.false_ne_true,
      Number.eq_zero_of_mantissa_zero _ hAA ha, if_pos (by decide)] at h'
    obtain rfl := Except.ok.inj h'
    rw [Number.toRat_eq_zero_of_mantissa_zero _ ha, zero_add] at hwle
    exact hwle
  have hna := Number.negative_false_of_nonneg _ hAA hAA0
  have hnd := Number.negative_false_of_nonneg _ hAD hAD0
  have hnz : ¬ v.assetsAvailable.operator_eq v.assetsDeployed.operator_neg = true := by
    simp [Number.operator_eq, Number.operator_neg, hd, hna, hnd]
  obtain ⟨_, _, _, _, _, hspec⟩ := operator_add_algorithmic_facts_same_sign_downward _ _ _ hAA hAD ha hd
    (by rw [hna, hnd]) hnz h
  obtain ⟨n, hlo, hval⟩ := operator_add_rounded_downward _ _ _ hAA hAD h hspec.result_mant_ne
  rw [hval]
  exact Number.lower_tight _ n hlo _ hw hwle

/-- The Open-limit check computes the total first. -/
lemma Vault.assetsTotal_of_exceedsOpenLimit (v : Vault) (x : Number) (b : Bool)
    (h : v.exceedsOpenLimit x = .ok b) : ∃ atot, v.assetsTotal = .ok atot := by
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit at h
  obtain ⟨atot, hat, -⟩ := bind_ok_peel _ _ _ h
  exact ⟨atot, hat⟩

/-- The vault update of a create succeeds and keeps the vault lawful. The principal moves within the
base grid, and an active loan adds a nonnegative interest the Open-limit check let through. -/
private lemma Loan.create_vault_update_lawful (broker : LoanBroker) (v : Vault)
    (principal principal' interestDue : Number) (pending : Bool) (jb : ℕ) (hasset : Vault.HoldsAsset v)
    (hgrid : Loan.CreateGrid broker v) (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hjb : principal.toRat = (jb : ℚ) * 10 ^ v.baseExponent) (hfunds : principal.toRat ≤ v.assetsAvailable.toRat)
    (hpN' : principal'.isNormalized) (hp' : principal'.toRat = principal.toRat)
    (hiDN : interestDue.isNormalized) (hiD0 : 0 ≤ interestDue.toRat)
    (hopen : v.exceedsOpenLimit interestDue = .ok false) :
    ∃ raw v', (v.adjustBalances (Loan.createChange principal principal' interestDue pending)).run =
      .ok (.ok raw) ∧ raw.to_lawful = .ok v' := by
  set b := v.baseExponent with hbdef
  have hbase := Vault.baseExponent_scale_range v
  have hb10 : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hs : minExponent + 18 ≤ b ∧ b ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  have hsmall : (10 : ℚ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  obtain ⟨a, ha, hav⟩ := hgrid.assetsAvailable
  obtain ⟨d, hd, hdv⟩ := hgrid.assetsDeployed
  obtain ⟨ar, har, harv⟩ := hgrid.assetsReserved
  obtain ⟨y, hy, hyv⟩ := hgrid.yieldUnrealized
  rw [← hbdef] at hav hdv harv hyv
  have hjba : jb ≤ a := by
    have : (jb : ℚ) * 10 ^ b ≤ (a : ℚ) * 10 ^ b := by rw [← hjb, ← hav]; exact hfunds
    exact_mod_cast le_of_mul_le_mul_right this hb10
  have hbig : ∀ k : ℕ, k < 10 ^ 17 → |((k : ℤ) : ℚ) * 10 ^ b| < 10 ^ 96 := by
    intro k hk
    rw [abs_of_nonneg (by positivity)]
    calc ((k : ℤ) : ℚ) * 10 ^ b ≤ (k : ℚ) * 1 := by push_cast; exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ < 10 ^ 96 := by rw [mul_one]; exact_mod_cast (show k < 10 ^ 96 by omega)
  have had16 : a + d < 10 ^ 16 := by
    obtain ⟨atot, hat⟩ := Vault.assetsTotal_of_exceedsOpenLimit v _ _ hopen
    have hopen := (Vault.exceedsOpenLimit_false_bound v interestDue hiDN hopen).2.2 atot hat
    by_contra hc
    push Not at hc
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) b (by norm_num) hs
    have hwle := Vault.assetsTotal_ge_of_le v atot hat w hw (by
      rw [hwv, hav, hdv]
      have h1 : (10 : ℚ) ^ 16 ≤ (a : ℚ) + d := by exact_mod_cast hc
      have h2 := mul_le_mul_of_nonneg_right h1 hb10.le
      push_cast
      linarith)
    rw [hwv] at hwle
    have h2 : (10 : ℚ) ^ (b - 1) = 10 ^ b / 10 := by
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
    rw [h2] at hopen
    push_cast at hopen hwle
    nlinarith
  have hnegN := Number.operator_neg_isNormalized _ hpN'
  have hnegv : principal'.operator_neg.toRat = -principal.toRat := by rw [Number.toRat_neg, hp']
  have hAAlt : v.assetsAvailable.toRat < 10 ^ 96 := by
    have := hbig a (by omega); rw [abs_of_nonneg (by positivity)] at this; rw [hav]; exact_mod_cast this
  obtain ⟨aa, hcash⟩ := Number.operator_add_ok_of_small v.assetsAvailable principal'.operator_neg .to_nearest
    v.wf.assetsAvailable_norm hnegN v.exact.assetsAvailable_nonneg hAAlt (by
      rw [hnegv, abs_neg, hjb]; exact hbig jb (by omega))
  have haav : aa.toRat = ((a - jb : ℕ) : ℚ) * 10 ^ b := by
    rw [Number.operator_add_toRat_of_grid _ _ aa a (-(jb : ℤ)) b v.wf.assetsAvailable_norm hnegN
      (by rw [hav]; norm_cast) (by rw [hnegv, hjb]; push_cast; ring) (by omega) hs hcash]
    push_cast [Nat.cast_sub hjba]; ring
  have haaN := operator_add_isNormalized_to_nearest_sz _ _ aa v.wf.assetsAvailable_norm hnegN hcash
  have hrepaa := Vault.HoldsAsset.isRounded_units hasset aa (a - jb) haaN (by omega) haav
  obtain ⟨aa', hrnd⟩ := STAmount.roundToNumericType_ok_of_isRounded_false _ _ hrepaa
  have haa' : aa'.toRat = aa.toRat := STAmount.roundToNumericType_of_isRounded_false _ _ _ haaN hrepaa hrnd
  have haa'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hrnd
  obtain ⟨ad', hdep⟩ := Number.operator_add_ok_of_small v.assetsDeployed principal .to_nearest
    v.wf.assetsDeployed_norm hp v.exact.assetsDeployed_nonneg (by
      have := hbig d (by omega); rw [abs_of_nonneg (by positivity)] at this; rw [hdv]; exact_mod_cast this)
    (by rw [hjb]; exact hbig jb (by omega))
  have hadv : ad'.toRat = ((d + jb : ℕ) : ℚ) * 10 ^ b := by
    rw [Number.operator_add_toRat_of_grid _ _ ad' d jb b v.wf.assetsDeployed_norm hp (by rw [hdv]; norm_cast)
      (by rw [hjb]; norm_cast) (by omega) hs hdep]
    push_cast; ring
  have had'N := operator_add_isNormalized_to_nearest_sz _ _ ad' v.wf.assetsDeployed_norm hp hdep
  have hloss : v.lossUnrealized.operator_add Number.zero .to_nearest = .ok v.lossUnrealized :=
    Number.operator_add_zero_right _ _
  obtain ⟨ar', hres, harv', har'N⟩ : ∃ ar', v.assetsReserved.operator_add (if pending then principal' else
      Number.zero) .to_nearest = .ok ar' ∧
      ar'.toRat = v.assetsReserved.toRat + (if pending then principal.toRat else 0) ∧ ar'.isNormalized := by
    cases pending with
    | true =>
      obtain ⟨ar', h⟩ := Number.operator_add_ok_of_small v.assetsReserved principal' .to_nearest
        v.wf.assetsReserved_norm hpN' v.exact.assetsReserved_nonneg (by
          have := hbig ar (by omega); rw [abs_of_nonneg (by positivity)] at this; rw [harv]
          exact_mod_cast this)
        (by rw [hp', hjb]; exact hbig jb (by omega))
      refine ⟨ar', h, ?_, operator_add_isNormalized_to_nearest_sz _ _ ar' v.wf.assetsReserved_norm hpN' h⟩
      rw [Number.operator_add_toRat_of_grid _ _ ar' ar jb b v.wf.assetsReserved_norm hpN'
        (by rw [harv]; norm_cast) (by rw [hp', hjb]; norm_cast) (by omega) hs h, if_pos rfl, harv, hjb]
      push_cast; ring
    | false =>
      exact ⟨v.assetsReserved, Number.operator_add_zero_right _ _, by rw [if_neg Bool.false_ne_true, add_zero],
        v.wf.assetsReserved_norm⟩
  obtain ⟨yu', hyld, hyu0, hyu'N⟩ : ∃ yu', v.yieldUnrealized.operator_add (if pending then Number.zero else
      interestDue) .to_nearest = .ok yu' ∧ 0 ≤ yu'.toRat ∧ yu'.isNormalized := by
    cases pending with
    | true =>
      exact ⟨v.yieldUnrealized, Number.operator_add_zero_right _ _, v.exact.yieldUnrealized_nonneg,
        v.wf.yieldUnrealized_norm⟩
    | false =>
      have hiDlt : |interestDue.toRat| < 10 ^ 96 := by
        rw [abs_of_nonneg hiD0]
        have hopen := (Vault.exceedsOpenLimit_false_bound v interestDue hiDN hopen).2.1
        have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
        have hL : ((9 * 10 ^ 16 + 5 : ℕ) : ℚ) * (10 : ℚ) ^ (v.baseExponent - 1) ≤ 10 ^ 17 := by
          have : (10 : ℚ) ^ (v.baseExponent - 1) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
          calc ((9 * 10 ^ 16 + 5 : ℕ) : ℚ) * (10 : ℚ) ^ (v.baseExponent - 1) ≤ ((9 * 10 ^ 16 + 5 : ℕ) : ℚ) * 1 :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ ≤ 10 ^ 17 := by norm_num
        linarith
      obtain ⟨yu', h⟩ := Number.operator_add_ok_of_small v.yieldUnrealized interestDue .to_nearest
        v.wf.yieldUnrealized_norm hiDN v.exact.yieldUnrealized_nonneg (by
          have := hbig y (by omega); rw [abs_of_nonneg (by positivity)] at this; rw [hyv]
          exact_mod_cast this) hiDlt
      have hR := operator_add_rounded_to_nearest _ _ yu' v.wf.yieldUnrealized_norm hiDN h
      have := hR.ge_of_le (Or.inl rfl) Number.zero Number.zero_isNormalized (by
        have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
        rw [Number.toRat_zero]; linarith)
      rw [Number.toRat_zero] at this
      exact ⟨yu', h, this, operator_add_isNormalized_to_nearest_sz _ _ yu' v.wf.yieldUnrealized_norm hiDN h⟩
  have hsums : Vault.AdjustSums v (Loan.createChange principal principal' interestDue pending)
      aa' ad' v.lossUnrealized ar' yu' :=
    ⟨⟨aa, hcash, hrnd⟩, hdep, hloss, hres, hyld⟩
  -- the new balances are nonnegative and LossUnrealized stays at most AssetsDeployed
  have haa0 : 0 ≤ aa'.toRat := by rw [haa', haav]; positivity
  have had0 : 0 ≤ ad'.toRat := by rw [hadv]; positivity
  have har0 : 0 ≤ ar'.toRat := by
    rw [harv']
    have : 0 ≤ v.assetsReserved.toRat := v.exact.assetsReserved_nonneg
    split
    · linarith
    · linarith
  have hlead : v.assetsDeployed.toRat ≤ ad'.toRat := by
    rw [hadv, hdv]; push_cast; nlinarith
  have hlu_le : v.lossUnrealized.toRat ≤ ad'.toRat := le_trans v.exact.lossUnrealized_le hlead
  have hsigns : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ v.lossUnrealized.signum ∧ 0 ≤ yu'.signum ∧
      0 ≤ ar'.signum :=
    ⟨(Number.signum_nonneg_iff_toRat haa'N).mpr haa0, (Number.signum_nonneg_iff_toRat had'N).mpr had0,
      (Number.signum_nonneg_iff_toRat v.wf.lossUnrealized_norm).mpr v.exact.lossUnrealized_nonneg,
      (Number.signum_nonneg_iff_toRat hyu'N).mpr hyu0, (Number.signum_nonneg_iff_toRat har'N).mpr har0⟩
  have hgt : v.lossUnrealized.operator_gt ad' = false := by
    cases h : v.lossUnrealized.operator_gt ad'
    · rfl
    · have := (operator_lt_iff _ _ had'N v.wf.lossUnrealized_norm).mp h
      linarith
  have hadj := Vault.adjustBalances_ok v _ aa' ad' v.lossUnrealized ar' yu' hsums hsigns hgt
  set raw : RawVault := { v.toRawVault with
    assetsAvailable := aa', assetsDeployed := ad', assetsReserved := ar', lossUnrealized := v.lossUnrealized,
    yieldUnrealized := yu' } with hraw
  have hrwf : raw.WF :=
    { v.wf with
      assetsAvailable_norm := haa'N
      assetsDeployed_norm := had'N
      assetsReserved_norm := har'N
      yieldUnrealized_norm := hyu'N }
  have hAApos : 0 < v.assetsAvailable.toRat := lt_of_lt_of_le hpos hfunds
  have hrvalid : raw.toExact.Valid :=
    { v.exact with
      assetsAvailable_nonneg := haa0
      assetsDeployed_nonneg := had0
      assetsReserved_nonneg := har0
      yieldUnrealized_nonneg := hyu0
      empty_shares := fun h0 => by
        have := (v.exact.empty_shares h0).1
        exact absurd this (ne_of_gt hAApos)
      lossUnrealized_le := hlu_le
      assetsDeployed_representable := by
        show STAmount.Representable v.numericType ad'.toRat
        have h1 := Vault.HoldsAsset.isRounded_units hasset ad' (d + jb) had'N (by omega) hadv
        rw [STAmount.isRounded_eq_false_iff _ _ had'N had0] at h1
        exact h1
      assetsReserved_le := by
        show ar'.toRat ≤ ad'.toRat
        rw [harv']
        have h1 : v.assetsReserved.toRat ≤ v.assetsDeployed.toRat := v.exact.assetsReserved_le
        have h2 : ad'.toRat = v.assetsDeployed.toRat + principal.toRat := by
          rw [hadv, hdv, hjb]; push_cast; ring
        split
        · linarith
        · linarith
      assetsAvailable_representable := by
        show STAmount.Representable v.numericType aa'.toRat
        have h1 := Vault.HoldsAsset.isRounded_units hasset aa' (a - jb) haa'N (by omega) (by rw [haa', haav])
        rwa [STAmount.isRounded_eq_false_iff _ _ haa'N haa0] at h1
      assetsAvailable_onGrid := ⟨((a - jb : ℕ) : ℤ), by
        show aa'.toRat = _ * 10 ^ v.baseExponent
        rw [haa', haav]; push_cast; rfl⟩ }
  exact ⟨raw, _, hadj, (RawVault.to_lawful_ok_of hrwf ((RawVault.valid_iff_exact raw hrwf).mpr hrvalid)).choose_spec.1⟩

/-- The broker after a create is lawful. Its new DebtTotal is the old one plus the principal, within
DebtMaximum by the limit check, and its LoanCount does not wrap. -/
private lemma Loan.create_broker_lawful (broker : LoanBroker) (v : Vault) (principal debtTotal' : Number)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat) (hcount : broker.loanCount + 1 ≠ 0)
    (hdebt : broker.debtTotal.operator_add principal .to_nearest = .ok debtTotal')
    (hlimits : broker.checkLimits debtTotal' v.baseExponent = .ok .tesSUCCESS) :
    ∃ broker', ({ broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
      : RawLoanBroker).to_lawful = .ok broker' := by
  have hdN := operator_add_isNormalized_to_nearest_sz _ _ _ broker.wf.debtTotal_norm hp hdebt
  have hDT0 : 0 ≤ broker.debtTotal.toRat := broker.exact.debtTotal_nonneg
  have hd0 : 0 ≤ debtTotal'.toRat := by
    have hR := operator_add_rounded_to_nearest _ _ _ broker.wf.debtTotal_norm hp hdebt
    have := hR.ge_of_le (Or.inl rfl) Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; linarith)
    rwa [Number.toRat_zero] at this
  -- the limit check keeps the new debt within a nonzero DebtMaximum
  have hcap : broker.debtMaximum ≠ Number.zero → debtTotal'.toRat ≤ broker.debtMaximum.toRat := by
    intro hm
    unfold LoanBroker.checkLimits at hlimits
    split at hlimits
    · exact absurd hlimits (by decide)
    · rename_i hc
      have hne : broker.debtMaximum.operator_ne Number.zero = true := by
        unfold Number.operator_ne
        cases h : broker.debtMaximum.operator_eq Number.zero
        · rfl
        · exact absurd ((Number.operator_eq_iff_eq _ _).mp h) hm
      rw [hne, Bool.true_and] at hc
      have hlt : broker.debtMaximum.operator_lt debtTotal' = false := by simpa using hc
      by_contra hgt
      push Not at hgt
      rw [(operator_lt_iff _ _ broker.wf.debtMaximum_norm hdN).mpr hgt] at hlt
      exact absurd hlt (by decide)
  set rb : RawLoanBroker := { broker.toRawLoanBroker with debtTotal := debtTotal', loanCount := broker.loanCount + 1 }
  have hwf : rb.WF := { broker.wf with debtTotal_norm := hdN }
  have hvalid : rb.toExact.Valid :=
    { broker.exact with
      debtTotal_nonneg := hd0
      debt_within_cap := fun hm => hcap (fun h => hm (by
        show broker.debtMaximum.toRat = 0; rw [h, Number.toRat_zero]))
      empty_broker := fun h0 => by
        have h0' : (broker.loanCount + 1).toNat = (0 : UInt32).toNat := h0
        exact absurd (UInt32.toNat_inj.mp h0') hcount }
  obtain ⟨broker', hb, -⟩ := RawLoanBroker.to_lawful_ok_of hwf ((RawLoanBroker.valid_iff_exact rb hwf).mpr hvalid)
  exact ⟨broker', hb⟩

/-- The new loan is lawful. Its amounts are the computed ones, whole numbers of LoanScale units within
the asset's range, its interest is not negative, and its terms and schedule passed the preflight. -/
private lemma Loan.create_loan_lawful (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (props : LoanProperties)
    (loanState : LoanState) (debtTotal' : Number) (broker' : LoanBroker)
    (hpre : Loan.CreatePreflight broker principal rates fees schedule) (hgrid : Loan.CreateGrid broker v)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal')
    (hbnt : broker'.numericType = broker.numericType) :
    ∃ loan, (RawLoan.build props rates fees schedule broker' allowsOverpayment pending).to_lawful = .ok loan := by
  obtain ⟨j, aT, mm, hlo, hls80, hlsmin, hls0, hj, hj1, hja, hj16, htvN, haTv, haT, hpoN, hpov, hmfN, hmm, hmmK,
    hppN, hpp0, -, -⟩ := Loan.create_checks_facts broker v principal rates fees schedule props loanState
      debtTotal' hpre hgrid hchecks
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  have hfee : ∀ fee ∈ fees.amountFields, fee.isNormalized ∧ 0 ≤ fee.toRat :=
    fun fee h => ⟨hpre.fees_norm fee h, hpre.fees_nonneg fee h⟩
  simp only [LoanFees.amountFields, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    at hfee
  obtain ⟨⟨ho, ho0⟩, ⟨hsv, hsv0⟩, ⟨hl, hl0⟩, ⟨hc, hc0⟩⟩ := hfee
  have hfits := hpre.fits
  have hn := hfits.paymentTotal_pos
  have hn' : 1 ≤ schedule.paymentTotal.toNat := by rw [UInt32.lt_iff_toNat_lt] at hn; simpa using hn
  have hend := hfits.ends_in_time
  have hmax : maxTime.toNat = 4294967295 := rfl
  have hint := hpre.paymentInterval_min
  have hint' : 60 ≤ schedule.paymentInterval.toNat := by
    rw [UInt32.le_iff_toNat_le] at hint; simpa [minPaymentInterval] using hint
  have hsi : schedule.startDate.toNat + schedule.paymentInterval.toNat < 2 ^ 32 := by
    have : schedule.paymentInterval.toNat ≤ schedule.paymentTotal.toNat * schedule.paymentInterval.toNat :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hnext : (schedule.startDate + schedule.paymentInterval).toNat =
      schedule.startDate.toNat + schedule.paymentInterval.toNat := by
    rw [UInt32.toNat_add]; omega
  set rl := RawLoan.build props rates fees schedule broker' allowsOverpayment pending with hrl
  have htv0 : 0 < props.totalValueOutstanding.toRat := by
    rw [haTv]; exact mul_pos (by exact_mod_cast (show 0 < aT by omega)) hp10
  have hbound : broker'.numericType.mantissaBound = broker.numericType.mantissaBound := by rw [hbnt]
  have haT' : aT < broker'.numericType.mantissaBound := by rw [hbound]; exact haT
  have hj' : j < broker'.numericType.mantissaBound := by rw [hbound]; omega
  have hmm' : mm < broker'.numericType.mantissaBound := by rw [hbound]; omega
  have hn0 : schedule.paymentTotal ≠ 0 := fun h => absurd (h ▸ hn) (by decide)
  have hpo0 : 0 ≤ props.principalOutstanding.toRat := by rw [hpov]; exact hpre.principal_pos.le
  have hmf0 : 0 ≤ props.managementFeeOutstanding.toRat := by rw [hmm]; positivity
  have hwf : rl.WF :=
    { periodicPayment_norm := hppN
      principalOutstanding_norm := hpoN
      totalValueOutstanding_norm := htvN
      managementFeeOutstanding_norm := hmfN
      originationFee_norm := ho
      serviceFee_norm := hsv
      latePaymentFee_norm := hl
      closePaymentFee_norm := hc
      loanScale_range := by
        show cMinOffset ≤ props.loanScale ∧ props.loanScale ≤ cMaxOffset
        unfold cMinOffset cMaxOffset; omega
      totalValueOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ htvN htv0.le).mpr ⟨aT, haT', haTv⟩
      principalOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hpoN hpo0).mpr ⟨j, hj', by
        show props.principalOutstanding.toRat = (j : ℚ) * 10 ^ props.loanScale; rw [hpov, hj]⟩
      managementFeeOutstanding_atExponent := (Number.isAtExponent_iff _ _ _ hmfN hmf0).mpr ⟨mm, hmm', hmm⟩ }
  have hvalid : rl.toExact.Valid :=
    { paid_zeroed := fun h => absurd h hn0
      unpaid_nonzero := fun _ => Or.inl (ne_of_gt htv0)
      principalOutstanding_nonneg := hpo0
      totalValueOutstanding_nonneg := htv0.le
      managementFeeOutstanding_nonneg := hmf0
      serviceFee_nonneg := hsv0
      latePaymentFee_nonneg := hl0
      closePaymentFee_nonneg := hc0
      periodicPayment_pos := hpp0
      paid_no_due_date := fun h => absurd h hn0
      interest_nonneg := by
        show 0 ≤ props.totalValueOutstanding.toRat - props.principalOutstanding.toRat -
            props.managementFeeOutstanding.toRat
        rw [haTv, hpov, hj, hmm]
        have h2 : ((j + mm : ℕ) : ℚ) ≤ (aT : ℚ) := by exact_mod_cast (by omega)
        push_cast at h2
        nlinarith
      paymentRemaining_le_total := UInt32.le_refl _
      -- a new loan is due one interval after StartDate
      dueDate_schedule := fun _ => by
        show (schedule.startDate + schedule.paymentInterval).toNat = schedule.startDate.toNat +
          (schedule.paymentTotal.toNat - schedule.paymentTotal.toNat + 1) * schedule.paymentInterval.toNat
        rw [hnext, Nat.sub_self, Nat.zero_add, Nat.one_mul]
      schedule_in_time := by
        show schedule.startDate.toNat + schedule.paymentTotal.toNat * schedule.paymentInterval.toNat ≤ maxTime.toNat
        omega
      interestRate_cap := UInt32.le_iff_toNat_le.mp hpre.interestRate_cap
      lateInterestRate_cap := UInt32.le_iff_toNat_le.mp hpre.lateInterestRate_cap
      closeInterestRate_cap := UInt32.le_iff_toNat_le.mp hpre.closeInterestRate_cap
      overpaymentInterestRate_cap := UInt32.le_iff_toNat_le.mp hpre.overpaymentInterestRate_cap
      overpaymentFee_cap := UInt32.le_iff_toNat_le.mp hpre.overpaymentFee_cap
      originationFee_nonneg := ho0
      paymentTotal_pos := hn
      paymentInterval_min := hpre.paymentInterval_min
      gracePeriod_range := hpre.gracePeriod_range }
  obtain ⟨loan, hloan, -⟩ := RawLoan.to_lawful_ok_of hwf ((RawLoan.valid_iff_exact rl hwf).mpr hvalid)
  exact ⟨loan, hloan⟩

/-- The checks of a create let the update and the re-checks through. On a vault of an IOU, XRP or an
MPT on its base grid, the vault update keeps every balance nonnegative and the loan, broker and vault are lawful. -/
lemma Loan.create_success_lawful (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (props : LoanProperties)
    (loanState : LoanState) (debtTotal' : Number)
    (hpre : Loan.CreatePreflight broker principal rates fees schedule) (hasset : Vault.HoldsAsset v)
    (hgrid : Loan.CreateGrid broker v) (hcount : broker.loanCount + 1 ≠ 0)
    (hchecks : Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal') :
    ∃ loan v', (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run =
      .ok (.ok { loan' := loan, pool' := v' }) := by
  obtain ⟨j, aT, mm, -, -, hlsmin, -, hj, -, -, -, -, -, -, -, -, -, -, -, -, -, hiDN, hiDv⟩ :=
    Loan.create_checks_facts broker v principal rates fees schedule props loanState debtTotal' hpre hgrid hchecks
  have hp := hpre.principal_norm
  have hpos := hpre.principal_pos
  have hst := hpre.principal_exact
  obtain ⟨principal', hround⟩ := STAmount.roundToNumericType_ok_of_isRounded_false _ _ hst
  have hp' : principal'.toRat = principal.toRat :=
    STAmount.roundToNumericType_of_isRounded_false _ _ _ hp hst hround
  have hpN' := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
  have hfunds : principal.toRat ≤ v.assetsAvailable.toRat := by
    have h1 := hchecks.funds
    by_contra hc'
    push Not at hc'
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hc'] at h1
    exact absurd h1 (by decide)
  have hjb : principal.toRat =
      ((j * 10 ^ (props.loanScale - v.baseExponent).toNat : ℕ) : ℚ) * 10 ^ v.baseExponent := by
    rw [hj]; exact grid_point_fine j _ _ hlsmin
  have hiD0 : 0 ≤ loanState.interestDue.toRat := by rw [hiDv]; positivity
  obtain ⟨raw, v', hadj, hv'⟩ := Loan.create_vault_update_lawful broker v principal principal' loanState.interestDue
    pending _ hasset hgrid hp hpos hjb hfunds hpN' hp' hiDN hiD0 hchecks.open_zone
  obtain ⟨broker', hbroker⟩ := Loan.create_broker_lawful broker v principal debtTotal' hp hpos hcount hchecks.debt
    hchecks.limits
  have hbnt : broker'.numericType = broker.numericType := by
    show broker'.toRawLoanBroker.numericType = _
    rw [(RawLoanBroker.to_lawful_ok hbroker).1]
  obtain ⟨loan, hloan⟩ := Loan.create_loan_lawful broker v principal rates fees schedule allowsOverpayment pending
    props loanState debtTotal' broker' hpre hgrid hchecks hbnt
  exact ⟨loan, v', Loan.create_success_proof broker v principal rates fees schedule allowsOverpayment pending props
    loanState debtTotal' principal' raw v' broker' loan hchecks hround hadj hv' hbroker hloan⟩

/-- A to-nearest rounding is at least a representable value at or below the truth. -/
private lemma rn_ge {r : Number} {t : ℚ} (hR : r.RoundsToRepresentable t .to_nearest) (w : Number)
    (hw : w.isNormalized) (hwt : w.toRat ≤ t) : w.toRat ≤ r.toRat :=
  hR.ge_of_le (Or.inl rfl) w hw hwt

/-- A to-nearest rounding of a nonnegative value is nonnegative. -/
private lemma rn_nonneg {r : Number} {t : ℚ} (hR : r.RoundsToRepresentable t .to_nearest) (ht : 0 ≤ t) :
    0 ≤ r.toRat := by
  have := rn_ge hR Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; exact ht)
  rwa [Number.toRat_zero] at this

/-- The `Number` one has the value one. -/
private lemma Number.ofInt64_one_toRat : (Number.ofInt64 1).toRat = 1 := by
  rw [Number.ofInt64_toRat_of_ne _ (by decide)]; rfl

/-- A power of a base at least one is at least one. Each squaring and each multiplication by the
base rounds a value at least one, and one is representable. -/
private lemma Number.power_ge_one (base : Number) (hb : base.isNormalized) (h1 : 1 ≤ base.toRat) :
    ∀ (k : Nat) (r : Number), base.power k = .ok r → 1 ≤ r.toRat := by
  have hone := Number.ofInt64_isNormalized 1
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r h
    match k, ih with
    | 0, _ =>
      rw [Number.power] at h
      cases h; rw [Number.ofInt64_one_toRat]
    | 1, _ =>
      rw [Number.power] at h
      cases h; exact h1
    | j + 2, ih =>
      rw [Number.power] at h
      obtain ⟨half, hh, h⟩ := bind_ok_peel _ _ _ h
      have hhalfN := Number.power_isNormalized base hb _ half hh
      have hhalf := ih ((j + 2) / 2) (by omega) half hh
      obtain ⟨sq, hs, h⟩ := bind_ok_peel _ _ _ h
      have hsqN := Number.operator_mul_isNormalized _ _ sq _ hhalfN hhalfN hs
      have hsq : 1 ≤ sq.toRat := by
        have := rn_ge (operator_mul_rounded_to_nearest _ _ _ hhalfN hhalfN hs) _ hone
          (by rw [Number.ofInt64_one_toRat]; nlinarith)
        rwa [Number.ofInt64_one_toRat] at this
      split at h
      · have := rn_ge (operator_mul_rounded_to_nearest _ _ _ hsqN hb h) _ hone
          (by rw [Number.ofInt64_one_toRat]; nlinarith)
        rwa [Number.ofInt64_one_toRat] at this
      · cases h; exact hsq

/-- A count below `2^63` converts to a `Number` at least zero. -/
private lemma Number.ofInt64_nat_nonneg (k : ℕ) (hk : k < 2 ^ 63) : 0 ≤ (Number.ofInt64 k.toInt64).toRat := by
  have hv : (k.toInt64).toInt = k := Int64.toInt_ofNat_of_lt hk
  have hne : k.toInt64 ≠ Int64.minValue := by
    intro h
    have := congrArg Int64.toInt h
    rw [hv, show Int64.minValue.toInt = -2 ^ 63 from by decide] at this
    omega
  rw [Number.ofInt64_toRat_of_ne _ hne, hv]
  positivity

/-- The binomial series of `(1 + rate)^n − 1` stays nonnegative. Each term is a product and a
quotient of nonnegative values, and each partial sum rounds a sum at least the previous one. -/
private lemma powerMinusOneLoop_nonneg (rate : Number) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat) (pr : Nat)
    (hpr : pr < 2 ^ 32) :
    ∀ (d index : Nat) (ct rs r : Number), pr - index = d → ct.isNormalized → rs.isNormalized →
      0 ≤ ct.toRat → 0 ≤ rs.toRat → powerMinusOneLoop rate pr index ct rs = .ok r → 0 ≤ r.toRat := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro index ct rs r hd hc hs hc0 hs0 h
    rw [powerMinusOneLoop] at h
    split at h
    · rename_i hlt
      obtain ⟨c1, h1, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨c2, h2, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨c3, h3, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨ns, h4, h⟩ := bind_ok_peel _ _ _ h
      have hc1 := Number.operator_mul_isNormalized _ _ c1 _ hc hrate h1
      have hc2 := Number.operator_mul_isNormalized _ _ c2 _ hc1 (Number.ofInt64_isNormalized _) h2
      have hc3 := Number.operator_div_isNormalized _ _ c3 _ hc2 (Number.ofInt64_isNormalized _) h3
      have hns := operator_add_isNormalized_to_nearest_sz _ _ ns hs hc3 h4
      have hc10 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hc hrate h1) (mul_nonneg hc0 hr0)
      have hc20 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hc1 (Number.ofInt64_isNormalized _) h2)
        (mul_nonneg hc10 (Number.ofInt64_nat_nonneg _ (by omega)))
      have hc30 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hc2 (Number.ofInt64_isNormalized _) h3)
        (div_nonneg hc20 (Number.ofInt64_nat_nonneg _ (by omega)))
      have hns0 := rn_nonneg (operator_add_rounded_to_nearest _ _ _ hs hc3 h4) (add_nonneg hs0 hc30)
      split at h
      · cases h; exact hs0
      · exact ih (pr - (index + 1)) (by omega) (index + 1) c3 ns r rfl hc3 hns hc30 hns0 h
    · cases h; exact hs0

/-- `(1 + rate)^n − 1` by the series is nonnegative. -/
private lemma computePowerMinusOne_nonneg (rate n : Number) (pr : UInt32) (r : Number) (hrate : rate.isNormalized)
    (hr0 : 0 ≤ rate.toRat) (hn : n.isNormalized) (hn0 : 0 ≤ n.toRat)
    (h : computePowerMinusOne rate n pr = .ok r) : 0 ≤ r.toRat := by
  unfold computePowerMinusOne at h
  dsimp only at h
  split at h
  · cases h; rw [Number.toRat_zero]
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨c, hc, h⟩ := bind_ok_peel _ _ _ h
    have hcN := Number.operator_mul_isNormalized _ _ c _ hn hrate hc
    have hc0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hn hrate hc) (mul_nonneg hn0 hr0)
    exact powerMinusOneLoop_nonneg rate hrate hr0 pr.toNat pr.toNat_lt _ 1 c c r rfl hcN hcN hc0 hc0 h

/-- `(1 + rate)^n − 1` by either method is nonnegative. -/
private lemma computePowerMinusOneHybrid_nonneg (rate n : Number) (pr : UInt32) (r : Number)
    (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat) (hn : n.isNormalized) (hn0 : 0 ≤ n.toRat)
    (h : computePowerMinusOneHybrid rate n pr = .ok r) : 0 ≤ r.toRat := by
  have hone := Number.ofInt64_isNormalized 1
  unfold computePowerMinusOneHybrid at h
  dsimp only at h
  split at h
  · cases h; rw [Number.toRat_zero]
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨nr, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨th, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨raised, hraised, h⟩ := bind_ok_peel _ _ _ h
      have hbN := operator_add_isNormalized_to_nearest_sz _ _ b hone hrate hb
      have hb1 : 1 ≤ b.toRat := by
        have := rn_ge (operator_add_rounded_to_nearest _ _ _ hone hrate hb) _ hone
          (by rw [Number.ofInt64_one_toRat]; linarith)
        rwa [Number.ofInt64_one_toRat] at this
      have hraisedN := Number.power_isNormalized b hbN _ raised hraised
      have hr1 := Number.power_ge_one b hbN hb1 _ raised hraised
      have := rn_nonneg (operator_sub_rounded_to_nearest _ _ _ hraisedN hone h)
        (by rw [Number.ofInt64_one_toRat]; linarith)
      exact this
    · exact computePowerMinusOne_nonneg rate n pr r hrate hr0 hn hn0 h

/-- The payment factor is nonnegative. -/
lemma computePaymentFactor_nonneg (rate n : Number) (pr : UInt32) (r : Number) (hrate : rate.isNormalized)
    (hr0 : 0 ≤ rate.toRat) (hn : n.isNormalized) (hn0 : 0 ≤ n.toRat)
    (h : computePaymentFactor rate n pr = .ok r) : 0 ≤ r.toRat := by
  have hone := Number.ofInt64_isNormalized 1
  unfold computePaymentFactor at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rw [Number.toRat_zero]
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · exact rn_nonneg (operator_div_rounded_to_nearest _ _ _ hone hn h)
        (div_nonneg (by rw [Number.ofInt64_one_toRat]; norm_num) hn0)
    · obtain ⟨pmo, hpmo, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨rr, hrr, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨num, hnum, h⟩ := bind_ok_peel _ _ _ h
      have hpN := computePowerMinusOneHybrid_isNormalized rate n pr pmo hrate hn hpmo
      have hp0 := computePowerMinusOneHybrid_nonneg rate n pr pmo hrate hr0 hn hn0 hpmo
      have hrrN := operator_add_isNormalized_to_nearest_sz _ _ rr hone hpN hrr
      have hrr0 := rn_nonneg (operator_add_rounded_to_nearest _ _ _ hone hpN hrr)
        (by rw [Number.ofInt64_one_toRat]; linarith)
      have hnumN := Number.operator_mul_isNormalized _ _ num _ hrate hrrN hnum
      have hnum0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hrate hrrN hnum) (mul_nonneg hr0 hrr0)
      exact rn_nonneg (operator_div_rounded_to_nearest _ _ _ hnumN hpN h) (div_nonneg hnum0 hp0)

/-- The periodic payment of a nonnegative principal at a nonnegative rate is nonnegative. -/
private lemma loanPeriodicPayment_nonneg (principal rate : Number) (pr : UInt32) (r : Number)
    (hp : principal.isNormalized) (hp0 : 0 ≤ principal.toRat) (hrate : rate.isNormalized)
    (hr0 : 0 ≤ rate.toRat) (h : loanPeriodicPayment principal rate pr = .ok r) : 0 ≤ r.toRat := by
  have hN := Number.ofInt64_isNormalized pr.toUInt64.toInt64
  have hN0 : 0 ≤ (Number.ofInt64 pr.toUInt64.toInt64).toRat := by rw [Number.ofInt64_count]; positivity
  unfold loanPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rw [Number.toRat_zero]
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · exact rn_nonneg (operator_div_rounded_to_nearest _ _ _ hp hN h) (div_nonneg hp0 hN0)
    · obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
      have hfN := computePaymentFactor_isNormalized rate _ pr f hrate hN hf
      have hf0 := computePaymentFactor_nonneg rate _ pr f hrate hr0 hN hN0 hf
      exact rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hp hfN h) (mul_nonneg hp0 hf0)

/-- The periodic rate is nonnegative. -/
lemma loanPeriodicRate_nonneg (ir : TenthBips32) (interval : UInt32) (rate : Number)
    (h : loanPeriodicRate ir interval = .ok rate) : 0 ≤ rate.toRat := by
  have heq : loanPeriodicRate ir interval =
      ((Number.ofInt64 interval.toUInt64.toInt64).operator_mul ir.toNumber .to_nearest >>=
        (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest)) >>=
        (fun t => t.operator_div secondsInYear .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨t, ht, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨p, hp, ht⟩ := bind_ok_peel _ _ _ ht
  have hI := Number.ofInt64_isNormalized interval.toUInt64.toInt64
  have hB := Number.ofInt64_isNormalized ir.toUInt64.toInt64
  have hU := Number.ofInt64_isNormalized kTenthBipsPerUnity.toUInt64.toInt64
  have hY := Number.ofInt64_isNormalized (31536000 : Int64)
  have hI0 : 0 ≤ (Number.ofInt64 interval.toUInt64.toInt64).toRat := by rw [Number.ofInt64_count]; positivity
  have hB0 : 0 ≤ (Number.ofInt64 ir.toUInt64.toInt64).toRat := by rw [Number.ofInt64_count]; positivity
  have hU0 : 0 ≤ (Number.ofInt64 kTenthBipsPerUnity.toUInt64.toInt64).toRat := by
    rw [Number.ofInt64_count]; positivity
  have hY0 : 0 ≤ (Number.ofInt64 (31536000 : Int64)).toRat := by
    rw [Number.ofInt64_toRat_of_ne _ (by decide), show (31536000 : Int64).toInt = 31536000 from by decide]
    norm_num
  have hpN := Number.operator_mul_isNormalized _ _ p _ hI hB hp
  have htN := Number.operator_div_isNormalized _ _ t _ hpN hU ht
  have hp0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hI hB hp) (mul_nonneg hI0 hB0)
  have ht0 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hpN hU ht) (div_nonneg hp0 hU0)
  exact rn_nonneg (operator_div_rounded_to_nearest _ _ _ htN hY h) (div_nonneg ht0 hY0)

end XRPL.Model.Lending

namespace XRPL.Model.Protocol

/-- Rounding a nonnegative value to an asset, at a scale in range, gives a nonnegative value. -/
lemma STAmount.roundToNumericType_some_nonneg (nt : NumericType) (x T : Number) (mode : rounding_mode) (s : ℤ)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) (hs : -81 ≤ s ∧ s ≤ 80)
    (hok : STAmount.roundToNumericType nt x mode (some s) = .ok T) : 0 ≤ T.toRat := by
  cases hnt : nt with
  | integral mv mo ms msh =>
    rw [hnt] at hok
    obtain ⟨hgf, -⟩ := STAmount.roundToNumericType_int_grid _ rfl x T mode _ hx h0 hmode hok
    have := hgf.lower 0 (by simp only [CharP.cast_eq_zero, zero_mul]; exact h0)
    simpa only [CharP.cast_eq_zero, zero_mul] using this
  | fractional =>
    rw [hnt] at hok
    unfold STAmount.roundToNumericType at hok
    cases hof : STAmount.ofNumber .fractional x mode with
    | error e => rw [hof] at hok; exact absurd hok (by simp)
    | ok st =>
      rw [hof] at hok
      simp only at hok
      have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
      have hint : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
      rw [if_neg (by rw [hint]; decide)] at hok
      have hst0 : 0 ≤ st.toRat :=
        STAmount.ofNumber_nonneg _ _ _ _ hx (Number.negative_false_of_nonneg x hx h0) hof
      cases hr : STAmount.roundToExponent st s mode with
      | error e => rw [hr] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hr] at hok
        simp only at hok
        by_cases hz : st.mValue = 0
        · have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s mode
            (Or.inr (Or.inl (by unfold STAmount.isZero; simp [hz]))) hr
          subst hrst
          rw [STAmount.toNumber_zero_fractional r mode hint hz, Except.ok.injEq] at hok
          rw [← hok, Number.toRat_zero]
        have hc := (STAmount.ofNumber_frac_stage x mode st hx h0 hmode hof hz).1
        have hsneg := STAmount.mIsNegative_false_of_nonneg st hst0 hz
        by_cases heq : s ≤ st.exponent
        · have hrst : r = st := STAmount.roundToExponent_ok_eq_self st r s mode (Or.inr (Or.inr heq)) hr
          subst hrst
          obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hc
          rw [hsn, Except.ok.injEq] at hok
          rw [← hok, hv]; exact hst0
        · push Not at heq
          obtain ⟨k, hrk, hrty, hrc, -⟩ :=
            STAmount.roundToExponent_nonneg_units st r s mode hc hsneg heq hs.1 hs.2 hr
          have hr0 : 0 ≤ r.toRat := by rw [hrk]; positivity
          rcases hrc with hr0' | hrc
          · have hrint : r.integral = false := by unfold STAmount.integral; rw [hrty]; rfl
            rw [STAmount.toNumber_zero_fractional r mode hrint hr0', Except.ok.injEq] at hok
            rw [← hok, Number.toRat_zero]
          · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hrc
            rw [hsn, Except.ok.injEq] at hok
            rw [← hok, hv]; exact hr0

end XRPL.Model.Protocol

namespace XRPL.Model.Lending
open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- What the amortization guards decided. tecPRECISION_LOSS, tecINTERNAL only for a zero InterestRate
with interest, or a pass with interest for a nonzero InterestRate and a nonzero rounded payment. -/
private lemma LoanProperties.amortizationGuards_cases (props : LoanProperties) (principal : Number) (ir : TenthBips32)
    (n : UInt32) (nt : NumericType) (g : TER)
    (h : props.amortizationGuards principal (ir != 0) n nt = .ok g) :
    ∃ ti, props.totalValueOutstanding.operator_sub principal .to_nearest = .ok ti ∧
      (g = .tecPRECISION_LOSS ∨ (g = .tecINTERNAL ∧ ir = 0 ∧ 0 < ti.signum) ∨
        (g = .tesSUCCESS ∧ (ir ≠ 0 → 0 < ti.signum) ∧
          ∃ rp, STAmount.roundToNumericType nt props.periodicPayment .upward (some props.loanScale) = .ok rp ∧
            rp.operator_eq Number.zero = false)) := by
  unfold LoanProperties.amortizationGuards at h
  cases hti : props.totalValueOutstanding.operator_sub principal .to_nearest with
  | error e => rw [hti] at h; exact absurd h (by simp [bind, Except.bind])
  | ok ti =>
    rw [hti] at h
    refine ⟨ti, rfl, ?_⟩
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · exact Or.inl (Except.ok.inj h).symm
    rename_i h1
    split at h
    · rename_i h2
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, decide_eq_true_eq, gt_iff_lt] at h2
      exact Or.inr (Or.inl ⟨(Except.ok.inj h).symm, h2.1, h2.2⟩)
    split at h
    · exact Or.inl (Except.ok.inj h).symm
    cases hrp : STAmount.roundToNumericType nt props.periodicPayment .upward (some props.loanScale) with
    | error e => rw [hrp] at h; exact absurd h (by simp)
    | ok rp =>
      rw [hrp] at h
      simp only at h
      split at h
      · exact Or.inl (Except.ok.inj h).symm
      rename_i h3
      cases hd : props.totalValueOutstanding.operator_div rp .upward with
      | error e => rw [hd] at h; exact absurd h (by simp)
      | ok ratio =>
        rw [hd] at h
        simp only at h
        cases hr : ratio.to_rep .upward with
        | error e => rw [hr] at h; exact absurd h (by simp)
        | ok c =>
          rw [hr] at h
          simp only at h
          split at h
          · exact Or.inl (Except.ok.inj h).symm
          · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and, not_le] at h1
            refine Or.inr (Or.inr ⟨(Except.ok.inj h).symm, fun hir => h1 hir, rp, rfl, by simpa using h3⟩)

open private checkPrecisionFields from XRPL.Model.Lending.Loan.LoanSet

/-- The precision check passes or rejects with tecPRECISION_LOSS. -/
private lemma checkPrecisionFields_codes (principal : Number) (fees : LoanFees) (f : Number → Except Error Bool)
    (ter : TER) (h : checkPrecisionFields principal fees f = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS := by
  unfold checkPrecisionFields LoanFees.amountFields at h
  simp only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure] at h
  cases h1 : f principal with
  | error e => rw [h1] at h; simp at h
  | ok b1 =>
    cases b1
    · rw [h1] at h; simp at h; exact Or.inr h.symm
    cases h2 : f fees.originationFee with
    | error e => rw [h1, h2] at h; simp at h
    | ok b2 =>
      cases b2
      · rw [h1, h2] at h; simp at h; exact Or.inr h.symm
      cases h3 : f fees.serviceFee with
      | error e => rw [h1, h2, h3] at h; simp at h
      | ok b3 =>
        cases b3
        · rw [h1, h2, h3] at h; simp at h; exact Or.inr h.symm
        cases h4 : f fees.latePaymentFee with
        | error e => rw [h1, h2, h3, h4] at h; simp at h
        | ok b4 =>
          cases b4
          · rw [h1, h2, h3, h4] at h; simp at h; exact Or.inr h.symm
          cases h5 : f fees.closePaymentFee with
          | error e => rw [h1, h2, h3, h4, h5] at h; simp at h
          | ok b5 =>
            cases b5
            · rw [h1, h2, h3, h4, h5] at h; simp at h; exact Or.inr h.symm
            · rw [h1, h2, h3, h4, h5] at h; simp at h; exact Or.inl h.symm

/-- The broker limits pass or reject with tecLIMIT_EXCEEDED or tecINSUFFICIENT_FUNDS. -/
private lemma LoanBroker.checkLimits_codes (broker : LoanBroker) (d : Number) (e : Int) (ter : TER)
    (h : broker.checkLimits d e = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecLIMIT_EXCEEDED ∨ ter = .tecINSUFFICIENT_FUNDS := by
  unfold LoanBroker.checkLimits at h
  split at h
  · exact Or.inr (Or.inl (Except.ok.inj h).symm)
  · cases hm : ({ broker.toRawLoanBroker with debtTotal := d } : RawLoanBroker).hasMinimumCover e with
    | error err => simp only [bind, Except.bind, hm] at h; exact absurd h (by simp)
    | ok b =>
      cases b
      · simp only [bind, Except.bind, hm] at h; exact Or.inr (Or.inr (Except.ok.inj h).symm)
      · simp only [bind, Except.bind, hm] at h; exact Or.inl (Except.ok.inj h).symm

/-- The guards of a create never reject with tecINTERNAL. With InterestRate `0` the total value is
PrincipalRequested, and once the amortization guards pass the sanity check passes too. -/
private lemma Loan.create_checkGuards_codes (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (props : LoanProperties)
    (hpre : Loan.CreatePreflight broker principal rates fees schedule) (hgrid : Loan.CreateGrid broker v)
    (hterms : Loan.CreateTerms broker v principal rates fees schedule props) (ter : TER)
    (h : props.checkGuards principal rates.interestRate schedule.paymentTotal broker.numericType = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS := by
  have hp := hpre.principal_norm
  have hpos := hpre.principal_pos
  have hst := hpre.principal_exact
  obtain ⟨rate, amount, amountSt, ti, hrt, hpp, hamt, hst', hls, htvo, hpo, hti, hmfo⟩ :=
    computeLoanProperties_inv _ _ _ _ _ _ _ _ hterms.properties_ok
  have hbase := Vault.baseExponent_scale_range v
  obtain ⟨hlsmin, hls0⟩ := computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hterms.properties_ok hbase.2
  have hls80 : props.loanScale ≤ 80 := by
    rw [hls]
    refine max_le (le_trans hbase.2 (by norm_num)) ?_
    cases hnt' : broker.numericType with
    | integral mv mo ms msh =>
      rw [hnt'] at hst'
      have := (STAmount.ofNumber_integral_canonical _ _ _ amountSt rfl hst').1.offset_zero
      show amountSt.mOffset ≤ 80; omega
    | fractional =>
      rw [hnt'] at hst'
      rcases STAmount.ofNumber_fractional_offset _ _ _ amountSt rfl hst' with h1 | h1
      · show amountSt.mOffset ≤ 80; omega
      · exact h1.2
  have hlo : -10 ≤ props.loanScale := le_trans hbase.1 hlsmin
  have hp10 : (0 : ℚ) < 10 ^ props.loanScale := zpow_pos (by norm_num) _
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType principal props.loanScale hp hpos.le hst
    ⟨by omega, hls80⟩ hls0 (hterms.exact principal List.mem_cons_self)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0] at hj; simp at hj; linarith
    · exact h0
  have hfunds : principal.toRat ≤ v.assetsAvailable.toRat := by
    have h1 := hterms.funds
    by_contra hc'
    push Not at hc'
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hc'] at h1
    exact absurd h1 (by decide)
  obtain ⟨a, ha, hav⟩ := hgrid.assetsAvailable
  have hj16 : j < 10 ^ 16 := by
    have h1 : (j : ℚ) * 10 ^ props.loanScale < (10 ^ 16 : ℕ) * 10 ^ props.loanScale := by
      calc (j : ℚ) * 10 ^ props.loanScale = principal.toRat := hj.symm
        _ ≤ v.assetsAvailable.toRat := hfunds
        _ = (a : ℚ) * 10 ^ v.baseExponent := hav
        _ < (10 ^ 16 : ℕ) * 10 ^ v.baseExponent :=
            mul_lt_mul_of_pos_right (by exact_mod_cast ha) (zpow_pos (by norm_num) _)
        _ ≤ (10 ^ 16 : ℕ) * 10 ^ props.loanScale :=
            mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hlsmin) (by positivity)
    exact_mod_cast lt_of_mul_lt_mul_right h1 hp10.le
  have htvN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ htvo
  have hpoN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hpo
  have hpov : props.principalOutstanding.toRat = principal.toRat :=
    STAmount.roundToNumericType_representable_grid broker.numericType principal _ .to_nearest props.loanScale hp
      hpos.le (Or.inl rfl) ⟨by omega, hls80⟩ hls0 hst j hj (fun _ => hj16) hpo
  have hzero : rates.interestRate = 0 → props.totalValueOutstanding.toRat = principal.toRat := by
    intro hir
    have hprops := hterms.properties_ok
    rw [hir] at hprops
    exact (computeLoanProperties_zero_rate_value principal _ _ _ _ _ props hp ⟨hbase.1, hbase.2⟩
      hpre.fits.paymentTotal_pos j hj1 hj (fun _ => by omega) hprops).1
  unfold LoanProperties.checkGuards at h
  cases hg : props.amortizationGuards principal (rates.interestRate != 0) schedule.paymentTotal broker.numericType with
  | error e => rw [hg] at h; exact absurd h (by simp [bind, Except.bind])
  | ok g =>
    rw [hg] at h
    simp only [bind, Except.bind] at h
    obtain ⟨ti', hsub, hcases⟩ := LoanProperties.amortizationGuards_cases _ _ _ _ _ g hg
    have htiN := operator_sub_isNormalized_to_nearest_sz _ _ ti' htvN hp hsub
    rcases hcases with rfl | ⟨rfl, hir, hti0⟩ | ⟨rfl, hpos', rp, hrp, hrp0⟩
    · simp only [show TER.tecPRECISION_LOSS.isTesSuccess = false from rfl, Bool.not_false, ↓reduceIte, pure,
        Except.pure, Except.ok.injEq] at h
      exact Or.inr h.symm
    · -- the zero-rate guard sees no interest
      exfalso
      have hR := operator_sub_rounded_to_nearest _ _ ti' htvN hp hsub
      rw [hzero hir, sub_self] at hR
      have := (Number.signum_pos_iff_toRat htiN).mp hti0
      rw [hR.toRat_of_zero (Or.inl rfl)] at this
      exact lt_irrefl _ this
    · -- the sanity check passes
      simp only [show TER.tesSUCCESS.isTesSuccess = true from rfl, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, pure, Except.pure] at h
      have hPT : principal.toRat ≤ props.totalValueOutstanding.toRat := by
        by_cases hir : rates.interestRate = 0
        · exact le_of_eq (hzero hir).symm
        · have hR := operator_sub_rounded_to_nearest _ _ ti' htvN hp hsub
          by_contra hc'
          push Not at hc'
          have := Number.roundsToRepresentable_nonpos ti' _ hR (by linarith)
          have := (Number.signum_pos_iff_toRat htiN).mp (hpos' hir)
          linarith
      have htv0 : 0 < props.totalValueOutstanding.toRat := lt_of_lt_of_le hpos hPT
      -- the payment is nonnegative, and nonzero since its rounding is
      have hrN := loanPeriodicRate_isNormalized _ _ rate hrt
      have hppN := loanPeriodicPayment_isNormalized _ _ _ _ hp hrN hpp
      have hpp0 := loanPeriodicPayment_nonneg _ _ _ _ hp hpos.le hrN (loanPeriodicRate_nonneg _ _ _ hrt) hpp
      have hppp : 0 < props.periodicPayment.toRat := by
        rcases lt_or_eq_of_le hpp0 with h1 | h1
        · exact h1
        · exfalso
          have hz : props.periodicPayment = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hppN).mp h1.symm
          rw [hz, STAmount.roundToNumericType_zero, Except.ok.injEq] at hrp
          rw [← hrp] at hrp0
          exact absurd hrp0 (by decide)
      -- the fee rounds down a nonnegative share of a nonnegative interest
      have hti0 : 0 ≤ ti.toRat := by
        have hR := operator_sub_rounded_to_nearest _ _ ti htvN hpoN hti
        exact rn_nonneg hR (by rw [hpov]; linarith)
      have htiN0 := operator_sub_isNormalized_to_nearest_sz _ _ ti htvN hpoN hti
      have heq : computeManagementFee broker.numericType ti broker.managementFeeRate props.loanScale =
          (tenthBipsOfValue ti broker.managementFeeRate.toTenthBips32 .to_nearest) >>=
            (fun raw => STAmount.roundToNumericType broker.numericType raw .downward (some props.loanScale)) := rfl
      rw [heq] at hmfo
      obtain ⟨raw, hraw, hmfo'⟩ := bind_ok_peel _ _ _ hmfo
      have hmfN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hmfo'
      have heq2 : tenthBipsOfValue ti broker.managementFeeRate.toTenthBips32 .to_nearest =
          ti.operator_mul broker.managementFeeRate.toTenthBips32.toNumber .to_nearest >>=
            (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest) := rfl
      rw [heq2] at hraw
      obtain ⟨y, hy, hraw⟩ := bind_ok_peel _ _ _ hraw
      have hRB := Number.ofInt64_isNormalized broker.managementFeeRate.toTenthBips32.toUInt64.toInt64
      have hU := Number.ofInt64_isNormalized kTenthBipsPerUnity.toUInt64.toInt64
      have hRB0 : 0 ≤ (Number.ofInt64 broker.managementFeeRate.toTenthBips32.toUInt64.toInt64).toRat := by
        rw [Number.ofInt64_count]; positivity
      have hU0 : 0 ≤ (Number.ofInt64 kTenthBipsPerUnity.toUInt64.toInt64).toRat := by
        rw [Number.ofInt64_count]; positivity
      have hyN := Number.operator_mul_isNormalized _ _ y _ htiN0 hRB hy
      have hy0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ htiN0 hRB hy) (mul_nonneg hti0 hRB0)
      have hrawN := Number.operator_div_isNormalized _ _ raw _ hyN hU hraw
      have hraw0 := rn_nonneg (operator_div_rounded_to_nearest _ _ _ hyN hU hraw) (div_nonneg hy0 hU0)
      have hmf0 : 0 ≤ props.managementFeeOutstanding.toRat :=
        STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hrawN hraw0 (Or.inr (Or.inr rfl)) ⟨by omega, hls80⟩ hmfo'
      have hsan : (decide (props.managementFeeOutstanding.signum < 0) || decide (props.totalValueOutstanding.signum ≤ 0)
          || decide (props.periodicPayment.signum ≤ 0)) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt, not_le]
        exact ⟨⟨(Number.signum_nonneg_iff_toRat hmfN).mpr hmf0, (Number.signum_pos_iff_toRat htvN).mpr htv0⟩,
          (Number.signum_pos_iff_toRat hppN).mpr hppp⟩
      rw [hsan] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
      exact Or.inl h.symm

/-- The checks of a create, read off the steps it walked. -/
private lemma Loan.createChecks_of_steps (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (props : LoanProperties) (loanState : LoanState)
    (debtTotal' : Number) (tp tg tl : TER) (b : Bool)
    (hfunds : ¬ (AssetPool.amounts v).assetsAvailable.operator_lt principal = true)
    (hprops : computeLoanProperties principal rates.interestRate schedule.paymentInterval schedule.paymentTotal
      broker.managementFeeRate broker.numericType (AssetPool.baseExponent v) = .ok props)
    (hprec : checkPrecisionFields principal fees (fun value => isRounded value props.loanScale broker.numericType) =
      .ok tp) (hprec' : ¬ (!tp.isTesSuccess) = true)
    (hguards : props.checkGuards principal rates.interestRate schedule.paymentTotal broker.numericType = .ok tg)
    (hguards' : ¬ (!tg.isTesSuccess) = true)
    (hstate : LoanState.build props.totalValueOutstanding principal props.managementFeeOutstanding = .ok loanState)
    (hopen : AssetPool.exceedsOpenLimit v loanState.interestDue = .ok b) (hopen' : ¬ b = true)
    (hdebt : broker.debtTotal.operator_add principal .to_nearest = .ok debtTotal')
    (hlimits : broker.checkLimits debtTotal' (AssetPool.baseExponent v) = .ok tl)
    (hlimits' : ¬ (!tl.isTesSuccess) = true) :
    Loan.CreateChecks broker v principal rates fees schedule props loanState debtTotal' := by
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hprec' hguards' hlimits'
  rw [(TER.isTesSuccess_iff tp).mp hprec'] at hprec
  rw [(TER.isTesSuccess_iff tg).mp hguards'] at hguards
  rw [(TER.isTesSuccess_iff tl).mp hlimits'] at hlimits
  simp only [Bool.not_eq_true] at hopen'
  rw [hopen'] at hopen
  exact { funds := by simpa [Vault.pool_amounts] using hfunds
          properties_ok := hprops
          exact := checkPrecisionFields_success_inv _ _ _ hprec
          guards := hguards
          state := hstate
          open_zone := hopen
          debt := hdebt
          limits := hlimits }

/-- A LoanSet that passed preflight, on a vault of an IOU, XRP or MPT with its balances on the base grid, fails
only with tecINSUFFICIENT_FUNDS, tecPRECISION_LOSS or tecLIMIT_EXCEEDED, while LoanCount has room for one more. -/
lemma Loan.create_error_codes_proof (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (ter : TER)
    (hpre : Loan.CreatePreflight broker principal rates fees schedule) (hasset : Vault.HoldsAsset v)
    (hgrid : Loan.CreateGrid broker v) (hcount : broker.loanCount + 1 ≠ 0)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.error ter)) :
    ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED := by
  have hok0 := hok
  simp only [Loan.create] at hok
  unfold_ter at hok
  walk_ok
  all_goals try first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
  · -- the precision check passes or rejects with tecPRECISION_LOSS
    rename_i hprec hc
    rcases checkPrecisionFields_codes _ _ _ _ hprec with h | h
    · subst h; exact absurd hc (by decide)
    · exact Or.inr (Or.inl h)
  · -- the guards never reject with tecINTERNAL
    rename_i hguards hc
    have hp := ‹checkPrecisionFields _ _ _ = Except.ok _›
    have hp' := ‹¬ (!(_ : TER).isTesSuccess) = true›
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hp'
    rw [(TER.isTesSuccess_iff _).mp hp'] at hp
    rcases Loan.create_checkGuards_codes broker v principal rates fees schedule _ hpre hgrid
        ⟨by simpa [Vault.pool_amounts] using ‹¬ (AssetPool.amounts v).assetsAvailable.operator_lt principal = true›,
          ‹computeLoanProperties _ _ _ _ _ _ _ = Except.ok _›, checkPrecisionFields_success_inv _ _ _ hp⟩ ter
        hguards with h | h
    · subst h; exact absurd hc (by decide)
    · exact Or.inr (Or.inl h)
  · -- the broker limits reject with tecLIMIT_EXCEEDED or tecINSUFFICIENT_FUNDS
    rename_i hlimits hc
    rcases LoanBroker.checkLimits_codes _ _ _ _ hlimits with h | h | h
    · subst h; exact absurd hc (by decide)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  all_goals
    -- every check passed, so the create succeeds
    exfalso
    obtain ⟨loan, v', hrun⟩ := Loan.create_success_lawful broker v principal rates fees schedule
      allowsOverpayment pending _ _ _ hpre hasset hgrid hcount
      (Loan.createChecks_of_steps broker v principal rates fees schedule _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
        ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›)
    rw [hrun] at hok0
    exact absurd hok0 (by simp)

end XRPL.Model.Lending
