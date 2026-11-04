import XRPL.Properties.Lending.Loan.Common.InterestDue

/-! # A re-amortization keeps interestDue at least zero on XRP and MPT loans

On an integral asset the loan counts whole units. The re-amortized value covers the new principal and fee, as
on an IOU loan, as long as the loan owes at most `10^16 + 1` units, so every rounding stays below a unit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private Loan.tryOverpayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.reamortization_gross_normalized LoanProperties.amortizationGuards_interest
  from XRPL.Properties.Lending.Loan.Common.ReamortizationInterest

/-- An integral rounding equals the integral amount it converts to. -/
private lemma STAmount.roundToNumericType_int_amount (nt : NumericType) (hnt : nt.isIntegral = true)
    (hmax : nt.maxValue.toNat ≤ maxRep.toNat) (x T : Number) (mode : rounding_mode) (s : Option ℤ)
    (hok : STAmount.roundToNumericType nt x mode s = .ok T) :
    ∃ st, STAmount.ofNumber nt x mode = .ok st ∧ T.toRat = st.toRat := by
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
      have h1 := hic.in_range
      rw [hty] at h1
      have h2 : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact st mode hic hsz
    rw [hsn, Except.ok.injEq] at hT
    subst hT
    exact ⟨st, rfl, hv⟩

/-- An integral rounding of a value at most zero is at most zero. -/
private lemma STAmount.roundToNumericType_int_nonpos (nt : NumericType) (hnt : nt.isIntegral = true)
    (hmax : nt.maxValue.toNat ≤ maxRep.toNat) (x T : Number) (mode : rounding_mode) (s : Option ℤ)
    (hx : x.isNormalized) (h0 : x.toRat ≤ 0) (hok : STAmount.roundToNumericType nt x mode s = .ok T) :
    T.toRat ≤ 0 := by
  obtain ⟨st, hof, hT⟩ := STAmount.roundToNumericType_int_amount nt hnt hmax x T mode s hok
  rw [hT]
  by_cases hneg : x.negative_ = true
  · exact STAmount.ofNumber_integral_negative_nonpos nt x mode st hnt hneg hof
  · have hx0 : x.toRat = 0 := le_antisymm h0 (Number.toRat_nonneg_of_nonnegative x (by simpa using hneg))
    obtain ⟨iv, hrep, hval⟩ := STAmount.ofNumber_integral_toRat nt x mode st hnt (by simpa using hneg) hof
    have hxz : x = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hx).mp hx0
    subst hxz
    have hiv : iv.toInt = 0 := by
      have : Number.zero.to_rep mode = .ok 0 := by cases mode <;> rfl
      rw [this, Except.ok.injEq] at hrep
      rw [← hrep]; rfl
    rw [hval, hiv]; simp

/-- An integral to-nearest rounding of a value below `0.49` and at least zero is zero. -/
private lemma STAmount.roundToNumericType_int_small (nt : NumericType) (hnt : nt.isIntegral = true)
    (hmax : nt.maxValue.toNat ≤ maxRep.toNat) (x T : Number) (s : Option ℤ) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hsmall : x.toRat < 49 / 100)
    (hok : STAmount.roundToNumericType nt x .to_nearest s = .ok T) : T.toRat = 0 := by
  obtain ⟨st, hof, hT⟩ := STAmount.roundToNumericType_int_amount nt hnt hmax x T .to_nearest s hok
  have hneg := Number.negative_false_of_nonneg x hx h0
  have hhalf := STAmount.ofNumber_integral_within_half nt x st hnt hx hneg hof
  obtain ⟨-, ⟨k, hk⟩, -, -⟩ := STAmount.roundToNumericType_int_grid nt hnt x T .to_nearest s hx h0 (Or.inl rfl) hok
  rw [← hT, abs_le] at hhalf
  have hk1 : (k : ℚ) < 1 := by rw [← hk]; linarith [hhalf.2]
  have : k = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hk1)
  rw [hk, this]; simp

/-- An integral rounding of a value at least zero is at most the value's ceiling. -/
private lemma STAmount.roundToNumericType_int_le_ceil (nt : NumericType) (hnt : nt.isIntegral = true)
    (x T : Number) (s : Option ℤ) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hok : STAmount.roundToNumericType nt x .to_nearest s = .ok T) : T.toRat ≤ (⌈x.toRat⌉ : ℚ) := by
  obtain ⟨hgf, -, -, -⟩ := STAmount.roundToNumericType_int_grid nt hnt x T .to_nearest s hx h0 (Or.inl rfl) hok
  have hc0 : 0 ≤ ⌈x.toRat⌉ := Int.ceil_nonneg h0
  have := hgf.upper ⌈x.toRat⌉.toNat (by
    rw [zpow_zero, mul_one]
    have : ((⌈x.toRat⌉.toNat : ℕ) : ℚ) = (⌈x.toRat⌉ : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hc0
    rw [this]; exact Int.le_ceil _)
  rw [zpow_zero, mul_one] at this
  have h2 : ((⌈x.toRat⌉.toNat : ℕ) : ℚ) = (⌈x.toRat⌉ : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hc0
  rwa [h2] at this

private lemma Loan.reamortized_interestDue_nonneg_int (l : Loan) (opc : PaymentComponents)
    {rate v18 pinnedP G pm po interest tvo tvo' mfo io : Number} {st th th2 st15 s11 s5 : LoanState}
    {de : LoanStateDeltas} {props : LoanProperties} {g : TER}
    (hint' : l.broker.numericType.isIntegral = true)
    (hmax : l.broker.numericType.maxValue.toNat ≤ maxRep.toNat) (hls0 : l.loanScale = 0)
    (hT : l.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ l.loanScale) (hi : 0 ≤ l.toExact.interestDue)
    (hpd : opc.principalDelta.isNormalized) (hrate : l.periodicRate = .ok rate) (hst : l.state = .ok st)
    (hth : LoanState.buildTheoretical l.periodicPayment rate l.paymentRemaining l.broker.managementFeeRate = .ok th)
    (hde : st.calculateDeltas th = .ok de)
    (h18 : th.principalOutstanding.operator_sub opc.principalDelta .to_nearest = .ok v18)
    (hprops : computeLoanPropertiesFromPeriodicRate (v18.max Number.zero) rate l.paymentRemaining
      l.broker.managementFeeRate l.broker.numericType l.loanScale = .ok props)
    (hth2 : LoanState.buildTheoretical props.periodicPayment rate l.paymentRemaining
      l.broker.managementFeeRate = .ok th2)
    (h15 : th2.addDeltas de = .ok st15)
    (hpin : st.principalOutstanding.operator_sub opc.principalDelta .to_nearest = .ok pinnedP)
    (hG : st15.valueOutstanding.operator_sub pinnedP .to_nearest = .ok G)
    (hpm : tenthBipsOfValue G l.broker.managementFeeRate.toTenthBips32 .to_nearest = .ok pm)
    (h11 : LoanState.build st15.valueOutstanding pinnedP pm = .ok s11)
    (hpo : roundAndClamp s11.principalOutstanding st.principalOutstanding .upward l.broker.numericType
      l.loanScale = .ok po)
    (hint : s11.grossInterestOutstanding = .ok interest)
    (htvo : po.operator_add interest .to_nearest = .ok tvo)
    (htvo' : roundAndClamp tvo st.valueOutstanding .upward l.broker.numericType l.loanScale = .ok tvo')
    (hmfo : roundAndClamp s11.managementFeeDue st.managementFeeDue .to_nearest l.broker.numericType
      l.loanScale = .ok mfo)
    (h5 : LoanState.build tvo' po mfo = .ok s5) (hio : s5.grossInterestOutstanding = .ok io)
    (hguard : LoanProperties.amortizationGuards
      { props with totalValueOutstanding := tvo', principalOutstanding := po
                   managementFeeOutstanding := mfo, loanScale := l.loanScale }
      po (io.operator_ne Number.zero) l.paymentRemaining l.broker.numericType = .ok g)
    (hg : ¬(!g.isTesSuccess) = true)
    (hsig : ¬(decide (props.periodicPayment.signum ≤ 0) || decide (tvo'.signum ≤ 0) ||
      decide (mfo.signum < 0)) = true) :
    0 ≤ s5.valueOutstanding.toRat - s5.principalOutstanding.toRat - s5.managementFeeDue.toRat := by
  have hs := Loan.loanScale_bounds l
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨by omega, by omega⟩
  set u : ℚ := 10 ^ l.loanScale with hu_def
  have hu : 0 < u := zpow_pos (by norm_num) _
  have hgb : (2 : ℚ) ^ 63 * u > 0 := by positivity
  have hu1 : u = 1 := by rw [hu_def, hls0, zpow_zero]
  obtain ⟨gT, gP, gM, -, hP0, hM0, -⟩ := Loan.outstanding_grid l
  obtain ⟨hsT, hsP, hsM, -⟩ := LoanState.build_ok hst
  rw [hsP] at hpo hpin
  rw [hsT] at htvo'
  rw [hsM] at hmfo
  have hiD : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat :=
    hi
  -- the committed amounts, rounded at LoanScale and clamped
  obtain ⟨rpo, hrpo, rfl⟩ := roundAndClamp_ok hpo
  obtain ⟨rtv, hrtv, rfl⟩ := roundAndClamp_ok htvo'
  obtain ⟨rmf, hrmf, rfl⟩ := roundAndClamp_ok hmfo
  have grpo := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr (fun _ => le_of_eq hls0) hrpo
  have grtv := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr (fun _ => le_of_eq hls0) hrtv
  have grmf := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr (fun _ => le_of_eq hls0) hrmf
  have gpo := Number.OnGrid.clamp grpo (Number.OnGrid.zero _) gP
  have gtv := Number.OnGrid.clamp grtv (Number.OnGrid.zero _) gT
  have gmf := Number.OnGrid.clamp grmf (Number.OnGrid.zero _) gM
  obtain ⟨h5T, h5P, h5M, w5, hw5, hi5⟩ := LoanState.build_ok h5
  rw [h5T, h5P, h5M]
  -- every committed amount is between zero and the loan's own
  have hPT : l.principalOutstanding.toRat ≤ l.totalValueOutstanding.toRat := by linarith
  have hT16 : l.totalValueOutstanding.toRat ≤ 2 * 10 ^ 16 * u := by linarith
  have hclamp : ∀ (r cap : Number), r.isNormalized → cap.isNormalized → 0 ≤ cap.toRat →
      0 ≤ (Number.clamp r Number.zero cap).toRat ∧ (Number.clamp r Number.zero cap).toRat ≤ cap.toRat := by
    intro r cap hrn hcn hc0
    rcases Number.clamp_zero_cases r cap hrn hcn with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨h1, h2, he⟩
    · rw [he, Number.toRat_zero]; exact ⟨le_refl _, hc0⟩
    · rw [he]; exact ⟨hc0, le_refl _⟩
    · rw [he]; exact ⟨h1, h2⟩
  obtain ⟨vpo0, vpoP⟩ := hclamp rpo _ grpo.1 gP.1 hP0
  obtain ⟨vmf0, vmfM⟩ := hclamp rmf _ grmf.1 gM.1 hM0
  obtain ⟨vtv0, vtvT⟩ := hclamp rtv _ grtv.1 gT.1 (by linarith)
  generalize hpo_def : Number.clamp rpo Number.zero l.principalOutstanding = po at *
  generalize htvo'_def : Number.clamp rtv Number.zero l.totalValueOutstanding = tvo' at *
  generalize hmfo_def : Number.clamp rmf Number.zero l.managementFeeOutstanding = mfo at *
  have hbsub : ∀ x y : Number, 0 ≤ x.toRat → x.toRat ≤ 2 * 10 ^ 16 * u → 0 ≤ y.toRat → y.toRat ≤ 2 * 10 ^ 16 * u →
      |x.toRat - y.toRat| < 2 ^ 63 * u := by
    intro x y h1 h2 h3 h4
    rw [abs_lt]; constructor <;> nlinarith
  have htvpos : 0 < tvo'.toRat := by
    have hn : ¬ (tvo'.signum ≤ 0) := by
      intro hle; apply hsig; simp [hle]
    rw [signum_eq _ gtv.1] at hn
    split_ifs at hn with h1 h2
    · exact h1
    · exact absurd (show (-1 : Int) ≤ 0 by decide) hn
    · exact absurd (show (0 : Int) ≤ 0 by decide) hn
  -- the amortization check: a nonzero interest must be positive, so the new value is at least the principal
  have hw5v : w5.toRat = tvo'.toRat - po.toRat :=
    Number.OnGrid.sub_toRat gtv gpo hs (hbsub _ _ vtv0 (by linarith) vpo0 (by linarith)) hw5
  have gw5 := Number.OnGrid.sub gtv gpo hs hw5
  have hi5v : s5.interestDue.toRat = w5.toRat - mfo.toRat := by
    refine Number.OnGrid.sub_toRat gw5 gmf hs ?_ hi5
    rw [hw5v, abs_lt]; constructor <;> nlinarith
  have gi5 := Number.OnGrid.sub gw5 gmf hs hi5
  unfold LoanState.grossInterestOutstanding at hio
  rw [h5M] at hio
  have hiov : io.toRat = tvo'.toRat - po.toRat := by
    rw [Number.OnGrid.add_toRat gi5 gmf hs (by rw [hi5v, hw5v, abs_lt]; constructor <;> nlinarith) hio, hi5v, hw5v]
    ring
  have gio := Number.OnGrid.add gi5 gmf hs hio
  have hpo_le : po.toRat ≤ tvo'.toRat := by
    by_contra hlt
    push Not at hlt
    have hexp : io.operator_ne Number.zero = true :=
      (operator_ne_iff _ _ gio.1 Number.zero_isNormalized).mpr (by rw [hiov, Number.toRat_zero]; linarith)
    rw [hexp] at hguard
    obtain ⟨ti, hti, hpos⟩ := LoanProperties.amortizationGuards_interest hguard (by simpa using hg)
    have htiv := Number.OnGrid.sub_toRat gtv gpo hs (hbsub _ _ vtv0 (by linarith) vpo0 (by linarith)) hti
    have gti := Number.OnGrid.sub gtv gpo hs hti
    rw [signum_eq _ gti.1] at hpos
    split_ifs at hpos with h1 h2
    · linarith
    · exact absurd hpos (by decide)
    · exact absurd hpos (by decide)
  -- with no management fee left the guard is enough
  rcases eq_or_lt_of_le vmf0 with hm0 | hmpos
  · rw [← hm0]; linarith
  -- a value clamped at the old total owes at least the old interest
  rcases Number.clamp_zero_cases rtv _ grtv.1 gT.1 with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨h1, _, he⟩
  · rw [← htvo'_def, he, Number.toRat_zero] at htvpos; exact absurd htvpos (lt_irrefl 0)
  · rw [← htvo'_def, he]; linarith
  have htv_eq : tvo'.toRat = rtv.toRat := by rw [← htvo'_def, he]
  obtain ⟨hmfo_le, hrmf_pos⟩ : mfo.toRat ≤ rmf.toRat ∧ 0 < rmf.toRat := by
    have hmpos' : 0 < mfo.toRat := hmpos
    rcases Number.clamp_zero_cases rmf _ grmf.1 gM.1 with ⟨_, he⟩ | ⟨h1, _, he⟩ | ⟨_, _, he⟩
    · have he' : mfo = Number.zero := by rw [← hmfo_def, he]
      rw [he', Number.toRat_zero] at hmpos'; exact absurd hmpos' (lt_irrefl 0)
    · have he' : mfo = l.managementFeeOutstanding := by rw [← hmfo_def, he]
      rw [he'] at hmpos' ⊢; exact ⟨h1.le, by linarith⟩
    · have he' : mfo = rmf := by rw [← hmfo_def, he]
      rw [he'] at hmpos' ⊢; exact ⟨le_refl _, hmpos'⟩
  -- the pinned state: its interestDue is `G - pm` and its fee is `pm`
  obtain ⟨-, -, h11M, w11, hw11, hi11⟩ := LoanState.build_ok h11
  have hw11G : w11 = G := by rw [hG] at hw11; exact (Except.ok.inj hw11).symm
  rw [hw11G] at hi11
  rw [h11M] at hrmf
  unfold LoanState.grossInterestOutstanding at hint
  rw [h11M] at hint
  have hGN := Loan.reamortization_gross_normalized l opc hpd hrate hst hth hde h18 hprops hth2 h15
    (by rw [hsP]; exact hpin) hG
  have hpmN := tenthBipsOfValue_normalized hGN hpm
  have hi11N := operator_sub_isNormalized_to_nearest_sz _ _ _ hGN hpmN hi11
  have hintN := operator_add_isNormalized_to_nearest_sz _ _ _ hi11N hpmN hint
  have htvoN := operator_add_isNormalized_to_nearest_sz _ _ _ gpo.1 hintN htvo
  -- a fee rounding to a positive amount is at least 0.49 units
  have hpm_pos : 0 < pm.toRat := by
    by_contra hc
    push Not at hc
    have := STAmount.roundToNumericType_int_nonpos _ hint' hmax _ _ _ _ hpmN hc hrmf
    linarith
  have hpm_big : 49 / 100 * u ≤ pm.toRat := by
    by_contra hc
    push Not at hc
    have := STAmount.roundToNumericType_int_small _ hint' hmax _ _ _ hpmN hpm_pos.le (by rw [hu1] at hc; linarith)
      hrmf
    linarith
  -- the fee is at most a tenth of the interest it is taken from
  obtain ⟨hG0, hpm_le⟩ := tenthBipsOfValue_pos_le hGN hpm hpm_pos
  have hrate : ((l.broker.managementFeeRate.toTenthBips32).toNat : ℚ) ≤ 10000 := by
    have := l.broker.exact.managementFeeRate_cap
    have h' : l.broker.managementFeeRate.toTenthBips32.toNat = l.broker.managementFeeRate.toNat := by
      simp [TenthBips16.toTenthBips32]
    rw [h']
    exact_mod_cast this
  have hpm_le' : pm.toRat ≤ G.toRat / 10 * (1 + 1 / 10 ^ 18) ^ 2 := by
    refine le_trans hpm_le ?_
    have : G.toRat * ((l.broker.managementFeeRate.toTenthBips32).toNat : ℚ) ≤ G.toRat * 10000 :=
      mul_le_mul_of_nonneg_left hrate hG0.le
    have hf : (0 : ℚ) ≤ (1 + 1 / 10 ^ 18) ^ 2 := by positivity
    nlinarith
  have hpm_lin : pm.toRat ≤ G.toRat / 10 + G.toRat / 10 ^ 17 := by
    have hc : (1 + 1 / 10 ^ 18 : ℚ) ^ 2 ≤ 1 + 10 / 10 ^ 18 := by norm_num
    have := mul_le_mul_of_nonneg_left hc (show (0 : ℚ) ≤ G.toRat / 10 by positivity)
    linarith
  -- the pinned interestDue is at least the fee, so it is nonzero and rounds within its relative error
  have hR11 := operator_sub_rounded_to_nearest G pm _ hGN hpmN hi11
  have hiD_ge : pm.toRat ≤ s11.interestDue.toRat :=
    Number.roundsToRepresentable_ge _ _ hR11 _ hpmN (by linarith)
  have hGm := (hGN.mantissaBounds_nat (Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hG0)))
  have hW11 := operator_sub_rounds_to_nearest G pm _ hGN hpmN
    (Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hG0))
    (Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hpm_pos))
    (fun h => by have := (operator_eq_iff _ _ hGN hpmN).mp h; linarith) hi11
    (Number.mantissa_ne_zero_of_toRat_ne_zero (by linarith))
  have hWint := operator_add_nonneg_rounds _ _ _ hi11N hpmN (by linarith) hpm_pos.le hint
  have hint0 : 0 ≤ interest.toRat := by
    have h := (abs_le.mp (show |interest.toRat - (s11.interestDue.toRat + pm.toRat)| ≤
      |s11.interestDue.toRat + pm.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) from hWint)).1
    rw [abs_of_nonneg (by linarith)] at h
    have he : (0 : ℚ) ≤ 6 / (2 ^ 63 - 3 : ℚ) ∧ 6 / (2 ^ 63 - 3 : ℚ) ≤ 1 := by norm_num
    have := mul_le_mul_of_nonneg_left he.2 (show (0 : ℚ) ≤ s11.interestDue.toRat + pm.toRat by linarith)
    linarith
  have hWtvo := operator_add_nonneg_rounds _ _ _ gpo.1 hintN vpo0 hint0 htvo
  have htvo0 : 0 ≤ tvo.toRat := by
    have h := (abs_le.mp (show |tvo.toRat - (po.toRat + interest.toRat)| ≤
      |po.toRat + interest.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) from hWtvo)).1
    rw [abs_of_nonneg (by linarith)] at h
    have he : (0 : ℚ) ≤ 6 / (2 ^ 63 - 3 : ℚ) ∧ 6 / (2 ^ 63 - 3 : ℚ) ≤ 1 := by norm_num
    have := mul_le_mul_of_nonneg_left he.2 (show (0 : ℚ) ≤ po.toRat + interest.toRat by linarith)
    linarith
  have htvo_le : tvo.toRat ≤ tvo'.toRat := by
    rw [htv_eq]
    exact (STAmount.roundToNumericType_int_grid _ hint' _ _ _ _ htvoN htvo0 (Or.inr (Or.inl rfl)) hrtv).2.2.1 rfl
  -- the rounding errors stay far below a unit, so the new value keeps at least the fee above the principal
  have key : pm.toRat ≤ tvo.toRat - po.toRat := by
    have e1 := abs_le.mp (show |s11.interestDue.toRat - (G.toRat - pm.toRat)| ≤
      |G.toRat - pm.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) from hW11)
    have e2 := abs_le.mp (show |interest.toRat - (s11.interestDue.toRat + pm.toRat)| ≤
      |s11.interestDue.toRat + pm.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) from hWint)
    have e3 := abs_le.mp (show |tvo.toRat - (po.toRat + interest.toRat)| ≤
      |po.toRat + interest.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) from hWtvo)
    rw [abs_of_pos (by linarith : (0 : ℚ) < G.toRat - pm.toRat)] at e1
    rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ s11.interestDue.toRat + pm.toRat)] at e2
    rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ po.toRat + interest.toRat)] at e3
    have hsum : po.toRat + interest.toRat ≤ 4 * 10 ^ 16 * u := by linarith [e3.1]
    have h1 : (G.toRat - pm.toRat) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) ≤ s11.interestDue.toRat := by linarith [e1.1]
    have h2 : (s11.interestDue.toRat + pm.toRat) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) ≤ interest.toRat := by
      linarith [e2.1]
    have h3 : interest.toRat - 4 * 10 ^ 16 * u * (6 / (2 ^ 63 - 3 : ℚ)) ≤ tvo.toRat - po.toRat := by
      have := mul_le_mul_of_nonneg_right hsum (show (0 : ℚ) ≤ 6 / (2 ^ 63 - 3) by norm_num)
      linarith [e3.1]
    have h4 : (G.toRat - pm.toRat) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) +
        pm.toRat * (1 - 6 / (2 ^ 63 - 3 : ℚ)) ≤ interest.toRat := by
      have := mul_le_mul_of_nonneg_right h1 (show (0 : ℚ) ≤ 1 - 6 / (2 ^ 63 - 3) by norm_num)
      linarith
    linarith
  -- the fee is at most its next grid point, which the new interest covers
  have hmfo_ceil : mfo.toRat ≤ (⌈pm.toRat / u⌉ : ℚ) * u := by
    refine le_trans hmfo_le ?_
    rw [hu1, div_one, mul_one]
    exact STAmount.roundToNumericType_int_le_ceil _ hint' _ _ _ hpmN hpm_pos.le hrmf
  obtain ⟨a, ha⟩ := gtv.2
  obtain ⟨b, hb⟩ := gpo.2
  have hj : (⌈pm.toRat / u⌉ : ℚ) ≤ ((a - b : ℤ) : ℚ) := by
    have : pm.toRat / u ≤ ((a - b : ℤ) : ℚ) := by
      rw [div_le_iff₀ hu]
      push_cast
      rw [sub_mul, ← ha, ← hb]
      linarith
    exact_mod_cast Int.ceil_le.mpr (by exact_mod_cast this)
  have hab : ((a - b : ℤ) : ℚ) * u = tvo'.toRat - po.toRat := by push_cast; rw [sub_mul, ← ha, ← hb]
  have := mul_le_mul_of_nonneg_right hj hu.le
  linarith

/-- A re-amortization that passes keeps interestDue at least zero on an XRP or MPT loan whose interestDue is
at least zero and that owes at most `10^16 + 1` units, for an overpayment with a normalized principal part. -/
lemma Loan.tryOverpayment_interestDue_nonneg_int (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hint : l.broker.numericType.isIntegral = true) (hmax : l.broker.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hls0 : l.loanScale = 0) (hT : l.totalValueOutstanding.toRat ≤ (10 ^ 16 + 1) * 10 ^ l.loanScale)
    (hi : 0 ≤ l.toExact.interestDue) (hpd : opc.principalDelta.isNormalized)
    (h : Loan.tryOverpayment l opc = .ok (some re)) :
    0 ≤ re.state.valueOutstanding.toRat - re.state.principalOutstanding.toRat - re.state.managementFeeDue.toRat := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  exact Loan.reamortized_interestDue_nonneg_int l opc hint hmax hls0 hT hi hpd ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end XRPL.Model.Lending
