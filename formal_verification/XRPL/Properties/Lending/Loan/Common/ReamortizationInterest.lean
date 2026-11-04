import XRPL.Properties.Lending.Loan.Common.Amortization
import XRPL.Properties.Lending.Loan.Common.PayUnits
import XRPL.Properties.Lending.Loan.Common.RoundToNearest
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Properties.Protocol.Common.TenthBips
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Sub.RoundsWithin
import XRPL.Properties.Vault.Proofs.Support.NumberFacts

/-! # A re-amortization keeps interestDue at least zero

The re-amortized value covers the new principal and the new management fee, which is at most a tenth of the new
interest, and every rounding on the way stays far below one LoanScale unit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private Loan.tryOverpayment Loan.overpaymentComponents roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay

/-- A state built from three amounts holds them, and its interestDue is their difference. -/
lemma LoanState.build_ok {a b c : Number} {st : LoanState} (h : LoanState.build a b c = .ok st) :
    st.valueOutstanding = a ∧ st.principalOutstanding = b ∧ st.managementFeeDue = c ∧
      ∃ v, a.operator_sub b .to_nearest = .ok v ∧ v.operator_sub c .to_nearest = .ok st.interestDue := by
  unfold LoanState.build at h
  obtain ⟨v, hv, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨i, hi, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  exact ⟨rfl, rfl, rfl, v, hv, hi⟩

/-- A state built from three normalized amounts has normalized fields. -/
private lemma LoanState.build_normalized {a b c : Number} {st : LoanState} (ha : a.isNormalized)
    (hb : b.isNormalized) (hc : c.isNormalized) (h : LoanState.build a b c = .ok st) :
    st.valueOutstanding.isNormalized ∧ st.principalOutstanding.isNormalized ∧ st.interestDue.isNormalized ∧
      st.managementFeeDue.isNormalized := by
  obtain ⟨h1, h2, h3, v, hv, hi⟩ := LoanState.build_ok h
  rw [h1, h2, h3]
  exact ⟨ha, hb, operator_sub_isNormalized_to_nearest_sz _ _ _
    (operator_sub_isNormalized_to_nearest_sz _ _ _ ha hb hv) hc hi, hc⟩

/-- The principal a periodic payment implies is normalized. -/
private lemma loanPrincipalFromPeriodicPayment_normalized {pp rate r : Number} {n : UInt32}
    (hpp : pp.isNormalized) (hrate : rate.isNormalized) (h : loanPrincipalFromPeriodicPayment pp rate n = .ok r) :
    r.isNormalized := by
  unfold loanPrincipalFromPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Number.zero_isNormalized
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · exact Number.operator_mul_isNormalized _ _ r _ hpp (Number.ofInt64_isNormalized _) h
    · obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
      exact Number.operator_div_isNormalized _ _ r _ hpp
        (computePaymentFactor_isNormalized rate _ n f hrate (Number.ofInt64_isNormalized _) hf) h

/-- The theoretical state of a schedule with a normalized payment and rate has normalized fields. -/
private lemma LoanState.buildTheoretical_normalized {pp rate : Number} {n : UInt32} {mgmt : TenthBips16}
    {st : LoanState} (hpp : pp.isNormalized) (hrate : rate.isNormalized)
    (h : LoanState.buildTheoretical pp rate n mgmt = .ok st) :
    st.valueOutstanding.isNormalized ∧ st.principalOutstanding.isNormalized ∧ st.interestDue.isNormalized ∧
      st.managementFeeDue.isNormalized := by
  unfold LoanState.buildTheoretical at h
  dsimp only at h
  split at h
  · obtain rfl := (Except.ok.inj h).symm
    exact ⟨Number.zero_isNormalized, Number.zero_isNormalized, Number.zero_isNormalized, Number.zero_isNormalized⟩
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨tv, htv, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨p, hp, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨g, hg, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨m, hm, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨i, hi, h⟩ := bind_ok_peel _ _ _ h
    obtain rfl := (Except.ok.inj h).symm
    have htvn := Number.operator_mul_isNormalized _ _ _ _ hpp (Number.ofInt64_isNormalized _) htv
    have hpn := loanPrincipalFromPeriodicPayment_normalized hpp hrate hp
    have hgn := operator_sub_isNormalized_to_nearest_sz _ _ _ htvn hpn hg
    have hmn := tenthBipsOfValue_normalized hgn hm
    exact ⟨htvn, hpn, operator_sub_isNormalized_to_nearest_sz _ _ _ hgn hmn hi, hmn⟩

/-- The deltas between two states with normalized fields are normalized. -/
private lemma LoanState.calculateDeltas_normalized {x y : LoanState} {d : LoanStateDeltas}
    (hx : x.principalOutstanding.isNormalized ∧ x.interestDue.isNormalized ∧ x.managementFeeDue.isNormalized)
    (hy : y.principalOutstanding.isNormalized ∧ y.interestDue.isNormalized ∧ y.managementFeeDue.isNormalized)
    (h : x.calculateDeltas y = .ok d) :
    d.principal.isNormalized ∧ d.interest.isNormalized ∧ d.managementFee.isNormalized := by
  unfold LoanState.calculateDeltas at h
  obtain ⟨p, hp, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨i, hi, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨m, hm, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ hx.1 hy.1 hp,
    operator_sub_isNormalized_to_nearest_sz _ _ _ hx.2.1 hy.2.1 hi,
    operator_sub_isNormalized_to_nearest_sz _ _ _ hx.2.2 hy.2.2 hm⟩

/-- Adding normalized deltas to a normalized value keeps it normalized. -/
private lemma LoanState.addDeltas_value_normalized {x y : LoanState} {d : LoanStateDeltas}
    (hx : x.valueOutstanding.isNormalized)
    (hd : d.principal.isNormalized ∧ d.interest.isNormalized ∧ d.managementFee.isNormalized)
    (h : x.addDeltas d = .ok y) : y.valueOutstanding.isNormalized := by
  unfold LoanState.addDeltas LoanStateDeltas.total at h
  obtain ⟨t, ht, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pi, hpi, ht⟩ := bind_ok_peel _ _ _ ht
  obtain ⟨tv, htv, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  have hpin := operator_add_isNormalized_to_nearest_sz _ _ _ hd.1 hd.2.1 hpi
  exact operator_add_isNormalized_to_nearest_sz _ _ _ hx
    (operator_add_isNormalized_to_nearest_sz _ _ _ hpin hd.2.2 ht) htv

/-- The periodic payment a re-amortization computes from a normalized principal is normalized. -/
private lemma computeLoanPropertiesFromPeriodicRate_periodicPayment_normalized {principal rate : Number}
    {n : UInt32} {mgmt : TenthBips16} {nt : NumericType} {minScale : Int} {props : LoanProperties}
    (hp : principal.isNormalized) (hrate : rate.isNormalized)
    (h : computeLoanPropertiesFromPeriodicRate principal rate n mgmt nt minScale = .ok props) :
    props.periodicPayment.isNormalized := by
  unfold computeLoanPropertiesFromPeriodicRate at h
  obtain ⟨pp, hpp, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
  simp only [pure, Except.pure, Except.ok.injEq] at h
  rw [← h]
  exact loanPeriodicPayment_isNormalized _ _ _ _ hp hrate hpp

/-- A positive tenth-bips share comes from a positive value and is at most the rate's share of it, up to two
19-digit roundings. -/
lemma tenthBipsOfValue_pos_le {G pm : Number} {rate : TenthBips32} (hG : G.isNormalized)
    (h : tenthBipsOfValue G rate .to_nearest = .ok pm) (hpm : 0 < pm.toRat) :
    0 < G.toRat ∧ pm.toRat ≤ G.toRat * rate.toNat / 100000 * (1 + 1 / 10 ^ 18) ^ 2 := by
  obtain ⟨hrn, hrv⟩ := TenthBips32.toNumber_facts rate
  obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  have hu : ((kTenthBipsPerUnity.toNat : ℕ) : ℚ) = 100000 := by rfl
  have heq : tenthBipsOfValue G rate .to_nearest = (G.operator_mul rate.toNumber .to_nearest) >>=
      (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨p, hp, h⟩ := bind_ok_peel _ _ _ h
  have hpn := Number.operator_mul_isNormalized _ _ _ _ hG hrn hp
  have hpm0 : pm.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hpm)
  have hp0 : p.mantissa_ ≠ 0 := (operator_div_operands_ne_zero hpn hun h hpm0).1
  have hdiv : |pm.toRat - p.toRat / 100000| ≤ |p.toRat / 100000| * (6 / ((2 : ℚ) ^ 63 - 3)) := by
    have := operator_div_rounds_to_nearest p _ pm hpn hun h hpm0
    rw [huv, hu] at this
    exact this
  have hmul : |p.toRat - G.toRat * rate.toNat| ≤ |G.toRat * rate.toNat| * (5 / (2 ^ 63 + 7 : ℚ)) := by
    have := operator_mul_rounds_to_nearest G _ p hG hrn hp hp0
    rw [hrv] at this
    exact this
  have he1 : (6 / ((2 : ℚ) ^ 63 - 3)) ≤ 1 / 10 ^ 18 := by norm_num
  have he2 : (5 / (2 ^ 63 + 7 : ℚ)) ≤ 1 / 10 ^ 18 := by norm_num
  have hr0 : (0 : ℚ) ≤ rate.toNat := by positivity
  -- the quotient is positive, so the product is positive
  have hq : 0 < p.toRat := by
    by_contra hc
    push Not at hc
    have hq0 : p.toRat / 100000 ≤ 0 := by linarith
    rw [abs_of_nonpos hq0] at hdiv
    have := (abs_le.mp hdiv).2
    nlinarith
  have hGr : 0 < G.toRat * rate.toNat := by
    by_contra hc
    push Not at hc
    rw [abs_of_nonpos hc] at hmul
    have := (abs_le.mp hmul).2
    nlinarith
  have hG0 : 0 < G.toRat := by
    by_contra hc
    push Not at hc
    nlinarith
  refine ⟨hG0, ?_⟩
  rw [abs_of_pos (by positivity : (0 : ℚ) < p.toRat / 100000)] at hdiv
  rw [abs_of_pos hGr] at hmul
  have h1 := (abs_le.mp hdiv).2
  have h2 := (abs_le.mp hmul).2
  have h3 : pm.toRat ≤ p.toRat / 100000 * (1 + 1 / 10 ^ 18) := by nlinarith
  have h4 : p.toRat ≤ G.toRat * rate.toNat * (1 + 1 / 10 ^ 18) := by nlinarith
  calc pm.toRat ≤ p.toRat / 100000 * (1 + 1 / 10 ^ 18) := h3
    _ ≤ G.toRat * rate.toNat * (1 + 1 / 10 ^ 18) / 100000 * (1 + 1 / 10 ^ 18) := by
        gcongr
    _ = G.toRat * rate.toNat / 100000 * (1 + 1 / 10 ^ 18) ^ 2 := by ring

/-- A passing amortization check that expects interest has a positive interest. -/
private lemma LoanProperties.amortizationGuards_interest {p : LoanProperties} {principal : Number} {n : UInt32}
    {nt : NumericType} {g : TER} (h : p.amortizationGuards principal true n nt = .ok g) (hg : g.isTesSuccess = true) :
    ∃ ti, p.totalValueOutstanding.operator_sub principal .to_nearest = .ok ti ∧ 0 < ti.signum := by
  unfold LoanProperties.amortizationGuards at h
  obtain ⟨ti, hti, h⟩ := bind_ok_peel _ _ _ h
  refine ⟨ti, hti, ?_⟩
  by_contra hc
  push Not at hc
  simp only [Bool.true_and, decide_eq_true_eq, hc, ↓reduceIte] at h
  obtain rfl := (Except.ok.inj h).symm
  exact absurd hg (by decide)

/-- A rounded value clamped into `[0, cap]` is the rounded value, zero below it, or the cap above it. -/
lemma roundAndClamp_ok {value cap y : Number} {mode : rounding_mode} {nt : NumericType} {s : Int}
    (h : roundAndClamp value cap mode nt s = .ok y) :
    ∃ r, STAmount.roundToNumericType nt value mode (some s) = .ok r ∧ y = Number.clamp r Number.zero cap := by
  unfold roundAndClamp at h
  obtain ⟨r, hr, h⟩ := bind_ok_peel _ _ _ h
  exact ⟨r, hr, (Except.ok.inj h).symm⟩

/-- The three outcomes of a clamp into `[0, cap]`. -/
lemma Number.clamp_zero_cases (x cap : Number) (hx : x.isNormalized) (hcap : cap.isNormalized) :
    (x.toRat < 0 ∧ Number.clamp x Number.zero cap = Number.zero) ∨
      (cap.toRat < x.toRat ∧ 0 ≤ x.toRat ∧ Number.clamp x Number.zero cap = cap) ∨
      (0 ≤ x.toRat ∧ x.toRat ≤ cap.toRat ∧ Number.clamp x Number.zero cap = x) := by
  unfold Number.clamp
  by_cases h1 : x.operator_lt Number.zero = true
  · left
    have := (operator_lt_iff _ _ hx Number.zero_isNormalized).mp h1
    rw [Number.toRat_zero] at this
    exact ⟨this, by rw [if_pos h1]⟩
  · have h1' : 0 ≤ x.toRat := by
      have := (operator_lt_eq_false_iff _ _ hx Number.zero_isNormalized).mp (by simpa using h1)
      rwa [Number.toRat_zero] at this
    rw [if_neg h1]
    by_cases h2 : cap.operator_lt x = true
    · right; left
      exact ⟨(operator_lt_iff _ _ hcap hx).mp h2, h1', by rw [if_pos h2]⟩
    · right; right
      exact ⟨h1', (operator_lt_eq_false_iff _ _ hcap hx).mp (by simpa using h2), by rw [if_neg h2]⟩

/-- A lawful fractional loan's amounts are on the LoanScale grid. TotalValueOutstanding and ManagementFeeOutstanding
are below `10^16` units, PrincipalOutstanding and ManagementFeeOutstanding are not negative. -/
private lemma Loan.outstanding_units (l : Loan) (hfrac : l.broker.numericType = .fractional) :
    Number.OnGrid l.loanScale l.totalValueOutstanding ∧ Number.OnGrid l.loanScale l.principalOutstanding ∧
      Number.OnGrid l.loanScale l.managementFeeOutstanding ∧
      l.totalValueOutstanding.toRat ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ l.loanScale ∧
      l.managementFeeOutstanding.toRat ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ l.loanScale ∧
      0 ≤ l.principalOutstanding.toRat ∧ 0 ≤ l.managementFeeOutstanding.toRat := by
  have heg := Loan.grid l
  have hb : l.toExact.numericType.mantissaBound = 10 ^ 16 := by
    show l.broker.numericType.mantissaBound = _
    rw [hfrac]; rfl
  have hp : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  obtain ⟨t, ht, htv⟩ := heg.totalValueOutstanding_atExponent
  obtain ⟨p, -, hpv⟩ := heg.principalOutstanding_atExponent
  obtain ⟨m, hm, hmv⟩ := heg.managementFeeOutstanding_atExponent
  rw [hb] at ht hm
  simp only [RawLoan.toExact] at htv hpv hmv
  have hle : ∀ k : ℕ, k < 10 ^ 16 → (k : ℚ) * 10 ^ l.loanScale ≤ ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ l.loanScale :=
    fun k hk => mul_le_mul_of_nonneg_right (by exact_mod_cast (show k ≤ 10 ^ 16 - 1 by omega)) hp.le
  refine ⟨⟨l.wf.totalValueOutstanding_norm, t, by rw [htv]; push_cast; rfl⟩,
    ⟨l.wf.principalOutstanding_norm, p, by rw [hpv]; push_cast; rfl⟩,
    ⟨l.wf.managementFeeOutstanding_norm, m, by rw [hmv]; push_cast; rfl⟩, ?_, ?_, ?_, ?_⟩
  · show l.toRawLoan.totalValueOutstanding.toRat ≤ _; rw [htv]; exact hle t ht
  · show l.toRawLoan.managementFeeOutstanding.toRat ≤ _; rw [hmv]; exact hle m hm
  · show 0 ≤ l.toRawLoan.principalOutstanding.toRat; rw [hpv]; positivity
  · show 0 ≤ l.toRawLoan.managementFeeOutstanding.toRat; rw [hmv]; positivity

/-- The gross interest a re-amortization pins is normalized. -/
private lemma Loan.reamortization_gross_normalized (l : Loan) (opc : PaymentComponents)
    {rate v18 pinnedP G : Number} {st th th2 st15 : LoanState} {de : LoanStateDeltas} {props : LoanProperties}
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
    (hG : st15.valueOutstanding.operator_sub pinnedP .to_nearest = .ok G) : G.isNormalized := by
  have hrateN : rate.isNormalized := loanPeriodicRate_isNormalized _ _ _ hrate
  have hstN := LoanState.build_normalized l.wf.totalValueOutstanding_norm l.wf.principalOutstanding_norm
    l.wf.managementFeeOutstanding_norm hst
  have hthN := LoanState.buildTheoretical_normalized l.wf.periodicPayment_norm hrateN hth
  have hdeN := LoanState.calculateDeltas_normalized ⟨hstN.2.1, hstN.2.2.1, hstN.2.2.2⟩
    ⟨hthN.2.1, hthN.2.2.1, hthN.2.2.2⟩ hde
  have h18N := operator_sub_isNormalized_to_nearest_sz _ _ _ hthN.2.1 hpd h18
  have hmaxN : (v18.max Number.zero).isNormalized := by
    unfold Number.max; split
    · exact Number.zero_isNormalized
    · exact h18N
  have hppN := computeLoanPropertiesFromPeriodicRate_periodicPayment_normalized hmaxN hrateN hprops
  have hth2N := LoanState.buildTheoretical_normalized hppN hrateN hth2
  have h15N := LoanState.addDeltas_value_normalized hth2N.1 hdeN h15
  have hpinN := operator_sub_isNormalized_to_nearest_sz _ _ _ hstN.2.1 hpd hpin
  exact operator_sub_isNormalized_to_nearest_sz _ _ _ h15N hpinN hG

/-- The re-amortized state owes at least its principal and management fee. The hypotheses are the steps of
`Loan.tryOverpayment`, in order. -/
private lemma Loan.reamortized_interestDue_nonneg (l : Loan) (opc : PaymentComponents)
    {rate v18 pinnedP G pm po interest tvo tvo' mfo io : Number} {st th th2 st15 s11 s5 : LoanState}
    {de : LoanStateDeltas} {props : LoanProperties} {g : TER}
    (hlo : -81 ≤ l.loanScale) (hfrac : l.broker.numericType = .fractional) (hi : 0 ≤ l.toExact.interestDue)
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
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  have hnt : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0 := by rw [hfrac]; intro h; cases h
  set u : ℚ := 10 ^ l.loanScale with hu_def
  have hu : 0 < u := zpow_pos (by norm_num) _
  have hgb : (2 : ℚ) ^ 63 * u > 0 := by positivity
  obtain ⟨gT, gP, gM, hTb, hMb, hP0, hM0⟩ := Loan.outstanding_units l hfrac
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
  rw [hfrac] at hrpo hrtv hrmf
  have grpo := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr (by intro h; cases h) hrpo
  have grtv := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr (by intro h; cases h) hrtv
  have grmf := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr (by intro h; cases h) hrmf
  have gpo := Number.OnGrid.clamp grpo (Number.OnGrid.zero _) gP
  have gtv := Number.OnGrid.clamp grtv (Number.OnGrid.zero _) gT
  have gmf := Number.OnGrid.clamp grmf (Number.OnGrid.zero _) gM
  obtain ⟨h5T, h5P, h5M, w5, hw5, hi5⟩ := LoanState.build_ok h5
  rw [h5T, h5P, h5M]
  -- every committed amount is between zero and the loan's own
  have hPT : l.principalOutstanding.toRat ≤ l.totalValueOutstanding.toRat := by linarith
  have hT16 : l.totalValueOutstanding.toRat ≤ 10 ^ 16 * u := by
    have : ((10 ^ 16 - 1 : ℕ) : ℚ) * u ≤ 10 ^ 16 * u := mul_le_mul_of_nonneg_right (by norm_num) hu.le
    linarith
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
  have hbsub : ∀ x y : Number, 0 ≤ x.toRat → x.toRat ≤ 10 ^ 16 * u → 0 ≤ y.toRat → y.toRat ≤ 10 ^ 16 * u →
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
    have := STAmount.roundToNumericType_frac_nonpos _ _ _ _ hpmN hc hr hrmf
    linarith
  have hpm_big : 49 / 100 * u ≤ pm.toRat := by
    by_contra hc
    push Not at hc
    have := STAmount.roundToNumericType_to_nearest_small _ _ _ hpmN hpm_pos.le hr hc hrmf
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
    exact STAmount.roundToNumericType_frac_upward_ge _ _ _ htvoN htvo0 hr
      (by rw [← htv_eq]; exact ne_of_gt htvpos) hrtv
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
    have hsum : po.toRat + interest.toRat ≤ 2 * 10 ^ 16 * u := by linarith [e3.1]
    have h1 : (G.toRat - pm.toRat) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) ≤ s11.interestDue.toRat := by linarith [e1.1]
    have h2 : (s11.interestDue.toRat + pm.toRat) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) ≤ interest.toRat := by
      linarith [e2.1]
    have h3 : interest.toRat - 2 * 10 ^ 16 * u * (6 / (2 ^ 63 - 3 : ℚ)) ≤ tvo.toRat - po.toRat := by
      have := mul_le_mul_of_nonneg_right hsum (show (0 : ℚ) ≤ 6 / (2 ^ 63 - 3) by norm_num)
      linarith [e3.1]
    have h4 : (G.toRat - pm.toRat) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) * (1 - 6 / (2 ^ 63 - 3 : ℚ)) +
        pm.toRat * (1 - 6 / (2 ^ 63 - 3 : ℚ)) ≤ interest.toRat := by
      have := mul_le_mul_of_nonneg_right h1 (show (0 : ℚ) ≤ 1 - 6 / (2 ^ 63 - 3) by norm_num)
      linarith
    linarith
  -- the fee is at most its next grid point, which the new interest covers
  have hmfo_ceil : mfo.toRat ≤ (⌈pm.toRat / u⌉ : ℚ) * u := by
    by_cases hpmM : pm.toRat < ((10 ^ 16 - 1 : ℕ) : ℚ) * u
    · exact le_trans hmfo_le (STAmount.roundToNumericType_frac_le_ceil _ _ _ _ hpmN hpm_pos.le (Or.inl rfl) hr
        hpmM hrmf)
    · push Not at hpmM
      have : pm.toRat ≤ (⌈pm.toRat / u⌉ : ℚ) * u := by
        calc pm.toRat = pm.toRat / u * u := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (Int.le_ceil _) hu.le
      linarith
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

/-- A re-amortization that passes keeps interestDue at least zero, on a fractional loan whose interestDue is
at least zero, for an overpayment with a normalized principal part. -/
lemma Loan.tryOverpayment_interestDue_nonneg (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hlo : -81 ≤ l.loanScale) (hfrac : l.broker.numericType = .fractional) (hi : 0 ≤ l.toExact.interestDue)
    (hpd : opc.principalDelta.isNormalized) (h : Loan.tryOverpayment l opc = .ok (some re)) :
    0 ≤ re.state.valueOutstanding.toRat - re.state.principalOutstanding.toRat - re.state.managementFeeDue.toRat := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  exact Loan.reamortized_interestDue_nonneg l opc hlo hfrac hi hpd ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

/-- The principal part of an overpayment of a normalized amount is normalized. -/
lemma Loan.overpaymentComponents_principalDelta_normalized (l : Loan) (overpayment : Number) (opc : PaymentComponents)
    (hov : overpayment.isNormalized) (h : Loan.overpaymentComponents l overpayment = .ok opc) :
    opc.principalDelta.isNormalized := by
  unfold Loan.overpaymentComponents at h
  obtain ⟨fee, hfee, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨fee', hfee', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨oi, hoi, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨⟨net, mf⟩, hsplit, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pai, hpai, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨paf, hpaf, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pd, hpd, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  -- the split interest: the rounded interest less its normalized management fee
  unfold roundAndSplitInterest at hsplit
  obtain ⟨i', hi', hsplit⟩ := bind_ok_peel _ _ _ hsplit
  obtain ⟨m', hm', hsplit⟩ := bind_ok_peel _ _ _ hsplit
  obtain ⟨n', hn', hsplit⟩ := bind_ok_peel _ _ _ hsplit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hsplit).symm
  have hi'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hi'
  have hm'n := computeManagementFee_isNormalized _ _ _ _ _ hm'
  have hnet := operator_sub_isNormalized_to_nearest_sz _ _ _ hi'n hm'n hn'
  have hf'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hfee'
  have h1 := operator_sub_isNormalized_to_nearest_sz _ _ _ hov hnet hpai
  have h2 := operator_sub_isNormalized_to_nearest_sz _ _ _ h1 hm'n hpaf
  exact operator_sub_isNormalized_to_nearest_sz _ _ _ h2 hf'n hpd

end XRPL.Model.Lending
