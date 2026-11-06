import XRPL.Properties.Lending.Loan.Common.InterestMonotone
import XRPL.Properties.Lending.Loan.Common.SetPhase
import XRPL.Properties.Lending.Loan.Common.SetUpdates

/-! # What a payment charges

A LoanSet keeps every fee on the LoanScale grid, so while a payment's amounts stay below `10^16` LoanScale units
every sum it computes is exact: each scheduled payment charges exactly its totalDue. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private checkPrecisionFields canFundLoan from XRPL.Model.Lending.Loan.LoanSet
open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment roundAndSplitInterest
  Loan.unimpairIfImpaired from XRPL.Model.Lending.Loan.LoanPay
open private rn_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful

/-- A fee a LoanSet accepted is a normalized whole number of LoanScale units. -/
private lemma Loan.Created.fee_onGrid {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) (x : Number)
    (hx : x ∈ start.fees.amountFields) (hn : x.isNormalized) (h0 : 0 ≤ x.toRat) : Number.OnGrid start.loanScale x := by
  obtain ⟨broker, v, principal, rates, fees, _, _, _, _, twoStep, allowsOverpayment, r, hcan, hok, rfl⟩ := h
  obtain ⟨props, _, _, _, broker', _, _, _, _, _, hchecks, -, -, -, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees _ allowsOverpayment twoStep r hok
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hF : r.loan'.fees = fees := by
    show r.loan'.toRawLoan.fees = _; rw [hl]; rfl
  rw [hF] at hx
  have hmem : x ∈ principal :: fees.amountFields := List.mem_cons_of_mem _ hx
  have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hcan x hmem
  have hchk := hchecks.exact x hmem
  obtain ⟨hlo, hhi, hint⟩ := Loan.create_loanScale_range broker v principal rates fees _ props _ _ hchecks
    (by rw [← hLS]; exact r.loan'.wf.loanScale_range.2)
  obtain ⟨j, hj⟩ := isRounded_grid broker.numericType x props.loanScale hn h0 hst ⟨by omega, hhi⟩ hint hchk
  rw [hLS]
  exact ⟨hn, j, by rw [hj]; push_cast; rfl⟩

/-- A reachable loan holds LoanServiceFee, LatePaymentFee and ClosePaymentFee on its LoanScale grid. -/
lemma Loan.Reachable.fees_onGrid {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    Number.OnGrid loan.loanScale loan.fees.serviceFee ∧ Number.OnGrid loan.loanScale loan.fees.latePaymentFee ∧
      Number.OnGrid loan.loanScale loan.fees.closePaymentFee := by
  obtain ⟨s0, t0, hc, hr0⟩ := hr
  have hft := Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr0
  rw [hft.2.1, hft.2.2.2.2.2.2.1]
  have he := s0.exact
  have hw := s0.wf
  refine ⟨hc.fee_onGrid _ (by simp [LoanFees.amountFields]) hw.serviceFee_norm he.serviceFee_nonneg,
    hc.fee_onGrid _ (by simp [LoanFees.amountFields]) hw.latePaymentFee_norm he.latePaymentFee_nonneg,
    hc.fee_onGrid _ (by simp [LoanFees.amountFields]) hw.closePaymentFee_norm he.closePaymentFee_nonneg⟩

/-- `2 * 10^16` units of `10^s`, as a normalized number. -/
private lemma Number.twoE16 (s : Int) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) :
    ∃ m : Number, m.isNormalized ∧ m.toRat = 2 * 10 ^ 16 * 10 ^ s := by
  obtain ⟨x, hx, -, -, hv, -⟩ := exists_normalized_of_int_mul_pow (2 * 10 ^ 15) (s + 1) (by norm_num) (by norm_num)
    (by omega) (by omega)
  refine ⟨x, hx, ?_⟩
  rw [hv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
  push_cast
  ring

/-- A to-nearest sum of two grid amounts is exact when it lands below `2 * 10^16` units, for a sum at least
zero. -/
private lemma Number.OnGrid.add_exact_of_le {s : Int} {x y d : Number} (hx : Number.OnGrid s x)
    (hy : Number.OnGrid s y) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (h0 : 0 ≤ x.toRat + y.toRat)
    (hd : d.toRat < 2 * 10 ^ 16 * 10 ^ s) (h : x.operator_add y .to_nearest = .ok d) :
    d.toRat = x.toRat + y.toRat := by
  obtain ⟨m, hm, hmv⟩ := Number.twoE16 s hs
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hlt : x.toRat + y.toRat < 2 * 10 ^ 16 * 10 ^ s := by
    by_contra hge
    push Not at hge
    have := Number.roundsToRepresentable_ge _ _ (operator_add_rounded_to_nearest x y d hx.1 hy.1 h) _ hm
      (by rw [hmv]; exact hge)
    linarith
  exact Number.OnGrid.add_toRat hx hy hs (by rw [abs_lt]; constructor <;> linarith) h

/-- The same for a difference. -/
private lemma Number.OnGrid.sub_exact_of_le {s : Int} {x y d : Number} (hx : Number.OnGrid s x)
    (hy : Number.OnGrid s y) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (h0 : 0 ≤ x.toRat - y.toRat)
    (hd : d.toRat < 2 * 10 ^ 16 * 10 ^ s) (h : x.operator_sub y .to_nearest = .ok d) :
    d.toRat = x.toRat - y.toRat := by
  obtain ⟨m, hm, hmv⟩ := Number.twoE16 s hs
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hlt : x.toRat - y.toRat < 2 * 10 ^ 16 * 10 ^ s := by
    by_contra hge
    push Not at hge
    have := Number.roundsToRepresentable_ge _ _ (operator_sub_rounded_to_nearest x y d hx.1 hy.1 h) _ hm
      (by rw [hmv]; exact hge)
    linarith
  exact Number.OnGrid.sub_toRat hx hy hs (by rw [abs_lt]; constructor <;> linarith) h

/-- The deltas of a scheduled instalment: on the LoanScale grid, each between zero and what the loan owes, the
fee delta at most the value delta, and the value delta taken off TotalValueOutstanding exactly. -/
private lemma Loan.instalment_deltas (l l' : Loan) (pc0 pc : PaymentComponents) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (hpc0 : Loan.scheduledComponents l = .ok pc0) (e1 : pc.totalValueDelta = pc0.totalValueDelta)
    (e2 : pc.principalDelta = pc0.principalDelta) (e3 : pc.managementFeeDelta = pc0.managementFeeDelta)
    (e4 : pc.isFinal = pc0.isFinal) (hdo : Loan.doPayment l pc = .ok l') :
    Number.OnGrid l.loanScale pc.totalValueDelta ∧ Number.OnGrid l.loanScale pc.principalDelta ∧
      Number.OnGrid l.loanScale pc.managementFeeDelta ∧
      0 ≤ pc.principalDelta.toRat ∧ pc.principalDelta.toRat ≤ l.principalOutstanding.toRat ∧
      0 ≤ pc.managementFeeDelta.toRat ∧ pc.managementFeeDelta.toRat ≤ l.managementFeeOutstanding.toRat ∧
      0 ≤ pc.totalValueDelta.toRat ∧ pc.totalValueDelta.toRat ≤ l.totalValueOutstanding.toRat ∧
      pc.managementFeeDelta.toRat ≤ pc.totalValueDelta.toRat ∧
      l'.totalValueOutstanding.toRat = l.totalValueOutstanding.toRat - pc.totalValueDelta.toRat := by
  have hs := Loan.loanScale_bounds l
  obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  have hiD : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat :=
    hi
  rw [e1, e2, e3]
  rcases Loan.scheduledComponents_tracked l pc0 hlo hint hi hpc0 with hf | ⟨hf, ht⟩
  · obtain ⟨-, hfin⟩ := Loan.scheduledComponents_shape l pc0 hpc0
    obtain ⟨f1, f2, f3⟩ := hfin hf
    have hpaid : l'.paymentRemaining = 0 := by
      simp only [Loan.doPayment, show pc.isFinal = true by rw [e4]; exact hf, ↓reduceIte] at hdo
      unfold_ter at hdo
      walk_ok
      exact congrArg RawLoan.paymentRemaining (RawLoan.to_lawful_ok ‹_›).1
    have hz : l'.totalValueOutstanding.toRat = 0 := (l'.exact.paid_zeroed hpaid).1
    rw [f1, f2, f3, hz]
    exact ⟨gT, gP, gM, hP0, le_refl _, hM0, le_refl _, hT0, le_refl _, by linarith, by ring⟩
  · obtain ⟨gtv, gpd, gmd, ⟨tv0, tv1⟩, ⟨pd0, pd1⟩, ⟨md0, md1⟩, -, hmv⟩ := ht
    have hpcf : pc.isFinal = false := by rw [e4]; exact hf
    simp only [Loan.doPayment, hpcf, Bool.false_eq_true, ↓reduceIte] at hdo
    unfold_ter at hdo
    walk_ok
    rename_i _ tv htv _ _ _ _ _ _ _ _ hlaw
    have hr := (RawLoan.to_lawful_ok hlaw).1
    have r1 := (congrArg RawLoan.totalValueOutstanding hr :)
    simp only at r1
    rw [e1] at htv
    have vtv := Number.OnGrid.sub_toRat gT gtv hs (by rw [abs_lt]; constructor <;> linarith) htv
    refine ⟨gtv, gpd, gmd, pd0, pd1, md0, md1, tv0, tv1, hmv, ?_⟩
    rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl, r1, vtv]

/-- One scheduled instalment charges exactly its totalDue, the value it takes off the loan plus its untracked
interest and fee, while totalDue stays below `10^16` LoanScale units. -/
private lemma Loan.instalment_charge (l l' : Loan) (pc0 pc : PaymentComponents) (a : PaymentAmounts) (due : Number)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (hpc0 : Loan.scheduledComponents l = .ok pc0)
    (e1 : pc.totalValueDelta = pc0.totalValueDelta) (e2 : pc.principalDelta = pc0.principalDelta)
    (e3 : pc.managementFeeDelta = pc0.managementFeeDelta) (e4 : pc.isFinal = pc0.isFinal)
    (gi : Number.OnGrid l.loanScale pc.untrackedInterest) (gf : Number.OnGrid l.loanScale pc.untrackedManagementFee)
    (hi0 : 0 ≤ pc.untrackedInterest.toRat) (hf0 : 0 ≤ pc.untrackedManagementFee.toRat)
    (hpa : pc.paidAmounts = .ok a) (hdue : pc.totalDue = .ok due) (hdo : Loan.doPayment l pc = .ok l')
    (hC : due.toRat < 10 ^ 16 * 10 ^ l.loanScale) :
    a.principalPaid.toRat + a.interestPaid.toRat + a.feePaid.toRat = due.toRat ∧
      due.toRat = l.totalValueOutstanding.toRat - l'.totalValueOutstanding.toRat + pc.untrackedInterest.toRat +
        pc.untrackedManagementFee.toRat ∧
      pc.untrackedInterest.toRat ≤ due.toRat ∧ pc.untrackedManagementFee.toRat ≤ due.toRat := by
  have hs := Loan.loanScale_bounds l
  have hp : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  have hiD : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat :=
    hi
  obtain ⟨gtv, gpd, gmd, pd0, pd1, md0, md1, tv0, tv1, hmv, hTV⟩ :=
    Loan.instalment_deltas l l' pc0 pc hlo hint hi hpc0 e1 e2 e3 e4 hdo
  -- totalDue: the value delta plus the untracked interest, plus the untracked fee, both exact
  unfold PaymentComponents.totalDue at hdue
  obtain ⟨v1, hv1, hdue⟩ := bind_ok_peel _ _ _ hdue
  have g1 := Number.OnGrid.add gtv gi hs hv1
  have hv10 : 0 ≤ v1.toRat := rn_nonneg (operator_add_rounded_to_nearest _ _ _ gtv.1 gi.1 hv1)
    (by linarith)
  have hC2 : due.toRat < 2 * 10 ^ 16 * 10 ^ l.loanScale := by nlinarith
  have vdue := Number.OnGrid.add_exact_of_le g1 gf hs (by linarith) hC2 hdue
  have vv1 := Number.OnGrid.add_exact_of_le gtv gi hs (by linarith) (by linarith) hv1
  -- the paid amounts: the principal delta, the interest part plus the untracked interest, the fee plus the
  -- untracked fee, each exact
  obtain ⟨d1, d2, h1, h2, h3⟩ := PaymentComponents.paidAmounts_interest pc a hpa
  have hfee : pc.managementFeeDelta.operator_add pc.untrackedManagementFee .to_nearest = .ok a.feePaid ∧
      a.principalPaid = pc.principalDelta := by
    unfold PaymentComponents.paidAmounts at hpa
    obtain ⟨_, -, hpa⟩ := bind_ok_peel _ _ _ hpa
    obtain ⟨_, -, hpa⟩ := bind_ok_peel _ _ _ hpa
    obtain ⟨fp, hfp, hpa⟩ := bind_ok_peel _ _ _ hpa
    obtain rfl := (Except.ok.inj hpa).symm
    exact ⟨hfp, rfl⟩
  have hb : (2 : ℚ) ^ 63 * 10 ^ l.loanScale > 4 * 10 ^ 16 * 10 ^ l.loanScale := by nlinarith
  have vd1 := Number.OnGrid.sub_toRat gtv gpd hs (by rw [abs_lt]; constructor <;> linarith) h1
  have gd1 := Number.OnGrid.sub gtv gpd hs h1
  have vd2 := Number.OnGrid.sub_toRat gd1 gmd hs (by rw [vd1, abs_lt]; constructor <;> linarith) h2
  have gd2 := Number.OnGrid.sub gd1 gmd hs h2
  have vip := Number.OnGrid.add_toRat gd2 gi hs (by rw [vd2, vd1, abs_lt]; constructor <;> linarith) h3
  have vfp := Number.OnGrid.add_toRat gmd gf hs (by rw [abs_lt]; constructor <;> linarith) hfee.1
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · rw [hfee.2, vip, vfp, vd2, vd1, vdue, vv1]; ring
  · rw [vdue, vv1, hTV]; ring

/-- A tenth-bips share of a value at least zero is at least zero. -/
private lemma tenthBipsOfValue_nonneg {x r : Number} {rate : TenthBips32} (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (h : tenthBipsOfValue x rate .to_nearest = .ok r) : 0 ≤ r.toRat := by
  obtain ⟨hrn, hrv⟩ := TenthBips32.toNumber_facts rate
  obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  have heq : tenthBipsOfValue x rate .to_nearest = (x.operator_mul rate.toNumber .to_nearest) >>=
      (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨p, hp, h⟩ := bind_ok_peel _ _ _ h
  have hpn := Number.operator_mul_isNormalized _ _ _ _ hx hrn hp
  have hp0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hx hrn hp) (by rw [hrv]; positivity)
  exact rn_nonneg (operator_div_rounded_to_nearest _ _ _ hpn hun h) (by rw [huv]; positivity)

/-- The management fee on interest at least zero is on the grid, between zero and the interest, at a rate
of at most 10%. -/
private lemma computeManagementFee_le (nt : NumericType) (x f : Number) (rate : TenthBips16) (s : Int)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hrate : rate.toNat ≤ 10000) (hs : -81 ≤ s ∧ s ≤ 80)
    (hint : nt.isIntegral = true → s ≤ 0) (h : computeManagementFee nt x rate s = .ok f) :
    Number.OnGrid s f ∧ 0 ≤ f.toRat ∧ f.toRat ≤ x.toRat := by
  unfold computeManagementFee at h
  obtain ⟨tb, htb, h⟩ := bind_ok_peel _ _ _ h
  have htbn := tenthBipsOfValue_normalized hx htb
  have htb0 := tenthBipsOfValue_nonneg hx h0 htb
  have hr32 : ((rate.toTenthBips32).toNat : ℚ) ≤ 10000 := by
    have h' : rate.toTenthBips32.toNat = rate.toNat := by simp [TenthBips16.toTenthBips32]
    rw [h']; exact_mod_cast hrate
  have htbx : tb.toRat ≤ x.toRat := by
    rcases eq_or_lt_of_le htb0 with hz | hpos
    · rw [← hz]; exact h0
    · obtain ⟨hx0, hle⟩ := tenthBipsOfValue_pos_le hx htb hpos
      have hc : (1 + 1 / 10 ^ 18 : ℚ) ^ 2 ≤ 2 := by norm_num
      have h1 : x.toRat * ((rate.toTenthBips32).toNat : ℚ) ≤ x.toRat * 10000 :=
        mul_le_mul_of_nonneg_left hr32 h0
      have h2 : x.toRat * ((rate.toTenthBips32).toNat : ℚ) / 100000 * (1 + 1 / 10 ^ 18) ^ 2 ≤
          x.toRat * 10000 / 100000 * 2 := by
        apply mul_le_mul _ hc (by positivity) (by positivity)
        exact div_le_div_of_nonneg_right h1 (by norm_num)
      linarith
  refine ⟨STAmount.roundToNumericType_onGrid _ _ _ _ _ hs hint h,
    STAmount.roundToNumericType_some_nonneg _ _ _ _ _ htbn htb0 (Or.inr (Or.inr rfl)) hs h, ?_⟩
  refine le_trans ?_ htbx
  cases hnt : nt with
  | fractional =>
    rw [hnt] at h
    exact STAmount.roundToNumericType_frac_downward_le _ _ _ htbn htb0 hs h
  | integral mv mo ms msh =>
    rw [hnt] at h
    exact (STAmount.roundToNumericType_int_grid _ rfl _ _ _ _ htbn htb0 (Or.inr (Or.inr rfl)) h).2.2.2 rfl

/-- The late interest of a lawful loan is a normalized amount at least zero. -/
private lemma loanLatePaymentInterest_nonneg (l : Loan) (now : UInt32) (li : Number)
    (h : loanLatePaymentInterest l.principalOutstanding l.rates.lateInterestRate now l.nextPaymentDueDate = .ok li) :
    li.isNormalized ∧ 0 ≤ li.toRat := by
  have hzero : li = Number.zero → li.isNormalized ∧ 0 ≤ li.toRat := fun hz => by
    subst hz; exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero]⟩
  unfold loanLatePaymentInterest at h
  by_cases h1 : l.principalOutstanding.operator_eq Number.zero = true
  · simp only [h1, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact hzero h.symm
  by_cases h2 : (l.rates.lateInterestRate == 0) = true
  · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, Except.ok.injEq, bind, Except.bind] at h
    exact hzero h.symm
  by_cases h3 : now ≤ l.nextPaymentDueDate
  · simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, Except.ok.injEq, bind,
      Except.bind] at h
    exact hzero h.symm
  simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, bind, Except.bind,
    UInt32.subChecked_of_le (UInt32.le_of_lt (UInt32.not_le.mp h3))] at h
  split at h
  · cases h
  rename_i rate hrate
  have hrn := loanPeriodicRate_isNormalized _ _ _ hrate
  have hr0 : 0 ≤ rate.toRat := by
    have heq : loanPeriodicRate l.rates.lateInterestRate (now - l.nextPaymentDueDate) =
        (tenthBipsOfValue (Number.ofInt64 (now - l.nextPaymentDueDate).toInt64)
          l.rates.lateInterestRate .to_nearest) >>= (fun t => t.operator_div secondsInYear .to_nearest) := rfl
    rw [heq] at hrate
    obtain ⟨tb, htb, hrate⟩ := bind_ok_peel _ _ _ hrate
    have hin := Number.ofInt64_isNormalized (now - l.nextPaymentDueDate).toInt64
    have hi0 : 0 ≤ (Number.ofInt64 (now - l.nextPaymentDueDate).toInt64).toRat := by
      have := TenthBips32.toNumber_facts (now - l.nextPaymentDueDate)
      rw [show Number.ofInt64 (now - l.nextPaymentDueDate).toInt64 =
        TenthBips32.toNumber (now - l.nextPaymentDueDate) from rfl, this.2]
      positivity
    have htbn := tenthBipsOfValue_normalized hin htb
    have htb0 := tenthBipsOfValue_nonneg hin hi0 htb
    obtain ⟨hyn, hyv⟩ := TenthBips32.toNumber_facts (31536000 : UInt32)
    have hy : secondsInYear = TenthBips32.toNumber (31536000 : UInt32) := rfl
    rw [hy] at hrate
    exact rn_nonneg (operator_div_rounded_to_nearest _ _ _ htbn hyn hrate) (by rw [hyv]; positivity)
  exact ⟨Number.operator_mul_isNormalized _ _ _ _ l.wf.principalOutstanding_norm hrn h,
    rn_nonneg (operator_mul_rounded_to_nearest _ _ _ l.wf.principalOutstanding_norm hrn h)
      (mul_nonneg l.exact.principalOutstanding_nonneg hr0)⟩

/-- The parts of a late instalment: the next scheduled one, plus the rounded late interest less its management
fee as untracked interest, and the service, late and management fees as untracked fee. -/
private lemma Loan.lateComponents_parts (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (h : Loan.lateComponents l now = .ok pc) :
    ∃ pc0 li lr split net sf uf, Loan.scheduledComponents l = .ok pc0 ∧
      loanLatePaymentInterest l.principalOutstanding l.rates.lateInterestRate now l.nextPaymentDueDate = .ok li ∧
      STAmount.roundToNumericType l.broker.numericType li .to_nearest (some l.loanScale) = .ok lr ∧
      computeManagementFee l.broker.numericType lr l.broker.managementFeeRate l.loanScale = .ok split ∧
      lr.operator_sub split .to_nearest = .ok net ∧
      l.fees.serviceFee.operator_add l.fees.latePaymentFee .to_nearest = .ok sf ∧
      sf.operator_add split .to_nearest = .ok uf ∧
      pc = { pc0 with untrackedInterest := net, untrackedManagementFee := uf } := by
  unfold Loan.lateComponents at h
  obtain ⟨pc0, hpc0, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨li, hli, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨⟨net, split⟩, hsplit, h⟩ := bind_ok_peel _ _ _ h
  unfold roundAndSplitInterest at hsplit
  obtain ⟨lr, hlr, hsplit⟩ := bind_ok_peel _ _ _ hsplit
  obtain ⟨split', hsplit', hsplit⟩ := bind_ok_peel _ _ _ hsplit
  obtain ⟨net', hnet', hsplit⟩ := bind_ok_peel _ _ _ hsplit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hsplit).symm
  obtain ⟨sf, hsf, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨uf, huf, h⟩ := bind_ok_peel _ _ _ h
  exact ⟨pc0, li, lr, split, net, sf, uf, hpc0, hli, hlr, hsplit', hnet', hsf, huf, (Except.ok.inj h).symm⟩

/-- One instalment paid by `payInstalment`: its totalDue, its amounts and the loan it leaves. -/
private lemma Loan.payInstalment_parts (loan : Loan) (v : Vault) (pc : PaymentComponents) (amount : Number)
    (p : UnsettledPayment Vault) (h : (loan.payInstalment v pc amount).run = .ok (.ok p)) :
    pc.totalDue = .ok p.totalPaid ∧ pc.paidAmounts = .ok p.amounts ∧ Loan.doPayment loan pc = .ok p.loan := by
  simp only [Loan.payInstalment] at h
  unfold_ter at h
  walk_ok
  exact ⟨‹_›, ‹_›, ‹_›⟩

/-- A late instalment charges exactly its totalDue, the value it takes off the loan plus LoanServiceFee,
LatePaymentFee and the late interest rounded to LoanScale, while totalDue stays below `10^16` LoanScale units. -/
private lemma Loan.late_instalment_charge (l l' : Loan) (now : UInt32) (pc : PaymentComponents) (a : PaymentAmounts)
    (due : Number) (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (gs : Number.OnGrid l.loanScale l.fees.serviceFee)
    (gl : Number.OnGrid l.loanScale l.fees.latePaymentFee) (hpc : Loan.lateComponents l now = .ok pc)
    (hpa : pc.paidAmounts = .ok a) (hdue : pc.totalDue = .ok due) (hdo : Loan.doPayment l pc = .ok l')
    (hC : due.toRat < 10 ^ 16 * 10 ^ l.loanScale) :
    a.principalPaid.toRat + a.interestPaid.toRat + a.feePaid.toRat = due.toRat ∧
      ∃ li lr, loanLatePaymentInterest l.principalOutstanding l.rates.lateInterestRate now l.nextPaymentDueDate =
          .ok li ∧ STAmount.roundToNumericType l.broker.numericType li .to_nearest (some l.loanScale) = .ok lr ∧
        due.toRat = l.totalValueOutstanding.toRat - l'.totalValueOutstanding.toRat + l.fees.serviceFee.toRat +
          l.fees.latePaymentFee.toRat + lr.toRat := by
  have hs := Loan.loanScale_bounds l
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  have hp : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  obtain ⟨pc0, li, lr, split, net, sf, uf, hpc0, hli, hlr, hsp, hnet, hsf, huf, rfl⟩ :=
    Loan.lateComponents_parts l now pc hpc
  obtain ⟨hlin, hli0⟩ := loanLatePaymentInterest_nonneg l now li hli
  have glr := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hlr
  have hlr0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hlin hli0 (Or.inl rfl) hr hlr
  have hrate : l.broker.managementFeeRate.toNat ≤ 10000 := by
    have := l.broker.exact.managementFeeRate_cap
    exact_mod_cast this
  obtain ⟨gsp, hsp0, hsplr⟩ := computeManagementFee_le _ _ _ _ _ glr.1 hlr0 hrate hr hint hsp
  have gnet := Number.OnGrid.sub glr gsp hs hnet
  have hnet0 := rn_nonneg (operator_sub_rounded_to_nearest _ _ _ glr.1 gsp.1 hnet) (by linarith)
  have gsf := Number.OnGrid.add gs gl hs hsf
  have hs0 : 0 ≤ l.fees.serviceFee.toRat := l.exact.serviceFee_nonneg
  have hl0 : 0 ≤ l.fees.latePaymentFee.toRat := l.exact.latePaymentFee_nonneg
  have hsf0 := rn_nonneg (operator_add_rounded_to_nearest _ _ _ gs.1 gl.1 hsf) (by linarith)
  have guf := Number.OnGrid.add gsf gsp hs huf
  have huf0 := rn_nonneg (operator_add_rounded_to_nearest _ _ _ gsf.1 gsp.1 huf) (by linarith)
  obtain ⟨hsum, hval, hnetle, hufle⟩ := Loan.instalment_charge l l' pc0
    { pc0 with untrackedInterest := net, untrackedManagementFee := uf } a due hlo hint hi hpc0 rfl rfl rfl rfl
    gnet guf hnet0 huf0 hpa hdue hdo hC
  refine ⟨hsum, li, lr, hli, hlr, ?_⟩
  -- every fee and interest sum below totalDue is exact
  have hC2 : due.toRat < 2 * 10 ^ 16 * 10 ^ l.loanScale := by linarith
  have vuf := Number.OnGrid.add_exact_of_le gsf gsp hs (by linarith) (by simp only at hufle; linarith) huf
  have vsf := Number.OnGrid.add_exact_of_le gs gl hs (by linarith) (by simp only at hufle; linarith) hsf
  have vnet := Number.OnGrid.sub_exact_of_le glr gsp hs (by linarith) (by simp only at hnetle; linarith) hnet
  simp only at hval
  rw [hval, vuf, vsf, vnet]
  ring

/-- A reachable loan is at LoanScale at least `-81`, at LoanScale at most `0` when integral, with interestDue at
least zero and its LoanServiceFee and LatePaymentFee on its LoanScale grid. -/
private lemma Loan.Reachable.pay_facts {loan : Loan} {t : UInt32} (hreach : loan.Reachable t) :
    -81 ≤ loan.loanScale ∧ (loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) ∧
      0 ≤ loan.toExact.interestDue ∧ Number.OnGrid loan.loanScale loan.fees.serviceFee ∧
      Number.OnGrid loan.loanScale loan.fees.latePaymentFee := by
  obtain ⟨s0, t0, hc, hr0⟩ := hreach
  have hft := Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr0
  obtain ⟨gs, gl, -⟩ := Loan.Reachable.fees_onGrid ⟨s0, t0, hc, hr0⟩
  refine ⟨by rw [hft.2.2.2.2.2.2.1]; have := hc.loanScale_ge; omega, fun h => ?_,
    Loan.Reachable.interestDue_nonneg ⟨s0, t0, hc, hr0⟩, gs, gl⟩
  rw [hft.2.2.2.2.2.2.1]
  exact hc.loanScale_integral (by rw [← hr0.numericType]; exact h)

end XRPL.Model.Lending
