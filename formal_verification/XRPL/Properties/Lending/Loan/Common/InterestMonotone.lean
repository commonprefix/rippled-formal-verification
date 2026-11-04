import XRPL.Properties.Lending.Loan.Common.InterestDue

/-! # interestDue never rises unless late or overpayment interest covers a negative interest part

An instalment pays as interest what it takes off interestDue, and the settlement rejects a negative interest
part. Late and overpayment interest also count in that part, so they can let a negative part through. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment UnsettledPayment.payInstalments
  UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.settlePayment Loan.overpaymentComponents
  roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay
open private Loan.lateComponents_scheduled from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private ite_bind_ok from XRPL.Properties.Lending.Loan.Common.InterestDue

/-- Rounding zero gives zero, in every mode and at every scale. -/
private lemma STAmount.roundToNumericType_zero_some (nt : NumericType) (mode : rounding_mode) (e : Int) :
    STAmount.roundToNumericType nt Number.zero mode (some e) = .ok Number.zero := by
  cases nt with
  | fractional => cases mode <;> rfl
  | integral mv mo ms msh => cases mode <;> rfl

/-- A share of zero is zero. -/
private lemma tenthBipsOfValue_zero_rate' (rate : TenthBips32) :
    tenthBipsOfValue Number.zero rate .to_nearest = .ok Number.zero := by
  have heq : tenthBipsOfValue Number.zero rate .to_nearest =
      (Number.zero.operator_mul rate.toNumber .to_nearest) >>=
        (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest) := rfl
  rw [heq]
  have hm : Number.zero.operator_mul rate.toNumber .to_nearest = .ok Number.zero := by
    unfold Number.operator_mul
    rw [if_pos (by decide)]
    rfl
  rw [hm]
  exact zero_div_unity .to_nearest

/-- The management fee on zero interest is zero. -/
private lemma computeManagementFee_zero (nt : NumericType) (rate : TenthBips16) (s : Int) :
    computeManagementFee nt Number.zero rate s = .ok Number.zero := by
  unfold computeManagementFee
  rw [tenthBipsOfValue_zero_rate' rate.toTenthBips32]
  exact STAmount.roundToNumericType_zero_some nt .downward s

/-- Zero interest splits into zero net interest and zero management fee. -/
private lemma roundAndSplitInterest_zero (rate : TenthBips16) (mode : rounding_mode) (nt : NumericType) (s : Int) :
    roundAndSplitInterest Number.zero rate mode nt s = .ok (Number.zero, Number.zero) := by
  unfold roundAndSplitInterest
  rw [STAmount.roundToNumericType_zero_some]
  simp only [bind, Except.bind]
  rw [computeManagementFee_zero]
  rfl

/-- A scheduled instalment carries no untracked interest, and the last one takes everything the loan owes. -/
lemma Loan.scheduledComponents_shape (l : Loan) (pc : PaymentComponents)
    (h : Loan.scheduledComponents l = .ok pc) :
    pc.untrackedInterest = Number.zero ∧ (pc.isFinal = true → pc.totalValueDelta = l.totalValueOutstanding ∧
      pc.principalDelta = l.principalOutstanding ∧ pc.managementFeeDelta = l.managementFeeOutstanding) := by
  unfold Loan.scheduledComponents at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  split at h
  · obtain rfl := (Except.ok.inj h).symm
    exact ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
  · repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
    obtain ⟨_, -, h⟩ := ite_bind_ok _ _ _ _ _ h
    repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
    obtain ⟨_, -, h⟩ := ite_bind_ok _ _ _ _ _ h
    repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
    obtain rfl := (Except.ok.inj h).symm
    exact ⟨rfl, fun h => by cases h⟩

/-- The interest part of an instalment: its value delta less its principal and fee deltas, plus its untracked
interest. -/
lemma PaymentComponents.paidAmounts_interest (pc : PaymentComponents) (a : PaymentAmounts)
    (h : pc.paidAmounts = .ok a) :
    ∃ d1 d2, pc.totalValueDelta.operator_sub pc.principalDelta .to_nearest = .ok d1 ∧
      d1.operator_sub pc.managementFeeDelta .to_nearest = .ok d2 ∧
      d2.operator_add pc.untrackedInterest .to_nearest = .ok a.interestPaid := by
  unfold PaymentComponents.paidAmounts PaymentComponents.interestDelta at h
  obtain ⟨d2, hd2, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d1, hd1, hd2⟩ := bind_ok_peel _ _ _ hd2
  obtain ⟨ip, hip, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  exact ⟨d1, d2, hd1, hd2, hip⟩

/-- One scheduled instalment pays as interest exactly what it takes off interestDue, and leaves interestDue
at least zero. `pc` has the deltas of the scheduled instalment `pc0` and no untracked interest. -/
private lemma Loan.instalment_interestPaid (l l' : Loan) (pc0 pc : PaymentComponents) (amts : PaymentAmounts)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (hpc0 : Loan.scheduledComponents l = .ok pc0)
    (e1 : pc.totalValueDelta = pc0.totalValueDelta) (e2 : pc.principalDelta = pc0.principalDelta)
    (e3 : pc.managementFeeDelta = pc0.managementFeeDelta) (e4 : pc.isFinal = pc0.isFinal)
    (hu : pc.untrackedInterest = Number.zero) (hpa : pc.paidAmounts = .ok amts)
    (hdo : Loan.doPayment l pc = .ok l') :
    Number.OnGrid l.loanScale amts.interestPaid ∧
      amts.interestPaid.toRat = l.toExact.interestDue - l'.toExact.interestDue ∧ 0 ≤ l'.toExact.interestDue := by
  have hs := Loan.loanScale_bounds l
  obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  obtain ⟨d1, d2, h1, h2, h3⟩ := PaymentComponents.paidAmounts_interest pc amts hpa
  rw [hu, Number.operator_add_zero_right, Except.ok.injEq] at h3
  subst h3
  have hiD : l.toExact.interestDue =
      l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat := rfl
  have hp : (0 : ℚ) < 2 ^ 63 * 10 ^ l.loanScale := by positivity
  rcases Loan.scheduledComponents_tracked l pc0 hlo hint hi hpc0 with hf | ⟨hf, ht⟩
  · -- the last instalment takes the whole loan and leaves nothing
    obtain ⟨-, hfin⟩ := Loan.scheduledComponents_shape l pc0 hpc0
    obtain ⟨f1, f2, f3⟩ := hfin hf
    rw [e1, f1, e2, f2] at h1
    rw [e3, f3] at h2
    have v1 := Number.OnGrid.sub_toRat gT gP hs (by rw [abs_lt]; constructor <;> linarith) h1
    have g1 := Number.OnGrid.sub gT gP hs h1
    have v2 := Number.OnGrid.sub_toRat g1 gM hs (by rw [v1, abs_lt]; constructor <;> linarith) h2
    have hpaid : l'.paymentRemaining = 0 := by
      simp only [Loan.doPayment, show pc.isFinal = true by rw [e4]; exact hf, ↓reduceIte] at hdo
      unfold_ter at hdo
      walk_ok
      exact congrArg RawLoan.paymentRemaining (RawLoan.to_lawful_ok ‹_›).1
    rw [Loan.interestDue_paid l' hpaid]
    exact ⟨Number.OnGrid.sub g1 gM hs h2, by rw [v2, v1, hiD]; ring, le_refl _⟩
  · -- any other instalment takes its tracked deltas off the loan exactly
    obtain ⟨gtv, gpd, gmd, ⟨tv0, tv1⟩, ⟨pd0, pd1⟩, ⟨md0, md1⟩, hle, -⟩ := ht
    rw [e1] at h1; rw [e2] at h1; rw [e3] at h2
    have v1 := Number.OnGrid.sub_toRat gtv gpd hs (by rw [abs_lt]; constructor <;> linarith) h1
    have g1 := Number.OnGrid.sub gtv gpd hs h1
    have v2 := Number.OnGrid.sub_toRat g1 gmd hs (by rw [v1, abs_lt]; constructor <;> linarith) h2
    have hpcf : pc.isFinal = false := by rw [e4]; exact hf
    simp only [Loan.doPayment, hpcf, Bool.false_eq_true, ↓reduceIte] at hdo
    unfold_ter at hdo
    walk_ok
    rename_i _ tv htv _ pv hpv _ mv hmv hlaw
    have hr := (RawLoan.to_lawful_ok hlaw).1
    have r1 := (congrArg RawLoan.totalValueOutstanding hr :)
    have r2 := (congrArg RawLoan.principalOutstanding hr :)
    have r3 := (congrArg RawLoan.managementFeeOutstanding hr :)
    simp only at r1 r2 r3
    rw [e1] at htv; rw [e2] at hpv; rw [e3] at hmv
    have vtv := Number.OnGrid.sub_toRat gT gtv hs (by rw [abs_lt]; constructor <;> linarith) htv
    have vpv := Number.OnGrid.sub_toRat gP gpd hs (by rw [abs_lt]; constructor <;> linarith) hpv
    have vmv := Number.OnGrid.sub_toRat gM gmd hs (by rw [abs_lt]; constructor <;> linarith) hmv
    have hiD' : l'.toExact.interestDue = l.toExact.interestDue -
        (pc0.totalValueDelta.toRat - pc0.principalDelta.toRat - pc0.managementFeeDelta.toRat) := by
      show l'.totalValueOutstanding.toRat - l'.principalOutstanding.toRat - l'.managementFeeOutstanding.toRat = _
      rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl, r1,
        show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl, r2,
        show l'.managementFeeOutstanding = l'.toRawLoan.managementFeeOutstanding from rfl, r3, vtv, vpv, vmv, hiD]
      ring
    have hle' : pc0.totalValueDelta.toRat - pc0.principalDelta.toRat - pc0.managementFeeDelta.toRat ≤
        l.toExact.interestDue := hle
    refine ⟨Number.OnGrid.sub g1 gmd hs h2, by rw [v2, v1, hiD']; ring, by rw [hiD']; linarith⟩

/-- The same for a scheduled instalment that carries the service fee. -/
private lemma Loan.scheduled_instalment_interestPaid (l l' : Loan) (pc0 : PaymentComponents) (fee : Number)
    (amts : PaymentAmounts) (hlo : -81 ≤ l.loanScale)
    (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0) (hi : 0 ≤ l.toExact.interestDue)
    (hpc0 : Loan.scheduledComponents l = .ok pc0)
    (hpa : ({ pc0 with untrackedManagementFee := fee } : PaymentComponents).paidAmounts = .ok amts)
    (hdo : Loan.doPayment l { pc0 with untrackedManagementFee := fee } = .ok l') :
    Number.OnGrid l.loanScale amts.interestPaid ∧
      amts.interestPaid.toRat = l.toExact.interestDue - l'.toExact.interestDue ∧ 0 ≤ l'.toExact.interestDue :=
  Loan.instalment_interestPaid l l' pc0 { pc0 with untrackedManagementFee := fee } amts hlo hint hi hpc0 rfl rfl rfl
    rfl (Loan.scheduledComponents_shape l pc0 hpc0).1 hpa hdo

/-- The interest delta of an instalment, its value delta less its principal and fee deltas, is what it takes off
interestDue. This holds with or without untracked interest. -/
private lemma Loan.instalment_interestDelta (l l' : Loan) (pc0 pc : PaymentComponents) (amts : PaymentAmounts)
    (d : Number) (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (hpc0 : Loan.scheduledComponents l = .ok pc0)
    (e1 : pc.totalValueDelta = pc0.totalValueDelta) (e2 : pc.principalDelta = pc0.principalDelta)
    (e3 : pc.managementFeeDelta = pc0.managementFeeDelta) (e4 : pc.isFinal = pc0.isFinal)
    (hpa : pc.paidAmounts = .ok amts) (hd : pc.interestDelta = .ok d) (hdo : Loan.doPayment l pc = .ok l') :
    d.toRat = l.toExact.interestDue - l'.toExact.interestDue := by
  unfold PaymentComponents.paidAmounts at hpa
  obtain ⟨d', hd', hpa⟩ := bind_ok_peel _ _ _ hpa
  rw [hd, Except.ok.injEq] at hd'
  subst hd'
  obtain ⟨_, -, hpa⟩ := bind_ok_peel _ _ _ hpa
  obtain ⟨fp, hfp, -⟩ := bind_ok_peel _ _ _ hpa
  -- the same instalment without untracked interest pays exactly its interest part
  have hpaz : ({ pc with untrackedInterest := Number.zero } : PaymentComponents).paidAmounts =
      .ok { principalPaid := pc.principalDelta, interestPaid := d, feePaid := fp } := by
    unfold PaymentComponents.paidAmounts
    rw [show ({ pc with untrackedInterest := Number.zero } : PaymentComponents).interestDelta = .ok d from hd]
    simp only [bind, Except.bind, Number.operator_add_zero_right]
    rw [show ({ pc with untrackedInterest := Number.zero } : PaymentComponents).managementFeeDelta.operator_add
      ({ pc with untrackedInterest := Number.zero } : PaymentComponents).untrackedManagementFee .to_nearest =
        .ok fp from hfp]
    rfl
  exact (Loan.instalment_interestPaid l l' pc0 { pc with untrackedInterest := Number.zero } _ hlo hint hi hpc0 e1 e2
    e3 e4 rfl hpaz hdo).2.1

/-- A lawful loan's interestDue is below `2^63` LoanScale units. -/
private lemma Loan.interestDue_lt (l : Loan) : l.toExact.interestDue < 2 ^ 63 * 10 ^ l.loanScale := by
  obtain ⟨-, -, -, hTb, hP0, hM0, -⟩ := Loan.outstanding_grid l
  show l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat < _
  linarith

/-- The loan an instalment leaves has its interestDue below `2^63` units too. -/
private lemma Loan.doPayment_interestDue_lt (l l' : Loan) (pc : PaymentComponents) (h : Loan.doPayment l pc = .ok l') :
    l'.toExact.interestDue < 2 ^ 63 * 10 ^ l.loanScale := by
  rw [← (Loan.doPayment_sameTerms _ _ _ h).loanScale]
  exact Loan.interestDue_lt l'

/-- The instalment loop pays as interest exactly what it takes off interestDue. -/
private lemma UnsettledPayment.payInstalments_interestPaid {α : Type} (l0 : Loan) (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), -81 ≤ payment.loan.loanScale →
      (payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0) →
      payment.loan.loanScale = l0.loanScale → 0 ≤ payment.loan.toExact.interestDue →
      0 ≤ l0.toExact.interestDue →
      Number.OnGrid l0.loanScale payment.amounts.interestPaid →
      payment.amounts.interestPaid.toRat = l0.toExact.interestDue - payment.loan.toExact.interestDue →
      UnsettledPayment.payInstalments payment n amount = .ok p' →
      Number.OnGrid l0.loanScale p'.amounts.interestPaid ∧
        p'.amounts.interestPaid.toRat = l0.toExact.interestDue - p'.loan.toExact.interestDue := by
  intro n
  induction n with
  | zero =>
    intro payment p' _ _ _ _ _ hg hv h
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨hg, hv⟩
  | succ n ih =>
    intro payment p' hlo hint hsc hi h0 hg hv h
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact ⟨hg, hv⟩
    · exact ⟨hg, hv⟩
    all_goals
      have hpc := ‹Loan.scheduledComponents payment.loan = _›
      obtain ⟨gi, vi, hi'⟩ := Loan.scheduled_instalment_interestPaid payment.loan _ _ _ _ hlo hint hi hpc ‹_› ‹_›
      have hst := Loan.doPayment_sameTerms _ _ _ ‹Loan.doPayment _ _ = _›
      have hadd := PaymentAmounts.add_interest _ _ _ ‹PaymentAmounts.add _ _ = _›
      have hs0 := Loan.loanScale_bounds l0
      rw [hsc] at gi
      have hlt := Loan.doPayment_interestDue_lt _ _ _ ‹Loan.doPayment _ _ = _›
      have hlt' := Loan.interestDue_lt l0
      rw [hsc] at hlt
      have hsum := Number.OnGrid.add_toRat hg gi hs0 (by
        rw [hv, vi, abs_lt]
        constructor <;> linarith) hadd
      have gsum := Number.OnGrid.add hg gi hs0 hadd
    · exact ⟨gsum, by rw [hsum, hv, vi]; ring⟩
    · have h3 := ‹UnsettledPayment.payInstalments _ n amount = _›
      have key := fun a b c d e => ih _ p' a b c d h0 gsum e h3
      simp only at key
      rw [hst.loanScale, hst.broker] at key
      exact key hlo hint hsc hi' (by rw [hsum, hv, vi]; ring)

/-- A re-amortization whose interest delta is not negative leaves a state that owes at most the loan's
interestDue. -/
private lemma Loan.reamortized_interestDue_le (l : Loan) {po tvo' mfo x y z : Number} {st s5 : LoanState}
    {d : LoanStateDeltas} (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (hst : l.state = .ok st)
    (hpo : roundAndClamp x st.principalOutstanding .upward l.broker.numericType l.loanScale = .ok po)
    (htvo' : roundAndClamp y st.valueOutstanding .upward l.broker.numericType l.loanScale = .ok tvo')
    (hmfo : roundAndClamp z st.managementFeeDue .to_nearest l.broker.numericType l.loanScale = .ok mfo)
    (h5 : LoanState.build tvo' po mfo = .ok s5) (hd : st.calculateDeltas s5 = .ok d)
    (hgi : ¬d.interest.operator_neg.operator_gt Number.zero = true) :
    s5.valueOutstanding.toRat - s5.principalOutstanding.toRat - s5.managementFeeDue.toRat ≤ l.toExact.interestDue := by
  have hs := Loan.loanScale_bounds l
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
  obtain ⟨hsT, hsP, hsM, w, hw, hwi⟩ := LoanState.build_ok hst
  rw [hsP] at hpo
  rw [hsT] at htvo'
  rw [hsM] at hmfo
  have hclamp : ∀ (v cap r : Number) (mode : rounding_mode), Number.OnGrid l.loanScale cap → 0 ≤ cap.toRat →
      roundAndClamp v cap mode l.broker.numericType l.loanScale = .ok r →
      Number.OnGrid l.loanScale r ∧ 0 ≤ r.toRat ∧ r.toRat ≤ cap.toRat := by
    intro v cap r mode gc hc0 h
    obtain ⟨q, hq, rfl⟩ := roundAndClamp_ok h
    have gq := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hq
    refine ⟨Number.OnGrid.clamp gq (Number.OnGrid.zero _) gc, ?_⟩
    rcases Number.clamp_zero_cases q cap gq.1 gc.1 with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨h1, h2, he⟩
    · rw [he, Number.toRat_zero]; exact ⟨le_refl _, hc0⟩
    · rw [he]; exact ⟨hc0, le_refl _⟩
    · rw [he]; exact ⟨h1, h2⟩
  obtain ⟨gpo, vpo0, vpoP⟩ := hclamp _ _ _ _ gP hP0 hpo
  obtain ⟨gtv, vtv0, vtvT⟩ := hclamp _ _ _ _ gT hT0 htvo'
  obtain ⟨gmf, vmf0, vmfM⟩ := hclamp _ _ _ _ gM hM0 hmfo
  have hp : (0 : ℚ) < 2 ^ 63 * 10 ^ l.loanScale := by positivity
  have hiD : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat :=
    hi
  have vw := Number.OnGrid.sub_toRat gT gP hs (by rw [abs_lt]; constructor <;> linarith) hw
  have gw := Number.OnGrid.sub gT gP hs hw
  have vwi := Number.OnGrid.sub_toRat gw gM hs (by rw [vw, abs_lt]; constructor <;> linarith) hwi
  have gwi := Number.OnGrid.sub gw gM hs hwi
  obtain ⟨h5T, h5P, h5M, w5, hw5, hi5⟩ := LoanState.build_ok h5
  have vw5 := Number.OnGrid.sub_toRat gtv gpo hs (by rw [abs_lt]; constructor <;> linarith) hw5
  have gw5 := Number.OnGrid.sub gtv gpo hs hw5
  have vi5 := Number.OnGrid.sub_toRat gw5 gmf hs (by rw [vw5, abs_lt]; constructor <;> linarith) hi5
  have gi5 := Number.OnGrid.sub gw5 gmf hs hi5
  unfold LoanState.calculateDeltas at hd
  obtain ⟨_, -, hd⟩ := bind_ok_peel _ _ _ hd
  obtain ⟨di, hdi, hd⟩ := bind_ok_peel _ _ _ hd
  obtain ⟨_, -, hd⟩ := bind_ok_peel _ _ _ hd
  obtain rfl := (Except.ok.inj hd).symm
  have vdi := Number.OnGrid.sub_toRat gwi gi5 hs
    (by rw [vwi, vw, vi5, vw5, abs_lt]; constructor <;> linarith) hdi
  have gdi := Number.OnGrid.sub gwi gi5 hs hdi
  have hdi0 : 0 ≤ di.toRat := by
    by_contra hc
    push Not at hc
    apply hgi
    have hn := Number.operator_neg_isNormalized di gdi.1
    rw [operator_gt_iff _ _ hn Number.zero_isNormalized, Number.toRat_neg, Number.toRat_zero]
    linarith
  rw [h5T, h5P, h5M]
  show _ ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat
  rw [vdi, vwi, vw, vi5, vw5] at hdi0
  linarith

/-- A re-amortization that passes never raises interestDue, and pays as interest only the overpayment's
untracked interest. -/
private lemma Loan.tryOverpayment_interestDue_le (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (h : Loan.tryOverpayment l opc = .ok (some re)) :
    re.amounts.interestPaid = opc.untrackedInterest ∧
      re.state.valueOutstanding.toRat - re.state.principalOutstanding.toRat - re.state.managementFeeDue.toRat ≤
        l.toExact.interestDue := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  -- Match the steps by their shape only. A full search unfolds the `Number` operators of the other steps.
  exact ⟨rfl, Loan.reamortized_interestDue_le l hlo hint hi (by with_reducible assumption)
    (by with_reducible assumption) (by with_reducible assumption) (by with_reducible assumption)
    (by with_reducible assumption) (by with_reducible assumption) (by with_reducible assumption)⟩

/-- Without an OverpaymentInterestRate an overpayment carries no untracked interest. -/
private lemma Loan.overpaymentComponents_untracked (l : Loan) (ov : Number) (opc : PaymentComponents)
    (hov : ov.isNormalized) (hrate : l.rates.overpaymentInterestRate = 0)
    (h : Loan.overpaymentComponents l ov = .ok opc) : opc.untrackedInterest = Number.zero := by
  unfold Loan.overpaymentComponents at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨oi, hoi, h⟩ := bind_ok_peel _ _ _ h
  rw [hrate, tenthBipsOfValue_zero_rate ov hov, Except.ok.injEq] at hoi
  subst hoi
  obtain ⟨⟨net, mf⟩, hsplit, h⟩ := bind_ok_peel _ _ _ h
  rw [roundAndSplitInterest_zero, Except.ok.injEq] at hsplit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsplit
  repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
  obtain rfl := (Except.ok.inj h).symm
  rfl

/-- Without a LateInterestRate a late instalment carries no untracked interest. -/
lemma Loan.lateComponents_untracked (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (hrate : l.rates.lateInterestRate = 0) (h : Loan.lateComponents l now = .ok pc) :
    pc.untrackedInterest = Number.zero := by
  unfold Loan.lateComponents at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨li, hli, h⟩ := bind_ok_peel _ _ _ h
  have hz : li = Number.zero := by
    unfold loanLatePaymentInterest at hli
    rw [hrate] at hli
    simp only [beq_self_eq_true, ↓reduceIte, pure, Except.pure] at hli
    split at hli <;> exact (Except.ok.inj hli).symm
  subst hz
  obtain ⟨⟨net, mf⟩, hsplit, h⟩ := bind_ok_peel _ _ _ h
  rw [roundAndSplitInterest_zero, Except.ok.injEq] at hsplit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsplit
  repeat (obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h)
  obtain rfl := (Except.ok.inj h).symm
  rfl

/-- Without overpayment interest, the overpayment tail pays no interest and never raises interestDue. -/
private lemma UnsettledPayment.applyOverpayment_interest (payment p' : UnsettledPayment Vault) (amount : Number)
    (hlo : -81 ≤ payment.loan.loanScale)
    (hint : payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0)
    (hi : 0 ≤ payment.loan.toExact.interestDue) (hover : payment.loan.rates.overpaymentInterestRate = 0)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') :
    p'.amounts.interestPaid = payment.amounts.interestPaid ∧
      p'.loan.toExact.interestDue ≤ payment.loan.toExact.interestDue := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact ⟨rfl, le_refl _⟩
    | skip
  have hopc := ‹Loan.overpaymentComponents _ _ = _›
  have hovn := STAmount.roundToNumericType_isNormalized _ _ _ _ _
    ‹STAmount.roundToNumericType _ _ rounding_mode.downward _ = _›
  have hu := Loan.overpaymentComponents_untracked _ _ _ hovn hover hopc
  obtain ⟨hip, hle⟩ := Loan.tryOverpayment_interestDue_le _ _ _ hlo hint hi ‹Loan.tryOverpayment _ _ = _›
  have hadd := PaymentAmounts.add_interest _ _ _ ‹PaymentAmounts.add _ _ = _›
  rw [hip, hu, Number.operator_add_zero_right, Except.ok.injEq] at hadd
  have h1 := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = _›).1
  refine ⟨hadd.symm, ?_⟩
  dsimp only
  rw [Loan.interestDue_of_raw _ _ h1]
  exact hle

/-- The overpayment tail never raises interestDue. -/
private lemma UnsettledPayment.applyOverpayment_interestDue_le (payment p' : UnsettledPayment Vault)
    (amount : Number) (hlo : -81 ≤ payment.loan.loanScale)
    (hint : payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0)
    (hi : 0 ≤ payment.loan.toExact.interestDue) (h : UnsettledPayment.applyOverpayment payment amount = .ok p') :
    p'.loan.toExact.interestDue ≤ payment.loan.toExact.interestDue := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact le_refl _
    | skip
  obtain ⟨-, hle⟩ := Loan.tryOverpayment_interestDue_le _ _ _ hlo hint hi ‹Loan.tryOverpayment _ _ = _›
  have h1 := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = _›).1
  dsimp only
  rw [Loan.interestDue_of_raw _ _ h1]
  exact hle

/-- A payment never raises interestDue when a late instalment takes nonnegative interest off the loan, and so do
the scheduled payments before an overpayment tail. With a zero late or overpayment rate the settlement checks that. -/
lemma Loan.pay_interestDue_le (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hlo : -81 ≤ loan.loanScale)
    (hint : loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) (hi : 0 ≤ loan.toExact.interestDue)
    (hlate : pt = .late → loan.rates.lateInterestRate ≠ 0 → ∀ pc d, loan.paymentComponents .late now = .ok pc →
      pc.interestDelta = .ok d → 0 ≤ d.toRat)
    (hover : pt = .overpayment → loan.rates.overpaymentInterestRate ≠ 0 → ∀ p,
      (loan.payInstalments v .regular amount now).run = .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat)
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.toExact.interestDue ≤ loan.toExact.interestDue := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  rw [Loan.settle_interestDue p r hs]
  obtain ⟨_, _, _, _, _, _, _, hsums, -⟩ := UnsettledPayment.settle_ok p r hs
  have hparts := hsums.parts
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hparts
  have hiu : loan.unimpaired.toExact.interestDue = loan.toExact.interestDue := rfl
  have hnn : ∀ x : Number, x.isNormalized → 0 ≤ x.signum → 0 ≤ x.toRat := fun x hx h =>
    (Number.signum_nonneg_iff_toRat hx).mp h
  cases pt
  · obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
    obtain ⟨g, hv⟩ := UnsettledPayment.payInstalments_interestPaid loan.unimpaired amount maxPaymentsPerTransaction
      { loan := loan.unimpaired, pool := p.pool, amounts := PaymentAmounts.zero, totalPaid := Number.zero,
        count := 0, scheduledInterest := si } p hlo hint rfl hi hi (Number.OnGrid.zero _)
      (by simp only [PaymentAmounts.zero, Number.toRat_zero, sub_self]) hloop
    have := hnn _ g.1 hparts.1.2
    rw [hv, hiu] at this
    linarith
  · obtain ⟨pc, hpc, hpa, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    obtain ⟨pc0, hpc0, e1, e2, e3, e4⟩ := Loan.lateComponents_scheduled loan now pc hpc
    by_cases hrate : loan.rates.lateInterestRate = 0
    · obtain ⟨g, hv, -⟩ := Loan.instalment_interestPaid loan.unimpaired p.loan pc0 pc p.amounts hlo hint hi
        (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0) e1 e2 e3 e4
        (Loan.lateComponents_untracked loan now pc hrate hpc) hpa hdo
      have := hnn _ g.1 hparts.1.2
      rw [hv, hiu] at this
      linarith
    · -- the late interest can cover a negative interest part, so the hypothesis rules one out
      obtain ⟨d1, d2, h1, h2, -⟩ := PaymentComponents.paidAmounts_interest pc p.amounts hpa
      have hd : pc.interestDelta = .ok d2 := by
        unfold PaymentComponents.interestDelta
        rw [h1]
        exact h2
      have hv := Loan.instalment_interestDelta loan.unimpaired p.loan pc0 pc p.amounts d2 hlo hint hi
        (by rw [Loan.scheduledComponents_unimpaired]; exact hpc0) e1 e2 e3 e4 hpa hd hdo
      have := hlate rfl hrate pc d2 hpc hd
      rw [hv, hiu] at this
      linarith
  · obtain ⟨pc, hpc, -, hdo⟩ := Loan.fullPayInstalments_ok loan v amount now p hp
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ :=
      Loan.fullComponents_ok_inv loan now pc hpc
    have hpaid : p.loan.paymentRemaining = 0 := by
      simp only [Loan.doPayment, hfin, ↓reduceIte] at hdo
      unfold_ter at hdo
      walk_ok
      exact congrArg RawLoan.paymentRemaining (RawLoan.to_lawful_ok ‹_›).1
    rw [Loan.interestDue_paid p.loan hpaid]
    exact hi
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 h0
    obtain ⟨g, hv⟩ := UnsettledPayment.payInstalments_interestPaid loan.unimpaired amount maxPaymentsPerTransaction
      { loan := loan.unimpaired, pool := p0.pool, amounts := PaymentAmounts.zero, totalPaid := Number.zero,
        count := 0, scheduledInterest := si } p0 hlo hint rfl hi hi (Number.OnGrid.zero _)
      (by simp only [PaymentAmounts.zero, Number.toRat_zero, sub_self]) hloop
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now p0 h0
    have hi0 : 0 ≤ p0.loan.toExact.interestDue :=
      Loan.payInstalments_interestDue loan v .regular amount now p0 (by decide) hlo hint hi h0
    by_cases hrate : loan.rates.overpaymentInterestRate = 0
    · obtain ⟨hip, hle⟩ := UnsettledPayment.applyOverpayment_interest p0 p amount
        (by rw [hst.loanScale]; exact hlo) (by rw [hst.loanScale, hst.broker]; exact hint) hi0
        (by rw [hst.rates]; exact hrate) h1
      have := hnn _ (by rw [hip]; exact g.1) hparts.1.2
      rw [hip, hv, hiu] at this
      linarith
    · -- the overpayment interest can cover a negative interest part, so the hypothesis rules one out
      have hle := UnsettledPayment.applyOverpayment_interestDue_le p0 p amount (by rw [hst.loanScale]; exact hlo)
        (by rw [hst.loanScale, hst.broker]; exact hint) hi0 h1
      have := hover rfl hrate p0 h0
      rw [hv, hiu] at this
      linarith

/-- An integral loan a LoanSet creates has LoanScale at most `0`. -/
lemma Loan.Created.loanScale_integral {start : Loan} {t₀ : UInt32} (h : Loan.Created start t₀) :
    start.broker.numericType.isIntegral = true → start.loanScale ≤ 0 := by
  obtain ⟨broker, v, principal, rates, fees, _, _, _, _, twoStep, allowsOverpayment, r, -, hok, rfl⟩ := h
  obtain ⟨props, _, _, _, broker', _, _, _, _, _, hchecks, -, -, -, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees _ allowsOverpayment twoStep r hok
  have hbase := Vault.baseExponent_scale_range v
  have hls := (computeLoanProperties_loanScale _ _ _ _ _ _ _ _ hchecks.properties_ok hbase.2).2
  have hLS : r.loan'.loanScale = props.loanScale := by
    show r.loan'.toRawLoan.loanScale = _; rw [hl]; rfl
  have hnt : r.loan'.broker.numericType = broker.numericType := by
    show r.loan'.toRawLoan.broker.numericType = _
    rw [hl]
    show broker'.toRawLoanBroker.numericType = _
    rw [hb]
  intro hi
  rw [hLS, hls (by rw [← hnt]; exact hi)]

/-- An impair or unimpair keeps the broker. -/
private lemma Loan.changeImpairment_broker (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : r.loan'.broker = loan.broker := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact (congrArg RawLoan.broker (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1 :)

/-- Every loan transaction keeps the broker's asset. -/
lemma Loan.ReachableFrom.numericType {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    (hr : Loan.ReachableFrom start t₀ loan t) : loan.broker.numericType = start.broker.numericType := by
  induction hr with
  | refl => rfl
  | refresh loan loan' _ b _ hnt h ih =>
    rw [show loan'.broker = loan'.toRawLoan.broker from rfl, (RawLoan.to_lawful_ok h).1]
    exact hnt.trans ih
  | accept loan _ _ v r _ _ _ h ih => rw [Loan.accept_broker loan v r h]; exact ih
  | regularPayment loan _ _ v amount r _ _ _ h ih => rw [Loan.pay_numericType loan v .regular amount _ r h]; exact ih
  | latePayment loan _ _ v amount r _ _ _ h ih => rw [Loan.pay_numericType loan v .late amount _ r h]; exact ih
  | fullPayment loan _ _ v amount r _ _ _ h ih => rw [Loan.pay_numericType loan v .full amount _ r h]; exact ih
  | overpayment loan _ _ v amount r _ _ _ h ih =>
    rw [Loan.pay_numericType loan v .overpayment amount _ r h]; exact ih
  | impair loan _ t' v r _ _ _ h ih =>
    simp only [Loan.manageImpair] at h
    unfold_ter at h
    walk_ok
    rw [Loan.changeImpairment_broker loan v true r ‹_›]; exact ih
  | unimpair loan _ _ v r _ _ _ h ih => rw [Loan.changeImpairment_broker loan v false r h]; exact ih
  | default loan _ _ v r _ _ _ h ih =>
    obtain ⟨_, _, _, _, broker', -, -, -, -, -, -, hb, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
    rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]
    show broker'.toRawLoanBroker.numericType = _
    rw [hb]
    exact ih

end XRPL.Model.Lending
