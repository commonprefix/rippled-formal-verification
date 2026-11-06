import XRPL.Properties.Lending.Loan.Common.ScheduledDue
import XRPL.Properties.Lending.Loan.Common.RegularPayoff
import XRPL.Properties.Lending.Loan.Common.PaymentRoom
import XRPL.Properties.Lending.Loan.Common.PaySize
import XRPL.Properties.Lending.Loan.Common.ManageCover
import XRPL.Properties.Lending.Loan.Common.TheoreticalPrincipal

/-! # What a payment charges against requestedAmount

While the amount due fits 16 digits at LoanScale each scheduled, late or full instalment charges exactly its totalDue,
and the extra amount of an overpayment charges at most what is left of requestedAmount rounded towards zero. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.doPayment_interestDue from XRPL.Properties.Lending.Loan.Common.InterestDue
open private PaymentAmounts.add_parts from XRPL.Properties.Lending.Loan.Common.RegularPayoff
open private Loan.Reachable.pay_facts from XRPL.Properties.Lending.Loan.Common.PaySums
open private Loan.overpaymentComponents Loan.tryOverpayment roundAndSplitInterest UnsettledPayment.applyOverpayment
  from XRPL.Model.Lending.Loan.LoanPay
open private computeManagementFee_le from XRPL.Properties.Lending.Loan.Common.PaySums
open private STAmount.ofNumber_towards_zero_le from XRPL.Properties.Lending.Loan.Common.ManageCover
open private LoanState.calculateDeltas_principal from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Loan.lateComponents Loan.fullComponents Loan.unimpairIfImpaired from XRPL.Model.Lending.Loan.LoanPay
open private Loan.payInstalment_parts Loan.late_instalment_charge from XRPL.Properties.Lending.Loan.Common.PaySums
open private Loan.unimpairIfImpaired_loan from XRPL.Properties.Lending.Loan.Common.PaySteps
open private Loan.lateComponents_norm from XRPL.Properties.Lending.Loan.Common.PayBounds
open private Number.OnGrid.unitsAt from XRPL.Properties.Lending.Loan.Common.FullPaymentSize

/-- What the scheduled payments summed so far charge, read exactly against the loan they started from, which owed
`T0` of value, `P0` of principal and `M0` of management fee. -/
private structure UnsettledPayment.Charges {α : Type} (p : UnsettledPayment α) (s : Int) (nt : NumericType)
    (fee : Number) (T0 P0 M0 : ℚ) : Prop where
  loanScale : p.loan.loanScale = s
  numericType : p.loan.broker.numericType = nt
  serviceFee : p.loan.fees.serviceFee = fee
  interest_nonneg : 0 ≤ p.loan.toExact.interestDue
  charged : p.totalPaid.toRat = (T0 - p.loan.totalValueOutstanding.toRat) + fee.toRat * p.count
  principal : p.amounts.principalPaid.toRat = P0 - p.loan.principalOutstanding.toRat
  interest : p.amounts.interestPaid.toRat = (T0 - p.loan.totalValueOutstanding.toRat) -
    (P0 - p.loan.principalOutstanding.toRat) - (M0 - p.loan.managementFeeOutstanding.toRat)
  feePart : p.amounts.feePaid.toRat = (M0 - p.loan.managementFeeOutstanding.toRat) + fee.toRat * p.count
  value_le : p.loan.totalValueOutstanding.toRat ≤ T0
  principal_le : p.loan.principalOutstanding.toRat ≤ P0
  mgmt_le : p.loan.managementFeeOutstanding.toRat ≤ M0
  charged_grid : Number.OnGrid s p.totalPaid
  principal_grid : Number.OnGrid s p.amounts.principalPaid
  interest_grid : Number.OnGrid s p.amounts.interestPaid
  fee_grid : Number.OnGrid s p.amounts.feePaid

/-- One more regular instalment keeps the sums exact, while the loan owes at most `10^16 + 1` units, LoanServiceFee
is below `10^16` units and at most 100 instalments are paid. -/
private lemma UnsettledPayment.Charges.step {α : Type} {p : UnsettledPayment α} {s : Int} {nt : NumericType}
    {fee : Number} {T0 P0 M0 : ℚ} (hm : p.Charges s nt fee T0 P0 M0) (hlo : -81 ≤ s)
    (hnt : nt.isIntegral = true → s ≤ 0) (gfee : Number.OnGrid s fee) (hfee0 : 0 ≤ fee.toRat)
    (hT0b : T0 ≤ (10 ^ 16 + 1) * 10 ^ s) (hfeeb : fee.toRat < 10 ^ 16 * 10 ^ s) (hcount : p.count + 1 ≤ 100)
    (hPT : P0 ≤ T0) (hMT : M0 ≤ T0)
    {pc : PaymentComponents} {due tp : Number} {inst amounts' : PaymentAmounts} {loan' : Loan}
    (hpc : Loan.scheduledComponents p.loan = .ok pc)
    (hdue : ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents).totalDue = .ok due)
    (hpa : ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents).paidAmounts = .ok inst)
    (hdo : Loan.doPayment p.loan { pc with untrackedManagementFee := p.loan.fees.serviceFee } = .ok loan')
    (hadd : p.amounts.add inst = .ok amounts') (htp : p.totalPaid.operator_add due .to_nearest = .ok tp) :
    ({ p with loan := loan', amounts := amounts', totalPaid := tp, count := p.count + 1 } :
      UnsettledPayment α).Charges s nt fee T0 P0 M0 := by
  have hls := hm.loanScale
  have hsb : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1 := by rw [← hls]; exact Loan.loanScale_bounds p.loan
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hfee := hm.serviceFee
  rw [hfee] at hdue hpa hdo
  have hint : p.loan.broker.numericType.isIntegral = true → p.loan.loanScale ≤ 0 := fun h => by
    rw [hls]; exact hnt (by rw [← hm.numericType]; exact h)
  -- the counts as rationals: LoanServiceFee charged so far is at most 99 times LoanServiceFee
  set c : ℚ := (p.count : ℚ) with hc
  set f : ℚ := fee.toRat with hf
  have hc0 : 0 ≤ c := by positivity
  have hc99 : c ≤ 99 := by rw [hc]; exact_mod_cast (by omega : p.count ≤ 99)
  have hfc0 : 0 ≤ f * c := mul_nonneg hfee0 hc0
  have hfc : f * c ≤ 99 * f := by nlinarith
  have hT := hm.value_le
  have hP := hm.principal_le
  have hM := hm.mgmt_le
  have hT0 : 0 ≤ T0 := le_trans p.loan.exact.totalValueOutstanding_nonneg hT
  have hTb : p.loan.totalValueOutstanding.toRat + fee.toRat < 2 ^ 62 * 10 ^ p.loan.loanScale := by
    rw [hls]; nlinarith
  have hmv := Loan.regularInstalment_moves p.loan loan' pc fee due inst (by rw [hls]; exact hlo) hint
    hm.interest_nonneg (by rw [hls]; exact gfee) hfee0 hTb hpc hdue hpa hdo
  have gdue := hmv.charge_grid
  have gpp := hmv.grid_principal
  have gip := hmv.grid_interest
  have gfp := hmv.grid_fee
  rw [hls] at gdue gpp gip gfp
  have hkt := Loan.doPayment_keepsTerms _ _ _ hdo
  have hst := Loan.doPayment_sameTerms _ _ _ hdo
  obtain ⟨a1, a2, a3⟩ := PaymentAmounts.add_parts _ _ _ hadd
  obtain ⟨-, -, -, -, hP', hM', -⟩ := Loan.outstanding_grid loan'
  have hT' : 0 ≤ loan'.totalValueOutstanding.toRat := loan'.exact.totalValueOutstanding_nonneg
  have hTv := hmv.value_le
  have hPv := hmv.principal_le
  have hMv := hmv.fee_le
  have hB : (10 ^ 16 + 1) * (10 : ℚ) ^ s + 100 * (10 ^ 16 * 10 ^ s) < 2 ^ 63 * 10 ^ s := by nlinarith
  have vtp := Number.OnGrid.add_toRat hm.charged_grid gdue hsb (by
    rw [hm.charged, hmv.charge, abs_lt]; constructor <;> nlinarith) htp
  have vpp := Number.OnGrid.add_toRat hm.principal_grid gpp hsb (by
    rw [hm.principal, hmv.principal, abs_lt]; constructor <;> nlinarith) a1
  have vip := Number.OnGrid.add_toRat hm.interest_grid gip hsb (by
    rw [hm.interest, hmv.interest, abs_lt]; constructor <;> nlinarith) a2
  have vfp := Number.OnGrid.add_toRat hm.fee_grid gfp hsb (by
    rw [hm.feePart, hmv.feePart, abs_lt]; constructor <;> nlinarith) a3
  have hi' : 0 ≤ loan'.toExact.interestDue := by
    refine Loan.doPayment_interestDue _ _ _ hm.interest_nonneg ?_ hdo
    rcases Loan.scheduledComponents_tracked p.loan pc (by rw [hls]; exact hlo) hint hm.interest_nonneg hpc with
      hf | ⟨hf, ht⟩
    · exact Or.inl hf
    · exact Or.inr ⟨hf, ht.totalValue_grid, ht.principal_grid, ht.managementFee_grid, ht.totalValue_range,
        ht.principal_range, ht.managementFee_range, ht.interest_le, ht.managementFee_le_value⟩
  refine ⟨by rw [hkt.loanScale, hls], by rw [hst.broker]; exact hm.numericType, by rw [hkt.fees, hfee], hi',
    ?_, ?_, ?_, ?_, by linarith [hmv.value_le], by linarith [hmv.principal_le, hm.principal_le],
    by linarith [hmv.fee_le, hm.mgmt_le], Number.OnGrid.add hm.charged_grid gdue hsb htp,
    Number.OnGrid.add hm.principal_grid gpp hsb a1,
    Number.OnGrid.add hm.interest_grid gip hsb a2,
    Number.OnGrid.add hm.fee_grid gfp hsb a3⟩
  · show tp.toRat = _
    rw [vtp, hm.charged, hmv.charge]; push_cast; ring
  · show amounts'.principalPaid.toRat = _
    rw [vpp, hm.principal, hmv.principal]; ring
  · show amounts'.interestPaid.toRat = _
    rw [vip, hm.interest, hmv.interest]; ring
  · show amounts'.feePaid.toRat = _
    rw [vfp, hm.feePart, hmv.feePart]; push_cast; ring

/-- The regular instalments of a payment keep the sums exact. -/
private lemma UnsettledPayment.payInstalments_charges {α : Type} (amount : Number) (s : Int) (nt : NumericType)
    (fee : Number) (T0 P0 M0 : ℚ) (hlo : -81 ≤ s) (hnt : nt.isIntegral = true → s ≤ 0)
    (gfee : Number.OnGrid s fee) (hfee0 : 0 ≤ fee.toRat) (hT0b : T0 ≤ (10 ^ 16 + 1) * 10 ^ s)
    (hfeeb : fee.toRat < 10 ^ 16 * 10 ^ s) (hPT : P0 ≤ T0) (hMT : M0 ≤ T0) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      payment.count + n ≤ 100 → payment.Charges s nt fee T0 P0 M0 → p.Charges s nt fee T0 P0 M0 := by
  intro n
  induction n with
  | zero =>
    intro payment p h _ hm
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hm
  | succ k ih =>
    intro payment p h hn hm
    unfold UnsettledPayment.payInstalments at h
    unfold_ter at h
    walk_ok
    · exact hm
    · exact hm
    · exact hm.step hlo hnt gfee hfee0 hT0b hfeeb (by omega) hPT hMT ‹Loan.scheduledComponents payment.loan = _›
        ‹PaymentComponents.totalDue _ = _› ‹PaymentComponents.paidAmounts _ = _› ‹Loan.doPayment _ _ = _›
        ‹PaymentAmounts.add _ _ = _› ‹payment.totalPaid.operator_add _ _ = _›
    · rename_i hrec
      exact ih _ p hrec (by dsimp only; omega) (hm.step hlo hnt gfee hfee0 hT0b hfeeb (by omega) hPT hMT
        ‹Loan.scheduledComponents payment.loan = _› ‹PaymentComponents.totalDue _ = _›
        ‹PaymentComponents.paidAmounts _ = _› ‹Loan.doPayment _ _ = _› ‹PaymentAmounts.add _ _ = _›
        ‹payment.totalPaid.operator_add _ _ = _›)

/-- The scheduled payments of a reachable loan charge exactly what they are due, when they are due less than
`10^16` LoanScale units. -/
private lemma Loan.regular_charges (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (p : UnsettledPayment Vault) (hreach : loan.Reachable t)
    (hp : (loan.payInstalments v .regular amount now).run = .ok (.ok p))
    (hdue : p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    p.Charges loan.loanScale loan.broker.numericType loan.fees.serviceFee loan.totalValueOutstanding.toRat
      loan.principalOutstanding.toRat loan.managementFeeOutstanding.toRat := by
  obtain ⟨hlo, hint, hi, gs, -⟩ := Loan.Reachable.pay_facts hreach
  have hfee0 : 0 ≤ loan.fees.serviceFee.toRat := loan.exact.serviceFee_nonneg
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
  have hiD : 0 ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := hi
  have hfee := (Loan.regularPayment_dues loan v amount now p hp).1
  obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
  have u1 : loan.unimpaired.totalValueOutstanding = loan.totalValueOutstanding := rfl
  have u2 : loan.unimpaired.principalOutstanding = loan.principalOutstanding := rfl
  have u3 : loan.unimpaired.managementFeeOutstanding = loan.managementFeeOutstanding := rfl
  have hstart : (⟨loan.unimpaired, p.pool, PaymentAmounts.zero, Number.zero, 0, si⟩ :
      UnsettledPayment Vault).Charges loan.loanScale loan.broker.numericType loan.fees.serviceFee
      loan.totalValueOutstanding.toRat loan.principalOutstanding.toRat loan.managementFeeOutstanding.toRat :=
    ⟨rfl, rfl, rfl, hi, by simp [Number.toRat_zero, u1], by simp [PaymentAmounts.zero, Number.toRat_zero, u2],
      by simp [PaymentAmounts.zero, Number.toRat_zero, u1, u2, u3],
      by simp [PaymentAmounts.zero, Number.toRat_zero, u3], le_refl _, le_refl _, le_refl _,
      Number.OnGrid.zero _, Number.OnGrid.zero _, Number.OnGrid.zero _, Number.OnGrid.zero _⟩
  exact UnsettledPayment.payInstalments_charges amount _ _ _ _ _ _ hlo hint gs hfee0 hreach.totalValue_le
    (by linarith) (by linarith) (by linarith) _ _ _ hloop (by simp [maxPaymentsPerTransaction]) hstart

/-- The parts a payment with exact sums charges add up to its totalPaid. -/
private lemma UnsettledPayment.Charges.sum {α : Type} {p : UnsettledPayment α} {s : Int} {nt : NumericType}
    {fee : Number} {T0 P0 M0 : ℚ} (hm : p.Charges s nt fee T0 P0 M0) :
    p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat = p.totalPaid.toRat := by
  rw [hm.principal, hm.interest, hm.feePart, hm.charged]; ring

/-- The parts of an overpayment that pays some principal add up to it exactly: the principal, the interest, its
management fee and the overpayment fee, each on the LoanScale grid and the last three at least zero. -/
private lemma Loan.overpaymentComponents_parts (l : Loan) (ov : Number) (opc : PaymentComponents)
    (gov : Number.OnGrid l.loanScale ov) (hov0 : 0 ≤ ov.toRat) (hovb : ov.toRat < 2 ^ 62 * 10 ^ l.loanScale)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (h : Loan.overpaymentComponents l ov = .ok opc) (hpd : 0 < opc.principalDelta.toRat) :
    Number.OnGrid l.loanScale opc.principalDelta ∧ Number.OnGrid l.loanScale opc.untrackedInterest ∧
      Number.OnGrid l.loanScale opc.managementFeeDelta ∧ Number.OnGrid l.loanScale opc.untrackedManagementFee ∧
      0 ≤ opc.untrackedInterest.toRat ∧ 0 ≤ opc.managementFeeDelta.toRat ∧
      0 ≤ opc.untrackedManagementFee.toRat ∧
      opc.principalDelta.toRat + opc.untrackedInterest.toRat + opc.managementFeeDelta.toRat +
        opc.untrackedManagementFee.toRat = ov.toRat := by
  have hs := Loan.loanScale_bounds l
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  have hu : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  unfold Loan.overpaymentComponents at h
  obtain ⟨of, hof, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨of', hof', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨oi, hoi, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨⟨net, mf⟩, hsplit, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pai, hpai, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨paf, hpaf, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pd, hpdv, h⟩ := bind_ok_peel _ _ _ h
  obtain rfl := (Except.ok.inj h).symm
  simp only at hpd ⊢
  obtain ⟨hofN, hof0, -⟩ := tenthBipsOfValue_le_share _ _ _ gov.1 hov0 hof
  have gof' := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hof'
  have hof'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hofN hof0 (Or.inl rfl) hr hof'
  obtain ⟨hoiN, hoi0, -⟩ := tenthBipsOfValue_le_share _ _ _ gov.1 hov0 hoi
  obtain ⟨lr, hlr, hfee, hnet⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ hsplit
  have glr := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hlr
  have hlr0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hoiN hoi0 (Or.inl rfl) hr hlr
  obtain ⟨gmf, hmf0, hmflr⟩ := computeManagementFee_le _ _ _ _ _ glr.1 hlr0 l.broker.managementFeeRate_le hr hint hfee
  have gnet := Number.OnGrid.sub glr gmf hs hnet
  have hnet0 := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
    (operator_sub_rounded_to_nearest _ _ _ glr.1 gmf.1 hnet) (by linarith)
  -- some principal is left, so each part comes off a positive remainder and every difference is exact
  have gpai := Number.OnGrid.sub gov gnet hs hpai
  have gpaf := Number.OnGrid.sub gpai gmf hs hpaf
  have gpd := Number.OnGrid.sub gpaf gof' hs hpdv
  have h3 : of'.toRat < paf.toRat := by
    by_contra hc
    push Not at hc
    have := (Number.sub_near _ _ _ gpaf.1 gof'.1 hpdv).nonpos (by linarith)
    linarith
  have h2 : mf.toRat < pai.toRat := by
    by_contra hc
    push Not at hc
    have := (Number.sub_near _ _ _ gpai.1 gmf.1 hpaf).nonpos (by linarith)
    linarith
  have h1 : net.toRat < ov.toRat := by
    by_contra hc
    push Not at hc
    have := (Number.sub_near _ _ _ gov.1 gnet.1 hpai).nonpos (by linarith)
    linarith
  have hb : (2 : ℚ) ^ 62 * 10 ^ l.loanScale < 2 ^ 63 * 10 ^ l.loanScale := by nlinarith
  have vpai := Number.OnGrid.sub_toRat gov gnet hs (by rw [abs_lt]; constructor <;> linarith) hpai
  have vpaf := Number.OnGrid.sub_toRat gpai gmf hs (by rw [abs_lt]; constructor <;> linarith) hpaf
  have vpd := Number.OnGrid.sub_toRat gpaf gof' hs (by rw [abs_lt]; constructor <;> linarith) hpdv
  refine ⟨gpd, gnet, gmf, gof', hnet0, hmf0, hof'0, ?_⟩
  rw [vpd, vpaf, vpai]
  ring

/-- Rounding up at a scale never lowers an amount on that scale's grid, at least zero. -/
private lemma STAmount.roundToNumericType_upward_grid (nt : NumericType) (x T : Number) (s : ℤ)
    (hx : Number.OnGrid s x) (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80)
    (hok : STAmount.roundToNumericType nt x .upward (some s) = .ok T) : x.toRat ≤ T.toRat := by
  rcases eq_or_lt_of_le h0 with hz | hpos
  · rw [← hz]
    exact STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hx.1 h0 (Or.inr (Or.inl rfl)) hs hok
  refine STAmount.roundToNumericType_upward_ge_of_large nt x T s hx.1 ?_ hs hok
  obtain ⟨-, k, hk⟩ := hx
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hk1 : (1 : ℤ) ≤ k := by
    by_contra hc
    push Not at hc
    have : (k : ℚ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
    rw [hk] at hpos
    nlinarith
  rw [hk]
  calc (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ s := zpow_le_zpow_right₀ (by norm_num) hs.1
    _ = 1 * 10 ^ s := (one_mul _).symm
    _ ≤ (k : ℚ) * 10 ^ s := mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) hp.le

/-- A re-amortization pays at most the overpayment's principal. The new PrincipalOutstanding is the old one less
that principal, rounded up and clamped into `[0, PrincipalOutstanding]`, and it must drop. -/
private lemma Loan.reamortized_principal_le (l : Loan) (opc : PaymentComponents) {st s11 s5 : LoanState}
    {pin pm vo po tvo' mfo : Number} {de : LoanStateDeltas}
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (gpd : Number.OnGrid l.loanScale opc.principalDelta) (hpd0 : 0 ≤ opc.principalDelta.toRat)
    (hpdb : opc.principalDelta.toRat < 2 ^ 62 * 10 ^ l.loanScale)
    (hst : l.state = .ok st)
    (hpin : st.principalOutstanding.operator_sub opc.principalDelta .to_nearest = .ok pin)
    (hb11 : LoanState.build vo pin pm = .ok s11)
    (hpo : roundAndClamp s11.principalOutstanding st.principalOutstanding .upward l.broker.numericType l.loanScale =
      .ok po)
    (hb5 : LoanState.build tvo' po mfo = .ok s5) (hdl : st.calculateDeltas s5 = .ok de)
    (hguard : ¬ st.principalOutstanding.operator_le po = true) :
    Number.OnGrid l.loanScale de.principal ∧ 0 ≤ de.principal.toRat ∧
      de.principal.toRat ≤ opc.principalDelta.toRat := by
  have hs := Loan.loanScale_bounds l
  have hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 80 := ⟨hlo, l.wf.loanScale_range.2⟩
  have hu : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  obtain ⟨gP, hPlt⟩ := Loan.principal_onGrid l
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  -- the current state holds the loan's PrincipalOutstanding, and the pinned principal is it less the overpayment's
  obtain ⟨-, hsP, -, -⟩ := LoanState.build_ok hst
  rw [hsP] at hpin hpo hguard
  obtain ⟨-, h11P, -, -⟩ := LoanState.build_ok hb11
  rw [h11P] at hpo
  obtain ⟨-, h5P, -, -⟩ := LoanState.build_ok hb5
  have hdp := LoanState.calculateDeltas_principal _ _ _ hdl
  rw [h5P, hsP] at hdp
  have gpin := Number.OnGrid.sub gP gpd hs hpin
  have vpin := Number.OnGrid.sub_toRat gP gpd hs (by rw [abs_lt]; constructor <;> nlinarith) hpin
  obtain ⟨rpo, hrpo, rfl⟩ := roundAndClamp_ok hpo
  have grpo := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint hrpo
  have gpo := Number.OnGrid.clamp grpo (Number.OnGrid.zero _) gP
  have hlt : (Number.clamp rpo Number.zero l.principalOutstanding).toRat < l.principalOutstanding.toRat := by
    have := (operator_le_iff _ _ gP.1 gpo.1).not.mp hguard
    push Not at this
    exact this
  have hpo_ge : pin.toRat ≤ (Number.clamp rpo Number.zero l.principalOutstanding).toRat := by
    rcases Number.clamp_zero_cases rpo l.principalOutstanding grpo.1 gP.1 with ⟨hneg, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    · rw [he, Number.toRat_zero]
      by_contra hc
      push Not at hc
      have := STAmount.roundToNumericType_upward_grid _ _ _ _ gpin hc.le hr hrpo
      linarith
    · rw [he] at hlt; exact absurd hlt (lt_irrefl _)
    · rw [he]
      rcases le_or_gt 0 pin.toRat with h0 | h0
      · exact STAmount.roundToNumericType_upward_grid _ _ _ _ gpin h0 hr hrpo
      · linarith
  have hpo0 : 0 ≤ (Number.clamp rpo Number.zero l.principalOutstanding).toRat := by
    rcases Number.clamp_zero_cases rpo l.principalOutstanding grpo.1 gP.1 with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨h1, _, he⟩
    · rw [he, Number.toRat_zero]
    · rw [he]; exact hP0
    · rw [he]; exact h1
  have vdp := Number.OnGrid.sub_toRat gP gpo hs (by rw [abs_lt]; constructor <;> nlinarith) hdp
  exact ⟨Number.OnGrid.sub gP gpo hs hdp, by rw [vdp]; linarith, by rw [vdp]; linarith⟩

/-- What a re-amortization that passes pays: the overpayment's interest, its management fee plus the overpayment
fee, and at most the overpayment's principal. -/
private lemma Loan.tryOverpayment_amounts (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (gpd : Number.OnGrid l.loanScale opc.principalDelta) (hpd0 : 0 ≤ opc.principalDelta.toRat)
    (hpdb : opc.principalDelta.toRat < 2 ^ 62 * 10 ^ l.loanScale)
    (h : Loan.tryOverpayment l opc = .ok (some re)) :
    re.amounts.interestPaid = opc.untrackedInterest ∧
      opc.managementFeeDelta.operator_add opc.untrackedManagementFee .to_nearest = .ok re.amounts.feePaid ∧
      Number.OnGrid l.loanScale re.amounts.principalPaid ∧ 0 ≤ re.amounts.principalPaid.toRat ∧
      re.amounts.principalPaid.toRat ≤ opc.principalDelta.toRat := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  exact ⟨rfl, ‹_›, Loan.reamortized_principal_le l opc hlo hint gpd hpd0 hpdb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›⟩

/-- Rounding towards zero at a scale stays between zero and a value that is not negative. -/
private lemma STAmount.roundToNumericType_towards_zero_some_le (nt : NumericType) (x c : Number) (e : Int)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (he : (-96 : ℤ) ≤ e ∧ e ≤ 80)
    (h : STAmount.roundToNumericType nt x .towards_zero (some e) = .ok c) : 0 ≤ c.toRat ∧ c.toRat ≤ x.toRat := by
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber nt x .towards_zero with
  | error err => rw [hof] at h; exact absurd h (by simp)
  | ok ret =>
    rw [hof] at h
    simp only at h
    obtain ⟨hret0, hretle⟩ := STAmount.ofNumber_towards_zero_le nt x ret hx h0 hof
    by_cases hint : ret.integral = true
    · rw [if_pos hint] at h
      obtain ⟨hv, -⟩ := STAmount.ofNumber_toNumber_exact nt x _ _ ret c hx (fun _ => h0) hof h
      exact ⟨hv ▸ hret0, hv ▸ hretle⟩
    rw [if_neg hint] at h
    have hnt : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral _ _ _ _ =>
        exfalso; apply hint
        unfold STAmount.integral; rw [STAmount.ofNumber_mNumericType _ _ _ _ hof]; rfl
    subst hnt
    cases hre : STAmount.roundToExponent ret e .towards_zero with
    | error err => rw [hre] at h; exact absurd h (by simp)
    | ok rounded =>
      rw [hre] at h
      simp only at h
      -- the rounded amount is the floor of `ret` on the scale grid, or zero
      have hrv : 0 ≤ rounded.toRat ∧ rounded.toRat ≤ ret.toRat := by
        by_cases hz : rounded.mValue = 0
        · rw [STAmount.toRat_eq_zero_of_mValue_zero rounded hz]; exact ⟨le_refl _, hret0⟩
        have hint' : ret.integral = false := by simpa using hint
        by_cases hrz : ret.mValue = 0
        · have : rounded = ret := by
            unfold STAmount.roundToExponent at hre
            simp only [hint', Bool.false_eq_true, if_false, STAmount.isZero, hrz, beq_self_eq_true, if_true,
              Except.ok.injEq] at hre
            exact hre.symm
          rw [this]; exact ⟨hret0, le_refl _⟩
        have hnz : x.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional x _ ret hof hrz
        obtain ⟨hlo, hhi⟩ := hx.mantissaBounds_nat hnz
        have hc := (STAmount.ofNumber_iou_ok_facts x _ ret hlo hhi (Number.exponent_ge_min x hx hnz) hof hrz).1
        have hfl := STAmount.roundToExponent_rounded ret rounded e .towards_zero hc he.1 he.2 hz hre
        have hp : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
        unfold RoundsToRepresentableAt at hfl
        simp only [ge_iff_le, hret0, if_true] at hfl
        change rounded.toRat = _ at hfl
        rw [hfl]
        refine ⟨by positivity, ?_⟩
        have := Int.floor_le (ret.toRat / 10 ^ e)
        rw [le_div_iff₀ hp] at this
        exact this
      -- the rounded amount is stored canonically, so its `Number` has the same value
      have hfc := STAmount.roundToExponent_fczr ret rounded e .towards_zero
        (STAmount.ofNumber_fractional_fczr x _ ret hof) hre
      have hcv : c.toRat = rounded.toRat := by
        rcases hfc.2 with hc' | hz'
        · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact rounded .towards_zero hc'
          rw [hsn, Except.ok.injEq] at h
          rw [← h, hv]
        · exact (STAmount.toNumber_zero_facts rounded _ c hz' h).1
      rw [hcv]
      exact ⟨hrv.1, hrv.2.trans hretle⟩

/-- The scheduled payments plus the extra amount of an overpayment pay at most requestedAmount in principal,
interest and fee. -/
private lemma UnsettledPayment.overpayment_tail_le (p0 : UnsettledPayment Vault) (amount : Number) {s : Int}
    {nt : NumericType} {fee : Number} {T0 P0 M0 : ℚ} (hm : p0.Charges s nt fee T0 P0 M0) (hlo : -81 ≤ s)
    (hnt : nt.isIntegral = true → s ≤ 0) (hT0b : T0 ≤ (10 ^ 16 + 1) * 10 ^ s) (hfeeb : fee.toRat < 10 ^ 16 * 10 ^ s)
    (hfee0 : 0 ≤ fee.toRat) (hPT : P0 ≤ T0) (hMT : M0 ≤ T0) (hcount : p0.count ≤ 100)
    (hamount : amount.isNormalized) (hcov : p0.totalPaid.toRat ≤ amount.toRat)
    {a' un ov : Number} {opc : PaymentComponents} {re : Reamortization} {am : PaymentAmounts}
    (ha' : STAmount.roundToNumericType p0.loan.broker.numericType amount .towards_zero (some p0.loan.loanScale) =
      .ok a')
    (hcond : ¬(!(p0.loan.allowsOverpayment && p0.loan.paymentRemaining != 0 && p0.totalPaid.operator_lt a' &&
      decide (p0.count < maxPaymentsPerTransaction))) = true)
    (hun : a'.operator_sub p0.totalPaid .to_nearest = .ok un)
    (hov : STAmount.roundToNumericType p0.loan.broker.numericType (un.min p0.loan.totalValueOutstanding) .downward
      (some p0.loan.loanScale) = .ok ov)
    (hopc : Loan.overpaymentComponents p0.loan ov = .ok opc)
    (hpd : ¬(!opc.principalDelta.operator_gt Number.zero) = true)
    (hre : Loan.tryOverpayment p0.loan opc = .ok (some re)) (ham : p0.amounts.add re.amounts = .ok am) :
    am.principalPaid.toRat + am.interestPaid.toRat + am.feePaid.toRat ≤ amount.toRat := by
  have hls := hm.loanScale
  have hsb : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1 := by rw [← hls]; exact Loan.loanScale_bounds p0.loan
  have hr : -81 ≤ s ∧ s ≤ 80 := ⟨hlo, by rw [← hls]; exact p0.loan.wf.loanScale_range.2⟩
  have hu : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hint : p0.loan.broker.numericType.isIntegral = true → p0.loan.loanScale ≤ 0 := fun h => by
    rw [hls]; exact hnt (by rw [← hm.numericType]; exact h)
  have hint' : p0.loan.broker.numericType.isIntegral = true → s ≤ 0 := fun h => by rw [← hls]; exact hint h
  have hT := hm.value_le
  have hP := hm.principal_le
  have hM := hm.mgmt_le
  have hTL : 0 ≤ p0.loan.totalValueOutstanding.toRat := p0.loan.exact.totalValueOutstanding_nonneg
  have hPL : 0 ≤ p0.loan.principalOutstanding.toRat := p0.loan.exact.principalOutstanding_nonneg
  have hML : 0 ≤ p0.loan.managementFeeOutstanding.toRat := p0.loan.exact.managementFeeOutstanding_nonneg
  have hc0 : (0 : ℚ) ≤ p0.count := by positivity
  have hc100 : (p0.count : ℚ) ≤ 100 := by exact_mod_cast hcount
  have hfc : fee.toRat * p0.count ≤ 100 * fee.toRat := by nlinarith
  have hfc0 : 0 ≤ fee.toRat * p0.count := mul_nonneg hfee0 hc0
  have htp0 : 0 ≤ p0.totalPaid.toRat := by rw [hm.charged]; linarith
  rw [hls] at ha' hov
  -- the requestedAmount rounded towards zero at LoanScale: on the grid, at most requestedAmount, above totalPaid
  obtain ⟨-, ha'le⟩ := STAmount.roundToNumericType_towards_zero_some_le _ _ _ _ hamount (le_trans htp0 hcov)
    ⟨by omega, hr.2⟩ ha'
  have ga' := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint' ha'
  have hlt : p0.totalPaid.toRat < a'.toRat := by
    have : p0.totalPaid.operator_lt a' = true := by
      revert hcond; cases p0.totalPaid.operator_lt a' <;> simp
    exact (operator_lt_iff _ _ hm.charged_grid.1 ga'.1).mp this
  -- the leftover, capped at TotalValueOutstanding and rounded down
  have hunN := operator_sub_isNormalized_to_nearest_sz _ _ _ ga'.1 hm.charged_grid.1 hun
  have hun0 := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
    (operator_sub_rounded_to_nearest _ _ _ ga'.1 hm.charged_grid.1 hun) (by linarith)
  have hmin : (un.min p0.loan.totalValueOutstanding).isNormalized ∧
      0 ≤ (un.min p0.loan.totalValueOutstanding).toRat ∧
      (un.min p0.loan.totalValueOutstanding).toRat ≤ p0.loan.totalValueOutstanding.toRat ∧
      (un.min p0.loan.totalValueOutstanding).toRat ≤ un.toRat := by
    unfold Number.min
    split
    · rename_i hc
      exact ⟨p0.loan.wf.totalValueOutstanding_norm, hTL, le_rfl,
        ((operator_lt_iff _ _ p0.loan.wf.totalValueOutstanding_norm hunN).mp hc).le⟩
    · rename_i hn
      exact ⟨hunN, hun0, (operator_lt_eq_false_iff _ _ p0.loan.wf.totalValueOutstanding_norm hunN).mp
        (by simpa using hn), le_rfl⟩
  obtain ⟨hmN, hm0, hmT, hmun⟩ := hmin
  have hovN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hov
  have hov0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hmN hm0 (Or.inr (Or.inr rfl)) hr hov
  have hovle := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hmN hm0 hr hov
  have gov := STAmount.roundToNumericType_onGrid _ _ _ _ _ hr hint' hov
  have hovT : ov.toRat ≤ (10 ^ 16 + 1) * 10 ^ s := by linarith
  have h62 : (10 ^ 16 + 1) * (10 : ℚ) ^ s < 2 ^ 62 * 10 ^ s := by nlinarith
  have hova : ov.toRat ≤ a'.toRat - p0.totalPaid.toRat := by
    by_cases hbig : a'.toRat - p0.totalPaid.toRat < 2 ^ 63 * 10 ^ s
    · have := Number.OnGrid.sub_toRat ga' hm.charged_grid hsb (by rw [abs_lt]; constructor <;> linarith) hun
      linarith
    · push Not at hbig
      nlinarith
  have hpdN := Loan.overpaymentComponents_principalDelta_normalized _ _ _ hovN hopc
  have hpd' : 0 < opc.principalDelta.toRat := by
    have : opc.principalDelta.operator_gt Number.zero = true := by
      revert hpd; cases opc.principalDelta.operator_gt Number.zero <;> simp
    have := (operator_gt_iff _ _ hpdN Number.zero_isNormalized).mp this
    rwa [Number.toRat_zero] at this
  obtain ⟨gpd, gui, gmf, gumf, hui0, hmf0, humf0, hsum⟩ := Loan.overpaymentComponents_parts p0.loan ov opc
    (by rw [hls]; exact gov) hov0 (by rw [hls]; linarith) (by rw [hls]; exact hlo) hint hopc hpd'
  obtain ⟨hreI, hreF, gPre, hPre0, hPrele⟩ := Loan.tryOverpayment_amounts p0.loan opc re (by rw [hls]; exact hlo)
    hint gpd hpd'.le (by rw [hls]; linarith) hre
  rw [hls] at gpd gui gmf gumf gPre
  have hb : (2 : ℚ) ^ 62 * 10 ^ s < 2 ^ 63 * 10 ^ s := by nlinarith
  have vF := Number.OnGrid.add_exact gmf gumf hmf0 humf0 (by linarith) hsb hreF
  have gF := Number.OnGrid.add gmf gumf hsb hreF
  obtain ⟨a1, a2, a3⟩ := PaymentAmounts.add_parts _ _ _ ham
  rw [hreI] at a2
  have hB3 : 3 * ((10 ^ 16 + 1) * (10 : ℚ) ^ s) + 100 * (10 ^ 16 * 10 ^ s) < 2 ^ 63 * 10 ^ s := by nlinarith
  have hpdov : opc.principalDelta.toRat ≤ ov.toRat := by linarith
  have hfov : opc.managementFeeDelta.toRat + opc.untrackedManagementFee.toRat ≤ ov.toRat := by linarith
  have vpp := Number.OnGrid.add_toRat hm.principal_grid gPre hsb (by
    rw [hm.principal, abs_lt]; constructor <;> linarith) a1
  have vip := Number.OnGrid.add_toRat hm.interest_grid gui hsb (by
    rw [hm.interest, abs_lt]; constructor <;> linarith) a2
  have vfp := Number.OnGrid.add_toRat hm.fee_grid gF hsb (by
    rw [hm.feePart, vF, abs_lt]; constructor <;> linarith) a3
  have hS := hm.sum
  rw [vpp, vip, vfp, vF]
  linarith

/-- The extra amount of an overpayment keeps the charge within requestedAmount. -/
private lemma UnsettledPayment.applyOverpayment_charge (p0 p : UnsettledPayment Vault) (amount : Number) {s : Int}
    {nt : NumericType} {fee : Number} {T0 P0 M0 : ℚ} (hm : p0.Charges s nt fee T0 P0 M0) (hlo : -81 ≤ s)
    (hnt : nt.isIntegral = true → s ≤ 0) (hT0b : T0 ≤ (10 ^ 16 + 1) * 10 ^ s) (hfeeb : fee.toRat < 10 ^ 16 * 10 ^ s)
    (hfee0 : 0 ≤ fee.toRat) (hPT : P0 ≤ T0) (hMT : M0 ≤ T0) (hcount : p0.count ≤ 100)
    (hamount : amount.isNormalized) (hcov : p0.totalPaid.toRat ≤ amount.toRat)
    (h : UnsettledPayment.applyOverpayment p0 amount = .ok p) :
    p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat ≤ amount.toRat := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals first
    | (rw [hm.sum]; exact hcov)
    | exact UnsettledPayment.overpayment_tail_le p0 amount hm hlo hnt hT0b hfeeb hfee0 hPT hMT hcount hamount hcov
        ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

/-- The amount a passing instalment check sees covers the instalment's totalDue. -/
private lemma Loan.payInstalment_covers (l : Loan) (v : Vault) (pc : PaymentComponents) (amount : Number)
    (p : UnsettledPayment Vault) (h : (l.payInstalment v pc amount).run = .ok (.ok p)) :
    amount.operator_lt p.totalPaid = false := by
  simp only [Loan.payInstalment] at h
  unfold_ter at h
  walk_ok
  simpa using ‹¬amount.operator_lt _ = true›

/-- A late payment charges exactly its totalDue, which requestedAmount covers, when it is due less than `10^16`
LoanScale units. -/
private lemma Loan.late_charge (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (p : UnsettledPayment Vault) (hreach : loan.Reachable t)
    (hp : (loan.payInstalments v .late amount now).run = .ok (.ok p))
    (hdue : p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat = p.totalPaid.toRat ∧
      p.totalPaid.isNormalized ∧ amount.operator_lt p.totalPaid = false := by
  obtain ⟨hlo, hint, hi, gs, gl⟩ := Loan.Reachable.pay_facts hreach
  simp only [Loan.payInstalments] at hp
  unfold_ter at hp
  walk_ok
  rename_i a hu _ _ pc hpc _ hpi
  have hl := Loan.unimpairIfImpaired_loan loan v a (by simp only [ExceptT.run]; exact hu)
  obtain ⟨l1, p1⟩ := a
  simp only at hl hpc hpi
  subst hl
  have hpi' : (loan.unimpaired.payInstalment p1 pc amount).run = .ok (.ok p) := by
    simp only [ExceptT.run]; exact hpi
  obtain ⟨hdue', hpa, hdo⟩ := Loan.payInstalment_parts loan.unimpaired p1 pc amount p hpi'
  have hpc' : Loan.lateComponents loan.unimpaired now = .ok pc := hpc
  obtain ⟨hsum, -⟩ := Loan.late_instalment_charge loan.unimpaired p.loan now pc p.amounts p.totalPaid hlo hint hi gs
    gl hpc' hpa hdue' hdo hdue
  obtain ⟨n1, -, -, n4, n5⟩ := Loan.lateComponents_norm _ _ _ hpc'
  unfold PaymentComponents.totalDue at hdue'
  obtain ⟨v1, hv1, hd⟩ := bind_ok_peel _ _ _ hdue'
  exact ⟨hsum, operator_add_isNormalized_to_nearest_sz _ _ _ (operator_add_isNormalized_to_nearest_sz _ _ _ n1 n4 hv1)
    n5 hd, Loan.payInstalment_covers _ _ _ _ _ hpi'⟩

/-- A full payment pays the payoff instalment of the loan without its impaired flag, whose totalDue the amount
covers. -/
private lemma Loan.full_parts (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments v .full amount now).run = .ok (.ok p)) :
    ∃ pc, Loan.fullComponents loan now = .ok pc ∧ pc.totalDue = .ok p.totalPaid ∧
      amount.operator_lt p.totalPaid = false := by
  simp only [Loan.payInstalments] at hp
  unfold_ter at hp
  walk_ok
  rename_i a hu _ _ pc hpc _ hpi
  have hl := Loan.unimpairIfImpaired_loan loan v a (by simp only [ExceptT.run]; exact hu)
  obtain ⟨l1, p1⟩ := a
  simp only at hl hpc hpi
  subst hl
  have hpi' : (loan.unimpaired.payInstalment p1 pc amount).run = .ok (.ok p) := by
    simp only [ExceptT.run]; exact hpi
  obtain ⟨hdue, -, -⟩ := Loan.payInstalment_parts loan.unimpaired p1 pc amount p hpi'
  exact ⟨pc, by rw [← Loan.fullComponents_unimpaired]; exact hpc, hdue, Loan.payInstalment_covers _ _ _ _ _ hpi'⟩

/-- An early payoff charges exactly its totalDue, when it is due less than `10^16` LoanScale units: principalPaid is
PrincipalOutstanding, interestPaid the floored interest less its fee, and feePaid ClosePaymentFee plus that fee. -/
private lemma Loan.full_charge (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (p : UnsettledPayment Vault) (hreach : loan.Reachable t)
    (hp : (loan.payInstalments v .full amount now).run = .ok (.ok p))
    (hdue : p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat = p.totalPaid.toRat ∧
      p.totalPaid.isNormalized := by
  obtain ⟨hlo, hhi, hint⟩ := hreach.loanScale_facts
  have hs81 : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 80 := ⟨by omega, hhi⟩
  have hint0 := hreach.loanScale_integral
  have hu0 : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have hs := Loan.loanScale_bounds loan
  -- the checks: the payoff is not late and the loan has two or more payments left
  have hchk := (Loan.payInstalments_ok loan v .full amount now p hp).1
  have hnl : now ≤ loan.nextPaymentDueDate := by
    have := hchk.not_late (by decide)
    rw [UInt32.lt_iff_toNat_lt] at this
    rw [UInt32.le_iff_toNat_le]; omega
  have hn : 2 ≤ loan.paymentRemaining.toNat := by
    have h1 := hchk.more_than_one
    rw [UInt32.le_iff_toNat_le] at h1
    simp at h1; omega
  obtain ⟨pc, hpc, hdue', -⟩ := Loan.full_parts loan v amount now p hp
  obtain ⟨rate, tpo, fi, net, split, state, cf, ppi, tracked, cfm, uf, ui, hrate, htpo, hfi, hsplit,
    hstate, hcf, hppi, htracked, hcfm, huf, hui, rfl⟩ := Loan.fullComponents_ok_inv loan now pc hpc
  obtain ⟨fl, hfloor, hsp, hnet⟩ := roundAndSplitInterest_ok_inv _ _ _ _ _ _ _ hsplit
  obtain ⟨hfN, hf0, hfB⟩ := hreach.fullInterest_le now rate tpo fi hnl hn hrate htpo hfi
  -- the floored interest `a`, its fee `b ≤ a` and ClosePaymentFee `c`, in LoanScale units
  have hfiN := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hfloor
  have hfi0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hfN hf0 (Or.inr (Or.inr rfl)) hs81 hfloor
  have hfi_le := STAmount.roundToNumericType_downward_le_of_nonneg _ _ _ _ hfN hf0 hs81 hfloor
  obtain ⟨a, hav, hav'⟩ := Number.OnGrid.unitsAt (STAmount.roundToNumericType_onGrid _ _ _ _ _ hs81 hint hfloor) hfi0
  obtain ⟨gfee, hfee0, hfee_le⟩ := computeManagementFee_le _ _ _ _ _ hfiN hfi0 loan.broker.managementFeeRate_le
    hs81 hint hsp
  obtain ⟨b, hbv, hbv'⟩ := Number.OnGrid.unitsAt gfee hfee0
  have hab : b ≤ a := by
    have : (b : ℚ) * 10 ^ loan.loanScale ≤ (a : ℚ) * 10 ^ loan.loanScale := by rw [← hbv', ← hav']; exact hfee_le
    exact_mod_cast le_of_mul_le_mul_right this hu0
  have ha : a ≤ 143 * (10 ^ 16 + 1) := by
    have : (a : ℚ) * 10 ^ loan.loanScale ≤ ((143 * (10 ^ 16 + 1) : ℕ) : ℚ) * 10 ^ loan.loanScale := by
      rw [← hav']; push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right this hu0
  obtain ⟨-, -, gcf⟩ := Loan.Reachable.fees_onGrid hreach
  have hcf0 : 0 ≤ loan.fees.closePaymentFee.toRat := loan.exact.closePaymentFee_nonneg
  have hrep := hreach.fees_representable loan.fees.closePaymentFee (by simp [LoanFees.amountFields])
  have hcfv := STAmount.roundToNumericType_of_representable _ _ _ _ loan.wf.closePaymentFee_norm hcf0 hs81 hint0 hrep
    gcf hcf
  have gcf' : Number.OnGrid loan.loanScale cf :=
    ⟨STAmount.roundToNumericType_isNormalized _ _ _ _ _ hcf, by obtain ⟨-, k, hk⟩ := gcf; exact ⟨k, by rw [hcfv, hk]⟩⟩
  obtain ⟨c, hcv, hcv'⟩ := Number.OnGrid.unitsAt gcf' (by rw [hcfv]; exact hcf0)
  obtain ⟨tN, pN, mN, -, -, -, htv, hpv, hmv, hiv, hge, h1, hpo, hm1⟩ := Loan.state_units loan state hstate
  have hTv : loan.totalValueOutstanding.toRat = (tN : ℚ) * 10 ^ loan.loanScale := by rw [← h1]; exact htv.val
  have ht : tN ≤ 10 ^ 16 + 1 := by
    have hT := hreach.totalValue_le
    have : (tN : ℚ) * 10 ^ loan.loanScale ≤ ((10 ^ 16 + 1 : ℕ) : ℚ) * 10 ^ loan.loanScale := by
      rw [← hTv]; push_cast; linarith
    exact_mod_cast le_of_mul_le_mul_right this hu0
  have hpm : (pN : ℤ) + mN ≤ 10 ^ 16 + 2 := by omega
  -- totalDue adds the value cleared, the interest beyond interestDue and the fees beyond the management fee
  unfold PaymentComponents.totalDue at hdue'
  obtain ⟨vpi, hvpi, hd⟩ := bind_ok_peel _ _ _ hdue'
  dsimp only at hvpi hd
  have hppi' := UnitsAt.add hpv hiv (by constructor <;> omega) hs hppi
  have htr := UnitsAt.add hppi' hmv (by constructor <;> omega) hs htracked
  have hnet' := UnitsAt.sub hav hbv (by constructor <;> omega) hs hnet
  have hui' := UnitsAt.sub hnet' hiv (by constructor <;> omega) hs hui
  have hvpi' := UnitsAt.add htr hui' (by constructor <;> omega) hs hvpi
  -- a ClosePaymentFee of `2^62` units or more would make the payoff due `10^16` units or more
  have hc : c < 2 ^ 62 := by
    by_contra hcon
    push Not at hcon
    have hC : (2 : ℚ) ^ 62 ≤ c := by exact_mod_cast hcon
    obtain ⟨m1, hm1N, hm1v⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) loan.loanScale (by norm_num) hs
    have hcfmN := operator_add_isNormalized_to_nearest_sz _ _ _ gcf'.1 gfee.1 hcfm
    have hcfm_ge := Number.RoundsToRepresentable.ge_of_ge_normalized _ _
      (operator_add_rounded_to_nearest _ _ _ gcf'.1 gfee.1 hcfm) cf gcf'.1 (by linarith)
    have hmq : (mN : ℚ) ≤ 10 ^ 16 + 2 := by
      have : (mN : ℤ) ≤ 10 ^ 16 + 2 := by omega
      exact_mod_cast this
    have huf_ge := Number.RoundsToRepresentable.ge_of_ge_normalized _ _
      (operator_sub_rounded_to_nearest _ _ _ hcfmN hmv.norm huf) m1 hm1N (by
        rw [hm1v, hmv.val]; rw [hcv'] at hcfm_ge; push_cast; nlinarith)
    have hvpi0 : 0 ≤ vpi.toRat := by
      rw [hvpi'.val]
      have : (0 : ℤ) ≤ (pN : ℤ) + ((tN : ℤ) - pN - mN) + mN + ((a - b) - ((tN : ℤ) - pN - mN)) := by omega
      have : (0 : ℚ) ≤ (((pN : ℤ) + ((tN : ℤ) - pN - mN) + mN + ((a - b) - ((tN : ℤ) - pN - mN)) : ℤ) : ℚ) := by
        exact_mod_cast this
      positivity
    have hufN := operator_sub_isNormalized_to_nearest_sz _ _ _ hcfmN hmv.norm huf
    have htp_ge := Number.RoundsToRepresentable.ge_of_ge_normalized _ _
      (operator_add_rounded_to_nearest _ _ _ hvpi'.norm hufN hd) m1 hm1N (by linarith)
    rw [hm1v] at htp_ge
    push_cast at htp_ge
    linarith
  -- every sum is exact: totalDue is PrincipalOutstanding + floored interest + ClosePaymentFee
  have hcfm' := UnitsAt.add hcv hbv (by constructor <;> omega) hs hcfm
  have huf' := UnitsAt.sub hcfm' hmv (by constructor <;> omega) hs huf
  have hd' := UnitsAt.add hvpi' huf' (by constructor <;> omega) hs hd
  obtain ⟨hpp, hip, hfp⟩ := hreach.full_units v amount now p rate tpo fi fl split hp hrate htpo hfi hfloor hsp
  have hfpv := hfp cf hcf gcf' (by rw [hcfv]; exact hcf0) (by
    rw [hcv', hbv']
    have : ((c + b : ℕ) : ℚ) < 2 ^ 63 := by
      have : c + b < 2 ^ 63 := by omega
      exact_mod_cast this
    push_cast at this
    nlinarith)
  refine ⟨?_, hd'.norm⟩
  rw [hpp, hip, hfpv, hd'.val, hav', hbv', hcv', ← hpo, hpv.val]
  push_cast
  ring

/-- The scheduled payments of a regular payment take at most 100 instalments, and requestedAmount covers their
totalPaid. -/
private lemma Loan.regular_covers (loan : Loan) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments v .regular amount now).run = .ok (.ok p)) :
    p.count ≤ 100 ∧ amount.operator_lt p.totalPaid = false := by
  obtain ⟨si, -, hloop, hc⟩ := Loan.payScheduled_loop loan v amount now p hp
  obtain ⟨hcount, -, hcov, -⟩ := UnsettledPayment.payInstalments_count _ _ _ _ hloop
  refine ⟨by simpa [maxPaymentsPerTransaction] using hcount, ?_⟩
  rcases hcov with hcov | hcov
  · rw [hcov] at hc; exact absurd rfl hc
  · exact hcov

/-- The extra amount of an overpayment keeps the scheduled payments' totalPaid. -/
private lemma UnsettledPayment.applyOverpayment_totalPaid (p0 p : UnsettledPayment Vault) (amount : Number)
    (h : UnsettledPayment.applyOverpayment p0 amount = .ok p) : p.totalPaid = p0.totalPaid := by
  unfold UnsettledPayment.applyOverpayment at h
  unfold_ter at h
  walk_ok
  all_goals rfl

/-- Proof body of the requestedAmount part of `Lending.payment_charge`. -/
lemma Loan.payment_charge_le_amount_proof (loan : Loan) (v : Vault) (amount : Number) (now t : UInt32)
    (paymentType : LoanPaymentType) (p : UnsettledPayment Vault) (hreach : loan.Reachable t)
    (hamount : amount.isNormalized) (hp : (loan.payInstalments v paymentType amount now).run = .ok (.ok p))
    (hdue : p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) :
    p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat ≤ amount.toRat := by
  cases paymentType
  · have hm := Loan.regular_charges loan v amount now t p hreach hp hdue
    rw [hm.sum]
    exact (operator_lt_eq_false_iff _ _ hamount hm.charged_grid.1).mp (Loan.regular_covers loan v amount now p hp).2
  · obtain ⟨hsum, hN, hcov⟩ := Loan.late_charge loan v amount now t p hreach hp hdue
    rw [hsum]
    exact (operator_lt_eq_false_iff _ _ hamount hN).mp hcov
  · obtain ⟨hsum, hN⟩ := Loan.full_charge loan v amount now t p hreach hp hdue
    obtain ⟨-, -, -, hcov⟩ := Loan.full_parts loan v amount now p hp
    rw [hsum]
    exact (operator_lt_eq_false_iff _ _ hamount hN).mp hcov
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
    have htp := UnsettledPayment.applyOverpayment_totalPaid p0 p amount h1
    rw [htp] at hdue
    obtain ⟨hlo, hint, hi, gs, -⟩ := Loan.Reachable.pay_facts hreach
    have hm := Loan.regular_charges loan v amount now t p0 hreach h0 hdue
    obtain ⟨hcount, hcov⟩ := Loan.regular_covers loan v amount now p0 h0
    have hfee := (Loan.regularPayment_dues loan v amount now p0 h0).1
    have hiD : 0 ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
        loan.managementFeeOutstanding.toRat := hi
    have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
    exact UnsettledPayment.applyOverpayment_charge p0 p amount hm hlo hint hreach.totalValue_le (by linarith)
      loan.exact.serviceFee_nonneg (by linarith) (by linarith) hcount hamount
      ((operator_lt_eq_false_iff _ _ hamount hm.charged_grid.1).mp hcov) h1

end XRPL.Model.Lending
