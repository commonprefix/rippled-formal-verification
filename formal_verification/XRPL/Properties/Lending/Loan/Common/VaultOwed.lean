import XRPL.Properties.Lending.Loan.Common.InterestMonotone

/-! # What a loan owes the vault never rises on a payment

PrincipalOutstanding + interestDue is what a loan still owes the vault. An instalment takes at least as much off
TotalValueOutstanding as off ManagementFeeOutstanding, and a re-amortization never raises principal or interest. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment UnsettledPayment.payInstalments
  UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.settlePayment Loan.overpaymentComponents
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.lateComponents_scheduled from XRPL.Properties.Lending.Loan.Common.PayMonotone
open private Loan.doPayment_interestDue from XRPL.Properties.Lending.Loan.Common.InterestDue
open private Loan.reamortized_interestDue_le from XRPL.Properties.Lending.Loan.Common.InterestMonotone

/-- What a loan owes the vault is TotalValueOutstanding less ManagementFeeOutstanding. -/
private lemma Loan.owed_eq (l : Loan) :
    l.principalOutstanding.toRat + l.toExact.interestDue =
      l.totalValueOutstanding.toRat - l.managementFeeOutstanding.toRat := by
  show _ + (l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat) = _
  ring

/-- A paid-off loan owes the vault nothing. -/
private lemma Loan.owed_paid (l : Loan) (h : l.paymentRemaining = 0) :
    l.totalValueOutstanding.toRat - l.managementFeeOutstanding.toRat = 0 := by
  obtain ⟨h1, -, h3⟩ := l.valid.paid_zeroed h
  rw [show l.totalValueOutstanding = l.toRawLoan.totalValueOutstanding from rfl, h1,
    show l.managementFeeOutstanding = l.toRawLoan.managementFeeOutstanding from rfl, h3, Number.toRat_zero]
  ring

/-- A loan with interestDue at least zero owes the vault at least zero. -/
private lemma Loan.owed_nonneg (l : Loan) (hi : 0 ≤ l.toExact.interestDue) :
    0 ≤ l.totalValueOutstanding.toRat - l.managementFeeOutstanding.toRat := by
  obtain ⟨-, -, -, -, hP0, -, -⟩ := Loan.outstanding_grid l
  rw [← Loan.owed_eq]
  linarith

/-- One instalment never raises what the loan owes the vault. The last one pays the loan off, any other takes
at least as much off TotalValueOutstanding as off ManagementFeeOutstanding. -/
private lemma Loan.doPayment_owed_le (l l' : Loan) (pc : PaymentComponents) (hi : 0 ≤ l.toExact.interestDue)
    (hpc : pc.isFinal = true ∨ (pc.isFinal = false ∧ pc.Tracked l)) (h : Loan.doPayment l pc = .ok l') :
    l'.totalValueOutstanding.toRat - l'.managementFeeOutstanding.toRat ≤
      l.totalValueOutstanding.toRat - l.managementFeeOutstanding.toRat := by
  rcases hpc with hf | ⟨hf, ht⟩
  · have hpaid : l'.paymentRemaining = 0 := by
      simp only [Loan.doPayment, hf, ↓reduceIte] at h
      unfold_ter at h
      walk_ok
      exact congrArg RawLoan.paymentRemaining (RawLoan.to_lawful_ok ‹_›).1
    rw [Loan.owed_paid l' hpaid]
    exact Loan.owed_nonneg l hi
  · obtain ⟨gtv, gpd, gmd, ⟨tv0, tv1⟩, ⟨pd0, pd1⟩, ⟨md0, md1⟩, -, hmv⟩ := ht
    obtain ⟨gT, gP, gM, hTb, hP0, hM0, hT0⟩ := Loan.outstanding_grid l
    have hs := Loan.loanScale_bounds l
    have hi0 : 0 ≤ l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat :=
      hi
    simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    rename_i _ tv htv _ pv hpv _ mv hmv' hlaw
    have h1 := (RawLoan.to_lawful_ok hlaw).1
    have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
    have e3 := (congrArg RawLoan.managementFeeOutstanding h1 :)
    simp only at e1 e3
    have vtv := Number.OnGrid.sub_toRat gT gtv hs (by rw [abs_lt]; constructor <;> linarith) htv
    have vmv := Number.OnGrid.sub_toRat gM gmd hs (by rw [abs_lt]; constructor <;> linarith) hmv'
    rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl, e1,
      show l'.managementFeeOutstanding = l'.toRawLoan.managementFeeOutstanding from rfl, e3, vtv, vmv]
    linarith

/-- The instalment loop never raises what the loan owes the vault. -/
private lemma UnsettledPayment.payInstalments_owed_le {α : Type} (payment : UnsettledPayment α) (n : Nat)
    (amount : Number) (p' : UnsettledPayment α) (h : UnsettledPayment.payInstalments payment n amount = .ok p')
    (hlo : -81 ≤ payment.loan.loanScale)
    (hint : payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0)
    (hi : 0 ≤ payment.loan.toExact.interestDue) :
    p'.loan.totalValueOutstanding.toRat - p'.loan.managementFeeOutstanding.toRat ≤
      payment.loan.totalValueOutstanding.toRat - payment.loan.managementFeeOutstanding.toRat := by
  induction n generalizing payment with
  | zero =>
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact le_refl _
  | succ n ih =>
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact le_refl _
    · exact le_refl _
    all_goals
      have hs := Loan.scheduledComponents_tracked payment.loan _ hlo hint hi
        ‹Loan.scheduledComponents payment.loan = _›
      have hd := Loan.doPayment_interestDue payment.loan _ _ hi hs ‹Loan.doPayment _ _ = _›
      have hle := Loan.doPayment_owed_le payment.loan _ _ hi hs ‹Loan.doPayment _ _ = _›
      have hst := Loan.doPayment_sameTerms _ _ _ ‹Loan.doPayment _ _ = _›
    · exact hle
    · have h3 := ‹UnsettledPayment.payInstalments _ n amount = _›
      have key := ih _ h3
      simp only at key
      rw [hst.loanScale, hst.broker] at key
      exact le_trans (key hlo hint hd) hle

/-- A rounded amount clamped at the loan's PrincipalOutstanding is at most it. -/
private lemma Loan.clamp_le_principal (l : Loan) {st : LoanState} {x q : Number} {nt : NumericType} {s : Int}
    {mode : rounding_mode} (hst : l.state = .ok st) (hq : STAmount.roundToNumericType nt x mode (some s) = .ok q) :
    (Number.clamp q Number.zero st.principalOutstanding).toRat ≤ l.principalOutstanding.toRat := by
  obtain ⟨-, hsP, -⟩ := LoanState.build_ok hst
  have hqn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hq
  obtain ⟨-, -, -, -, hP0, -, -⟩ := Loan.outstanding_grid l
  rw [hsP]
  rcases Number.clamp_zero_cases q _ hqn l.wf.principalOutstanding_norm with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, h2, he⟩
  · rw [he, Number.toRat_zero]; exact hP0
  · rw [he]
  · rw [he]; exact h2

/-- A re-amortization that passes never raises what the loan owes the vault. It keeps interestDue from rising
and leaves PrincipalOutstanding below the loan's. -/
private lemma Loan.tryOverpayment_owed_le (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hlo : -81 ≤ l.loanScale) (hint : l.broker.numericType.isIntegral = true → l.loanScale ≤ 0)
    (hi : 0 ≤ l.toExact.interestDue) (h : Loan.tryOverpayment l opc = .ok (some re)) :
    re.state.valueOutstanding.toRat - re.state.managementFeeDue.toRat ≤
      l.totalValueOutstanding.toRat - l.managementFeeOutstanding.toRat := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  -- Match the steps by their shape only. A full search unfolds the `Number` operators of the other steps.
  have hle := Loan.reamortized_interestDue_le l hlo hint hi (by with_reducible assumption)
    (by with_reducible assumption) (by with_reducible assumption) (by with_reducible assumption)
    (by with_reducible assumption) (by with_reducible assumption) (by with_reducible assumption)
  dsimp only
  -- the committed principal is clamped at the loan's
  have hpo := (by with_reducible assumption :
    roundAndClamp _ (LoanState.principalOutstanding _) rounding_mode.upward _ _ = _)
  obtain ⟨q, hq, rfl⟩ := roundAndClamp_ok hpo
  obtain ⟨-, h5P, -⟩ := LoanState.build_ok
    (by with_reducible assumption : LoanState.build _ (Number.clamp _ _ _) _ = _)
  have hcap := Loan.clamp_le_principal l (by with_reducible assumption : l.state = _) hq
  rw [h5P] at hle
  have hiD : l.toExact.interestDue =
      l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat := rfl
  linarith

/-- The overpayment tail never raises what the loan owes the vault. -/
private lemma UnsettledPayment.applyOverpayment_owed_le (payment p' : UnsettledPayment Vault) (amount : Number)
    (hlo : -81 ≤ payment.loan.loanScale)
    (hint : payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0)
    (hi : 0 ≤ payment.loan.toExact.interestDue)
    (h : UnsettledPayment.applyOverpayment payment amount = .ok p') :
    p'.loan.totalValueOutstanding.toRat - p'.loan.managementFeeOutstanding.toRat ≤
      payment.loan.totalValueOutstanding.toRat - payment.loan.managementFeeOutstanding.toRat := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact le_refl _
    | skip
  have hle := Loan.tryOverpayment_owed_le _ _ _ hlo hint hi ‹Loan.tryOverpayment _ _ = _›
  have h1 := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = _›).1
  have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
  have e3 := (congrArg RawLoan.managementFeeOutstanding h1 :)
  simp only at e1 e3
  dsimp only
  rw [e1, e3]
  exact hle

/-- A payment never raises what the loan owes the vault, PrincipalOutstanding + interestDue, while the loan's
interestDue is at least zero. -/
lemma Loan.pay_owed_le (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hlo : -81 ≤ loan.loanScale)
    (hint : loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) (hi : 0 ≤ loan.toExact.interestDue)
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.principalOutstanding.toRat + r.loan'.toExact.interestDue ≤
      loan.principalOutstanding.toRat + loan.toExact.interestDue := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  -- the settlement keeps the paid loan's amounts
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have h1 := (RawLoan.to_lawful_ok hloan).1
  have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
  have e3 := (congrArg RawLoan.managementFeeOutstanding h1 :)
  simp only at e1 e3
  rw [Loan.owed_eq, Loan.owed_eq]
  rw [show r.loan'.totalValueOutstanding = r.loan'.toRawLoan.totalValueOutstanding from rfl, e1,
    show r.loan'.managementFeeOutstanding = r.loan'.toRawLoan.managementFeeOutstanding from rfl, e3]
  show _ ≤ loan.unimpaired.totalValueOutstanding.toRat - loan.unimpaired.managementFeeOutstanding.toRat
  cases pt
  · obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
    have hA := UnsettledPayment.payInstalments_owed_le _ _ _ _ hloop
    have hB := hA hlo
    have hC := hB hint
    have hD := hC hi
    exact hD
  · obtain ⟨pc, hpc, -, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    obtain ⟨pc0, hpc0, e1, e2, e3, e4⟩ := Loan.lateComponents_scheduled loan now pc hpc
    refine Loan.doPayment_owed_le loan.unimpaired p.loan pc hi ?_ hdo
    rcases Loan.scheduledComponents_tracked loan pc0 hlo hint hi hpc0 with hf | ⟨hf, ht⟩
    · exact Or.inl (by rw [e4]; exact hf)
    · refine Or.inr ⟨by rw [e4]; exact hf, ?_⟩
      obtain ⟨g1, g2, g3, r1, r2, r3, hle, hmv⟩ := ht
      exact ⟨by rw [e1]; exact g1, by rw [e2]; exact g2, by rw [e3]; exact g3, by rw [e1]; exact r1,
        by rw [e2]; exact r2, by rw [e3]; exact r3, by rw [e1, e2, e3]; exact hle, by rw [e1, e3]; exact hmv⟩
  · obtain ⟨pc, hpc, -, hdo⟩ := Loan.fullPayInstalments_ok loan v amount now p hp
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ :=
      Loan.fullComponents_ok_inv loan now pc hpc
    exact Loan.doPayment_owed_le loan.unimpaired p.loan _ hi (Or.inl rfl) hdo
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 h0
    have hA := UnsettledPayment.payInstalments_owed_le _ _ _ _ hloop hlo hint hi
    obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v .regular amount now p0 h0
    have hi0 : 0 ≤ p0.loan.toExact.interestDue :=
      Loan.payInstalments_interestDue loan v .regular amount now p0 (by decide) hlo hint hi h0
    have hB := UnsettledPayment.applyOverpayment_owed_le p0 p amount (by rw [hst.loanScale]; exact hlo)
      (by rw [hst.loanScale, hst.broker]; exact hint) hi0 h1
    exact le_trans hB hA

end XRPL.Model.Lending
