import XRPL.Properties.Lending.Loan.Common.PayUnits
import XRPL.Properties.Lending.Loan.Common.BrokerDebt
import XRPL.Properties.Protocol.Number.Sub.ZeroShape

/-! # What a payment never raises

A payment never raises the outstanding amounts, PaymentRemaining or DebtTotal, and keeps AssetsReserved. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.doPayment UnsettledPayment.payInstalments
  UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.unimpairIfImpaired Loan.settlePayment
  from XRPL.Model.Lending.Loan.LoanPay
open private reduceCapped from XRPL.Model.Lending.Loan.LoanState

/-- The broker a payment writes differs from the loan's broker only in DebtTotal and CoverAvailable. -/
lemma Loan.pay_broker_fields (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.broker.toRawLoanBroker = { loan.broker.toRawLoanBroker with
      debtTotal := r.loan'.broker.debtTotal, coverAvailable := r.loan'.broker.coverAvailable } := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨_, _, _, cover', debtTotal', _, broker', -, -, -, hbroker, hloan, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hb : r.loan'.broker = broker' := (congrArg RawLoan.broker (RawLoan.to_lawful_ok hloan).1 :)
  have hraw := (RawLoanBroker.to_lawful_ok hbroker).1
  have hpb : p.loan.broker = loan.broker := hst.broker
  rw [hb, hraw, hpb]

/-! ## Normalized amounts -/

private lemma Number.min_isNormalized' {x y : Number} (hx : x.isNormalized) (hy : y.isNormalized) :
    (Number.min x y).isNormalized := by
  unfold Number.min; split <;> assumption

private lemma Number.max_isNormalized' {x y : Number} (hx : x.isNormalized) (hy : y.isNormalized) :
    (Number.max x y).isNormalized := by
  unfold Number.max; split <;> assumption

private lemma Number.clamp_isNormalized' {x lo hi : Number} (hx : x.isNormalized) (hlo : lo.isNormalized)
    (hhi : hi.isNormalized) : (Number.clamp x lo hi).isNormalized := by
  unfold Number.clamp; split
  · exact hlo
  · split <;> assumption

/-- A clamp into `[0, hi]` is never negative. -/
private lemma Number.clamp_zero_nonneg (x hi : Number) (hhi : 0 ≤ hi.toRat) :
    0 ≤ (Number.clamp x Number.zero hi).toRat := by
  unfold Number.clamp
  split
  · rw [Number.toRat_zero]
  · split
    · exact hhi
    · rename_i h _
      apply Number.toRat_nonneg_of_nonnegative
      cases hn : x.negative_
      · rfl
      · exfalso; apply h
        unfold Number.operator_lt
        simp [hn, Number.zero]

/-- A clamp into `[0, hi]` stays at or below `hi`. -/
private lemma Number.clamp_zero_le (x hi : Number) (hx : x.isNormalized) (hhi : hi.isNormalized)
    (h0 : 0 ≤ hi.toRat) : (Number.clamp x Number.zero hi).toRat ≤ hi.toRat := by
  unfold Number.clamp
  split
  · rw [Number.toRat_zero]; exact h0
  · split
    · exact le_refl _
    · rename_i h
      exact (operator_lt_eq_false_iff hi x hhi hx).mp (by simpa using h)

private lemma LoanStateDeltas.total_isNormalized' {d : LoanStateDeltas} (h1 : d.principal.isNormalized)
    (h2 : d.interest.isNormalized) (h3 : d.managementFee.isNormalized) (t : Number) (ht : d.total = .ok t) :
    t.isNormalized := by
  unfold LoanStateDeltas.total at ht
  simp only [bind, Except.bind] at ht
  split at ht
  · cases ht
  · rename_i s hs
    exact operator_add_isNormalized_to_nearest_sz _ _ _ (operator_add_isNormalized_to_nearest_sz _ _ _ h1 h2 hs)
      h3 ht

/-- The state of a lawful loan holds its outstanding amounts. -/
lemma Loan.state_fields (l : Loan) (s : LoanState) (h : l.state = .ok s) :
    s.valueOutstanding = l.totalValueOutstanding ∧ s.principalOutstanding = l.principalOutstanding ∧
      s.managementFeeDue = l.managementFeeOutstanding ∧ s.interestDue.isNormalized := by
  unfold Loan.state LoanState.build at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok s›)
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact operator_sub_isNormalized_to_nearest_sz _ _ _
    (operator_sub_isNormalized_to_nearest_sz _ _ _ l.wf.totalValueOutstanding_norm l.wf.principalOutstanding_norm
      ‹_›)
    l.wf.managementFeeOutstanding_norm ‹_›

/-- A lawful loan's interestDue is the one its state computes. -/
lemma Loan.state_of_interestDue (loan : Loan) (i : Number) (hi : loan.interestDue = .ok i) :
    loan.state = .ok ⟨loan.totalValueOutstanding, loan.principalOutstanding, i, loan.managementFeeOutstanding⟩ := by
  have hi' : (loan.totalValueOutstanding.operator_sub loan.principalOutstanding .to_nearest >>=
      fun x => x.operator_sub loan.managementFeeOutstanding .to_nearest) = .ok i := hi
  obtain ⟨x, hx, hix⟩ := bind_ok_peel _ _ _ hi'
  unfold Loan.state LoanState.build
  rw [hx, ok_bind, hix]
  rfl

private lemma LoanStateDeltas.nonNegative_principal_isNormalized (d : LoanStateDeltas)
    (h : d.principal.isNormalized) : d.nonNegative.principal.isNormalized := by
  unfold LoanStateDeltas.nonNegative; dsimp only; split
  · exact Number.zero_isNormalized
  · exact h

private lemma LoanStateDeltas.nonNegative_interest_isNormalized (d : LoanStateDeltas)
    (h : d.interest.isNormalized) : d.nonNegative.interest.isNormalized := by
  unfold LoanStateDeltas.nonNegative; dsimp only; split
  · exact Number.zero_isNormalized
  · exact h

private lemma LoanStateDeltas.nonNegative_managementFee_isNormalized (d : LoanStateDeltas)
    (h : d.managementFee.isNormalized) : d.nonNegative.managementFee.isNormalized := by
  unfold LoanStateDeltas.nonNegative; dsimp only; split
  · exact Number.zero_isNormalized
  · exact h

private lemma reduceCapped_normalized (value excess v' e' : Number) (hv : value.isNormalized)
    (he : excess.isNormalized) (h : reduceCapped value excess = .ok (v', e')) :
    v'.isNormalized ∧ e'.isNormalized := by
  unfold reduceCapped at h
  simp only [bind, Except.bind] at h
  split at h
  · walk_ok
    have hm := Number.min_isNormalized' hv he
    have h1 := Except.ok.inj ‹pure _ = Except.ok (v', e')›
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ hv hm ‹_›,
      operator_sub_isNormalized_to_nearest_sz _ _ _ he hm ‹_›⟩
  · have h1 := Except.ok.inj h
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact ⟨hv, he⟩

private lemma LoanStateDeltas.reduceByExcess_normalized' {d d' : LoanStateDeltas} {excess : Number}
    (h1 : d.principal.isNormalized) (h2 : d.interest.isNormalized) (h3 : d.managementFee.isNormalized)
    (he : excess.isNormalized) (hr : d.reduceByExcess excess = .ok d') :
    d'.principal.isNormalized ∧ d'.interest.isNormalized ∧ d'.managementFee.isNormalized := by
  unfold LoanStateDeltas.reduceByExcess at hr
  simp only [bind, Except.bind] at hr
  walk_ok
  rename_i _ a ha _ b hb _ c hc hd
  have g1 := reduceCapped_normalized _ _ a.1 a.2 h2 he ha
  have g2 := reduceCapped_normalized _ _ b.1 b.2 h3 g1.2 hb
  have g3 := reduceCapped_normalized _ _ c.1 c.2 h1 g2.2 hc
  obtain rfl := (Except.ok.inj hd).symm
  exact ⟨g3.1, g1.1, g2.1⟩

open Lean Meta Elab Tactic in
/-- A proof that `x` is normalized, from the local facts and the shape of `x`. -/
private partial def proveNorm (x : Expr) : MetaM (Option Expr) := do
  let target ← mkAppM ``Number.isNormalized #[x]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    if ← withReducible (isDefEq ldecl.type target) then return some ldecl.toExpr
    -- a fact `p ∧ q ∧ r` about the three fields of a delta
    let ty ← instantiateMVars ldecl.type
    if ty.isAppOfArity ``And 2 then
      let p := ty.appFn!.appArg!
      let qr := ty.appArg!
      if ← withReducible (isDefEq p target) then return some (← mkAppM ``And.left #[ldecl.toExpr])
      if qr.isAppOfArity ``And 2 then
        if ← withReducible (isDefEq qr.appFn!.appArg! target) then
          return some (← mkAppM ``And.left #[← mkAppM ``And.right #[ldecl.toExpr]])
        if ← withReducible (isDefEq qr.appArg! target) then
          return some (← mkAppM ``And.right #[← mkAppM ``And.right #[ldecl.toExpr]])
  let x' ← whnfR x
  if x'.isConstOf ``Number.zero then return some (mkConst ``Number.zero_isNormalized)
  let fn := x'.getAppFn.constName?
  let args := x'.getAppArgs
  if (fn == some ``Number.min || fn == some ``Number.max) && args.size == 2 then
    let some pa ← proveNorm args[0]! | return none
    let some pb ← proveNorm args[1]! | return none
    let lem := if fn == some ``Number.min then ``Number.min_isNormalized' else ``Number.max_isNormalized'
    return some (← mkAppM lem #[pa, pb])
  if fn == some ``Number.clamp && args.size == 3 then
    let some pa ← proveNorm args[0]! | return none
    let some pl ← proveNorm args[1]! | return none
    let some ph ← proveNorm args[2]! | return none
    return some (← mkAppM ``Number.clamp_isNormalized' #[pa, pl, ph])
  if fn == some ``Number.operator_neg && args.size == 1 then
    let some pa ← proveNorm args[0]! | return none
    return some (← mkAppM ``Number.operator_neg_isNormalized #[args[0]!, pa])
  let fields := [(``LoanStateDeltas.principal, ``LoanStateDeltas.nonNegative_principal_isNormalized),
    (``LoanStateDeltas.interest, ``LoanStateDeltas.nonNegative_interest_isNormalized),
    (``LoanStateDeltas.managementFee, ``LoanStateDeltas.nonNegative_managementFee_isNormalized)]
  -- a field of a delta, written as a projection function or as a raw projection
  let fieldOf : Option (Nat × Expr) :=
    match x.getAppFn.constName?, x.getAppArgs with
    | some ``LoanStateDeltas.principal, #[d] => some (0, d)
    | some ``LoanStateDeltas.interest, #[d] => some (1, d)
    | some ``LoanStateDeltas.managementFee, #[d] => some (2, d)
    | _, _ => match x' with
      | .proj ``LoanStateDeltas i d => some (i, d)
      | _ => none
  if let some (i, d) := fieldOf then
    let (proj, lem) := fields[i]!
    let d' ← whnfR d
    if d'.isAppOfArity ``LoanStateDeltas.nonNegative 1 then
      let e := d'.appArg!
      let some pe ← proveNorm (← mkAppM proj #[e]) | return none
      return some (← mkAppM lem #[e, pe])
  return none

open Lean Meta Elab Tactic in
/-- Add `c.isNormalized` for every Number step `h : f … = .ok c` whose operands are normalized. -/
elab "pay_norm_forward" : tactic => do
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 60 do
    changed := false
    rounds := rounds + 1
    let g ← getMainGoal
    let newFact ← g.withContext do
      for ldecl in (← getLCtx) do
        if ldecl.isImplementationDetail then continue
        let ty ← instantiateMVars ldecl.type
        let some (_, lhs, rhs) := ty.eq? | continue
        unless rhs.isAppOfArity ``Except.ok 3 do continue
        let c := rhs.appArg!
        let cty ← inferType c
        if cty.isConstOf ``Number then
          if (← proveNorm c).isSome then continue
        else if cty.isConstOf ``LoanStateDeltas then
          if (← proveNorm (← mkAppM ``LoanStateDeltas.principal #[c])).isSome then continue
        else continue
        let args := lhs.getAppArgs
        let pf? : Option Expr ← match lhs.getAppFn.constName? with
          | some ``Number.operator_sub =>
            if args.size == 3 && args[2]!.isConstOf ``rounding_mode.to_nearest then
              match ← proveNorm args[0]!, ← proveNorm args[1]! with
              | some p0, some p1 => pure (some (← mkAppM ``operator_sub_isNormalized_to_nearest_sz
                  #[args[0]!, args[1]!, c, p0, p1, ldecl.toExpr]))
              | _, _ => pure none
            else pure none
          | some ``Number.operator_add =>
            if args.size == 3 && args[2]!.isConstOf ``rounding_mode.to_nearest then
              match ← proveNorm args[0]!, ← proveNorm args[1]! with
              | some p0, some p1 => pure (some (← mkAppM ``operator_add_isNormalized_to_nearest_sz
                  #[args[0]!, args[1]!, c, p0, p1, ldecl.toExpr]))
              | _, _ => pure none
            else pure none
          | some ``STAmount.roundToNumericType =>
            pure (some (← mkAppM ``STAmount.roundToNumericType_isNormalized
              #[args[0]!, args[1]!, args[2]!, args[3]!, c, ldecl.toExpr]))
          | some ``LoanStateDeltas.reduceByExcess =>
            let d := args[0]!
            match ← proveNorm (← mkAppM ``LoanStateDeltas.principal #[d]),
                ← proveNorm (← mkAppM ``LoanStateDeltas.interest #[d]),
                ← proveNorm (← mkAppM ``LoanStateDeltas.managementFee #[d]), ← proveNorm args[1]! with
            | some p1, some p2, some p3, some pe =>
              let pf ← mkAppOptM ``LoanStateDeltas.reduceByExcess_normalized'
                #[some d, some c, some args[1]!, some p1, some p2, some p3, some pe, some ldecl.toExpr]
              pure (some pf)
            | _, _, _, _ => pure none
          | some ``LoanStateDeltas.total =>
            let d := args[0]!
            match ← proveNorm (← mkAppM ``LoanStateDeltas.principal #[d]),
                ← proveNorm (← mkAppM ``LoanStateDeltas.interest #[d]),
                ← proveNorm (← mkAppM ``LoanStateDeltas.managementFee #[d]) with
            | some p1, some p2, some p3 => pure (some (← mkAppOptM ``LoanStateDeltas.total_isNormalized'
                #[some d, some p1, some p2, some p3, some c, some ldecl.toExpr]))
            | _, _, _ => pure none
          | _ => pure none
        if let some pf := pf? then return some (pf, ← inferType pf)
      return none
    if let some (pf, ty) := newFact then
      let (_, g') ← (← g.assert `hnorm ty pf).intro1P
      replaceMainGoal [g']
      changed := true

open Lean Meta Elab Tactic in
/-- Close `x.isNormalized` from the local facts. -/
elab "pay_prove_norm" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some x := (ty.getAppFnArgs) |> fun (f, a) =>
      if f == ``Number.isNormalized && a.size == 1 then some a[0]! else none
    | throwError "pay_prove_norm: not an isNormalized goal"
  let some pf ← proveNorm x | throwError "pay_prove_norm: no proof found"
  g.assign pf
  replaceMainGoal []

private lemma Loan.scheduledComponents_sound (l : Loan) (pc : PaymentComponents)
    (h : Loan.scheduledComponents l = .ok pc) :
    pc.totalValueDelta.isNormalized ∧ pc.principalDelta.isNormalized ∧ pc.managementFeeDelta.isNormalized ∧
      0 ≤ pc.totalValueDelta.toRat ∧ 0 ≤ pc.principalDelta.toRat ∧ 0 ≤ pc.managementFeeDelta.toRat := by
  have hT := l.wf.totalValueOutstanding_norm
  have hP := l.wf.principalOutstanding_norm
  have hM := l.wf.managementFeeOutstanding_norm
  have hT0 : 0 ≤ l.totalValueOutstanding.toRat := l.exact.totalValueOutstanding_nonneg
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ l.managementFeeOutstanding.toRat := l.exact.managementFeeOutstanding_nonneg
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at *
    subst_vars
  all_goals first
    | exact ⟨hT, hP, hM, hT0, hP0, hM0⟩
    | (obtain ⟨h1, h2, h3, h4⟩ := Loan.state_fields l _ ‹l.state = _›
       rw [← h1] at hT hT0
       rw [← h2] at hP hP0
       rw [← h3] at hM hM0
       pay_norm_forward
       refine ⟨?_, ?_, ?_, Number.clamp_zero_nonneg _ _ hT0, Number.clamp_zero_nonneg _ _ hP0,
         Number.clamp_zero_nonneg _ _ hM0⟩ <;> pay_prove_norm)

/-- A scheduled instalment that isn't the last comes from a loan whose PaymentRemaining is not 1. -/
lemma Loan.scheduledComponents_not_last (l : Loan) (pc : PaymentComponents)
    (h : Loan.scheduledComponents l = .ok pc) (hf : pc.isFinal = false) : l.paymentRemaining ≠ 1 := by
  unfold Loan.scheduledComponents at h
  obtain ⟨rate, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨pp', -, h⟩ := bind_ok_peel _ _ _ h
  dsimp only at h
  split at h
  · obtain rfl := (Except.ok.inj h).symm
    simp at hf
  · rename_i hnf
    intro h1
    apply hnf
    simp [h1]

/-- The late instalment takes the same amounts off the loan as the next scheduled one. -/
private lemma Loan.lateComponents_scheduled (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (h : Loan.lateComponents l now = .ok pc) :
    ∃ pc0, Loan.scheduledComponents l = .ok pc0 ∧ pc.totalValueDelta = pc0.totalValueDelta ∧
      pc.principalDelta = pc0.principalDelta ∧ pc.managementFeeDelta = pc0.managementFeeDelta ∧
      pc.isFinal = pc0.isFinal := by
  unfold Loan.lateComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok pc›)
  refine ⟨_, ‹Loan.scheduledComponents l = _›, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- One instalment never raises an outstanding amount or PaymentRemaining. -/
private lemma Loan.doPayment_le (l l' : Loan) (pc : PaymentComponents) (hr : l.paymentRemaining ≠ 0)
    (hpc : pc.isFinal = false → pc.totalValueDelta.isNormalized ∧ pc.principalDelta.isNormalized ∧
      pc.managementFeeDelta.isNormalized ∧ 0 ≤ pc.totalValueDelta.toRat ∧ 0 ≤ pc.principalDelta.toRat ∧
      0 ≤ pc.managementFeeDelta.toRat)
    (h : Loan.doPayment l pc = .ok l') :
    l'.totalValueOutstanding.toRat ≤ l.totalValueOutstanding.toRat ∧
      l'.principalOutstanding.toRat ≤ l.principalOutstanding.toRat ∧
      l'.managementFeeOutstanding.toRat ≤ l.managementFeeOutstanding.toRat ∧
      l'.paymentRemaining ≤ l.paymentRemaining := by
  have hT0 : 0 ≤ l.totalValueOutstanding.toRat := l.exact.totalValueOutstanding_nonneg
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ l.managementFeeOutstanding.toRat := l.exact.managementFeeOutstanding_nonneg
  cases hf : pc.isFinal
  · obtain ⟨hn1, hn2, hn3, h01, h02, h03⟩ := hpc hf
    simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    have h1 := (RawLoan.to_lawful_ok ‹_›).1
    have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
    have e2 := (congrArg RawLoan.principalOutstanding h1 :)
    have e3 := (congrArg RawLoan.managementFeeOutstanding h1 :)
    have e4 := (congrArg RawLoan.paymentRemaining h1 :)
    simp only at e1 e2 e3 e4
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl, e1]
      exact Number.operator_sub_le_self l.wf.totalValueOutstanding_norm hn1 h01 ‹_›
    · rw [show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl, e2]
      exact Number.operator_sub_le_self l.wf.principalOutstanding_norm hn2 h02 ‹_›
    · rw [show l'.managementFeeOutstanding = l'.toRawLoan.managementFeeOutstanding from rfl, e3]
      exact Number.operator_sub_le_self l.wf.managementFeeOutstanding_norm hn3 h03 ‹_›
    · rw [show l'.paymentRemaining = l'.toRawLoan.paymentRemaining from rfl, e4]
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]; have := UInt32.toNat_inj.not.mpr hr; simp at this ⊢; omega)]
      simp
  · simp only [Loan.doPayment, hf, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    have h1 := (RawLoan.to_lawful_ok ‹_›).1
    have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
    have e2 := (congrArg RawLoan.principalOutstanding h1 :)
    have e3 := (congrArg RawLoan.managementFeeOutstanding h1 :)
    have e4 := (congrArg RawLoan.paymentRemaining h1 :)
    simp only at e1 e2 e3 e4
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show l'.totalValueOutstanding = l'.toRawLoan.totalValueOutstanding from rfl, e1, Number.toRat_zero]
      exact hT0
    · rw [show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl, e2, Number.toRat_zero]
      exact hP0
    · rw [show l'.managementFeeOutstanding = l'.toRawLoan.managementFeeOutstanding from rfl, e3,
        Number.toRat_zero]
      exact hM0
    · rw [show l'.paymentRemaining = l'.toRawLoan.paymentRemaining from rfl, e4]
      rw [UInt32.le_iff_toNat_le]; simp

/-- Summing two payments adds their principal parts. -/
private lemma PaymentAmounts.add_principal (a b c : PaymentAmounts) (h : a.add b = .ok c) :
    a.principalPaid.operator_add b.principalPaid .to_nearest = .ok c.principalPaid := by
  unfold PaymentAmounts.add at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok c›)
  exact ‹a.principalPaid.operator_add b.principalPaid .to_nearest = _›

/-- Summing two payments adds their interest parts. -/
lemma PaymentAmounts.add_interest (a b c : PaymentAmounts) (h : a.add b = .ok c) :
    a.interestPaid.operator_add b.interestPaid .to_nearest = .ok c.interestPaid := by
  unfold PaymentAmounts.add at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok c›)
  exact ‹a.interestPaid.operator_add b.interestPaid .to_nearest = _›

/-- Adding amounts to zero returns them. -/
lemma PaymentAmounts.zero_add (a : PaymentAmounts) : PaymentAmounts.zero.add a = .ok a := by
  unfold PaymentAmounts.add PaymentAmounts.zero
  rw [Number.operator_add_zero_left, ok_bind, Number.operator_add_zero_left, ok_bind, Number.operator_add_zero_left]
  rfl

/-- A rounded value clamped into `[0, cap]` is normalized, not negative and at most `cap`. -/
private lemma roundAndClamp_le (value cap : Number) (mode : rounding_mode) (nt : NumericType) (s : Int) (y : Number)
    (hcap : cap.isNormalized) (hcap0 : 0 ≤ cap.toRat) (h : roundAndClamp value cap mode nt s = .ok y) :
    y.isNormalized ∧ 0 ≤ y.toRat ∧ y.toRat ≤ cap.toRat := by
  unfold roundAndClamp at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    obtain rfl := (Except.ok.inj h).symm
    have hrn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hr
    exact ⟨Number.clamp_isNormalized' hrn Number.zero_isNormalized hcap, Number.clamp_zero_nonneg _ _ hcap0,
      Number.clamp_zero_le _ _ hrn hcap hcap0⟩

private lemma LoanState.build_fields (a b c : Number) (st : LoanState) (h : LoanState.build a b c = .ok st) :
    st.valueOutstanding = a ∧ st.principalOutstanding = b ∧ st.managementFeeDue = c := by
  unfold LoanState.build at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok st›)
  exact ⟨rfl, rfl, rfl⟩

private lemma LoanState.calculateDeltas_principal (x y : LoanState) (d : LoanStateDeltas)
    (h : x.calculateDeltas y = .ok d) :
    x.principalOutstanding.operator_sub y.principalOutstanding .to_nearest = .ok d.principal := by
  unfold LoanState.calculateDeltas at h
  simp only [bind, Except.bind] at h
  walk_ok
  obtain rfl := (Except.ok.inj ‹pure _ = Except.ok d›)
  exact ‹x.principalOutstanding.operator_sub y.principalOutstanding .to_nearest = _›

/-- A re-amortization that passes leaves each outstanding amount at most its old value, and pays a
principal of at least zero. -/
private lemma Loan.tryOverpayment_some (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (h : Loan.tryOverpayment l opc = .ok (some re)) :
    re.state.valueOutstanding.toRat ≤ l.totalValueOutstanding.toRat ∧
      re.state.principalOutstanding.toRat ≤ l.principalOutstanding.toRat ∧
      re.state.managementFeeDue.toRat ≤ l.managementFeeOutstanding.toRat ∧
      re.amounts.principalPaid.isNormalized ∧ 0 ≤ re.amounts.principalPaid.toRat := by
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  obtain ⟨hs1, hs2, hs3, -⟩ := Loan.state_fields l _ ‹l.state = _›
  have hT := l.wf.totalValueOutstanding_norm
  have hP := l.wf.principalOutstanding_norm
  have hM := l.wf.managementFeeOutstanding_norm
  have hT0 : 0 ≤ l.totalValueOutstanding.toRat := l.exact.totalValueOutstanding_nonneg
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ l.managementFeeOutstanding.toRat := l.exact.managementFeeOutstanding_nonneg
  rw [← hs1] at hT hT0
  rw [← hs2] at hP hP0
  rw [← hs3] at hM hM0
  obtain ⟨g1, g2, g3⟩ := roundAndClamp_le _ _ _ _ _ _ hP hP0
    ‹roundAndClamp _ (LoanState.principalOutstanding _) _ _ _ = _›
  obtain ⟨g4, g5, g6⟩ := roundAndClamp_le _ _ _ _ _ _ hT hT0
    ‹roundAndClamp _ (LoanState.valueOutstanding _) _ _ _ = _›
  obtain ⟨g7, g8, g9⟩ := roundAndClamp_le _ _ _ _ _ _ hM hM0
    ‹roundAndClamp _ (LoanState.managementFeeDue _) _ _ _ = _›
  obtain ⟨b1, b2, b3⟩ := LoanState.build_fields _ _ _ _ ‹LoanState.build _ _ _ = _›
  have hd := LoanState.calculateDeltas_principal _ _ _ ‹LoanState.calculateDeltas _ _ = _›
  rw [b2] at hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [b1, ← hs1]; exact g6
  · rw [b2, ← hs2]; exact g3
  · rw [b3, ← hs3]; exact g9
  · exact operator_sub_isNormalized_to_nearest_sz _ _ _ hP g1 hd
  · exact operator_sub_nonneg _ _ _ hP g1 hd (by linarith)

/-- What a payment carries forward: a principal sum of at least zero. -/
private def UnsettledPayment.PaidOk {α : Type} (p : UnsettledPayment α) : Prop :=
  p.amounts.principalPaid.isNormalized ∧ 0 ≤ p.amounts.principalPaid.toRat

/-- `p'` owes no more than `p` and has no more payments left. -/
private def UnsettledPayment.Below {α : Type} (p' p : UnsettledPayment α) : Prop :=
  p'.loan.totalValueOutstanding.toRat ≤ p.loan.totalValueOutstanding.toRat ∧
    p'.loan.principalOutstanding.toRat ≤ p.loan.principalOutstanding.toRat ∧
    p'.loan.managementFeeOutstanding.toRat ≤ p.loan.managementFeeOutstanding.toRat ∧
    p'.loan.paymentRemaining ≤ p.loan.paymentRemaining

private lemma UnsettledPayment.Below.refl {α : Type} (p : UnsettledPayment α) : p.Below p :=
  ⟨le_refl _, le_refl _, le_refl _, by rw [UInt32.le_iff_toNat_le]⟩

private lemma UnsettledPayment.Below.trans {α : Type} {a b c : UnsettledPayment α} (h1 : a.Below b) (h2 : b.Below c) :
    a.Below c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, by
    have := h1.2.2.2; have := h2.2.2.2; rw [UInt32.le_iff_toNat_le] at *; omega⟩

/-- Adding a principal of at least zero keeps the principal sum at least zero. -/
private lemma PaymentAmounts.add_paidOk (a b c : PaymentAmounts) (h : a.add b = .ok c)
    (ha : a.principalPaid.isNormalized ∧ 0 ≤ a.principalPaid.toRat)
    (hb : b.principalPaid.isNormalized ∧ 0 ≤ b.principalPaid.toRat) :
    c.principalPaid.isNormalized ∧ 0 ≤ c.principalPaid.toRat := by
  have hc := PaymentAmounts.add_principal a b c h
  exact ⟨operator_add_isNormalized_to_nearest_sz _ _ _ ha.1 hb.1 hc,
    operator_add_nonneg _ _ _ ha.1 hb.1 hc (by linarith [ha.2, hb.2])⟩

/-- The instalment loop never raises an outstanding amount or PaymentRemaining, and keeps the principal sum at
least zero. -/
private lemma UnsettledPayment.payInstalments_below {α : Type} (payment : UnsettledPayment α) (n : Nat)
    (amount : Number)
    (p' : UnsettledPayment α) (hok : payment.PaidOk)
    (h : UnsettledPayment.payInstalments payment n amount = .ok p') : p'.Below payment ∧ p'.PaidOk := by
  induction n generalizing payment with
  | zero =>
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨UnsettledPayment.Below.refl _, hok⟩
  | succ n ih =>
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact ⟨UnsettledPayment.Below.refl _, hok⟩
    · exact ⟨UnsettledPayment.Below.refl _, hok⟩
    all_goals
      have hr : payment.loan.paymentRemaining ≠ 0 := by
        simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
      have hs := Loan.scheduledComponents_sound payment.loan _ ‹Loan.scheduledComponents payment.loan = _›
      have hd := Loan.doPayment_le payment.loan _ _ hr (fun _ => hs) ‹Loan.doPayment _ _ = _›
      obtain ⟨_, _, -, -, -, -, hip⟩ := PaymentComponents.paidAmounts_ok_inv _ _ ‹PaymentComponents.paidAmounts _ = _›
      have hpaid := PaymentAmounts.add_paidOk _ _ _ ‹PaymentAmounts.add _ _ = _› hok
        ⟨by rw [hip]; exact hs.2.1, by rw [hip]; exact hs.2.2.2.2.1⟩
    · exact ⟨hd, hpaid⟩
    · have h3 := ‹UnsettledPayment.payInstalments _ n amount = _›
      have ih' := fun hh => ih _ hh h3
      obtain ⟨h1, h2⟩ := ih' hpaid
      exact ⟨h1.trans hd, h2⟩

/-- The overpayment tail never raises an outstanding amount or PaymentRemaining, and keeps the principal sum at
least zero. -/
private lemma UnsettledPayment.applyOverpayment_below (payment p' : UnsettledPayment Vault) (amount : Number)
    (hok : payment.PaidOk) (h : UnsettledPayment.applyOverpayment payment amount = .ok p') :
    p'.Below payment ∧ p'.PaidOk := by
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact ⟨UnsettledPayment.Below.refl _, hok⟩
    | skip
  obtain ⟨g1, g2, g3, g4, g5⟩ := Loan.tryOverpayment_some _ _ _ ‹Loan.tryOverpayment _ _ = _›
  have hpaid := PaymentAmounts.add_paidOk _ _ _ ‹PaymentAmounts.add _ _ = _› hok ⟨g4, g5⟩
  have h1 := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = _›).1
  have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
  have e2 := (congrArg RawLoan.principalOutstanding h1 :)
  have e3 := (congrArg RawLoan.managementFeeOutstanding h1 :)
  have e4 := (congrArg RawLoan.paymentRemaining h1 :)
  simp only at e1 e2 e3 e4
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hpaid⟩
  · show _ ≤ _; rw [show ∀ l : Loan, l.totalValueOutstanding = l.toRawLoan.totalValueOutstanding from fun _ => rfl,
      e1]; exact g1
  · show _ ≤ _; rw [show ∀ l : Loan, l.principalOutstanding = l.toRawLoan.principalOutstanding from fun _ => rfl,
      e2]; exact g2
  · show _ ≤ _; rw [show ∀ l : Loan, l.managementFeeOutstanding = l.toRawLoan.managementFeeOutstanding
      from fun _ => rfl, e3]; exact g3
  · show _ ≤ _; rw [show ∀ l : Loan, l.paymentRemaining = l.toRawLoan.paymentRemaining from fun _ => rfl, e4]
    rw [UInt32.le_iff_toNat_le]

/-- A payment's instalments never raise an outstanding amount or PaymentRemaining, and pay a principal of at
least zero. -/
private lemma Loan.payInstalments_below (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number)
    (now : UInt32)
    (p : UnsettledPayment Vault) (hp : (loan.payInstalments v pt amount now).run = .ok (.ok p)) :
    p.loan.totalValueOutstanding.toRat ≤ loan.totalValueOutstanding.toRat ∧
      p.loan.principalOutstanding.toRat ≤ loan.principalOutstanding.toRat ∧
      p.loan.managementFeeOutstanding.toRat ≤ loan.managementFeeOutstanding.toRat ∧
      p.loan.paymentRemaining ≤ loan.paymentRemaining ∧ p.PaidOk := by
  have hz : PaymentAmounts.zero.principalPaid.isNormalized ∧ 0 ≤ PaymentAmounts.zero.principalPaid.toRat :=
    ⟨Number.zero_isNormalized, by rw [show PaymentAmounts.zero.principalPaid = Number.zero from rfl,
      Number.toRat_zero]⟩
  obtain ⟨hchecks, -, -, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  have hscheduled : ∀ p0 : UnsettledPayment Vault, (loan.payInstalments v .regular amount now).run = .ok (.ok p0) →
      p0.loan.totalValueOutstanding.toRat ≤ loan.totalValueOutstanding.toRat ∧
        p0.loan.principalOutstanding.toRat ≤ loan.principalOutstanding.toRat ∧
        p0.loan.managementFeeOutstanding.toRat ≤ loan.managementFeeOutstanding.toRat ∧
        p0.loan.paymentRemaining ≤ loan.paymentRemaining ∧ p0.PaidOk := by
    intro p0 hp0
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 hp0
    have hbelow := fun hh => UnsettledPayment.payInstalments_below _ _ _ _ hh hloop
    obtain ⟨hb, hk⟩ := hbelow hz
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hk⟩
  cases pt
  · exact hscheduled p hp
  · obtain ⟨pc, hpc, hamt, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p hp
    obtain ⟨pc0, hpc0, e1, e2, e3, e4⟩ := Loan.lateComponents_scheduled loan now pc hpc
    have hs := Loan.scheduledComponents_sound loan pc0 hpc0
    rw [← e1, ← e2, ← e3] at hs
    have hd := Loan.doPayment_le loan.unimpaired p.loan pc hchecks.remaining (fun _ => hs) hdo
    obtain ⟨_, _, -, -, -, -, hip⟩ := PaymentComponents.paidAmounts_ok_inv _ _ hamt
    exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, by rw [UnsettledPayment.PaidOk, hip]; exact ⟨hs.2.1, hs.2.2.2.2.1⟩⟩
  · obtain ⟨pc, hpc, hamt, hdo⟩ := Loan.fullPayInstalments_ok loan v amount now p hp
    obtain ⟨_, _, _, _, _, state, _, _, _, _, _, _, -, -, -, -, hstate, -, -, -, -, -, -, rfl⟩ :=
      Loan.fullComponents_ok_inv loan now pc hpc
    have hd := Loan.doPayment_le loan.unimpaired p.loan _ hchecks.remaining (fun h => absurd h (by simp)) hdo
    obtain ⟨_, _, -, -, -, -, hip⟩ := PaymentComponents.paidAmounts_ok_inv _ _ hamt
    obtain ⟨-, h2, -, -⟩ := Loan.state_fields loan state hstate
    refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, ?_⟩
    rw [UnsettledPayment.PaidOk, hip]
    simp only
    rw [h2]
    exact ⟨loan.wf.principalOutstanding_norm,
      (loan.exact.principalOutstanding_nonneg : 0 ≤ loan.principalOutstanding.toRat)⟩
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p hp
    obtain ⟨b1, b2, b3, b4, hk0⟩ := hscheduled p0 h0
    obtain ⟨hb, hk⟩ := UnsettledPayment.applyOverpayment_below p0 p amount hk0 h1
    refine ⟨hb.1.trans b1, hb.2.1.trans b2, hb.2.2.1.trans b3, ?_, hk⟩
    have := hb.2.2.2
    rw [UInt32.le_iff_toNat_le] at this b4 ⊢
    omega

/-- The unimpair keeps AssetsReserved. -/
private lemma Loan.unimpairIfImpaired_reserved (loan : Loan) (v v1 : Vault)
    (h : (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := loan.unimpaired, pool' := v1 })) :
    v1.assetsReserved = v.assetsReserved := by
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp] at h
    obtain rfl : v = v1 := by injection h with h; injection h with h; injection h
    rfl
  · rw [Loan.unimpairIfImpaired_impaired loan v himp] at h
    split at h
    · cases h
    · cases h
    · rename_i v2 hadj
      obtain rfl : v2 = v1 := by injection h with h; injection h with h; injection h
      exact Vault.poolAdjust_reserved_zero v v2 _ rfl hadj

variable (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
  (r : LoanWithAmounts Vault)

/-- A payment never raises DebtTotal and keeps AssetsReserved. -/
lemma Loan.pay_debt (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.broker.debtTotal.toRat ≤ loan.broker.debtTotal.toRat ∧ r.pool'.assetsReserved = v.assetsReserved := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨-, -, -, -, hpaid⟩ := Loan.payInstalments_below loan v pt amount now p hp
  obtain ⟨_, _, _, _, debtTotal', raw, broker', hsums, hadj, hv', hbroker, hloan, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hb : r.loan'.broker = broker' := (congrArg RawLoan.broker (RawLoan.to_lawful_ok hloan).1 :)
  have hd : broker'.debtTotal = debtTotal' :=
    (congrArg RawLoanBroker.debtTotal (RawLoanBroker.to_lawful_ok hbroker).1 :)
  have hpb : p.loan.broker = loan.broker := hst.broker
  refine ⟨?_, ?_⟩
  · rw [hb, hd, ← hpb]
    exact Number.operator_sub_le_self p.loan.broker.wf.debtTotal_norm hpaid.1 hpaid.2 hsums.debt
  · rw [Vault.poolAdjust_reserved_zero p.pool r.pool' _ rfl (Vault.poolAdjust_ok _ _ raw r.pool' hadj hv')]
    exact Loan.unimpairIfImpaired_reserved loan v p.pool hu

/-- A payment never raises PrincipalOutstanding, TotalValueOutstanding, ManagementFeeOutstanding or
PaymentRemaining. -/
lemma Loan.pay_outstanding_le (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    r.loan'.principalOutstanding.toRat ≤ loan.principalOutstanding.toRat ∧
      r.loan'.totalValueOutstanding.toRat ≤ loan.totalValueOutstanding.toRat ∧
      r.loan'.managementFeeOutstanding.toRat ≤ loan.managementFeeOutstanding.toRat ∧
      r.loan'.paymentRemaining ≤ loan.paymentRemaining := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨b1, b2, b3, b4, -⟩ := Loan.payInstalments_below loan v pt amount now p hp
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have h1 := (RawLoan.to_lawful_ok hloan).1
  have e1 := (congrArg RawLoan.totalValueOutstanding h1 :)
  have e2 := (congrArg RawLoan.principalOutstanding h1 :)
  have e3 := (congrArg RawLoan.managementFeeOutstanding h1 :)
  have e4 := (congrArg RawLoan.paymentRemaining h1 :)
  simp only at e1 e2 e3 e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show r.loan'.principalOutstanding = r.loan'.toRawLoan.principalOutstanding from rfl, e2]; exact b2
  · rw [show r.loan'.totalValueOutstanding = r.loan'.toRawLoan.totalValueOutstanding from rfl, e1]; exact b1
  · rw [show r.loan'.managementFeeOutstanding = r.loan'.toRawLoan.managementFeeOutstanding from rfl, e3]
    exact b3
  · rw [show r.loan'.paymentRemaining = r.loan'.toRawLoan.paymentRemaining from rfl, e4]; exact b4

end XRPL.Model.Lending
