import XRPL.Properties.Lending.Common.Walk
import XRPL.Properties.Lending.Loan.Common.Grid
import XRPL.Properties.Lending.Loan.Common.Loss
import XRPL.Properties.Lending.Loan.Common.PayMonotone

/-! # The principal a payment pays, on the LoanScale grid

Every amount an instalment computes is a whole number of LoanScale units, so the principal it takes off
the loan comes off PrincipalOutstanding exactly, and the payment's principal sum is that drop. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.doPayment
  UnsettledPayment.payInstalments UnsettledPayment.applyOverpayment Loan.tryOverpayment Loan.settlePayment
  from XRPL.Model.Lending.Loan.LoanPay
open private reduceCapped from XRPL.Model.Lending.Loan.LoanState
open private Number.clamp_zero_nonneg Number.clamp_zero_le Loan.scheduledComponents_sound Loan.lateComponents_scheduled
  Loan.doPayment_le PaymentAmounts.add_principal LoanState.build_fields LoanState.calculateDeltas_principal
  UnsettledPayment.PaidOk Loan.payInstalments_below roundAndClamp_le
  from XRPL.Properties.Lending.Loan.Common.PayMonotone

/-! ## Deltas on the grid -/

private lemma Number.OnGrid.isNormalized_of {s : Int} {x : Number} (h : Number.OnGrid s x) : x.isNormalized := h.1

lemma UnitsAt.onGrid {x : Number} {s : Int} {k : ℤ} (h : UnitsAt x s k) : Number.OnGrid s x := ⟨h.norm, k, h.val⟩

private lemma LoanStateDeltas.nonNegative_principal_onGrid {s : Int} (d : LoanStateDeltas)
    (h : Number.OnGrid s d.principal) : Number.OnGrid s d.nonNegative.principal := by
  unfold LoanStateDeltas.nonNegative; dsimp only; split
  · exact Number.OnGrid.zero s
  · exact h

private lemma LoanStateDeltas.nonNegative_interest_onGrid {s : Int} (d : LoanStateDeltas)
    (h : Number.OnGrid s d.interest) : Number.OnGrid s d.nonNegative.interest := by
  unfold LoanStateDeltas.nonNegative; dsimp only; split
  · exact Number.OnGrid.zero s
  · exact h

private lemma LoanStateDeltas.nonNegative_managementFee_onGrid {s : Int} (d : LoanStateDeltas)
    (h : Number.OnGrid s d.managementFee) : Number.OnGrid s d.nonNegative.managementFee := by
  unfold LoanStateDeltas.nonNegative; dsimp only; split
  · exact Number.OnGrid.zero s
  · exact h

private lemma reduceCapped_onGrid {s : Int} (value excess v' e' : Number) (hv : Number.OnGrid s value)
    (he : Number.OnGrid s excess) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (h : reduceCapped value excess = .ok (v', e')) : Number.OnGrid s v' ∧ Number.OnGrid s e' := by
  unfold reduceCapped at h
  simp only [bind, Except.bind] at h
  split at h
  · walk_ok
    have hm := Number.OnGrid.min hv he
    have h1 := Except.ok.inj ‹pure _ = Except.ok (v', e')›
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact ⟨Number.OnGrid.sub hv hm hs ‹_›, Number.OnGrid.sub he hm hs ‹_›⟩
  · have h1 := Except.ok.inj h
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact ⟨hv, he⟩

private lemma LoanStateDeltas.reduceByExcess_onGrid {s : Int} {d d' : LoanStateDeltas} {excess : Number}
    (h1 : Number.OnGrid s d.principal) (h2 : Number.OnGrid s d.interest) (h3 : Number.OnGrid s d.managementFee)
    (he : Number.OnGrid s excess) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hr : d.reduceByExcess excess = .ok d') :
    Number.OnGrid s d'.principal ∧ Number.OnGrid s d'.interest ∧ Number.OnGrid s d'.managementFee := by
  unfold LoanStateDeltas.reduceByExcess at hr
  simp only [bind, Except.bind] at hr
  walk_ok
  rename_i _ a ha _ b hb _ c hc hd
  have g1 := reduceCapped_onGrid _ _ a.1 a.2 h2 he hs ha
  have g2 := reduceCapped_onGrid _ _ b.1 b.2 h3 g1.2 hs hb
  have g3 := reduceCapped_onGrid _ _ c.1 c.2 h1 g2.2 hs hc
  obtain rfl := (Except.ok.inj hd).symm
  exact ⟨g3.1, g1.1, g2.1⟩

private lemma LoanStateDeltas.total_onGrid {s : Int} {d : LoanStateDeltas} (h1 : Number.OnGrid s d.principal)
    (h2 : Number.OnGrid s d.interest) (h3 : Number.OnGrid s d.managementFee)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (t : Number) (ht : d.total = .ok t) :
    Number.OnGrid s t := by
  unfold LoanStateDeltas.total at ht
  simp only [bind, Except.bind] at ht
  split at ht
  · cases ht
  · rename_i u hu
    exact Number.OnGrid.add (Number.OnGrid.add h1 h2 hs hu) h3 hs ht

/-- A rounding at an exponent of at most zero is on that grid. -/
private lemma STAmount.roundToNumericType_onGrid' (nt : NumericType) (x T : Number) (mode : rounding_mode) (s : Int)
    (hs : -81 ≤ s ∧ s ≤ 0) (h : STAmount.roundToNumericType nt x mode (some s) = .ok T) : Number.OnGrid s T :=
  STAmount.roundToNumericType_onGrid nt x T mode s ⟨hs.1, by omega⟩ (fun _ => hs.2) h

/-! ## Forward reasoning on the grid -/

open Lean Meta Elab Tactic in
/-- A proof that `x` is on the grid `s`, from the local facts and the shape of `x`. -/
private partial def proveGrid (s x : Expr) : MetaM (Option Expr) := do
  let target ← mkAppM ``Number.OnGrid #[s, x]
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
  if x'.isConstOf ``Number.zero then return some (← mkAppM ``Number.OnGrid.zero #[s])
  let fn := x'.getAppFn.constName?
  let args := x'.getAppArgs
  if (fn == some ``Number.min || fn == some ``Number.max) && args.size == 2 then
    let some pa ← proveGrid s args[0]! | return none
    let some pb ← proveGrid s args[1]! | return none
    let lem := if fn == some ``Number.min then ``Number.OnGrid.min else ``Number.OnGrid.max
    return some (← mkAppM lem #[pa, pb])
  if fn == some ``Number.clamp && args.size == 3 then
    let some pa ← proveGrid s args[0]! | return none
    let some pl ← proveGrid s args[1]! | return none
    let some ph ← proveGrid s args[2]! | return none
    return some (← mkAppM ``Number.OnGrid.clamp #[pa, pl, ph])
  if fn == some ``Number.operator_neg && args.size == 1 then
    let some pa ← proveGrid s args[0]! | return none
    return some (← mkAppM ``Number.OnGrid.neg #[pa])
  let fields := [(``LoanStateDeltas.principal, ``LoanStateDeltas.nonNegative_principal_onGrid),
    (``LoanStateDeltas.interest, ``LoanStateDeltas.nonNegative_interest_onGrid),
    (``LoanStateDeltas.managementFee, ``LoanStateDeltas.nonNegative_managementFee_onGrid)]
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
      let some pe ← proveGrid s (← mkAppM proj #[e]) | return none
      return some (← mkAppOptM lem #[some s, some e, some pe])
  return none

open Lean Meta Elab Tactic in
/-- A local fact of type `ty`, if there is one. -/
private def findFact (ty : Expr) : MetaM (Option Expr) := do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    if ← withReducible (isDefEq ldecl.type ty) then return some ldecl.toExpr
  return none

open Lean Meta Elab Tactic in
/-- Add `Number.OnGrid s c` for every Number step `h : f … = .ok c` whose operands are on the grid `s`. It uses
the local facts `minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1` and `-81 ≤ s ∧ s ≤ 0`. -/
elab "grid_forward " st:term : tactic => do
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 80 do
    changed := false
    rounds := rounds + 1
    let g ← getMainGoal
    let newFact ← g.withContext do
      let s ← elabTerm st (some (mkConst ``Int))
      let hsTy ← mkAppM ``And #[← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkConst ``minExponent,
        mkIntLit 18], s], ← mkAppM ``LE.le #[s, ← mkAppM ``HSub.hSub #[mkConst ``maxExponent, mkIntLit 1]]]
      let hrTy ← mkAppM ``And #[← mkAppM ``LE.le #[mkIntLit (-81), s], ← mkAppM ``LE.le #[s, mkIntLit 0]]
      let some hs ← findFact hsTy | throwError "grid_forward: no exponent range fact"
      let some hr ← findFact hrTy | throwError "grid_forward: no scale range fact"
      for ldecl in (← getLCtx) do
        if ldecl.isImplementationDetail then continue
        let ty ← instantiateMVars ldecl.type
        let some (_, lhs, rhs) := ty.eq? | continue
        unless rhs.isAppOfArity ``Except.ok 3 do continue
        let c := rhs.appArg!
        let cty ← inferType c
        if cty.isConstOf ``Number then
          if (← proveGrid s c).isSome then continue
        else if cty.isConstOf ``LoanStateDeltas then
          if (← proveGrid s (← mkAppM ``LoanStateDeltas.principal #[c])).isSome then continue
        else continue
        let args := lhs.getAppArgs
        let pf? : Option Expr ← match lhs.getAppFn.constName? with
          | some ``Number.operator_sub =>
            if args.size == 3 && args[2]!.isConstOf ``rounding_mode.to_nearest then
              match ← proveGrid s args[0]!, ← proveGrid s args[1]! with
              | some p0, some p1 => pure (some (← mkAppM ``Number.OnGrid.sub #[p0, p1, hs, ldecl.toExpr]))
              | _, _ => pure none
            else pure none
          | some ``Number.operator_add =>
            if args.size == 3 && args[2]!.isConstOf ``rounding_mode.to_nearest then
              match ← proveGrid s args[0]!, ← proveGrid s args[1]! with
              | some p0, some p1 => pure (some (← mkAppM ``Number.OnGrid.add #[p0, p1, hs, ldecl.toExpr]))
              | _, _ => pure none
            else pure none
          | some ``STAmount.roundToNumericType =>
            if args.size == 4 then
              let sc ← whnfR args[3]!
              if sc.isAppOfArity ``Option.some 2 && (← isDefEq sc.appArg! s) then
                pure (some (← mkAppM ``STAmount.roundToNumericType_onGrid'
                  #[args[0]!, args[1]!, c, args[2]!, s, hr, ldecl.toExpr]))
              else pure none
            else pure none
          | some ``LoanStateDeltas.reduceByExcess =>
            let d := args[0]!
            match ← proveGrid s (← mkAppM ``LoanStateDeltas.principal #[d]),
                ← proveGrid s (← mkAppM ``LoanStateDeltas.interest #[d]),
                ← proveGrid s (← mkAppM ``LoanStateDeltas.managementFee #[d]), ← proveGrid s args[1]! with
            | some p1, some p2, some p3, some pe =>
              let pf ← mkAppOptM ``LoanStateDeltas.reduceByExcess_onGrid
                #[some s, some d, some c, some args[1]!, some p1, some p2, some p3, some pe, some hs,
                  some ldecl.toExpr]
              pure (some pf)
            | _, _, _, _ => pure none
          | some ``LoanStateDeltas.total =>
            let d := args[0]!
            match ← proveGrid s (← mkAppM ``LoanStateDeltas.principal #[d]),
                ← proveGrid s (← mkAppM ``LoanStateDeltas.interest #[d]),
                ← proveGrid s (← mkAppM ``LoanStateDeltas.managementFee #[d]) with
            | some p1, some p2, some p3 => pure (some (← mkAppOptM ``LoanStateDeltas.total_onGrid
                #[some s, some d, some p1, some p2, some p3, some hs, some c, some ldecl.toExpr]))
            | _, _, _ => pure none
          | _ => pure none
        if let some pf := pf? then return some (pf, ← inferType pf)
      return none
    if let some (pf, ty) := newFact then
      let (_, g') ← (← g.assert `hgrid ty pf).intro1P
      replaceMainGoal [g']
      changed := true

open Lean Meta Elab Tactic in
/-- Close `Number.OnGrid s x` from the local facts. -/
elab "grid_prove" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (s, x) := (ty.getAppFnArgs) |> fun (f, a) =>
      if f == ``Number.OnGrid && a.size == 2 then some (a[0]!, a[1]!) else none
    | throwError "grid_prove: not an OnGrid goal"
  let some pf ← proveGrid s x | throwError "grid_prove: no proof found"
  g.assign pf
  replaceMainGoal []

/-- The principal of a scheduled instalment. A final instalment clears PrincipalOutstanding, any other takes
a whole number of LoanScale units off it, between zero and all of it. -/
private lemma Loan.scheduledComponents_principal (l : Loan) (pc : PaymentComponents)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.scheduledComponents l = .ok pc) :
    (pc.isFinal = true ∧ pc.principalDelta = l.principalOutstanding) ∨
      (pc.isFinal = false ∧ Number.OnGrid l.loanScale pc.principalDelta ∧ 0 ≤ pc.principalDelta.toRat ∧
        pc.principalDelta.toRat ≤ l.principalOutstanding.toRat) := by
  have hsb := Loan.loanScale_bounds l
  have hP := l.wf.principalOutstanding_norm
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  unfold Loan.scheduledComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at *
    subst_vars
  all_goals first
    | exact Or.inl ⟨rfl, rfl⟩
    | (obtain ⟨t, p, m, -, -, -, ht, hp, hm, hi, -, h1, h2, h3⟩ := Loan.state_units l _ ‹l.state = _›
       have g1 := ht.onGrid
       have g2 := hp.onGrid
       have g3 := hm.onGrid
       have g4 := hi.onGrid
       rw [← h2] at hP hP0
       grid_forward l.loanScale
       refine Or.inr ⟨rfl, ?_, Number.clamp_zero_nonneg _ _ hP0, ?_⟩
       · grid_prove
       · rw [← h2]
         apply Number.clamp_zero_le _ _ _ hP hP0
         apply Number.OnGrid.isNormalized_of (s := l.loanScale)
         grid_prove)

/-- PrincipalOutstanding is a whole number of LoanScale units, below `2^63` of them. -/
lemma Loan.principal_onGrid (l : Loan) :
    Number.OnGrid l.loanScale l.principalOutstanding ∧
      l.principalOutstanding.toRat < 2 ^ 63 * (10 : ℚ) ^ l.loanScale := by
  obtain ⟨p, hp, hpv⟩ := UnitsAt.of_atExponent l.wf.principalOutstanding_norm
    (Loan.grid l).principalOutstanding_atExponent
  have hB := NumericType.mantissaBound_le l.toExact.numericType
  have hpos : (0 : ℚ) < (10 : ℚ) ^ l.loanScale := zpow_pos (by norm_num) _
  refine ⟨hpv.onGrid, ?_⟩
  rw [hpv.val]
  have : (p : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le hp hB
  exact mul_lt_mul_of_pos_right (by exact_mod_cast this) hpos

/-- Adding two amounts of at least zero units, whose sum stays below `2^63` units, is exact. -/
lemma Number.OnGrid.add_exact {s : Int} {x y d : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) (hlt : x.toRat + y.toRat < 2 ^ 63 * (10 : ℚ) ^ s)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hok : x.operator_add y .to_nearest = .ok d) :
    d.toRat = x.toRat + y.toRat := by
  obtain ⟨hxn, a, ha⟩ := hx
  obtain ⟨hyn, b, hb⟩ := hy
  have hp : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have ha0 : 0 ≤ a := by
    have : (0 : ℚ) ≤ (a : ℚ) * 10 ^ s := ha ▸ hx0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hb0 : 0 ≤ b := by
    have : (0 : ℚ) ≤ (b : ℚ) * 10 ^ s := hb ▸ hy0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hab : a + b < 2 ^ 63 := by
    have : ((a + b : ℤ) : ℚ) * 10 ^ s < ((2 ^ 63 : ℤ) : ℚ) * 10 ^ s := by
      push_cast; rw [add_mul, ← ha, ← hb]; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  rw [Number.operator_add_toRat_of_grid x y d a b s hxn hyn ha hb ⟨by omega, hab⟩ hs hok, ha, hb]
  push_cast; ring

/-- Taking an amount of at least zero units, at most the balance, off a balance below `2^63` units is exact. -/
lemma Number.OnGrid.sub_exact {s : Int} {x y d : Number} (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hy0 : 0 ≤ y.toRat) (hle : y.toRat ≤ x.toRat) (hlt : x.toRat < 2 ^ 63 * (10 : ℚ) ^ s)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hok : x.operator_sub y .to_nearest = .ok d) :
    d.toRat = x.toRat - y.toRat := by
  obtain ⟨hxn, a, ha⟩ := hx
  obtain ⟨hyn, b, hb⟩ := hy
  have hp : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have hb0 : 0 ≤ b := by
    have : (0 : ℚ) ≤ (b : ℚ) * 10 ^ s := hb ▸ hy0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hba : b ≤ a := by
    have : (b : ℚ) * 10 ^ s ≤ (a : ℚ) * 10 ^ s := by rw [← ha, ← hb]; exact hle
    exact_mod_cast le_of_mul_le_mul_right this hp
  have ha63 : a < 2 ^ 63 := by
    have : (a : ℚ) * 10 ^ s < ((2 ^ 63 : ℤ) : ℚ) * 10 ^ s := by push_cast; rw [← ha]; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  rw [Number.operator_sub_toRat_of_grid x y d a b s hxn hyn ha hb ⟨by omega, by omega⟩ hs hok, ha, hb]
  push_cast; ring

/-- An instalment takes its principal off PrincipalOutstanding, a final one clears it. -/
private lemma Loan.doPayment_principal (l l' : Loan) (pc : PaymentComponents) (h : Loan.doPayment l pc = .ok l') :
    (pc.isFinal = true → l'.principalOutstanding = Number.zero) ∧
      (pc.isFinal = false →
        l.principalOutstanding.operator_sub pc.principalDelta .to_nearest = .ok l'.principalOutstanding) ∧
      l'.loanScale = l.loanScale := by
  have hls := (Loan.doPayment_sameTerms l l' pc h).loanScale
  cases hf : pc.isFinal
  · simp only [Loan.doPayment, hf, Bool.false_eq_true, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    have h1 := (RawLoan.to_lawful_ok ‹_›).1
    refine ⟨fun h => (by cases h), fun _ => ?_, hls⟩
    rw [show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl, h1]
    assumption
  · simp only [Loan.doPayment, hf, ↓reduceIte] at h
    unfold_ter at h
    walk_ok
    have h1 := (RawLoan.to_lawful_ok ‹_›).1
    refine ⟨fun _ => ?_, fun h => (by cases h), hls⟩
    rw [show l'.principalOutstanding = l'.toRawLoan.principalOutstanding from rfl, h1]

/-- The principal a payment has summed so far: whole LoanScale units, at least zero, and together with
PrincipalOutstanding it is the principal the loan started with. -/
private def UnsettledPayment.PaidOn {α : Type} (p : UnsettledPayment α) (s : Int) (P0 : ℚ) : Prop :=
  Number.OnGrid s p.amounts.principalPaid ∧ 0 ≤ p.amounts.principalPaid.toRat ∧
    p.amounts.principalPaid.toRat + p.loan.principalOutstanding.toRat = P0

/-- One instalment keeps the principal sum exact. Its principal joins the sum and leaves
PrincipalOutstanding. -/
private lemma Loan.instalment_paidOn (l l' : Loan) (pc : PaymentComponents) (amounts inst amounts' : PaymentAmounts)
    (s : Int) (P0 : ℚ) (hr : -81 ≤ s ∧ s ≤ 0) (hP0 : P0 < 2 ^ 63 * (10 : ℚ) ^ s) (hls : l.loanScale = s)
    (hacc : Number.OnGrid s amounts.principalPaid ∧ 0 ≤ amounts.principalPaid.toRat ∧
      amounts.principalPaid.toRat + l.principalOutstanding.toRat = P0)
    (hδ : pc.isFinal = true ∧ pc.principalDelta = l.principalOutstanding ∨
      pc.isFinal = false ∧ Number.OnGrid s pc.principalDelta ∧ 0 ≤ pc.principalDelta.toRat ∧
        pc.principalDelta.toRat ≤ l.principalOutstanding.toRat)
    (hpaid : pc.paidAmounts = .ok inst) (hdo : Loan.doPayment l pc = .ok l')
    (hadd : amounts.add inst = .ok amounts') :
    (Number.OnGrid s amounts'.principalPaid ∧ 0 ≤ amounts'.principalPaid.toRat ∧
      amounts'.principalPaid.toRat + l'.principalOutstanding.toRat = P0) ∧ l'.loanScale = s := by
  subst hls
  have hsb := Loan.loanScale_bounds l
  obtain ⟨hPg, hPlt⟩ := Loan.principal_onGrid l
  have hP0' : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  obtain ⟨_, _, -, -, -, -, hip⟩ := PaymentComponents.paidAmounts_ok_inv _ _ hpaid
  have hsum := PaymentAmounts.add_principal _ _ _ hadd
  rw [hip] at hsum
  obtain ⟨hfin, hstep, hls'⟩ := Loan.doPayment_principal l l' pc hdo
  obtain ⟨hag, ha0, hae⟩ := hacc
  refine ⟨?_, hls'⟩
  rcases hδ with ⟨hf, hδ⟩ | ⟨hf, hδg, hδ0, hδle⟩
  · rw [hδ] at hsum
    have hv := Number.OnGrid.add_exact hag hPg ha0 hP0' (by linarith) hsb hsum
    refine ⟨Number.OnGrid.add hag hPg hsb hsum, by rw [hv]; linarith, ?_⟩
    rw [hfin hf, Number.toRat_zero, hv]; linarith
  · have hv := Number.OnGrid.add_exact hag hδg ha0 hδ0 (by linarith) hsb hsum
    have hpo := Number.OnGrid.sub_exact hPg hδg hδ0 hδle hPlt hsb (hstep hf)
    refine ⟨Number.OnGrid.add hag hδg hsb hsum, by rw [hv]; linarith, ?_⟩
    rw [hpo, hv]; linarith

/-- The scheduled instalments keep the principal sum exact. -/
lemma UnsettledPayment.payInstalments_paidOn {α : Type} (amount : Number) (s : Int) (P0 : ℚ)
    (hr : -81 ≤ s ∧ s ≤ 0) (hP0 : P0 < 2 ^ 63 * (10 : ℚ) ^ s) :
    ∀ (n : Nat) (payment p : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p →
      payment.loan.loanScale = s → payment.PaidOn s P0 → p.PaidOn s P0 ∧ p.loan.loanScale = s := by
  intro n
  induction n with
  | zero =>
    intro payment p h hls hp
    unfold UnsettledPayment.payInstalments at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hp, hls⟩
  | succ k ih =>
    intro payment p h hls hp
    unfold UnsettledPayment.payInstalments at h
    unfold_ter at h
    walk_ok'
    all_goals first
      | exact ⟨hp, hls⟩
      | (have hδ := Loan.scheduledComponents_principal payment.loan _ (hls ▸ hr)
           ‹Loan.scheduledComponents payment.loan = _›
         rw [hls] at hδ
         have hpaid := ‹PaymentComponents.paidAmounts _ = _›
         have hdo := ‹Loan.doPayment _ _ = _›
         have hadd := ‹PaymentAmounts.add _ _ = _›
         have hstep := Loan.instalment_paidOn payment.loan _ _ payment.amounts _ _ s P0 hr hP0 hls hp (by exact hδ)
           hpaid hdo hadd
         first
           | exact hstep
           | (have hrec := ‹UnsettledPayment.payInstalments _ k amount = _›
              exact ih _ _ hrec hstep.2 hstep.1))

/-- A rounding at the grid clamped into `[0, cap]` is on the grid. -/
private lemma roundAndClamp_onGrid (value cap : Number) (mode : rounding_mode) (nt : NumericType) (s : Int)
    (y : Number) (hr : -81 ≤ s ∧ s ≤ 0) (hcap : Number.OnGrid s cap) (h : roundAndClamp value cap mode nt s = .ok y) :
    Number.OnGrid s y := by
  unfold roundAndClamp at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hround
    obtain rfl := (Except.ok.inj h).symm
    exact Number.OnGrid.clamp (STAmount.roundToNumericType_onGrid' _ _ _ _ _ hr hround) (Number.OnGrid.zero s) hcap

/-- The principal an overpayment re-amortization pays is the drop in PrincipalOutstanding, whole LoanScale
units of at least zero. -/
private lemma Loan.tryOverpayment_principal (l : Loan) (opc : PaymentComponents) (re : Reamortization)
    (hr : -81 ≤ l.loanScale ∧ l.loanScale ≤ 0) (h : Loan.tryOverpayment l opc = .ok (some re)) :
    Number.OnGrid l.loanScale re.amounts.principalPaid ∧ 0 ≤ re.amounts.principalPaid.toRat ∧
      re.amounts.principalPaid.toRat + re.state.principalOutstanding.toRat = l.principalOutstanding.toRat ∧
      0 ≤ re.state.principalOutstanding.toRat := by
  have hsb := Loan.loanScale_bounds l
  obtain ⟨hPg, hPlt⟩ := Loan.principal_onGrid l
  unfold Loan.tryOverpayment at h
  simp only [bind, Except.bind] at h
  walk_ok
  all_goals first
    | (have hn := Except.ok.inj ‹pure none = Except.ok (some re)›; cases hn)
    | skip
  obtain rfl := Option.some.inj (Except.ok.inj ‹pure (some _) = Except.ok (some re)›)
  obtain ⟨-, hs2, -, -⟩ := Loan.state_fields l _ ‹l.state = _›
  have hP := l.wf.principalOutstanding_norm
  have hP0 : 0 ≤ l.principalOutstanding.toRat := l.exact.principalOutstanding_nonneg
  rw [← hs2] at hP hP0 hPg hPlt
  have hround := ‹roundAndClamp _ (LoanState.principalOutstanding _) _ _ _ = _›
  obtain ⟨-, g2, g3⟩ := roundAndClamp_le _ _ _ _ _ _ hP hP0 hround
  have hpog := roundAndClamp_onGrid _ _ _ _ _ _ hr hPg hround
  obtain ⟨-, b2, -⟩ := LoanState.build_fields _ _ _ _ ‹LoanState.build _ _ _ = _›
  have hd := LoanState.calculateDeltas_principal _ _ _ ‹LoanState.calculateDeltas _ _ = _›
  rw [b2] at hd
  have hv := Number.OnGrid.sub_exact hPg hpog g2 g3 hPlt hsb hd
  refine ⟨Number.OnGrid.sub hPg hpog hsb hd, by rw [hv]; linarith, ?_, ?_⟩
  · show _ + (LoanState.principalOutstanding _).toRat = _
    rw [hv, b2, ← hs2]; ring
  · show 0 ≤ (LoanState.principalOutstanding _).toRat
    rw [b2]; exact g2

/-- The overpayment tail keeps the principal sum exact. -/
private lemma UnsettledPayment.applyOverpayment_paidOn (payment p' : UnsettledPayment Vault) (amount : Number) (s : Int)
    (P0 : ℚ) (hr : -81 ≤ s ∧ s ≤ 0) (hP0 : P0 < 2 ^ 63 * (10 : ℚ) ^ s) (hls : payment.loan.loanScale = s)
    (hp : payment.PaidOn s P0) (h : UnsettledPayment.applyOverpayment payment amount = .ok p') :
    p'.PaidOn s P0 ∧ p'.loan.loanScale = s := by
  have hst := (UnsettledPayment.applyOverpayment_sameTerms payment p' amount h).1
  have hls' : p'.loan.loanScale = s := by rw [hst.loanScale, hls]
  simp only [UnsettledPayment.applyOverpayment] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact ⟨hp, hls⟩
    | skip
  refine ⟨?_, hls'⟩
  subst hls
  have hsb := Loan.loanScale_bounds payment.loan
  obtain ⟨g1, g2, g3, g4⟩ := Loan.tryOverpayment_principal _ _ _ hr ‹Loan.tryOverpayment _ _ = _›
  have hsum := PaymentAmounts.add_principal _ _ _ ‹PaymentAmounts.add _ _ = _›
  have hl := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = _›).1
  have e2 := (congrArg RawLoan.principalOutstanding hl :)
  simp only at e2
  obtain ⟨hag, ha0, hae⟩ := hp
  have hv := Number.OnGrid.add_exact hag g1 ha0 g2 (by
    have := Loan.principal_onGrid payment.loan
    linarith) hsb hsum
  refine ⟨Number.OnGrid.add hag g1 hsb hsum, by rw [hv]; linarith, ?_⟩
  rw [show ∀ l : Loan, l.principalOutstanding = l.toRawLoan.principalOutstanding from fun _ => rfl, e2, hv]
  linarith

/-- A single instalment that clears all of PrincipalOutstanding, or takes off whole units of at most all of
it, pays exactly that drop. -/
private lemma Loan.single_paidOn (loan l' : Loan) (pc : PaymentComponents) (amounts : PaymentAmounts)
    (hδ : pc.isFinal = true ∧ pc.principalDelta = loan.principalOutstanding ∨
      pc.isFinal = false ∧ Number.OnGrid loan.loanScale pc.principalDelta ∧ 0 ≤ pc.principalDelta.toRat ∧
        pc.principalDelta.toRat ≤ loan.principalOutstanding.toRat)
    (hamt : pc.paidAmounts = .ok amounts) (hdo : Loan.doPayment loan.unimpaired pc = .ok l') :
    Number.OnGrid loan.loanScale amounts.principalPaid ∧ 0 ≤ amounts.principalPaid.toRat ∧
      amounts.principalPaid.toRat + l'.principalOutstanding.toRat = loan.principalOutstanding.toRat := by
  have hsb := Loan.loanScale_bounds loan
  obtain ⟨hPg, hPlt⟩ := Loan.principal_onGrid loan
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  obtain ⟨_, _, -, -, -, -, hip⟩ := PaymentComponents.paidAmounts_ok_inv _ _ hamt
  obtain ⟨hfin, hstep, -⟩ := Loan.doPayment_principal loan.unimpaired l' pc hdo
  rw [hip]
  rcases hδ with ⟨hf, hδ⟩ | ⟨hf, hδg, hδ0, hδle⟩
  · rw [hδ, hfin hf, Number.toRat_zero]
    exact ⟨hPg, hP0, by ring⟩
  · have hpo := Number.OnGrid.sub_exact (s := loan.loanScale) hPg hδg hδ0 hδle hPlt hsb (hstep hf)
    exact ⟨hδg, hδ0, by rw [hpo]; ring⟩

/-- The principal a payment's instalments pay is the drop in PrincipalOutstanding, in whole LoanScale units
of at least zero. -/
lemma Loan.payInstalments_paidOn (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hr : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0)
    (h : (loan.payInstalments v pt amount now).run = .ok (.ok p)) :
    p.PaidOn loan.loanScale loan.principalOutstanding.toRat := by
  obtain ⟨-, hP0⟩ := Loan.principal_onGrid loan
  have hreg : ∀ p0 : UnsettledPayment Vault, (loan.payInstalments v .regular amount now).run = .ok (.ok p0) →
      p0.PaidOn loan.loanScale loan.principalOutstanding.toRat ∧ p0.loan.loanScale = loan.loanScale := by
    intro p0 hp0
    obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p0 hp0
    refine UnsettledPayment.payInstalments_paidOn amount _ _ hr hP0 _ _ _ hloop rfl ⟨Number.OnGrid.zero _, ?_, ?_⟩
    · show 0 ≤ Number.zero.toRat; rw [Number.toRat_zero]
    · show Number.zero.toRat + loan.principalOutstanding.toRat = _; rw [Number.toRat_zero, zero_add]
  cases pt
  · exact (hreg p h).1
  · obtain ⟨pc, hpc, hamt, hdo⟩ := Loan.latePayInstalments_ok loan v amount now p h
    obtain ⟨pc0, hpc0, -, e2, -, e4⟩ := Loan.lateComponents_scheduled loan now pc hpc
    have hδ := Loan.scheduledComponents_principal loan pc0 hr hpc0
    rw [← e2, ← e4] at hδ
    exact Loan.single_paidOn loan p.loan pc p.amounts hδ hamt hdo
  · obtain ⟨pc, hpc, hamt, hdo⟩ := Loan.fullPayInstalments_ok loan v amount now p h
    obtain ⟨_, _, _, _, _, state, _, _, _, _, _, _, -, -, -, -, hstate, -, -, -, -, -, -, rfl⟩ :=
      Loan.fullComponents_ok_inv loan now pc hpc
    obtain ⟨-, hs2, -, -⟩ := Loan.state_fields loan state hstate
    exact Loan.single_paidOn loan p.loan _ p.amounts (Or.inl ⟨rfl, hs2⟩) hamt hdo
  · obtain ⟨p0, h0, h1⟩ := Loan.overPayInstalments_ok loan v amount now p h
    obtain ⟨hp0, hls0⟩ := hreg p0 h0
    exact (UnsettledPayment.applyOverpayment_paidOn p0 p amount _ _ hr hP0 hls0 hp0 h1).1

/-- The principal a payment pays, read in the loan, the broker and the vault. It is whole LoanScale units of
at least zero, the drop in PrincipalOutstanding, and it leaves DebtTotal and AssetsDeployed. -/
lemma Loan.pay_principal (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hr : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0)
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    ∃ paid : Number, Number.OnGrid loan.loanScale paid ∧ 0 ≤ paid.toRat ∧
      paid.toRat + r.loan'.principalOutstanding.toRat = loan.principalOutstanding.toRat ∧
      loan.broker.debtTotal.operator_sub paid .to_nearest = .ok r.loan'.broker.debtTotal ∧
      v.assetsDeployed.operator_add paid.operator_neg .to_nearest = .ok r.pool'.assetsDeployed := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨hpg, hp0, hpe⟩ := Loan.payInstalments_paidOn loan v pt amount now p hr hp
  obtain ⟨_, _, _, _, debtTotal', raw, broker', hsums, hadj, hv', hbroker, hloan, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hl := (RawLoan.to_lawful_ok hloan).1
  have hb : r.loan'.broker = broker' := (congrArg RawLoan.broker hl :)
  have hd : broker'.debtTotal = debtTotal' :=
    (congrArg RawLoanBroker.debtTotal (RawLoanBroker.to_lawful_ok hbroker).1 :)
  have hpo : r.loan'.principalOutstanding = p.loan.principalOutstanding := (congrArg RawLoan.principalOutstanding hl :)
  have hpool := Vault.poolAdjust_ok _ _ raw r.pool' hadj hv'
  have hAD : p.pool.assetsDeployed = v.assetsDeployed := by
    cases himp : loan.isImpaired
    · rw [Loan.unimpairIfImpaired_not loan v himp] at hu
      obtain rfl : v = p.pool := by injection hu with hu; injection hu with hu; injection hu
      rfl
    · rw [Loan.unimpairIfImpaired_impaired loan v himp] at hu
      split at hu
      · cases hu
      · cases hu
      · rename_i v1 hadj1
        obtain rfl : v1 = p.pool := by injection hu with hu; injection hu with hu; injection hu
        exact Vault.poolAdjust_deployed_zero v _ _ rfl hadj1
  refine ⟨p.amounts.principalPaid, hpg, hp0, by rw [hpo]; exact hpe, ?_, ?_⟩
  · rw [hb, hd, ← show p.loan.broker = loan.broker from hst.broker]
    exact hsums.debt
  · rw [← hAD]
    exact (Vault.poolAdjust_adjustSums _ _ _ hpool).deployed

end XRPL.Model.Lending
