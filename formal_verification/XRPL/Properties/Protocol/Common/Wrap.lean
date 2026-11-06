import XRPL.Properties.Protocol.Common.Errors
import XRPL.Properties.Protocol.Common.FixedWidth
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap
import XRPL.Properties.Protocol.Number.Add.Common.NormalizedSum
import XRPL.Properties.Protocol.Number.Normalize.Common.MantissaBound
import XRPL.Properties.Protocol.Number.Normalize.NormalizedResult
import XRPL.Properties.Protocol.STAmount.Common.Checked
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero

/-! # Where a Protocol operation could wrap around

The Number and STAmount operations check their fixed-width arithmetic. Addition and subtraction never wrap on
normalized operands, division never wraps on a normalized divisor, and an STAmount conversion never wraps on an
amount whose signed value fits an `Int64`. The other operations never wrap. Every operation that lending runs
returns normalized Numbers and amounts that fit, so a lending computation that starts from such values never
wraps. -/

namespace XRPL.Model.Protocol

/-- One rule of `wrap_side`. The end of this file covers the Protocol operations, and the lending files add the
fields of the ledger objects. -/
syntax "wrap_rule" : tactic

/-- Prove that a value is normalized or fits from the step that returned it, with that step's result lemma. -/
syntax "wrap_result" : tactic

/-- Prove that a field is normalized from a predicate on its record, or from the record's well-formedness. -/
syntax "wrap_field" : tactic

/-- Prove that an operand is normalized or that an amount fits, from the hypotheses that produced it. The rules
match goals at the reducible transparency, so a rule that does not apply fails fast. -/
macro "wrap_side" : tactic => `(tactic| with_reducible first | assumption | wrap_result | wrap_field | wrap_rule)

/-- Prove a side condition about a value that a model function returned, by going through that function. The vault
files implement it, since they have the tactics that walk a function's code. -/
syntax "wrap_unfold" : tactic

/-- Close a path whose step `f … = .error .wrap` failed, by going through the code of the model function `f`. -/
syntax "wrap_inline" : tactic

open Lean Elab Tactic Meta in
/-- Run a tactic at the default transparency. A `simp` discharger otherwise runs at the reducible one. -/
elab "with_default_transparency " t:tactic : tactic => withTransparency .default (evalTactic t)

open Lean Elab Tactic Meta in
/-- Prove a `Normalized` predicate on a record that the code builds, one field at a time. -/
elab "wrap_mk" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let isPred := match tgt.getAppFn.constName? with
    | some (.str _ "Normalized") => true
    | _ => false
  let some x := tgt.getAppArgs.back? | throwError "wrap_mk: no record"
  let env ← getEnv
  let built := ((← whnfR x).getAppFn.constName?.bind env.find?).any (·.isCtor)
  unless isPred && built do throwError "wrap_mk: not a built record"
  evalTactic (← `(tactic| (constructor <;> (try dsimp only) <;> wrap_side)))

open Lean Elab Tactic Meta in
/-- Close an equation goal `f … = r` with a hypothesis about the same function `f`. The two sides are compared at
the reducible transparency, so a failed lookup never computes with the Numbers. -/
elab "wrap_hyp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := tgt.eq? | throwError "wrap_hyp: the goal is not an equation"
    let strip (e : Expr) : Expr := if e.isAppOf ``ExceptT.run then e.appArg! else e
    let some f := (strip lhs).getAppFn.constName? | throwError "wrap_hyp: no function on the left side"
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let some (_, lhs', rhs') := (← instantiateMVars ldecl.type).eq? | continue
      unless (strip lhs').getAppFn.constName? == some f do continue
      if ← withReducible (commitWhen (isDefEq (strip lhs) (strip lhs') <&&> isDefEq rhs rhs')) then
        g.assign (mkFVar ldecl.fvarId)
        replaceMainGoal []
        return
    throwError "wrap_hyp: no hypothesis about {f}"

open Lean Meta in
/-- The value a side condition is about, and the suffixes of the result lemmas that prove it. -/
def wrapResultTarget? (tgt : Expr) : Option (Expr × List String) :=
  if tgt.isAppOfArity ``Number.isNormalized 1 then
    some (tgt.appArg!, ["_isNormalized_any", "_isNormalized", "_normalized"])
  else if tgt.isAppOfArity `XRPL.Model.Protocol.STAmount.Fits 1 then some (tgt.appArg!, ["_fits"])
  else if tgt.isAppOfArity ``LT.lt 4 && (tgt.getArg! 2).isAppOfArity ``UInt64.toNat 1 &&
      (tgt.getArg! 2).appArg!.isAppOfArity ``STAmount.mValue 1 then
    some ((tgt.getArg! 2).appArg!.appArg!, ["_mValue_lt"])
  else match tgt.getAppFn.constName? with
    | some (.str _ "Normalized") => tgt.getAppArgs.back?.map (·, ["_normalized"])
    | _ => none

open Lean Meta in
/-- The local value a field read starts from: `x` in `x.a.b`. -/
partial def wrapRootFVar? (e : Expr) : MetaM (Option FVarId) := do
  let e ← whnfR e
  if let .fvar x := e then return some x
  if let .proj _ _ x := e then return ← wrapRootFVar? x
  if let some f := e.getAppFn.constName? then
    if (← getProjectionFnInfo? f).isSome then return ← wrapRootFVar? e.appArg!
  return none

-- the result lemma of a step is `f_isNormalized`, `f_normalized`, `f_fits` or `f_mValue_lt`. The step's own
-- equation fixes the lemma's operands, and `wrap_side` proves its other hypotheses.
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| wrap_result) => do
    let g ← getMainGoal
    let rest := (← getGoals).erase g
    g.withContext do
      let some (t, sufs) := wrapResultTarget? (← instantiateMVars (← g.getType)) | throwError "wrap_result: no value"
      let some root ← wrapRootFVar? t | throwError "wrap_result: no local value"
      let env ← getEnv
      let strip (e : Expr) : Expr := if e.isAppOf ``ExceptT.run then e.appArg! else e
      for ldecl in (← getLCtx) do
        if ldecl.isImplementationDetail then continue
        let some (_, lhs, rhs) := (← instantiateMVars ldecl.type).eq? | continue
        unless rhs.isAppOfArity ``Except.ok 3 && rhs.appArg!.containsFVar root do continue
        let some f := (strip lhs).getAppFn.constName? | continue
        let user := (privateToUserName? f).getD f
        for suf in sufs do
          for lem in [f.appendAfter suf, user.appendAfter suf, mkPrivateName env (user.appendAfter suf)] do
            unless env.contains lem do continue
            let s ← saveState
            try
              let gs ← withReducible (g.apply (← mkConstWithFreshMVarLevels lem))
              -- the step's own equation first, then the hypotheses on the operands it fixes
              let isStep (m : MVarId) : MetaM Bool := do
                let some (_, l, _) := (← instantiateMVars (← m.getType)).eq? | return false
                return (strip l).getAppFn.constName? == some f
              for m in gs do
                if ← isStep m then
                  setGoals [m]
                  evalTactic (← `(tactic| wrap_hyp))
              for m in gs do
                unless ← m.isAssigned do
                  setGoals [m]
                  evalTactic (← `(tactic| wrap_side))
                  unless (← getGoals).isEmpty do throwError "wrap_result: a hypothesis is left"
              setGoals rest
              return
            catch _ =>
              s.restore
      throwError "wrap_result: no result lemma applies"

-- a field `x.f` of a record with a predicate `S.Normalized` uses its field `S.Normalized.f`, and a field of a lawful
-- object `y` uses the well-formedness clause `RawS.WF.f_norm (T.wf y)`
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| wrap_field) => do
    let g ← getMainGoal
    g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let isPred := match tgt.getAppFn.constName? with
        | some (.str _ "Normalized") => true
        | _ => false
      unless tgt.isAppOfArity ``Number.isNormalized 1 || isPred do throwError "wrap_field: not a normalized value"
      let some a := tgt.getAppArgs.back? | throwError "wrap_field: no value"
      let some pf := a.getAppFn.constName? | throwError "wrap_field: not a field"
      unless (← getProjectionFnInfo? pf).isSome do throwError "wrap_field: not a field"
      let .str S fld := pf | throwError "wrap_field: not a field"
      let x := a.appArg!
      let env ← getEnv
      -- a record the code builds is read field by field after `dsimp only`
      if (x.getAppFn.constName?.bind env.find?).any (·.isCtor) then throwError "wrap_field: a built record"
      let pred := S ++ `Normalized ++ .mkSimple fld
      if env.contains pred then
        let s ← saveState
        try
          let [m] ← withReducible (g.apply (← mkConstWithFreshMVarLevels pred)) | throwError "wrap_field: goals"
          setGoals [m]
          evalTactic (← `(tactic| wrap_side))
          unless (← getGoals).isEmpty do throwError "wrap_field: left"
          return
        catch _ =>
          s.restore
      let wfLemma := S ++ `WF ++ .mkSimple (fld ++ "_norm")
      let some toRaw := x.getAppFn.constName? | throwError "wrap_field: not a lawful object"
      let wf := toRaw.getPrefix ++ `wf
      unless env.contains wfLemma && env.contains wf do throwError "wrap_field: no well-formedness clause"
      g.assign (← mkAppM wfLemma #[← mkAppM wf #[x.appArg!]])
      replaceMainGoal []

/-- A note that `wrap_facts` could not prove the fact about a value, so it does not try again. -/
def WrapNoFact {α : Sort _} (_ : α) : Prop := True

open Lean Elab Tactic Meta in
/-- Prove once, in the order the code computes them, that the values the steps returned are normalized, and add
each fact as a hypothesis. A fact that `wrap_side` cannot prove within a small budget is noted and skipped. -/
elab "wrap_facts" : tactic => do
  let env ← getEnv
  let mut g ← getMainGoal
  let rest := (← getGoals).erase g
  let decls := (← g.withContext getLCtx).decls.toList.filterMap id
  for ldecl in decls do
    if ldecl.isImplementationDetail then continue
    let fact? ← g.withContext do
      let some (_, _, rhs) := (← instantiateMVars ldecl.type).eq? | return none
      unless rhs.isAppOfArity ``Except.ok 3 do return none
      let p := rhs.appArg!
      let x := if p.isAppOfArity ``Except.ok 3 then p.appArg! else p
      unless x.isFVar do return none
      let ty ← whnfR (← inferType x)
      if ty.isConstOf ``Number then return some (mkApp (mkConst ``Number.isNormalized) x)
      let some c := ty.getAppFn.constName? | return none
      unless env.contains (c ++ `Normalized) do return none
      return some (← mkAppM (c ++ `Normalized) #[x])
    let some fact := fact? | continue
    let x := fact.appArg!
    let noFact ← g.withContext do mkAppM ``WrapNoFact #[x]
    if (← g.withContext getLCtx).any (fun d => d.type == fact || d.type == noFact) then continue
    let proof? ← g.withContext do
      let m ← mkFreshExprSyntheticOpaqueMVar fact
      let s ← saveState
      tryCatchRuntimeEx
        (do
          withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 }) <| withCurrHeartbeats do
            setGoals [m.mvarId!]
            evalTactic (← `(tactic| wrap_side))
            unless (← getGoals).isEmpty do throwError "wrap_facts: left"
          return some m)
        (fun _ => do s.restore; return none)
    let some m := proof? |
      g ← (← g.assert `hnofact noFact (mkConst ``True.intro)).intro1P <&> (·.2)
    g ← (← g.assert `hfact fact m).intro1P <&> (·.2)
  setGoals (g :: rest)

open Lean Elab Tactic Meta in
/-- Close a bound `a < b` or `a ≤ b` with a hypothesis, comparing at the default transparency. A bound is small, so
this stays cheap, and it sees through a literal like `2 ^ 63` or a field of a record the code built. -/
elab "wrap_bound" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isAppOf ``LT.lt || tgt.isAppOf ``LE.le do throwError "wrap_bound: not a bound"
  withTransparency .default (evalTactic (← `(tactic| assumption)))

open Lean Elab Tactic Meta in
/-- Close a path whose step `f … = .error .wrap` failed, with the lemma `f_ne_wrap` and `wrap_side` for its side
conditions, or else with `wrap_inline`. -/
elab "wrap_leaf" : tactic => do
  let g ← getMainGoal
  let rest := (← getGoals).erase g
  g.withContext do
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless rhs.isAppOfArity ``Except.error 3 do continue
      let some f := (if lhs.isAppOf ``ExceptT.run then lhs.appArg! else lhs).getAppFn.constName? | continue
      -- a private function's lemma may be private to the current file
      let user := ((privateToUserName? f).getD f).appendAfter "_ne_wrap"
      let some lem := [f.appendAfter "_ne_wrap", user, mkPrivateName (← getEnv) user].find? (← getEnv).contains
        | continue
      let s ← saveState
      try
        let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[lhs, rhs])
        setGoals [m.mvarId!]
        withTransparency .default (evalTactic (← `(tactic| apply $(mkIdent lem))))
        evalTactic (← `(tactic| all_goals wrap_side))
        unless (← getGoals).isEmpty do throwError "wrap_leaf: side conditions left"
        g.assign (← mkAppOptM ``absurd #[none, some (← g.getType), some (mkFVar ldecl.fvarId), some m])
        setGoals rest
        return
      catch _ =>
        s.restore
    evalTactic (← `(tactic| wrap_inline))

/-- Split every `match` and `if` of a `_ ≠ .error .wrap` goal and close each branch with the lemmas for the
calls it makes. `wrap_side` proves the side conditions of the lemmas. -/
macro "split_ne_wrap" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (repeat' (first | split | extract_lets)
             all_goals (try (intro hc; cases hc))
             all_goals first
               | (simp (disch := with_default_transparency wrap_side) only [$args,*, ne_eq, not_false_eq_true]; done)
               | (simp (disch := with_default_transparency wrap_side) only [$args,*] at *; done)
               | simp (disch := with_default_transparency wrap_side) [$args,*] at *))

/-- Close a branch whose hypothesis says an operation wrapped, with the lemmas for the operations it may name. -/
macro "close_wrap" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (simp (disch := with_default_transparency wrap_side) only [$args,*] at *; done)
    | (simp (disch := with_default_transparency wrap_side) [$args,*] at *; done))

/-- A checked add whose exact sum fits never wraps. -/
lemma _root_.UInt32.addChecked_ne_wrap {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) :
    a.addChecked b ≠ .error .wrap := by
  rw [UInt32.addChecked_of_lt h]; exact nofun

/-- A checked subtraction of a smaller value never wraps. -/
lemma _root_.UInt32.subChecked_ne_wrap {a b : UInt32} (h : b ≤ a) : a.subChecked b ≠ .error .wrap := by
  rw [UInt32.subChecked_of_le h]; exact nofun

/-- A checked conversion of a count below `2^63` never wraps. -/
lemma _root_.Nat.toInt64Checked_ne_wrap {n : Nat} (h : n < 2 ^ 63) : n.toInt64Checked ≠ .error .wrap := by
  rw [Nat.toInt64Checked_of_lt h]; exact nofun

/-! ## Number -/

lemma Number.normalize_ne_wrap (n : Number) {minM : UInt64} (maxM : UInt64) (mode : rounding_mode)
    (hmin : minM.toNat ≤ 10 ^ 18) : n.normalize minM maxM mode ≠ .error .wrap :=
  doNormalize_ne_wrap _ _ _ _ _ hmin

lemma Number.normalized_ne_wrap (negative : Bool) (mantissa : UInt64) (exponent : Int) {minM : UInt64}
    (maxM : UInt64) (mode : rounding_mode) (hmin : minM.toNat ≤ 10 ^ 18) :
    Number.normalized negative mantissa exponent minM maxM mode ≠ .error .wrap :=
  Number.normalize_ne_wrap _ _ _ hmin

lemma Number.from_rep_ne_wrap (mantissa : Int64) (exponent : Int) {minM : UInt64} (maxM : UInt64)
    (mode : rounding_mode) (hmin : minM.toNat ≤ 10 ^ 18) :
    Number.from_rep mantissa exponent minM maxM mode ≠ .error .wrap :=
  Number.normalized_ne_wrap _ _ _ _ _ hmin

/-- `normalizeToRange` signs a mantissa of at most `maxMantissa`, which fits an `Int64` for the 16-digit range. -/
lemma Number.normalizeToRange_ne_wrap (n : Number) (mode : rounding_mode) :
    n.normalizeToRange cMinValue cMaxValue mode ≠ .error .wrap := by
  unfold Number.normalizeToRange
  split
  · rename_i e he
    intro h; cases h
    exact doNormalize_ne_wrap _ _ _ _ _ cMinValue_toNat_le he
  · rename_i res hres
    have hle := doNormalize_mantissa_le (by decide) (by decide) (by decide) hres
    have hfit : res.mantissa_.toNat < 2 ^ 63 := by
      have : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
      omega
    rw [UInt64.toInt64Checked_of_lt hfit, ok_bind]
    have hnn : 0 ≤ res.mantissa_.toInt64.toInt := by
      rw [UInt64.toInt64_toInt_of_lt _ hfit]; positivity
    refine bind_ne_error ?_ fun _ => nofun
    split
    · rw [Int64.negChecked_of_ne (fun h => absurd hnn (by rw [h]; decide))]; exact nofun
    · exact nofun

lemma Number.truncate_ne_wrap (n : Number) : n.truncate ≠ .error .wrap := by
  unfold Number.truncate
  split
  · exact nofun
  · exact Number.normalized_ne_wrap _ _ _ _ _ largeRange_min_toNat_le

/-- `operator_mul` never wraps: the product of two 64-bit mantissas fits 128 bits. -/
lemma Number.operator_mul_ne_wrap (x y : Number) (mode : rounding_mode) :
    x.operator_mul y mode ≠ .error .wrap := by
  rw [Number.operator_mul_eq_spec]
  unfold Number.operator_mulSpec
  split
  · exact nofun
  split
  · exact nofun
  dsimp only
  split
  · rename_i err herr
    intro h; cases h
    exact Guard.doRoundUp_ne_wrap _ _ _ _ _ _ largeRange_min_toNat_le (by decide) herr
  · exact Number.normalize_ne_wrap _ _ _ largeRange_min_toNat_le

/-- The division quotient never wraps for a 19-digit divisor: the quotient stays below `2^61`. -/
lemma divQuotient128_ne_wrap (xm ym : UInt64) (xe ye : Int) (hym : 10 ^ 18 ≤ ym.toNat) :
    divQuotient128 xm ym xe ye ≠ .error .wrap := by
  have hx := xm.toNat_lt
  have hf : (100000000000000000 : UInt128).toNat = 10 ^ 17 := by decide
  have hc : (100000 : UInt128).toNat = 10 ^ 5 := by decide
  have hy := toNat_toUInt128 ym
  have hnum : (toUInt128 xm).toNat * (100000000000000000 : UInt128).toNat < 2 ^ 128 := by
    rw [toNat_toUInt128, hf]; omega
  have hnv : (toUInt128 xm * (100000000000000000 : UInt128)).toNat = xm.toNat * 10 ^ 17 := by
    rw [BitVec.toNat_mul_of_lt hnum, toNat_toUInt128, hf]
  intro h
  unfold divQuotient128 at h
  dsimp only at h
  rw [BitVec.mulChecked_of_lt hnum, ok_bind] at h
  by_cases hr : (toUInt128 xm * 100000000000000000 % toUInt128 ym != 0) = true
  · rw [if_pos hr] at h
    have hrem : (toUInt128 xm * 100000000000000000 % toUInt128 ym).toNat < ym.toNat := by
      rw [BitVec.toNat_umod, hy]; exact Nat.mod_lt _ (by omega)
    have hpn : (toUInt128 xm * 100000000000000000 % toUInt128 ym).toNat * (100000 : UInt128).toNat
        < 2 ^ 128 := by rw [hc]; have := ym.toNat_lt; omega
    rw [BitVec.mulChecked_of_lt hpn, ok_bind] at h
    by_cases hcr : ((toUInt128 xm * 100000000000000000 % toUInt128 ym * 100000) / toUInt128 ym != 0) = true
    · rw [if_pos hcr] at h
      have hq : (toUInt128 xm * 100000000000000000 / toUInt128 ym).toNat < 2 ^ 61 := by
        rw [BitVec.toNat_udiv, hnv, hy]
        calc xm.toNat * 10 ^ 17 / ym.toNat ≤ xm.toNat * 10 ^ 17 / 10 ^ 18 := Nat.div_le_div_left hym (by norm_num)
          _ < 2 ^ 61 := by omega
      have hzm : (toUInt128 xm * 100000000000000000 / toUInt128 ym).toNat * (100000 : UInt128).toNat
          < 2 ^ 128 := by rw [hc]; omega
      rw [BitVec.mulChecked_of_lt hzm, ok_bind] at h
      have hcorr : ((toUInt128 xm * 100000000000000000 % toUInt128 ym * 100000) / toUInt128 ym).toNat
          < 2 ^ 17 := by
        rw [BitVec.toNat_udiv, BitVec.toNat_mul_of_lt hpn, hc, hy]
        apply Nat.div_lt_of_lt_mul
        calc (toUInt128 xm * 100000000000000000 % toUInt128 ym).toNat * 10 ^ 5 < ym.toNat * 10 ^ 5 :=
              Nat.mul_lt_mul_of_pos_right hrem (by norm_num)
          _ ≤ ym.toNat * 2 ^ 17 := Nat.mul_le_mul_left _ (by norm_num)
      have hsum : (toUInt128 xm * 100000000000000000 / toUInt128 ym * 100000).toNat
          + ((toUInt128 xm * 100000000000000000 % toUInt128 ym * 100000) / toUInt128 ym).toNat < 2 ^ 128 := by
        rw [BitVec.toNat_mul_of_lt hzm, hc]; omega
      rw [BitVec.addChecked_of_lt hsum, ok_bind] at h
      cases h
    · rw [if_neg hcr] at h; cases h
  · rw [if_neg hr] at h; cases h

/-- `operator_div` never wraps on a normalized divisor. -/
lemma Number.operator_div_ne_wrap (x y : Number) (mode : rounding_mode) (hy : y.isNormalized) :
    x.operator_div y mode ≠ .error .wrap := by
  unfold Number.operator_div
  split
  · exact nofun
  rename_i hy0
  split
  · exact nofun
  have hym : 10 ^ 18 ≤ y.mantissa_.toNat := by
    rcases hy with hz | hb
    · exact absurd (by rw [hz]; decide) hy0
    · exact (mantissaBounds_nat_of ⟨hb.1, hb.2.1⟩).1
  intro h
  rcases hq : divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_ with e | ⟨zm, ze, d⟩
  · rw [hq, err_bind] at h; cases h; exact divQuotient128_ne_wrap _ _ _ _ hym hq
  · rw [hq, ok_bind] at h; exact doNormalize128_ne_wrap _ _ _ _ _ _ largeRange_min_toNat_le h

lemma Number.operator_sub_ne_wrap (x y : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) : x.operator_sub y mode ≠ .error .wrap :=
  Number.operator_add_ne_wrap _ _ _ hx (Number.operator_neg_isNormalized y hy)

lemma Number.power_ne_wrap (base : Number) (n : Nat) : base.power n ≠ .error .wrap := by
  fun_induction Number.power base n with
  | case1 => exact nofun
  | case2 => exact nofun
  | case3 k ih =>
    refine bind_ne_error ih fun half => bind_ne_error (Number.operator_mul_ne_wrap _ _ _) fun sq => ?_
    split
    · exact Number.operator_mul_ne_wrap _ _ _
    · exact nofun

lemma growSpec_ne_wrap (drops : rep) (offset : Int) : growSpec drops offset ≠ .error .wrap := by
  fun_induction growSpec drops offset <;> simp_all

/-- `to_rep` never wraps: it gives the result of its raw twin, which fails only on an overflow. -/
lemma Number.to_rep_ne_wrap (n : Number) (mode : rounding_mode) : n.to_rep mode ≠ .error .wrap := by
  rw [Number.to_rep_eq_spec]
  unfold Number.to_repSpec
  dsimp only
  have hgrow : ∀ (c : Prop) [Decidable c] (drops : rep) (offset : Int),
      (if c then growSpec drops offset else .ok drops) ≠ .error .wrap := by
    intro c _ drops offset; split
    · exact growSpec_ne_wrap _ _
    · exact nofun
  split_ne_wrap [hgrow]

/-! ## IntAmount and IOUAmount -/

lemma IntAmount.ofNumber_ne_wrap (n : Number) (mode : rounding_mode) : IntAmount.ofNumber n mode ≠ .error .wrap := by
  unfold IntAmount.ofNumber
  split_ne_wrap [Number.to_rep_ne_wrap]

lemma IntAmount.toNumber_ne_wrap (a : IntAmount) (mode : rounding_mode) : a.toNumber mode ≠ .error .wrap :=
  Number.from_rep_ne_wrap _ _ _ _ largeRange_min_toNat_le

lemma IOUAmount.fromNumber_ne_wrap (n : Number) (mode : rounding_mode) :
    IOUAmount.fromNumber n mode ≠ .error .wrap := by
  unfold IOUAmount.fromNumber
  split
  · rename_i e he; intro h; cases h; exact Number.normalizeToRange_ne_wrap _ _ he
  · exact nofun

lemma IOUAmount.normalize_ne_wrap (a : IOUAmount) (mode : rounding_mode) : a.normalize mode ≠ .error .wrap := by
  unfold IOUAmount.normalize
  split_ne_wrap [Number.from_rep_ne_wrap _ _ _ _ largeRange_min_toNat_le, IOUAmount.fromNumber_ne_wrap]

lemma IOUAmount.ofMantissaExp_ne_wrap (m : Int64) (e : Int) (mode : rounding_mode) :
    IOUAmount.ofMantissaExp m e mode ≠ .error .wrap :=
  IOUAmount.normalize_ne_wrap _ _

lemma IOUAmount.ofNumber_ne_wrap (n : Number) (mode : rounding_mode) : IOUAmount.ofNumber n mode ≠ .error .wrap := by
  unfold IOUAmount.ofNumber
  split_ne_wrap [IOUAmount.fromNumber_ne_wrap]

lemma IOUAmount.toNumber_ne_wrap (a : IOUAmount) (mode : rounding_mode) : a.toNumber mode ≠ .error .wrap :=
  Number.from_rep_ne_wrap _ _ _ _ largeRange_min_toNat_le

/-- `IOUAmount.operator_add` never wraps: it adds the normalized Numbers of its operands. -/
lemma IOUAmount.operator_add_ne_wrap (x y : IOUAmount) (mode : rounding_mode) :
    x.operator_add y mode ≠ .error .wrap := by
  unfold IOUAmount.operator_add
  split
  · exact nofun
  split
  · exact nofun
  intro h
  split at h
  · rename_i e he; cases h; exact IOUAmount.toNumber_ne_wrap _ _ he
  rename_i xn hxn
  split at h
  · rename_i e he; cases h; exact IOUAmount.toNumber_ne_wrap _ _ he
  rename_i yn hyn
  split at h
  · rename_i e he; cases h
    exact Number.operator_add_ne_wrap _ _ _ (Number.from_rep_isNormalized _ _ _ _ hxn)
      (Number.from_rep_isNormalized _ _ _ _ hyn) he
  · exact IOUAmount.ofNumber_ne_wrap _ _ h

/-- `doRoundUpSpec` keeps a cleared sign. -/
lemma doRoundUpSpec_negative_false {g : Guard} {m : UInt64} {e : Int} {minM maxM : UInt64} {mode : rounding_mode}
    {loc : Error} {r : RoundResult} (h : g.doRoundUpSpec false m e minM maxM mode loc = .ok r) :
    r.negative_ = false := by
  unfold Guard.doRoundUpSpec at h
  dsimp only [Guard.doDropDigit] at h
  have key : ∀ x : RoundResult,
      (if x.exponent_ > maxExponent then (.error loc : Except Error RoundResult) else .ok x) = .ok r → r = x := by
    intro x hx
    split at hx
    · cases hx
    · cases hx; rfl
  obtain rfl := key _ h
  split_ifs <;> (unfold Guard.bringIntoRangeSpec; dsimp only; split_ifs <;> rfl)

/-- `doNormalize` keeps a cleared sign. -/
lemma doNormalize_negative_false {m : UInt64} {e : Int} {minM maxM : UInt64} {mode : rounding_mode} {r : Number}
    (h : doNormalize false m e minM maxM mode = .ok r) : r.negative_ = false := by
  replace h := doNormalize_ok_spec h
  unfold doNormalizeSpec at h
  split at h
  · cases h; rfl
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h; rfl
  split at h
  · cases h
  split at h
  · cases h
  rename_i res hres
  cases h
  exact doRoundUpSpec_negative_false (Guard.doRoundUp_ok_spec hres)

/-- `normalizeToRange` of a value with a cleared sign gives a mantissa in `[0, 2^63)`. -/
lemma Number.normalizeToRange_nonneg {n : Number} {minM maxM : UInt64} {mode : rounding_mode} {m : Int64} {e : Int}
    (hneg : n.negative_ = false) (h : n.normalizeToRange minM maxM mode = .ok (m, e)) :
    0 ≤ m.toInt ∧ m.toInt < 2 ^ 63 := by
  unfold Number.normalizeToRange at h
  split at h
  · cases h
  rename_i res hres
  rw [hneg] at hres
  have hsign := doNormalize_negative_false hres
  obtain ⟨mant, hmant, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨hfit, rfl⟩ := UInt64.toInt64Checked_eq_ok.mp hmant
  rw [hsign] at h
  simp only [Bool.false_eq_true, if_false, pure_eq, ok_bind] at h
  cases h
  rw [UInt64.toInt64_toInt_of_lt _ hfit]
  omega

/-- The signed value of the amount fits an `Int64`. -/
def STAmount.Fits (s : STAmount) : Prop := -2 ^ 63 ≤ s.signedDrops ∧ s.signedDrops < 2 ^ 63

lemma STAmount.Fits.of_lt {s : STAmount} (h : s.mValue.toNat < 2 ^ 63) : s.Fits := by
  unfold STAmount.Fits STAmount.signedDrops; split <;> omega

/-- An amount that stores the magnitude and sign of an `Int64` fits. -/
lemma STAmount.Fits.of_magnitude {s : STAmount} (v : Int64) (hv : s.mValue = v.magnitude)
    (hneg : s.mIsNegative = decide (v < 0)) : s.Fits := by
  have h1 := v.le_toInt
  have h2 := v.toInt_lt
  unfold STAmount.Fits STAmount.signedDrops
  rw [hv, hneg, Int64.toNat_magnitude]
  by_cases h : v < 0
  · have hlt : v.toInt < 0 := by simpa using Int64.lt_iff_toInt_lt.mp h
    simp only [h, decide_true, if_true]
    omega
  · have hge : 0 ≤ v.toInt := by
      by_contra hc; exact h (Int64.lt_iff_toInt_lt.mpr (by simpa using not_le.mp hc))
    simp only [h, decide_false, Bool.false_eq_true, if_false]
    omega

/-- A negated amount fits when its magnitude does. -/
lemma STAmount.Fits.neg_of_lt {s : STAmount} (h : s.mValue.toNat < 2 ^ 63) : s.operator_neg.Fits := by
  apply STAmount.Fits.of_lt
  unfold STAmount.operator_neg
  split
  · exact h
  · exact h

/-- `normalizeToRange` signs a mantissa that fit the checked `Int64` conversion. -/
lemma Number.normalizeToRange_natAbs_lt {n : Number} {minM maxM : UInt64} {mode : rounding_mode} {m : Int64}
    {e : Int} (h : n.normalizeToRange minM maxM mode = .ok (m, e)) : m.toInt.natAbs < 2 ^ 63 := by
  unfold Number.normalizeToRange at h
  split at h
  · cases h
  obtain ⟨mant, hmant, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨hfit, rfl⟩ := UInt64.toInt64Checked_eq_ok.mp hmant
  have hv := UInt64.toInt64_toInt_of_lt _ hfit
  obtain ⟨sm, hsm, h⟩ := bind_ok_peel _ _ _ h
  cases h
  split at hsm
  · obtain ⟨-, rfl⟩ := Int64.negChecked_eq_ok.mp hsm
    rw [toInt_neg_of_nonneg _ (by rw [hv]; positivity), hv]
    omega
  · cases hsm; rw [hv]; omega

/-- A normalized `IOUAmount` has a mantissa below `2^63` in magnitude. -/
lemma IOUAmount.normalize_natAbs_lt {a i : IOUAmount} {mode : rounding_mode} (h : a.normalize mode = .ok i) :
    i.mantissa_.toInt.natAbs < 2 ^ 63 := by
  unfold IOUAmount.normalize at h
  split at h
  · cases h; decide
  split at h
  · cases h
  split at h
  · cases h
  rename_i r hr
  unfold IOUAmount.fromNumber at hr
  split at hr
  · cases hr
  rename_i m e hm
  cases hr
  split at h
  · cases h
  split at h
  · cases h; decide
  · cases h; exact Number.normalizeToRange_natAbs_lt hm

/-- A fractional `canonicalize` result has a magnitude below `2^63`. -/
lemma STAmount.canonicalize_fractional_mValue_lt {s r : STAmount} {mode : rounding_mode}
    (hint : ¬ s.integral = true) (h : s.canonicalize mode = .ok r) : r.mValue.toNat < 2 ^ 63 := by
  unfold STAmount.canonicalize at h
  rw [if_neg hint] at h
  split at h
  · cases h
  rename_i i hi
  cases h
  have hb := IOUAmount.normalize_natAbs_lt (STAmount.iou_ok_peel hint hi)
  show i.mantissa_.magnitude.toNat < 2 ^ 63
  rw [Int64.toNat_magnitude]
  exact hb

/-- An amount made from an `Int64` fits. -/
lemma STAmount.uncheckedFromInt64_fits (nt : NumericType) (v : Int64) (o : Int) :
    (STAmount.uncheckedFromInt64 nt v o).Fits := by
  refine STAmount.Fits.of_magnitude v (by unfold STAmount.uncheckedFromInt64; split <;> rfl) ?_
  unfold STAmount.uncheckedFromInt64
  split
  · rename_i h; simp [STAmount.unchecked, h]
  · rename_i h; simp [STAmount.unchecked, h]

lemma STAmount.intAmount_ne_wrap (s : STAmount) (h : s.Fits) : s.intAmount ≠ .error .wrap := by
  unfold STAmount.intAmount
  split
  · rw [Int.toInt64Checked_of_bounds h.1 h.2, ok_bind]; exact nofun
  · exact nofun

lemma STAmount.iou_ne_wrap (s : STAmount) (mode : rounding_mode) (h : s.Fits) : s.iou mode ≠ .error .wrap := by
  unfold STAmount.iou
  split
  · exact nofun
  · rw [Int.toInt64Checked_of_bounds h.1 h.2, ok_bind]; exact IOUAmount.ofMantissaExp_ne_wrap _ _ _

lemma STAmount.toNumber_ne_wrap (s : STAmount) (mode : rounding_mode) (h : s.Fits) :
    s.toNumber mode ≠ .error .wrap := by
  unfold STAmount.toNumber
  split_ne_wrap [STAmount.intAmount_ne_wrap _ h, IntAmount.toNumber_ne_wrap, STAmount.iou_ne_wrap _ _ h,
    IOUAmount.toNumber_ne_wrap]

lemma STAmount.canonicalize_ne_wrap (s : STAmount) (mode : rounding_mode) (h : s.Fits) :
    s.canonicalize mode ≠ .error .wrap := by
  unfold STAmount.canonicalize
  split_ne_wrap [IntAmount.ofNumber_ne_wrap, STAmount.iou_ne_wrap _ _ h]

/-- `canonicalize` stores the magnitude and sign of an `Int64`, so its result fits. -/
lemma STAmount.canonicalize_fits {s r : STAmount} {mode : rounding_mode} (h : s.canonicalize mode = .ok r) :
    r.Fits := by
  unfold STAmount.canonicalize at h
  split at h
  · split at h
    · cases h; exact STAmount.Fits.of_lt (by simp)
    split at h
    · cases h
    dsimp only at h
    split at h
    · cases h
    rename_i i hi
    split at h
    · cases h
    · cases h; exact STAmount.Fits.of_magnitude i.value rfl rfl
  · split at h
    · cases h
    rename_i i hi
    cases h
    exact STAmount.Fits.of_magnitude i.mantissa_ rfl (by simp [IOUAmount.signum_neg_iff])

lemma STAmount.checked_ne_wrap (nt : NumericType) (mValue : UInt64) (mOffset : Int) (mIsNegative : Bool)
    (mode : rounding_mode) (h : (STAmount.unchecked nt mValue mOffset mIsNegative).Fits) :
    STAmount.checked nt mValue mOffset mIsNegative mode ≠ .error .wrap :=
  STAmount.canonicalize_ne_wrap _ _ h

lemma STAmount.ofIOUAmount_ne_wrap (a : IOUAmount) (mode : rounding_mode) :
    STAmount.ofIOUAmount a mode ≠ .error .wrap :=
  STAmount.canonicalize_ne_wrap _ _
    (STAmount.Fits.of_magnitude a.mantissa_ rfl (by simp [STAmount.unchecked, IOUAmount.signum_neg_iff]))

/-- `ofNumber` never wraps: it converts the sign-cleared value, whose integer or 16-digit mantissa fits. -/
lemma STAmount.ofNumber_ne_wrap (nt : NumericType) (n : Number) (mode : rounding_mode) :
    STAmount.ofNumber nt n mode ≠ .error .wrap := by
  unfold STAmount.ofNumber
  have hw : (if decide (n.signum < 0) = true then n.operator_neg else n).negative_ = false := by
    rw [Number.signum_neg_decide]
    by_cases hn : n.negative_
    · rw [if_pos hn]
      unfold Number.operator_neg
      split
      · rfl
      · simp [hn]
    · rw [if_neg hn]; simpa using hn
  dsimp only
  split
  · split
    · rename_i e he; intro h; cases h; exact Number.to_rep_ne_wrap _ _ he
    · rename_i r hr
      obtain ⟨h0, hle⟩ := Number.to_rep_nonneg_range _ _ r hw hr
      rw [Int64.toUInt64Checked_of_nonneg (Int64.le_iff_toInt_le.mpr (by simpa using h0)), ok_bind]
      refine STAmount.checked_ne_wrap _ _ _ _ _ (STAmount.Fits.of_lt ?_)
      have := toUInt64_toNat_of_nonneg r h0
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      show r.toUInt64.toNat < 2 ^ 63
      omega
  · split
    · rename_i e he; intro h; cases h; exact Number.normalizeToRange_ne_wrap _ _ he
    · rename_i m ex hm
      obtain ⟨h0, hlt⟩ := Number.normalizeToRange_nonneg hw hm
      rw [Int64.toUInt64Checked_of_nonneg (Int64.le_iff_toInt_le.mpr (by simpa using h0)), ok_bind]
      refine STAmount.checked_ne_wrap _ _ _ _ _ (STAmount.Fits.of_lt ?_)
      have := toUInt64_toNat_of_nonneg m h0
      show m.toUInt64.toNat < 2 ^ 63
      omega

/-- An `ofNumber` result is canonicalized, so it fits. -/
lemma STAmount.ofNumber_fits {nt : NumericType} {n : Number} {mode : rounding_mode} {r : STAmount}
    (h : STAmount.ofNumber nt n mode = .ok r) : r.Fits := by
  unfold STAmount.ofNumber at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, _, h⟩ := bind_ok_peel _ _ _ h
      exact STAmount.canonicalize_fits h
  · split at h
    · cases h
    · obtain ⟨_, _, h⟩ := bind_ok_peel _ _ _ h
      exact STAmount.canonicalize_fits h

lemma STAmount.operator_lt_ne_wrap (lhs rhs : STAmount) : lhs.operator_lt rhs ≠ .error .wrap := by
  unfold STAmount.operator_lt
  split_ne_wrap []

lemma STAmount.operator_le_ne_wrap (lhs rhs : STAmount) : lhs.operator_le rhs ≠ .error .wrap := by
  unfold STAmount.operator_le
  split_ne_wrap [STAmount.operator_lt_ne_wrap]

/-- `operator_add` never wraps on amounts that fit, unless two integral amounts sum past an `Int64`. -/
lemma STAmount.operator_add_ne_wrap (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.Fits) (h2 : v2.Fits)
    (hsum : v1.integral = true →
      -2 ^ 63 ≤ v1.signedDrops + v2.signedDrops ∧ v1.signedDrops + v2.signedDrops < 2 ^ 63) :
    v1.operator_add v2 mode ≠ .error .wrap := by
  unfold STAmount.operator_add
  split
  · exact nofun
  split
  · exact nofun
  split
  · exact STAmount.checked_ne_wrap _ _ _ _ _ h2
  split
  · rename_i hint
    obtain ⟨hs1, hs2⟩ := hsum hint
    have hd1 : (v1.signedDrops.toInt64).toInt = v1.signedDrops :=
      Int64.toInt_ofInt_of_le (by have := h1.1; omega) (by have := h1.2; omega)
    have hd2 : (v2.signedDrops.toInt64).toInt = v2.signedDrops :=
      Int64.toInt_ofInt_of_le (by have := h2.1; omega) (by have := h2.2; omega)
    rw [Int.toInt64Checked_of_bounds h1.1 h1.2, ok_bind, Int.toInt64Checked_of_bounds h2.1 h2.2, ok_bind,
      Int64.addChecked_of_bounds (by rw [hd1, hd2]; exact hs1) (by rw [hd1, hd2]; exact hs2), ok_bind]
    dsimp only
    split
    · exact nofun
    · exact STAmount.canonicalize_ne_wrap _ _ (STAmount.uncheckedFromInt64_fits _ _ _)
  · intro h
    split at h
    · rename_i e he; cases h; exact STAmount.iou_ne_wrap _ _ h1 he
    split at h
    · rename_i e he; cases h; exact STAmount.iou_ne_wrap _ _ h2 he
    split at h
    · rename_i e he; cases h; exact IOUAmount.operator_add_ne_wrap _ _ _ he
    · exact STAmount.ofIOUAmount_ne_wrap _ _ h

/-- Adding to a fractional amount gives a fractional amount. -/
lemma STAmount.operator_add_fractional {v1 v2 r : STAmount} {mode : rounding_mode} (h1 : v1.integral = false)
    (h : v1.operator_add v2 mode = .ok r) : ¬ r.integral = true := by
  unfold STAmount.operator_add at h
  split at h
  · cases h
  split at h
  · cases h; simpa using h1
  split at h
  · have := STAmount.canonicalize_mNumericType _ _ _ h
    unfold STAmount.integral at h1 ⊢
    rw [this]; simpa using h1
  split at h
  · rename_i hi; exact absurd hi (by simpa using h1)
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    · have := STAmount.canonicalize_mNumericType _ _ _ h
      unfold STAmount.integral
      rw [this]; simp [STAmount.unchecked, NumericType.isIntegral]

/-- An `operator_add` result fits when its operands fit. -/
lemma STAmount.operator_add_fits {v1 v2 r : STAmount} {mode : rounding_mode} (h1 : v1.Fits)
    (h : v1.operator_add v2 mode = .ok r) : r.Fits := by
  unfold STAmount.operator_add at h
  split at h
  · cases h
  split at h
  · cases h; exact h1
  split at h
  · exact STAmount.canonicalize_fits h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, _, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨t, _, h⟩ := bind_ok_peel _ _ _ h
    dsimp only at h
    split at h
    · cases h
      exact STAmount.uncheckedFromInt64_fits _ _ _
    · exact STAmount.canonicalize_fits h
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    · exact STAmount.canonicalize_fits h

lemma STAmount.operator_sub_ne_wrap (v1 v2 : STAmount) (mode : rounding_mode) (h1 : v1.Fits)
    (h2 : v2.mValue.toNat < 2 ^ 63)
    (hsum : v1.integral = true →
      -2 ^ 63 ≤ v1.signedDrops + v2.operator_neg.signedDrops ∧ v1.signedDrops + v2.operator_neg.signedDrops < 2 ^ 63) :
    v1.operator_sub v2 mode ≠ .error .wrap :=
  STAmount.operator_add_ne_wrap _ _ _ h1 (STAmount.Fits.neg_of_lt h2) hsum

/-- `roundToExponent` never wraps on a fractional amount that fits, and leaves an integral one alone. -/
lemma STAmount.roundToExponent_ne_wrap (value : STAmount) (exponent : Int) (rounding : rounding_mode)
    (h : value.Fits) : value.roundToExponent exponent rounding ≠ .error .wrap := by
  unfold STAmount.roundToExponent
  split
  · exact nofun
  rename_i hint
  split
  · exact nofun
  split
  · exact nofun
  have hrefF : ∀ r : STAmount, STAmount.checked value.mNumericType kMinValue exponent value.negative rounding = .ok r →
      r.Fits := fun r hr => STAmount.canonicalize_fits hr
  split
  · rename_i e he; intro hh; cases hh
    exact STAmount.checked_ne_wrap _ _ _ _ _ (STAmount.Fits.of_lt (show kMinValue.toNat < 2 ^ 63 by decide)) he
  rename_i ref href
  split
  · rename_i e he; intro hh; cases hh
    exact STAmount.operator_add_ne_wrap _ _ _ h (hrefF _ href) (fun hi => absurd hi hint) he
  rename_i sum hsum
  have hfr : ¬ (STAmount.unchecked value.mNumericType kMinValue exponent value.negative).integral = true := hint
  refine STAmount.operator_sub_ne_wrap _ _ _ (STAmount.operator_add_fits h hsum)
    (STAmount.canonicalize_fractional_mValue_lt hfr href) ?_
  intro hi
  exact absurd hi (STAmount.operator_add_fractional (by simpa using hint) hsum)

/-- A `roundToExponent` result fits when its amount does. -/
lemma STAmount.roundToExponent_fits {value r : STAmount} {exponent : Int} {rounding : rounding_mode}
    (h : value.Fits) (hr : value.roundToExponent exponent rounding = .ok r) : r.Fits := by
  unfold STAmount.roundToExponent at hr
  split at hr
  · cases hr; exact h
  split at hr
  · cases hr; exact h
  split at hr
  · cases hr; exact h
  split at hr
  · cases hr
  split at hr
  · cases hr
  rename_i sum hsum
  exact STAmount.operator_add_fits (STAmount.operator_add_fits h hsum) hr

/-- `roundToNumericType` never wraps: it rounds through amounts that `ofNumber` makes, which fit. -/
lemma STAmount.roundToNumericType_ne_wrap (nt : NumericType) (value : Number) (rounding : rounding_mode)
    (scale : Option Int) : STAmount.roundToNumericType nt value rounding scale ≠ .error .wrap := by
  unfold STAmount.roundToNumericType
  split
  · rename_i e he; intro h; cases h; exact STAmount.ofNumber_ne_wrap _ _ _ he
  rename_i ret hret
  have hf := STAmount.ofNumber_fits hret
  split
  · exact STAmount.toNumber_ne_wrap _ _ hf
  · split
    · exact STAmount.toNumber_ne_wrap _ _ hf
    · intro h
      split at h
      · rename_i e he; cases h; exact STAmount.roundToExponent_ne_wrap _ _ _ hf he
      · rename_i rounded hr; exact STAmount.toNumber_ne_wrap _ _ (STAmount.roundToExponent_fits hf hr) h

lemma Number.isOnExponentGrid_ne_wrap (value : Number) (exponent : Int) (nt : NumericType) :
    value.isOnExponentGrid exponent nt ≠ .error .wrap := by
  unfold Number.isOnExponentGrid
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [STAmount.roundToNumericType_ne_wrap]

lemma STAmount.isFractionalNonPositive_ne_wrap (amount : STAmount) :
    amount.isFractionalNonPositive ≠ .error .wrap := by
  unfold STAmount.isFractionalNonPositive
  split_ne_wrap [STAmount.operator_le_ne_wrap]

lemma numberExponent_ne_wrap (amount : Number) (exponent : Int) (nt : NumericType) :
    numberExponent amount exponent nt ≠ .error .wrap := by
  unfold numberExponent
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [STAmount.ofNumber_ne_wrap]

lemma postSumExponent_ne_wrap (amount amountDelta : Number) (exponent : Int) (nt : NumericType)
    (ha : amount.isNormalized) (hd : amountDelta.isNormalized) :
    postSumExponent amount amountDelta exponent nt ≠ .error .wrap := by
  unfold postSumExponent
  exact bind_ne_error (Number.operator_add_ne_wrap _ _ _ ha hd) fun _ => numberExponent_ne_wrap _ _ _

/-- A block fails with `e` only when its first step or, after that step succeeded, the rest of it does. -/
private lemma bind_ne_error' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {e : ε} (hx : x ≠ .error e)
    (hf : ∀ a, x = .ok a → f a ≠ .error e) : (x >>= f) ≠ .error e := by
  cases x with
  | error e' => rw [err_bind]; intro h; exact hx (by cases h; rfl)
  | ok a => rw [ok_bind]; exact hf a rfl

lemma sumRoundAndSubtract_ne_wrap (amount amountDelta : Number) (exponent : Int) (nt : NumericType)
    (mode : rounding_mode) (ha : amount.isNormalized) (hd : amountDelta.isNormalized) :
    sumRoundAndSubtract amount amountDelta exponent nt mode ≠ .error .wrap := by
  unfold sumRoundAndSubtract
  dsimp only
  split
  · exact bind_ne_error (STAmount.ofNumber_ne_wrap _ _ _) fun _ => nofun
  rw [pure_eq, ok_bind]
  refine bind_ne_error (postSumExponent_ne_wrap _ _ _ _ ha hd) fun e => ?_
  refine bind_ne_error (Number.operator_add_ne_wrap _ _ _ ha hd) fun sum => ?_
  refine bind_ne_error' (STAmount.roundToNumericType_ne_wrap _ _ _ _) fun sum' hsum' => ?_
  exact bind_ne_error (Number.operator_sub_ne_wrap _ _ _
    (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hsum') ha) fun _ => STAmount.ofNumber_ne_wrap _ _ _

/-- `clampToSumExponent` never wraps for a normalized amount and a delta whose magnitude fits an `Int64`. -/
lemma clampToSumExponent_ne_wrap (amount : Number) (amountDelta : STAmount) (exponent : Int)
    (ha : amount.isNormalized) (hd : amountDelta.mValue.toNat < 2 ^ 63) :
    clampToSumExponent amount amountDelta exponent ≠ .error .wrap := by
  unfold clampToSumExponent
  dsimp only
  split
  · exact nofun
  rw [pure_eq, ok_bind]
  refine bind_ne_error' (STAmount.toNumber_ne_wrap _ _ (STAmount.Fits.of_lt hd)) fun n hn => ?_
  refine bind_ne_error (postSumExponent_ne_wrap _ _ _ _ ha (STAmount.toNumber_isNormalized _ _ _ hn)) fun _ => ?_
  apply STAmount.roundToExponent_ne_wrap
  split
  · exact STAmount.Fits.neg_of_lt hd
  · exact STAmount.Fits.of_lt hd

lemma tenthBipsOfValue_ne_wrap (value : Number) (bips : TenthBips32) (mode : rounding_mode) :
    tenthBipsOfValue value bips mode ≠ .error .wrap := by
  unfold tenthBipsOfValue
  exact bind_ne_error (Number.operator_mul_ne_wrap _ _ _) fun _ =>
    Number.operator_div_ne_wrap _ _ _ (Number.ofInt64_isNormalized _)

/-! ## The side conditions -/

lemma Number.normalized_isNormalized {negative : Bool} {mantissa : UInt64} {exponent : Int} {mode : rounding_mode}
    {r : Number} (h : Number.normalized negative mantissa exponent largeRange.min largeRange.max mode = .ok r) :
    r.isNormalized :=
  Number.normalize_isNormalized _ _ _ h

lemma Number.truncate_isNormalized {n r : Number} (hn : n.isNormalized) (h : n.truncate = .ok r) :
    r.isNormalized := by
  unfold Number.truncate at h
  split at h
  · cases h; exact hn
  · exact Number.normalized_isNormalized h

lemma tenthBipsOfValue_isNormalized {value r : Number} {bips : TenthBips32} {mode : rounding_mode}
    (hv : value.isNormalized) (h : tenthBipsOfValue value bips mode = .ok r) : r.isNormalized := by
  unfold tenthBipsOfValue at h
  obtain ⟨p, hp, h⟩ := bind_ok_peel _ _ _ h
  exact Number.operator_div_isNormalized _ _ _ _
    (Number.operator_mul_isNormalized _ _ _ _ hv (Number.ofInt64_isNormalized _) hp) (Number.ofInt64_isNormalized _) h

lemma STAmount.checked_fits {nt : NumericType} {mValue : UInt64} {mOffset : Int} {mIsNegative : Bool}
    {mode : rounding_mode} {r : STAmount} (h : STAmount.checked nt mValue mOffset mIsNegative mode = .ok r) :
    r.Fits :=
  STAmount.canonicalize_fits h

/-- An XRP or MPT amount is at most the largest value of its type, so a type whose largest value fits an `Int64`
keeps the magnitude below `2^63`. An IOU magnitude always is. -/
lemma STAmount.canonicalize_mValue_lt {s r : STAmount} {mode : rounding_mode}
    (hnt : s.mNumericType.maxValue.toNat < 2 ^ 63) (h : s.canonicalize mode = .ok r) : r.mValue.toNat < 2 ^ 63 := by
  by_cases hint : s.integral = true
  · unfold STAmount.canonicalize at h
    rw [if_pos hint] at h
    split at h
    · cases h; simp
    split at h
    · cases h
    dsimp only at h
    split at h
    · cases h
    split at h
    · cases h
    · rename_i hv
      cases h
      exact lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hv)) hnt
  · exact STAmount.canonicalize_fractional_mValue_lt hint h

lemma STAmount.ofNumber_mValue_lt {nt : NumericType} {n : Number} {mode : rounding_mode} {r : STAmount}
    (hnt : nt.maxValue.toNat < 2 ^ 63) (h : STAmount.ofNumber nt n mode = .ok r) : r.mValue.toNat < 2 ^ 63 := by
  unfold STAmount.ofNumber at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, _, h⟩ := bind_ok_peel _ _ _ h
      exact STAmount.canonicalize_mValue_lt hnt h
  · split at h
    · cases h
    · obtain ⟨_, _, h⟩ := bind_ok_peel _ _ _ h
      exact STAmount.canonicalize_mValue_lt hnt h

lemma STAmount.checked_mValue_lt {nt : NumericType} {mValue : UInt64} {mOffset : Int} {mIsNegative : Bool}
    {mode : rounding_mode} {r : STAmount} (hnt : nt.maxValue.toNat < 2 ^ 63)
    (h : STAmount.checked nt mValue mOffset mIsNegative mode = .ok r) : r.mValue.toNat < 2 ^ 63 :=
  STAmount.canonicalize_mValue_lt hnt h

lemma STAmount.operator_neg_mValue (s : STAmount) : s.operator_neg.mValue = s.mValue := by
  unfold STAmount.operator_neg
  split <;> rfl

lemma NumericType.int64_maxValue_lt : NumericType.int64.maxValue.toNat < 2 ^ 63 := by decide

/-- The zero amount of a type has a magnitude below `2^63`. -/
lemma STAmount.zero_mValue_lt (nt : NumericType) : (STAmount.zero nt).mValue.toNat < 2 ^ 63 := by
  unfold STAmount.zero
  split
  · rename_i s hs
    by_cases hint : (STAmount.unchecked nt 0 0 false).integral = true
    · unfold STAmount.checked STAmount.canonicalize at hs
      rw [if_pos hint, if_pos (by simp [STAmount.unchecked])] at hs
      cases hs
      simp
    · exact STAmount.canonicalize_fractional_mValue_lt hint hs
  · simp [STAmount.unchecked]

/-- An IOU sum whose first operand has a magnitude below `2^63` has a magnitude below `2^63`. -/
lemma STAmount.operator_add_fractional_mValue_lt {v1 v2 r : STAmount} {mode : rounding_mode}
    (hint : ¬ v1.integral = true) (h1 : v1.mValue.toNat < 2 ^ 63) (h : v1.operator_add v2 mode = .ok r) :
    r.mValue.toNat < 2 ^ 63 := by
  unfold STAmount.operator_add at h
  split at h
  · cases h
  split at h
  · cases h; exact h1
  split at h
  · exact STAmount.canonicalize_fractional_mValue_lt
      (s := STAmount.unchecked v1.mNumericType v2.mValue v2.mOffset v2.mIsNegative) hint h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · unfold STAmount.ofIOUAmount at h
    exact STAmount.canonicalize_fractional_mValue_lt
      (by simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]) h

lemma STAmount.roundToExponent_mValue_lt {value r : STAmount} {exponent : Int} {rounding : rounding_mode}
    (h : value.mValue.toNat < 2 ^ 63) (hr : value.roundToExponent exponent rounding = .ok r) :
    r.mValue.toNat < 2 ^ 63 := by
  unfold STAmount.roundToExponent at hr
  split at hr
  · cases hr; exact h
  rename_i hint
  split at hr
  · cases hr; exact h
  split at hr
  · cases hr; exact h
  split at hr
  · cases hr
  split at hr
  · cases hr
  rename_i sum hsum
  have hsint : ¬ sum.integral = true := STAmount.operator_add_fractional (by simpa using hint) hsum
  exact STAmount.operator_add_fractional_mValue_lt hsint (STAmount.operator_add_fractional_mValue_lt hint h hsum) hr

lemma clampToSumExponent_mValue_lt {amount : Number} {amountDelta r : STAmount} {exponent : Int}
    (hd : amountDelta.mValue.toNat < 2 ^ 63) (h : clampToSumExponent amount amountDelta exponent = .ok r) :
    r.mValue.toNat < 2 ^ 63 := by
  have habs : (if amountDelta.negative then amountDelta.operator_neg else amountDelta).mValue.toNat < 2 ^ 63 := by
    split <;> (try rw [STAmount.operator_neg_mValue]) <;> exact hd
  unfold clampToSumExponent at h
  dsimp only at h
  split at h
  · cases h; exact habs
  rw [pure_eq, ok_bind] at h
  obtain ⟨_, _, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, _, h⟩ := bind_ok_peel _ _ _ h
  exact STAmount.roundToExponent_mValue_lt habs h

lemma Number.min_isNormalized {x y : Number} (hx : x.isNormalized) (hy : y.isNormalized) :
    (Number.min x y).isNormalized := by
  unfold Number.min; split <;> assumption

lemma Number.max_isNormalized {x y : Number} (hx : x.isNormalized) (hy : y.isNormalized) :
    (Number.max x y).isNormalized := by
  unfold Number.max; split <;> assumption

lemma Number.clamp_isNormalized {v low high : Number} (hv : v.isNormalized) (hl : low.isNormalized)
    (hh : high.isNormalized) : (Number.clamp v low high).isNormalized := by
  unfold Number.clamp; split
  · exact hl
  · split <;> assumption

lemma Number.ite_isNormalized {c : Prop} [Decidable c] {x y : Number} (hx : x.isNormalized) (hy : y.isNormalized) :
    (if c then x else y).isNormalized := by
  split <;> assumption

macro_rules
  | `(tactic| wrap_rule) => `(tactic| first
    | wrap_bound
    | exact XRPL.Model.Protocol.Number.zero_isNormalized
    | exact XRPL.Model.Protocol.Number.ofInt64_isNormalized _
    | exact XRPL.Model.Protocol.STAmount.uncheckedFromInt64_fits _ _ _
    | exact XRPL.Model.Protocol.NumericType.int64_maxValue_lt
    | exact XRPL.Model.Protocol.largeRange_min_toNat_le
    | exact XRPL.Model.Protocol.STAmount.zero_mValue_lt _
    | (refine XRPL.Model.Protocol.STAmount.Fits.of_lt ?_; wrap_side)
    | (rw [XRPL.Model.Protocol.STAmount.operator_neg_mValue]; wrap_side)
    | (refine XRPL.Model.Protocol.Number.operator_neg_isNormalized _ ?_; wrap_side)
    | (refine XRPL.Model.Protocol.Number.min_isNormalized ?_ ?_ <;> wrap_side)
    | (refine XRPL.Model.Protocol.Number.max_isNormalized ?_ ?_ <;> wrap_side)
    | (refine XRPL.Model.Protocol.Number.clamp_isNormalized ?_ ?_ ?_ <;> wrap_side)
    | (refine XRPL.Model.Protocol.Number.ite_isNormalized ?_ ?_ <;> wrap_side)
    | wrap_mk
    | (dsimp only; wrap_side)
    | wrap_unfold
    | (split <;> wrap_side))

end XRPL.Model.Protocol
