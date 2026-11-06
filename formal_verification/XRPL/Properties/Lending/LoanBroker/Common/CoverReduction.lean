import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverClawback
import XRPL.Properties.Lending.Common.Reduction
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Vault.Proofs.Walk

/-! # Shared reductions for the cover operations

Steps shared by deposit, withdraw and clawback: what each check and operation computes when it succeeds, the fields
each operation leaves alone, and the new `coverAvailable` when the result fits a `Number`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

/-- A successful credit converts the amount, adds it to `coverAvailable`, and
stores the sum. -/
lemma LoanBroker.applyCoverTransaction_credit_inv (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.applyCoverTransaction .credit amount = .ok res) :
    ∃ m c', amount.toNumber .to_nearest = .ok m ∧
      lb.coverAvailable.operator_add m .to_nearest = .ok c' ∧ res.amount' = amount ∧
      res.loanBroker'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  unfold LoanBroker.applyCoverTransaction at hok
  obtain ⟨m, hm, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨c', hc, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨lb', hl, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [pure_eq, Except.ok.injEq] at hok
  subst hok
  exact ⟨m, c', hm, hc, rfl, (RawLoanBroker.to_lawful_ok hl).1⟩

/-- A successful debit converts the amount, subtracts it from `coverAvailable`,
and stores the difference. -/
lemma LoanBroker.applyCoverTransaction_debit_inv (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.applyCoverTransaction .debit amount = .ok res) :
    ∃ m c', amount.toNumber .to_nearest = .ok m ∧
      lb.coverAvailable.operator_sub m .to_nearest = .ok c' ∧ res.amount' = amount ∧
      res.loanBroker'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  unfold LoanBroker.applyCoverTransaction at hok
  obtain ⟨m, hm, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨c', hc, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨lb', hl, hok⟩ := bind_ok_peel _ _ _ hok
  simp only [pure_eq, Except.ok.injEq] at hok
  subst hok
  exact ⟨m, c', hm, hc, rfl, (RawLoanBroker.to_lawful_ok hl).1⟩

/-- The amount a clawback asks for: all cover above the minimum when no amount or a zero amount is
given, otherwise the amount, capped at that excess. -/
def LoanBroker.clawRequest (maxClawAmount : Number) (amount : Option STAmount) : Except Error Number :=
  match amount with
  | none => .pure maxClawAmount
  | some a =>
    if a.isZero then .pure maxClawAmount
    else do
      let magnitude ← a.toNumber .to_nearest
      .pure (if magnitude.operator_gt maxClawAmount then maxClawAmount else magnitude)

/-- What a deposit's rounding computes: the credit that floors `coverAvailable` plus the amount onto the grid
of the sum. A credit that is not positive is `tecPRECISION_LOSS`. -/
lemma LoanBroker.roundedCoverAmount_run (lb : LoanBroker) (pool : α) (amount : STAmount)
    (aN : Number) (r : STAmount) (hnum : amount.toNumber .to_nearest = .ok aN)
    (hr : sumRoundAndSubtract lb.coverAvailable aN (AssetPool.baseExponent pool) lb.numericType
      .downward = .ok r) :
    (lb.roundedCoverAmount pool amount).run =
      if r.signum ≤ 0 then .ok (.error .tecPRECISION_LOSS) else .ok (.ok r) := by
  unfold LoanBroker.roundedCoverAmount
  unfold_ter
  rw [hnum]
  simp only
  rw [hr]
  dsimp only
  split <;> rfl

/-- A deposit's rounding that succeeds returns a positive credit. -/
lemma LoanBroker.roundedCoverAmount_ok (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (hok : (lb.roundedCoverAmount pool amount).run = .ok (.ok r)) :
    ∃ aN, amount.toNumber .to_nearest = .ok aN ∧
      sumRoundAndSubtract lb.coverAvailable aN (AssetPool.baseExponent pool) lb.numericType
        .downward = .ok r ∧ 0 < r.signum := by
  cases hnum : amount.toNumber .to_nearest with
  | error e =>
    unfold LoanBroker.roundedCoverAmount at hok
    unfold_ter at hok
    rw [hnum] at hok
    cases hok
  | ok aN =>
    cases hr : sumRoundAndSubtract lb.coverAvailable aN (AssetPool.baseExponent pool) lb.numericType
        .downward with
    | error e =>
      unfold LoanBroker.roundedCoverAmount at hok
      unfold_ter at hok
      rw [hnum] at hok
      simp only at hok
      rw [hr] at hok
      cases hok
    | ok r' =>
      rw [LoanBroker.roundedCoverAmount_run lb pool amount aN r' hnum hr] at hok
      split at hok
      · cases hok
      · cases hok
        exact ⟨aN, rfl, hr, not_le.mp (by assumption)⟩

/-- `tecPRECISION_LOSS` is the only code a deposit's rounding returns. -/
lemma LoanBroker.roundedCoverAmount_error_codes_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (ter : TER) (hok : (lb.roundedCoverAmount pool amount).run = .ok (.error ter)) :
    ter = .tecPRECISION_LOSS := by
  unfold LoanBroker.roundedCoverAmount at hok
  unfold_ter at hok
  walk_ok
  rfl

/-- What the Open-limit check of a deposit reads when it passes: the sum stays at the base
exponent and, rounded toward zero, within the pool's Open limit. -/
lemma LoanBroker.checkCoverOpenLimit_ok (lb : LoanBroker) (pool : α) (amount : STAmount)
    (hok : lb.checkCoverOpenLimit pool amount = .ok .tesSUCCESS) :
    ∃ aN c' limit, amount.toNumber .to_nearest = .ok aN ∧
      postSumExponent lb.coverAvailable aN (AssetPool.baseExponent pool) lb.numericType =
        .ok (AssetPool.baseExponent pool) ∧
      lb.coverAvailable.operator_add aN .towards_zero = .ok c' ∧
      AssetPool.openLimit pool = .ok limit ∧ c'.operator_gt limit = false := by
  unfold LoanBroker.checkCoverOpenLimit at hok
  unfold_ter at hok
  walk_ok
  rename_i _ aN hnum _ e hps hne _ c' hadd _ limit hlimit hgt
  have he : e = AssetPool.baseExponent pool := by simpa using hne
  subst he
  exact ⟨aN, c', limit, hnum, hps, hadd, hlimit, by simpa using hgt⟩

/-- The deposit check passes only when the rounding gives a nonzero credit that passes the
Open-limit check. -/
lemma LoanBroker.canCoverDeposit_ok (lb : LoanBroker) (pool : α) (amount : STAmount)
    (hok : lb.canCoverDeposit pool amount = .ok .tesSUCCESS) :
    ∃ r, (lb.roundedCoverAmount pool amount).run = .ok (.ok r) ∧
      lb.checkCoverOpenLimit pool r = .ok .tesSUCCESS := by
  unfold LoanBroker.canCoverDeposit at hok
  cases h : (lb.roundedCoverAmount pool amount).run with
  | error e => rw [h] at hok; cases hok
  | ok x =>
    rw [h] at hok
    cases x with
    | error ter =>
      have := LoanBroker.roundedCoverAmount_error_codes_proof lb pool amount ter h
      subst this
      cases hok
    | ok r => exact ⟨r, rfl, hok⟩

/-- A successful deposit credits the rounded amount. -/
lemma LoanBroker.coverDeposit_ok_inv (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit pool amount).run = .ok (.ok res)) :
    ∃ r, (lb.roundedCoverAmount pool amount).run = .ok (.ok r) ∧
      lb.applyCoverTransaction .credit r = .ok res := by
  unfold LoanBroker.coverDeposit at hok
  unfold_ter at hok
  cases h : lb.roundedCoverAmount pool amount with
  | error e => rw [h] at hok; cases hok
  | ok x =>
    rw [h] at hok
    cases x with
    | error ter => cases hok
    | ok r =>
      simp only at hok
      cases happ : lb.applyCoverTransaction .credit r with
      | error e => rw [happ] at hok; cases hok
      | ok res' => rw [happ] at hok; cases hok; exact ⟨r, rfl, happ⟩

/-- What a passing withdrawal check computes: the amount clamped onto the grid of the difference, nonzero, no
more than `coverAvailable`, and a new `coverAvailable` that keeps the minimum cover at the base exponent. -/
lemma LoanBroker.canCoverWithdraw_ok (lb : LoanBroker) (pool : α) (amount : STAmount)
    (hok : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS) :
    ∃ a aN c', clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) =
        .ok a ∧ a.isZero = false ∧ a.toNumber .to_nearest = .ok aN ∧
      lb.coverAvailable.operator_lt aN = false ∧
      lb.coverAvailable.operator_sub aN .to_nearest = .ok c' ∧
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover
        (AssetPool.baseExponent pool) = .ok true := by
  unfold LoanBroker.canCoverWithdraw at hok
  unfold_ter at hok
  walk_ok
  rename_i _ a ha hz _ aN hnum hlt _ c' hsub _ b hmin hb
  have hb' : b = true := by simpa using hb
  subst hb'
  exact ⟨a, aN, c', ha, by simpa using hz, hnum, by simpa using hlt, hsub, hmin⟩

/-- A successful withdrawal debits the amount clamped onto the grid of the difference. -/
lemma LoanBroker.coverWithdraw_ok_inv (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw pool amount).run = .ok (.ok res)) :
    ∃ a, clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) =
        .ok a ∧ lb.applyCoverTransaction .debit a = .ok res := by
  unfold LoanBroker.coverWithdraw at hok
  unfold_ter at hok
  cases h : clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) with
  | error e => rw [h] at hok; cases hok
  | ok a =>
    rw [h] at hok
    simp only at hok
    cases happ : lb.applyCoverTransaction .debit a with
    | error e => rw [happ] at hok; cases hok
    | ok res' => rw [happ] at hok; cases hok; exact ⟨a, rfl, happ⟩

/-- What a successful clawback rounding computes: the minimum cover, a positive excess above it, the request
capped at that excess, converted to the asset and clamped onto the grid of the difference, nonzero. -/
lemma LoanBroker.roundedCoverClawback_ok (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (c : STAmount) (hok : (lb.roundedCoverClawback pool amount).run = .ok (.ok c)) :
    ∃ minimumCover maxClaw claw claw',
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum (AssetPool.baseExponent pool) =
        .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧ 0 < maxClaw.signum ∧
      LoanBroker.clawRequest maxClaw amount = .ok claw ∧
      STAmount.ofNumber lb.numericType claw .to_nearest = .ok claw' ∧
      clampToSumExponent lb.coverAvailable claw'.operator_neg (AssetPool.baseExponent pool) = .ok c ∧
      c.isZero = false := by
  unfold LoanBroker.roundedCoverClawback at hok
  unfold_ter at hok
  walk_ok
  all_goals
    refine ⟨_, _, _, _, ‹minimumBrokerCover _ _ _ _ = _›, ‹Number.operator_sub _ _ _ = _›,
      not_le.mp ‹¬ (_ : ℤ) ≤ 0›, ?_, ‹STAmount.ofNumber _ _ _ = _›, ‹clampToSumExponent _ _ _ = _›,
      by simpa using ‹¬ c.isZero = true›⟩
    simp_all [LoanBroker.clawRequest]

/-- A clawback's rounding returns only `tecINSUFFICIENT_FUNDS` or `tecPRECISION_LOSS`. -/
lemma LoanBroker.roundedCoverClawback_error_codes_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (ter : TER)
    (hok : (lb.roundedCoverClawback pool amount).run = .ok (.error ter)) :
    ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS := by
  unfold LoanBroker.roundedCoverClawback at hok
  unfold_ter at hok
  walk_ok
  all_goals simp

/-- The clawback check passes exactly when the asset is not XRP and the clawback's rounding succeeds. -/
lemma LoanBroker.canCoverClawback_ok_iff (lb : LoanBroker) (pool : α) (amount : Option STAmount) :
    lb.canCoverClawback pool amount = .ok .tesSUCCESS ↔
      lb.numericType ≠ .native ∧ ∃ c, (lb.roundedCoverClawback pool amount).run = .ok (.ok c) := by
  unfold LoanBroker.canCoverClawback
  by_cases hn : lb.numericType = .native
  · simp [hn]
  cases h : (lb.roundedCoverClawback pool amount).run with
  | error e => simp [hn]
  | ok x =>
    cases x with
    | error ter =>
      rcases LoanBroker.roundedCoverClawback_error_codes_proof lb pool amount ter h with h' | h' <;>
        subst h' <;> simp [hn]
    | ok c => simp [hn]

/-- A successful clawback debits the amount its rounding returns. -/
lemma LoanBroker.coverClawback_ok_inv (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback pool amount).run = .ok (.ok res)) :
    ∃ c, (lb.roundedCoverClawback pool amount).run = .ok (.ok c) ∧
      lb.applyCoverTransaction .debit c = .ok res := by
  unfold LoanBroker.coverClawback at hok
  unfold_ter at hok
  cases h : lb.roundedCoverClawback pool amount with
  | error e => rw [h] at hok; cases hok
  | ok x =>
    rw [h] at hok
    cases x with
    | error ter => cases hok
    | ok c =>
      simp only at hok
      cases happ : lb.applyCoverTransaction .debit c with
      | error e => rw [happ] at hok; cases hok
      | ok res' => rw [happ] at hok; cases hok; exact ⟨c, rfl, happ⟩

/-- The fields no LoanBroker operation writes: the numeric type, `debtTotal`,
`loanCount` and the three rates. -/
structure LoanBroker.SameFixedFields (a b : LoanBroker) : Prop where
  numericType : b.numericType = a.numericType
  debtTotal : b.debtTotal = a.debtTotal
  loanCount : b.loanCount = a.loanCount
  managementFeeRate : b.managementFeeRate = a.managementFeeRate
  coverRateMinimum : b.coverRateMinimum = a.coverRateMinimum
  coverRateLiquidation : b.coverRateLiquidation = a.coverRateLiquidation

/-- Fixed fields kept over two steps are kept over both. -/
lemma LoanBroker.SameFixedFields.trans {a b c : LoanBroker}
    (hab : LoanBroker.SameFixedFields a b) (hbc : LoanBroker.SameFixedFields b c) :
    LoanBroker.SameFixedFields a c :=
  ⟨hbc.numericType.trans hab.numericType, hbc.debtTotal.trans hab.debtTotal,
    hbc.loanCount.trans hab.loanCount, hbc.managementFeeRate.trans hab.managementFeeRate,
    hbc.coverRateMinimum.trans hab.coverRateMinimum,
    hbc.coverRateLiquidation.trans hab.coverRateLiquidation⟩

/-- A broker that only differs in `coverAvailable` keeps the fixed fields. -/
private lemma LoanBroker.sameFixedFields_cover (a b : LoanBroker) (c : Number)
    (h : b.toRawLoanBroker = { a.toRawLoanBroker with coverAvailable := c }) :
    LoanBroker.SameFixedFields a b := by
  have e1 := congrArg RawLoanBroker.numericType h
  have e2 := congrArg RawLoanBroker.debtTotal h
  have e3 := congrArg RawLoanBroker.loanCount h
  have e4 := congrArg RawLoanBroker.managementFeeRate h
  have e5 := congrArg RawLoanBroker.coverRateMinimum h
  have e6 := congrArg RawLoanBroker.coverRateLiquidation h
  exact ⟨e1, e2, e3, e4, e5, e6⟩

/-- A deposit only changes `coverAvailable`. -/
lemma LoanBroker.coverDeposit_fixed_fields (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit pool amount).run = .ok (.ok res)) :
    LoanBroker.SameFixedFields lb res.loanBroker' := by
  obtain ⟨r, _, happ⟩ := LoanBroker.coverDeposit_ok_inv lb pool amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  exact LoanBroker.sameFixedFields_cover lb res.loanBroker' c' hraw

/-- A withdrawal only changes `coverAvailable`. -/
lemma LoanBroker.coverWithdraw_fixed_fields (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw pool amount).run = .ok (.ok res)) :
    LoanBroker.SameFixedFields lb res.loanBroker' := by
  obtain ⟨a, _, happ⟩ := LoanBroker.coverWithdraw_ok_inv lb pool amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb a res happ
  exact LoanBroker.sameFixedFields_cover lb res.loanBroker' c' hraw

/-- A clawback only changes `coverAvailable`. -/
lemma LoanBroker.coverClawback_fixed_fields (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hok : (lb.coverClawback pool amount).run = .ok (.ok res)) :
    LoanBroker.SameFixedFields lb res.loanBroker' := by
  obtain ⟨c, _, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb c res happ
  exact LoanBroker.sameFixedFields_cover lb res.loanBroker' c' hraw

/-- A deposit keeps `debtMaximum`. -/
lemma LoanBroker.coverDeposit_debtMaximum (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit pool amount).run = .ok (.ok res)) :
    res.loanBroker'.debtMaximum = lb.debtMaximum := by
  obtain ⟨r, _, happ⟩ := LoanBroker.coverDeposit_ok_inv lb pool amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  have h := congrArg RawLoanBroker.debtMaximum hraw
  exact h

/-- A withdrawal keeps `debtMaximum`. -/
lemma LoanBroker.coverWithdraw_debtMaximum (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw pool amount).run = .ok (.ok res)) :
    res.loanBroker'.debtMaximum = lb.debtMaximum := by
  obtain ⟨a, _, happ⟩ := LoanBroker.coverWithdraw_ok_inv lb pool amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb a res happ
  have h := congrArg RawLoanBroker.debtMaximum hraw
  exact h

/-- A clawback keeps `debtMaximum`. -/
lemma LoanBroker.coverClawback_debtMaximum (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hok : (lb.coverClawback pool amount).run = .ok (.ok res)) :
    res.loanBroker'.debtMaximum = lb.debtMaximum := by
  obtain ⟨c, _, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  obtain ⟨_, c', _, _, _, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb c res happ
  have h := congrArg RawLoanBroker.debtMaximum hraw
  exact h

/-- The new `coverAvailable` after a credit, as a rational. -/
lemma LoanBroker.applyCoverTransaction_credit_value (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult)
    (hok : lb.applyCoverTransaction .credit amount = .ok res) (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + amount.toRat) :
    res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable + amount.toRat ∧
      res.amount' = amount := by
  obtain ⟨m, c', hm, hadd, hamt, hraw⟩ :=
    LoanBroker.applyCoverTransaction_credit_inv lb amount res hok
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of amount m hc hm
  refine ⟨?_, hamt⟩
  show res.loanBroker'.toRawLoanBroker.coverAvailable.toRat = lb.coverAvailable.toRat + amount.toRat
  rw [hraw]
  show c'.toRat = lb.coverAvailable.toRat + amount.toRat
  obtain ⟨w, hw, hwt⟩ := hexact
  rw [← hmv] at hwt ⊢
  exact Number.roundsToRepresentable_eq c' _
    (operator_add_rounded_to_nearest _ _ _ lb.wf.coverAvailable_norm hmn hadd) w hw hwt

/-- The new `coverAvailable` after a debit, as a rational. -/
lemma LoanBroker.applyCoverTransaction_debit_value (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult)
    (hok : lb.applyCoverTransaction .debit amount = .ok res) (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - amount.toRat) :
    res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable - amount.toRat ∧
      res.amount' = amount := by
  obtain ⟨m, c', hm, hsub, hamt, hraw⟩ :=
    LoanBroker.applyCoverTransaction_debit_inv lb amount res hok
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of amount m hc hm
  refine ⟨?_, hamt⟩
  show res.loanBroker'.toRawLoanBroker.coverAvailable.toRat = lb.coverAvailable.toRat - amount.toRat
  rw [hraw]
  show c'.toRat = lb.coverAvailable.toRat - amount.toRat
  obtain ⟨w, hw, hwt⟩ := hexact
  rw [← hmv] at hwt ⊢
  exact Number.roundsToRepresentable_eq c' _
    (operator_sub_rounded_to_nearest _ _ _ lb.wf.coverAvailable_norm hmn hsub) w hw hwt

/-- A raw broker whose `coverAvailable` compares below zero is not lawful. -/
lemma RawLoanBroker.to_lawful_negative_cover (lb : LoanBroker) (c' : Number)
    (hneg : Number.zero.operator_le c' = false) :
    ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful =
      .error .notLawful := by
  apply RawLoanBroker.to_lawful_not_lawful
  rintro ⟨_, hv⟩
  have h : Number.zero.operator_le c' = true := hv.coverAvailable_nonneg
  rw [hneg] at h
  exact absurd h (by decide)

/-- A broker that only changes `coverAvailable`, to a normalized nonnegative
value, passes the `to_lawful` re-check. -/
lemma LoanBroker.withCover_lawful (lb : LoanBroker) (c' : Number) (hcn : c'.isNormalized)
    (hc0 : 0 ≤ c'.toRat) :
    ∃ lb' : LoanBroker,
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful = .ok lb' ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  have hwf : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).WF :=
    ⟨lb.wf.debtTotal_norm, lb.wf.debtMaximum_norm, hcn⟩
  have hlb := lb.exact
  have he : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).toExact.Valid :=
    { debtTotal_nonneg := hlb.debtTotal_nonneg
      coverAvailable_nonneg := hc0
      debt_within_cap := hlb.debt_within_cap
      empty_broker := hlb.empty_broker
      debtMaximum_nonneg := hlb.debtMaximum_nonneg
      debtMaximum_cap := hlb.debtMaximum_cap
      managementFeeRate_cap := hlb.managementFeeRate_cap
      coverRateMinimum_cap := hlb.coverRateMinimum_cap
      coverRateLiquidation_cap := hlb.coverRateLiquidation_cap
      coverRates_coupled := hlb.coverRates_coupled }
  exact RawLoanBroker.to_lawful_ok_of hwf ((RawLoanBroker.valid_iff_exact _ hwf).mpr he)

/-- Subtracting a normalized amount no larger than `coverAvailable` leaves a
broker that passes the `to_lawful` re-check. -/
lemma LoanBroker.debit_lawful (lb : LoanBroker) (m c' : Number) (hmn : m.isNormalized)
    (hge : lb.coverAvailable.operator_lt m = false)
    (hsub : lb.coverAvailable.operator_sub m .to_nearest = .ok c') :
    ∃ lb' : LoanBroker,
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful = .ok lb' ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  have hle := (operator_lt_eq_false_iff _ _ lb.wf.coverAvailable_norm hmn).mp hge
  exact LoanBroker.withCover_lawful lb c'
    (operator_sub_isNormalized_to_nearest_sz _ _ _ lb.wf.coverAvailable_norm hmn hsub)
    (operator_sub_nonneg _ _ _ lb.wf.coverAvailable_norm hmn hsub (sub_nonneg.mpr hle))

/-- Adding a normalized nonnegative amount to `coverAvailable` leaves a broker that
passes the `to_lawful` re-check. -/
lemma LoanBroker.credit_lawful (lb : LoanBroker) (m c' : Number) (hmn : m.isNormalized)
    (hm0 : 0 ≤ m.toRat) (hadd : lb.coverAvailable.operator_add m .to_nearest = .ok c') :
    ∃ lb' : LoanBroker,
      ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).to_lawful = .ok lb' ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  have hcn := lb.wf.coverAvailable_norm
  have hcn' : c'.isNormalized := by
    by_cases h0 : c'.mantissa_ = 0
    · rw [Number.operator_add_zero_shape_sz _ _ _ hcn hmn hadd h0]
      exact Or.inl rfl
    · exact operator_add_isNormalized_to_nearest _ _ _ hcn hmn hadd h0
  have hc0 : 0 ≤ c'.toRat :=
    le_trans lb.exact.coverAvailable_nonneg
      (operator_add_ge_of_ge_normalized _ _ _ _ hcn hmn hadd hcn (by linarith))
  exact LoanBroker.withCover_lawful lb c' hcn' hc0

/-- A whole `coverAvailable` below `2^63` minus a nonnegative canonical whole
amount is debited exactly. -/
lemma LoanBroker.applyCoverTransaction_debit_integral (lb : LoanBroker) (a : STAmount)
    (res : LoanBrokerCoverResult) (happ : lb.applyCoverTransaction .debit a = .ok res)
    (hic : a.IntegralCanonical) (hsz : a.mValue.toNat ≤ 2 ^ 63 - 1) (ha0 : 0 ≤ a.toRat)
    (hcint : lb.toExact.coverAvailable.den = 1) (hbound : lb.toExact.coverAvailable < 2 ^ 63) :
    res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable - a.toRat ∧
      res.amount' = a := by
  have hden := Rat.den_one_sub _ _ hcint (STAmount.IntegralCanonical.den_eq_one a hic)
  have hamax := (abs_le.mp (STAmount.IntegralCanonical.abs_toRat_le_of_mValue_le a hic hsz)).2
  have hcov0 : 0 ≤ lb.toExact.coverAvailable := lb.exact.coverAvailable_nonneg
  exact LoanBroker.applyCoverTransaction_debit_value lb a res happ (Or.inr ⟨hic, hsz⟩)
    (Number.exists_of_int _ hden (by linarith) (by linarith))

end XRPL.Model.Lending
