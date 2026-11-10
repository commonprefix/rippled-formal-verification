import XRPL.Properties.Lending.Loan.Common.ScheduledDue

/-! # Witnesses for what a scheduled payment of a regular payment is due

Concrete creates and regular payments on closed-ended IOU vaults, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- A closed-ended IOU vault at the given scale holding `assets`, with nothing lent out. -/
private def sdVault (scale : UInt8) (assets : Number) : RawVault :=
  { assetsAvailable := assets, assetsDeployed := Number.zero
  , assetsReserved := Number.zero, assetsMaximum := none, numericType := .fractional, scale := scale
  , sharesTotal := ⟨false, 1000000000000000000, -15⟩, lossUnrealized := Number.zero
  , yieldUnrealized := Number.zero, schedule := some { subscriptionDate := 900, redemptionDate := 900000900 }
  , earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

/-- An IOU broker with no loans, no cover requirement and the given management fee rate. -/
private def sdBroker (managementFeeRate : TenthBips16) : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := managementFeeRate, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := Number.zero, loanCount := 0 }

/-- The given LoanServiceFee and no other fee. -/
private def sdFees (serviceFee : Number) : LoanFees :=
  { originationFee := Number.zero, serviceFee := serviceFee, latePaymentFee := Number.zero
  , closePaymentFee := Number.zero }

/-- The given InterestRate and no other rate. -/
private def sdRates (interestRate : TenthBips32) : LoanRates :=
  { interestRate := interestRate, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0
  , overpaymentFee := 0 }

/-- One regular payment of exactly the next totalDue at its due date, after the LoanPay checks, from close time `t`.
Irreducible, so the run's equations never unfold the payment. -/
@[irreducible] private def sdStep (loan : Loan) (v : Vault) (t : UInt32) : Option (Loan × Vault) :=
  if decide (t ≤ loan.nextPaymentDueDate) && (loan.canPay .regular).isTesSuccess then
    match loan.paymentComponents .regular loan.nextPaymentDueDate with
    | .ok pc =>
      match pc.totalDue with
      | .ok due =>
        match (loan.regularPayment v due loan.nextPaymentDueDate).run with
        | .ok (.ok r) => some (r.loan', r.pool')
        | _ => none
      | .error _ => none
    | .error _ => none
  else none

/-- A step that passes is a regular payment that passed its checks, at or after `t`. -/
private lemma sdStep_ok (loan : Loan) (v : Vault) (t : UInt32) (loan' : Loan) (v' : Vault)
    (h : sdStep loan v t = some (loan', v')) :
    t ≤ loan.nextPaymentDueDate ∧ loan.canPay .regular = .tesSUCCESS ∧
      ∃ amount r, (loan.regularPayment v amount loan.nextPaymentDueDate).run = .ok (.ok r) ∧ r.loan' = loan' := by
  unfold sdStep at h
  split at h
  · rename_i hc
    rw [Bool.and_eq_true, decide_eq_true_iff, TER.isTesSuccess_iff] at hc
    split at h
    · split at h
      · split at h
        · rename_i r hpay
          injection h with h
          injection h with h1 h2
          exact ⟨hc.1, hc.2, _, r, hpay, h1⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- Pay the next scheduled payment `n` times, each with its totalDue at its due date, from close time `t`. -/
private def sdPayDue : Nat → Loan → Vault → UInt32 → Option (Loan × Vault × UInt32)
  | 0, loan, v, t => some (loan, v, t)
  | n + 1, loan, v, t =>
    match sdStep loan v t with
    | some (loan', v') => sdPayDue n loan' v' loan.nextPaymentDueDate
    | none => none

/-- The scheduled payments keep the loan reachable. -/
private lemma sdPayDue_reachable (start : Loan) (t₀ : UInt32) :
    ∀ (n : Nat) (loan : Loan) (v : Vault) (t : UInt32) (loan' : Loan) (v' : Vault) (t' : UInt32),
      sdPayDue n loan v t = some (loan', v', t') → Loan.ReachableFrom start t₀ loan t →
      Loan.ReachableFrom start t₀ loan' t' := by
  intro n
  induction n with
  | zero =>
    intro loan v t loan' v' t' h hr
    rw [sdPayDue] at h
    injection h with h
    injection h with h1 h2
    injection h2 with h2 h3
    subst h1; subst h3
    exact hr
  | succ n ih =>
    intro loan v t loan' v' t' h hr
    rw [sdPayDue] at h
    split at h
    · rename_i l1 v1 hstep
      obtain ⟨ht, hcan, amount, r, hpay, rfl⟩ := sdStep_ok _ _ _ _ _ hstep
      exact ih _ _ _ _ _ _ h (.regularPayment loan t _ v _ r hr ht hcan hpay)
    · cases h

/-- A vault at scale `10^-8` holding `10^6`. -/
private def sdLastVault : Vault := ⟨sdVault 8 ⟨false, 1000000000000000000, -12⟩, by native_decide, by native_decide⟩

/-- The broker with a 0.1% management fee. -/
private def sdLastBroker : LoanBroker := ⟨sdBroker 100, by native_decide, by native_decide⟩

/-- `190.623`. -/
private def sdLastPrincipal : Number := ⟨false, 1906230000000000000, -16⟩

/-- Thirty-six payments 30 days apart, starting at the LoanSet close time `1000`. -/
private def sdLastSchedule : LoanSchedule := LoanSchedule.build (some 2592000) (some 36) (some 60) 1000 1000 false

/-- The loan of `190.623` at 12% over 36 monthly payments with a 0.1% management fee, after its first 35 payments,
pays its last scheduled payment with exactly its totalDue, more than ⌈PeriodicPayment⌉ + LoanServiceFee. -/
private def lastCheck : Bool :=
  match Loan.canCreate sdLastBroker sdLastVault sdLastPrincipal (sdFees Number.zero) sdLastSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create sdLastBroker sdLastVault sdLastPrincipal (sdRates 12000) (sdFees Number.zero) sdLastSchedule
        false false).run with
    | .ok (.ok r0) =>
      match sdPayDue 35 r0.loan' r0.pool' 1000 with
      | some (loan, v, _) =>
        match loan.paymentComponents .regular loan.nextPaymentDueDate,
            STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) with
        | .ok pc, .ok pp' =>
          match pc.totalDue with
          | .ok due =>
            match (loan.payInstalments v .regular due loan.nextPaymentDueDate).run with
            | .ok (.ok p) => decide (0 < p.count) && decide (p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) &&
                decide (pp'.toRat + loan.fees.serviceFee.toRat < due.toRat)
            | _ => false
          | .error _ => false
        | _, _ => false
      | none => false
    | _ => false
  | _ => false

private lemma lastCheck_true : lastCheck = true := by native_decide

/-- **The last scheduled payment of a reachable loan can be due more than ⌈PeriodicPayment⌉ + LoanServiceFee.** The
loan of `190.623` owes `6.31645547` after 35 of its 36 monthly payments, ⌈PeriodicPayment⌉ is `6.31645546`. -/
lemma Loan.regularPayment_amount_last_witness :
    ∃ (loan : Loan) (t : UInt32) (v : Vault) (amount : Number) (now : UInt32) (p : UnsettledPayment Vault) (k : Nat)
      (l : Loan) (pc : PaymentComponents) (due pp' : Number),
      loan.Reachable t ∧ (loan.payInstalments v .regular amount now).run = .ok (.ok p) ∧ k < p.count ∧
      loan.ScheduledBefore now k l ∧ l.paymentComponents .regular now = .ok pc ∧ pc.totalDue = .ok due ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale ∧
      pp'.toRat + loan.fees.serviceFee.toRat < due.toRat := by
  have h := lastCheck_true
  unfold lastCheck at h
  split at h
  · rename_i hcan
    split at h
    · rename_i r0 h0
      split at h
      · rename_i loan v t hrun
        split at h
        · rename_i pc pp' hpc hpp
          split at h
          · rename_i due hdue
            split at h
            · rename_i p hp
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨⟨hk, hfit⟩, hbad⟩ := h
              have hc : Loan.Created r0.loan' 1000 :=
                ⟨sdLastBroker, sdLastVault, sdLastPrincipal, sdRates 12000, sdFees Number.zero, some 2592000, some 36,
                  some 60, 1000, false, false, r0, hcan, h0, rfl⟩
              have hreach : loan.Reachable t :=
                ⟨r0.loan', 1000, hc, sdPayDue_reachable r0.loan' 1000 35 _ _ _ _ _ _ hrun .refl⟩
              exact ⟨loan, t, v, due, loan.nextPaymentDueDate, p, 0, loan.unimpaired, pc, due, pp', hreach, hp, hk,
                .first, hpc, hdue, hpp, hfit, hbad⟩
            · exact absurd h (by decide)
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- A vault at scale `10^-2` holding `10^12`. -/
private def sdFeeVault : Vault := ⟨sdVault 2 ⟨false, 1000000000000000000, -6⟩, by native_decide, by native_decide⟩

/-- The broker without a management fee. -/
private def sdFeeBroker : LoanBroker := ⟨sdBroker 0, by native_decide, by native_decide⟩

/-- `1001`. -/
private def sdFeePrincipal : Number := ⟨false, 1001000000000000000, -15⟩

/-- LoanServiceFee `10^17`. -/
private def sdBigFee : Number := ⟨false, 1000000000000000000, -1⟩

/-- Thirty payments 60 seconds apart, starting at the LoanSet close time `1000`. -/
private def sdFeeSchedule : LoanSchedule := LoanSchedule.build (some 60) (some 30) (some 60) 1000 1000 false

/-- The loan of `1001` at 1% over 30 payments with LoanServiceFee `10^17` pays its first scheduled payment with
exactly its totalDue, which rounds `33.37` up to `33.4` next to the fee. -/
private def feeCheck : Bool :=
  match Loan.canCreate sdFeeBroker sdFeeVault sdFeePrincipal (sdFees sdBigFee) sdFeeSchedule 1000 false with
  | .ok .tesSUCCESS =>
    match (Loan.create sdFeeBroker sdFeeVault sdFeePrincipal (sdRates 1000) (sdFees sdBigFee) sdFeeSchedule
        false false).run with
    | .ok (.ok r0) =>
      match r0.loan'.paymentComponents .regular 1011,
          STAmount.roundToNumericType r0.loan'.broker.numericType r0.loan'.periodicPayment .upward
            (some r0.loan'.loanScale) with
      | .ok pc, .ok pp' =>
        match pc.totalDue with
        | .ok due =>
          match (r0.loan'.payInstalments r0.pool' .regular due 1011).run with
          | .ok (.ok p) => decide (0 < p.count) && decide (r0.loan'.paymentRemaining ≠ 1) &&
              decide (pp'.toRat + r0.loan'.fees.serviceFee.toRat < due.toRat)
          | _ => false
        | .error _ => false
      | _, _ => false
    | _ => false
  | _ => false

private lemma feeCheck_true : feeCheck = true := by native_decide

/-- **A scheduled payment that is not the last can be due more than ⌈PeriodicPayment⌉ + LoanServiceFee.** With
LoanServiceFee `10^17` the 19-digit totalDue rounds ⌈PeriodicPayment⌉ `33.37` up to `33.4`. -/
lemma Loan.regularPayment_amount_fee_witness :
    ∃ (loan : Loan) (t : UInt32) (v : Vault) (amount : Number) (now : UInt32) (p : UnsettledPayment Vault) (k : Nat)
      (l : Loan) (pc : PaymentComponents) (due pp' : Number),
      loan.Reachable t ∧ (loan.payInstalments v .regular amount now).run = .ok (.ok p) ∧ k < p.count ∧
      loan.ScheduledBefore now k l ∧ l.paymentComponents .regular now = .ok pc ∧ pc.totalDue = .ok due ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ l.paymentRemaining ≠ 1 ∧ pp'.toRat + loan.fees.serviceFee.toRat < due.toRat := by
  have h := feeCheck_true
  unfold feeCheck at h
  split at h
  · rename_i hcan
    split at h
    · rename_i r0 h0
      split at h
      · rename_i pc pp' hpc hpp
        split at h
        · rename_i due hdue
          split at h
          · rename_i p hp
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hk, hrem⟩, hbad⟩ := h
            have hc : Loan.Created r0.loan' 1000 :=
              ⟨sdFeeBroker, sdFeeVault, sdFeePrincipal, sdRates 1000, sdFees sdBigFee, some 60, some 30, some 60,
                1000, false, false, r0, hcan, h0, rfl⟩
            exact ⟨r0.loan', 1000, r0.pool', due, 1011, p, 0, r0.loan'.unimpaired, pc, due, pp',
              ⟨r0.loan', 1000, hc, .refl⟩, hp, hk, .first, hpc, hdue, hpp, hrem, hbad⟩
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
