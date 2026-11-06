import XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness
import XRPL.Properties.Lending.Loan.Common.LifetimeLedger
import XRPL.Properties.Lending.Loan.Common.RegularPayoffLedger
import XRPL.Properties.Lending.Loan.Common.RegularPayoffWitness

/-! # Ledger runs where interestDue rises and regular payoffs pay less

The loan of `NegativeInterestWitness.lean`, at a tiny rate, after its first two instalments: a late payment or an
overpayment with its own interest raises interestDue, and in the redemption phase the late payment raises
YieldUnrealized. The payoffs of `RegularPayoffWitness.lean` replayed as ledger transactions: on a coarsened vault the
vault gets less, and a LoanServiceFee of `10^30` drops the loan's value from the 19-digit sums. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private niGenesis niGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness
open private rwFeeTxs rwHugeFee rwVaultTxs rwInstalment from XRPL.Properties.Lending.Loan.Common.RegularPayoffWitness

/-- The loan at `i` read with its broker's ledger copy, as every loan transaction reads it. -/
private def LendingLedger.readLoan (l : LendingLedger) (i : Nat) : Option Loan :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b =>
      match e.loan.withBroker b with
      | .ok loan => some loan
      | .error _ => none
    | none => none
  | none => none

private lemma LendingLedger.readLoan_loanAt {l : LendingLedger} {i : Nat} {loan : Loan} (h : l.readLoan i = some loan) :
    l.LoanAt i loan := by
  unfold LendingLedger.readLoan at h
  split at h
  · rename_i e he
    split at h
    · rename_i b hb
      split at h
      · rename_i loan' hw
        obtain rfl := Option.some.inj h
        exact ⟨e, b, he, hb, hw⟩
      · cases h
    · cases h
  · cases h

/-- The last transaction of a prefix of a one-transaction run is that transaction. -/
private lemma prefix_single {pre : List LendingTx} {tx tx' : LendingTx} (h : pre ++ [tx] <+: [tx']) : tx = tx' := by
  obtain ⟨rest, h⟩ := h
  cases pre with
  | nil =>
    simp only [List.nil_append, List.singleton_append, List.cons.injEq] at h
    exact h.1
  | cons a pre => simp at h

/-- An InterestRate of 6 tenth basis points with the given LateInterestRate and OverpaymentInterestRate. -/
private def imRates (lateInterestRate overpaymentInterestRate : TenthBips32) : LoanRates :=
  { interestRate := 6, lateInterestRate := lateInterestRate, closeInterestRate := 0,
    overpaymentInterestRate := overpaymentInterestRate, overpaymentFee := 0 }

/-- The run of `NegativeInterestWitness.lean` with `rates` and the overpayment flag: the loan of 5198461379.86 in
thirty payments 60 seconds apart and its first two instalments, then close time `now`. -/
private def imTxs (rates : LoanRates) (allowsOverpayment : Bool) (now : UInt32) : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-3)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 5198461379860000000, -9⟩ rates cwFees (some 60) (some 30) (some 60) 0 false allowsOverpayment,
   .close 1012,
   .loanPay 0 .regular ⟨false, 1732820465500000000, -10⟩,
   .close 1013,
   .loanPay 0 .regular ⟨false, 1732820465500000000, -10⟩,
   .close now]

/-- A LoanPay of type `pt` on loan 0 after `imTxs` succeeds and raises its interestDue. -/
private def raiseCheck (rates : LoanRates) (allowsOverpayment : Bool) (now : UInt32) (pt : LoanPaymentType)
    (amount : Number) : Bool :=
  match niGenesis.run (imTxs rates allowsOverpayment now) with
  | .ok l =>
    match l.readLoan 0, (l.apply (.loanPay 0 pt amount)).run with
    | some loan, .ok (.ok l') =>
      match l'.readLoan 0 with
      | some loan' => decide (loan.toExact.interestDue < loan'.toExact.interestDue)
      | none => false
    | _, _ => false
  | .error _ => false

private lemma raiseCheck_sound {rates : LoanRates} {allowsOverpayment : Bool} {now : UInt32} {pt : LoanPaymentType}
    {amount : Number} (h : raiseCheck rates allowsOverpayment now pt amount = true) :
    ∃ (l l' : LendingLedger) (loan loan' : Loan), l.Reachable ∧
      LendingLedger.Reaches l [.loanPay 0 pt amount] l' ∧ l.LoanAt 0 loan ∧ l'.LoanAt 0 loan' ∧
      loan.toExact.interestDue < loan'.toExact.interestDue := by
  unfold raiseCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i loan l' hloan hok
  split at h
  case h_2 => cases h
  rename_i loan' hloan'
  exact ⟨l, l', loan, loan', LendingLedger.Reachable.of_run niGenesis_genesis hl, LendingLedger.Reaches.single hok,
    LendingLedger.readLoan_loanAt hloan, LendingLedger.readLoan_loanAt hloan', of_decide_eq_true h⟩

private lemma lateRaise_true :
    raiseCheck (imRates 100000 0) false 1201 .late ⟨false, 1800000000000000000, -10⟩ = true := by
  native_decide

private lemma overRaise_true :
    raiseCheck (imRates 0 50000) true 1014 .overpayment ⟨false, 1732820565600000000, -10⟩ = true := by
  native_decide

/-- A late payment can raise interestDue: its late interest covers the instalment's negative interest part, and
C++ checks only the summed parts (LoanPay.cpp:479). The run has no overpayment. -/
lemma LendingLedger.interest_monotone_late_witness :
    ∃ (l l' : LendingLedger) (txs : List LendingTx) (i : Nat) (loan loan' : Loan), l.Reachable ∧
      LendingLedger.Reaches l txs l' ∧ l.LoanAt i loan ∧ l'.LoanAt i loan' ∧
      (∀ (pre : List LendingTx) (l₁ l₂ : LendingLedger) (amount : Number) (loan₁ : Loan)
        (p : UnsettledPayment Vault), pre ++ [.loanPay i .overpayment amount] <+: txs →
        LendingLedger.Reaches l pre l₁ → (l₁.apply (.loanPay i .overpayment amount)).run = .ok (.ok l₂) →
        l₁.LoanAt i loan₁ → loan₁.rates.overpaymentInterestRate ≠ 0 →
        (loan₁.payInstalments l₁.vault .regular amount l₁.now).run = .ok (.ok p) →
        0 ≤ p.amounts.interestPaid.toRat) ∧
      loan.toExact.interestDue < loan'.toExact.interestDue := by
  obtain ⟨l, l', loan, loan', hr, hrun, hat, hat', hlt⟩ := raiseCheck_sound lateRaise_true
  refine ⟨l, l', _, 0, loan, loan', hr, hrun, hat, hat', fun pre _ _ amount _ _ hpre => ?_, hlt⟩
  have := prefix_single hpre
  simp at this

/-- An overpayment can raise interestDue. Its overpayment interest covers the negative interest part of the
instalment before it, so the settlement passes. The run has no late payment. -/
lemma LendingLedger.interest_monotone_overpayment_witness :
    ∃ (l l' : LendingLedger) (txs : List LendingTx) (i : Nat) (loan loan' : Loan), l.Reachable ∧
      LendingLedger.Reaches l txs l' ∧ l.LoanAt i loan ∧ l'.LoanAt i loan' ∧
      (∀ (pre : List LendingTx) (l₁ l₂ : LendingLedger) (amount : Number) (loan₁ : Loan)
        (pc : PaymentComponents) (d : Number), pre ++ [.loanPay i .late amount] <+: txs →
        LendingLedger.Reaches l pre l₁ → (l₁.apply (.loanPay i .late amount)).run = .ok (.ok l₂) →
        l₁.LoanAt i loan₁ → loan₁.rates.lateInterestRate ≠ 0 → loan₁.paymentComponents .late l₁.now = .ok pc →
        pc.interestDelta = .ok d → 0 ≤ d.toRat) ∧
      loan.toExact.interestDue < loan'.toExact.interestDue := by
  obtain ⟨l, l', loan, loan', hr, hrun, hat, hat', hlt⟩ := raiseCheck_sound overRaise_true
  refine ⟨l, l', _, 0, loan, loan', hr, hrun, hat, hat', fun pre _ _ amount _ _ _ hpre => ?_, hlt⟩
  have := prefix_single hpre
  simp at this

/-- After `imTxs` at close time `now`, the vault is in the redemption phase and a late payment of `amount` on loan 0
succeeds and raises YieldUnrealized. -/
private def yieldRaiseCheck (rates : LoanRates) (now : UInt32) (amount : Number) : Bool :=
  match niGenesis.run (imTxs rates false now) with
  | .ok l =>
    match (l.apply (.loanPay 0 .late amount)).run with
    | .ok (.ok l') =>
      decide (l.vault.phase l.now = .redemption) &&
        decide (l.vault.yieldUnrealized.toRat < l'.vault.yieldUnrealized.toRat)
    | _ => false
  | .error _ => false

private lemma yieldRaiseCheck_true :
    yieldRaiseCheck (imRates 100000 0) 77761001 ⟨false, 5000000000000000000, -8⟩ = true := by
  native_decide

/-- In the redemption phase a late payment can raise YieldUnrealized. At close time 77761001, past RedemptionDate,
the late payment at a 100% LateInterestRate covers the third instalment's interest part of −3.24. -/
lemma LendingLedger.redemption_yield_witness :
    ∃ (l l' : LendingLedger) (tx : LendingTx), l.Reachable ∧ l.vault.phase l.now = .redemption ∧
      (l.apply tx).run = .ok (.ok l') ∧ l.vault.yieldUnrealized.toRat < l'.vault.yieldUnrealized.toRat := by
  have h := yieldRaiseCheck_true
  unfold yieldRaiseCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨l, l', _, LendingLedger.Reachable.of_run niGenesis_genesis hl, h.1, hok, h.2⟩

/-- After `txs`, a regular payment of `amount` on loan `i` pays it off, and `good` holds for its ledger, loan,
instalments and result. -/
private def payoffCheck (txs : List LendingTx) (i : Nat) (amount : Number)
    (good : LendingLedger → Loan → UnsettledPayment Vault → LoanWithAmounts Vault → Bool) : Bool :=
  match cwGenesis.run txs with
  | .ok l =>
    match l.readLoan i with
    | some loan =>
      match (loan.payInstalments l.vault .regular amount l.now).run, (loan.regularPayment l.vault amount l.now).run,
          (l.apply (.loanPay i .regular amount)).run with
      | .ok (.ok p), .ok (.ok r), .ok (.ok l') =>
        match l'.readLoan i with
        | some loan' => loan'.paymentRemaining == 0 && good l loan p r
        | none => false
      | _, _, _ => false
    | none => false
  | .error _ => false

private lemma payoffCheck_sound {txs : List LendingTx} {i : Nat} {amount : Number}
    {good : LendingLedger → Loan → UnsettledPayment Vault → LoanWithAmounts Vault → Bool}
    (h : payoffCheck txs i amount good = true) :
    ∃ (l l' : LendingLedger) (loan loan' : Loan) (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault),
      l.Reachable ∧ l.LoanAt i loan ∧ (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) ∧
      (loan.regularPayment l.vault amount l.now).run = .ok (.ok r) ∧
      (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l'.LoanAt i loan' ∧
      loan'.paymentRemaining = 0 ∧ good l loan p r = true := by
  unfold payoffCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i loan hloan
  split at h
  case h_2 => cases h
  rename_i p r l' hp hreg hok
  split at h
  case h_2 => cases h
  rename_i loan' hloan'
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨l, l', loan, loan', p, r, LendingLedger.Reachable.of_run cwGenesis_genesis hl,
    LendingLedger.readLoan_loanAt hloan, hp, hreg, hok, LendingLedger.readLoan_loanAt hloan', h.1, h.2⟩

/-- The payoff of loan 0 after `rwFeeTxs` by its totalDue `10^30`: it charges less than the schedule, and with the
broker above its minimum cover the broker gets less too. -/
private lemma feeCheck_true : payoffCheck rwFeeTxs 0 rwHugeFee (fun l loan p r =>
    decide (p.totalPaid.toRat <
      loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat) &&
    loan.broker.hasMinimumCover l.vault.baseExponent == .ok true &&
    decide (r.amountToBroker.toRat <
      loan.managementFeeOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat)) = true := by
  native_decide

/-- Loan D's payoff of 1.5 after `rwVaultTxs`, on the coarsened vault: the vault gets less than the loan's value. -/
private lemma vaultCheck_true : payoffCheck rwVaultTxs 3 rwInstalment (fun _ loan _ r =>
    decide (r.amountToPool.toRat < loan.totalValueOutstanding.toRat - loan.managementFeeOutstanding.toRat)) = true := by
  native_decide

/-- A regular payoff can charge less than TotalValueOutstanding plus its LoanServiceFees. A LoanServiceFee of
`10^30` makes the 19-digit charge drop the loan's value. -/
lemma LendingLedger.regularPayoff_cost_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (cost toVault toBroker : ℚ), l.Reachable ∧
      l.LoanAt i loan ∧ l.RegularPayoff i (fun _ _ _ => True) l' cost toVault toBroker ∧ l'.LoanAt i loan' ∧
      loan'.paymentRemaining = 0 ∧
      cost < loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat := by
  obtain ⟨l, l', loan, loan', p, r, hr, hat, hp, hreg, hok, hat', hpaid, hgood⟩ := payoffCheck_sound feeCheck_true
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgood
  refine ⟨l, l', 0, loan, loan', _, _, _, hr, hat, .pay rwHugeFee loan p r .refl hat hp trivial hreg hok, hat', hpaid,
    ?_⟩
  rw [zero_add]
  exact hgood.1.1

/-- A regular payoff on a reachable coarsened vault credits the vault less than the loan's value less its
management fee. Loan D's payment of 1.5 is credited on the coarser grid as 1. -/
lemma LendingLedger.regularPayoff_vault_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (cost toVault toBroker : ℚ), l.Reachable ∧
      l.LoanAt i loan ∧ l.RegularPayoff i (fun _ _ _ => True) l' cost toVault toBroker ∧ l'.LoanAt i loan' ∧
      loan'.paymentRemaining = 0 ∧
      toVault < loan.totalValueOutstanding.toRat - loan.managementFeeOutstanding.toRat := by
  obtain ⟨l, l', loan, loan', p, r, hr, hat, hp, hreg, hok, hat', hpaid, hgood⟩ := payoffCheck_sound vaultCheck_true
  simp only [decide_eq_true_eq] at hgood
  refine ⟨l, l', 3, loan, loan', _, _, _, hr, hat, .pay rwInstalment loan p r .refl hat hp trivial hreg hok, hat',
    hpaid, ?_⟩
  rw [zero_add]
  exact hgood

/-- A regular payoff can pay the broker less than ManagementFeeOutstanding plus its LoanServiceFees, with the
cover not coarsened. A LoanServiceFee of `10^30` makes the 19-digit fee drop the management fee. -/
lemma LendingLedger.regularPayoff_broker_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (cost toVault toBroker : ℚ), l.Reachable ∧
      l.LoanAt i loan ∧ l.RegularPayoff i LendingLedger.PaysCoverUncoarsened l' cost toVault toBroker ∧
      l'.LoanAt i loan' ∧ loan'.paymentRemaining = 0 ∧
      toBroker < loan.managementFeeOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat := by
  obtain ⟨l, l', loan, loan', p, r, hr, hat, hp, hreg, hok, hat', hpaid, hgood⟩ := payoffCheck_sound feeCheck_true
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hgood
  obtain ⟨⟨-, hmc⟩, hb⟩ := hgood
  have hfit : LendingLedger.PaysCoverUncoarsened l loan p := fun h => by rw [hmc] at h; cases h
  refine ⟨l, l', 0, loan, loan', _, _, _, hr, hat, .pay rwHugeFee loan p r .refl hat hp hfit hreg hok, hat', hpaid,
    ?_⟩
  rw [zero_add]
  exact hb

end XRPL.Model.Lending
