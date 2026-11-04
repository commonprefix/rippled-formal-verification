import XRPL.Properties.Lending.Loan.Common.PayLedgerWitness
import XRPL.Properties.Lending.Loan.Common.ScheduledDue
import XRPL.Properties.Lending.Loan.Common.PayLedgerDue
import XRPL.Properties.Lending.Loan.Common.SetWitness

/-! # Witnesses for what a LoanPay transaction charges, on reachable ledgers

Runs from new closed-ended IOU vaults at Scale 0, 2, 6 and 8, a deposit, a broker and a LoanSet, then LoanPay
transactions, checked by `native_decide`. A payment amount that a 16-digit asset amount cannot hold is rounded up to
one it can. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

open private plLoan plLoan_loanAt plPay plPay_spec from XRPL.Properties.Lending.Loan.Common.PayLedgerWitness

/-- Subscription until 1000, redemption about 28 years later. -/
private def pdSchedule : VaultSchedule := ⟨1000, 1000 + 900000000⟩

/-- The new IOU vault VaultCreate makes at Scale `s` for `pdSchedule`. -/
private def pdRawVault (s : UInt8) : RawVault := { cwRawVault with scale := s, schedule := some pdSchedule }

private def pdVault2 : Vault := ⟨pdRawVault 2, by native_decide, by native_decide⟩
private def pdVault6 : Vault := ⟨pdRawVault 6, by native_decide, by native_decide⟩
private def pdVault8 : Vault := ⟨pdRawVault 8, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def pdGenesis (v : Vault) : LendingLedger := { vault := v, shares := [], brokers := [], loans := [], now := 0 }

private lemma pdGenesis2 : (pdGenesis pdVault2).Genesis where
  created := ⟨some 2, none, pdSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨pdVault2.wf, pdVault2.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

private lemma pdGenesis6 : (pdGenesis pdVault6).Genesis where
  created := ⟨some 6, none, pdSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨pdVault6.wf, pdVault6.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

private lemma pdGenesis8 : (pdGenesis pdVault8).Genesis where
  created := ⟨some 8, none, pdSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨pdVault8.wf, pdVault8.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- LoanServiceFee and LatePaymentFee of `10^30`. -/
private def pdBigFees : LoanFees :=
  { lwFees with serviceFee := ⟨false, 1000000000000000000, 12⟩, latePaymentFee := ⟨false, 1000000000000000000, 12⟩ }

/-- A deposit of `10^12` into the Scale 2 vault, a broker without a fee, and at close time `1001` a loan of
`5198461379.86` at 1% with fees of `10^30`, in thirty payments 60 seconds apart. -/
private def pdBigFeeTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-3)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 5198461379860000000, -9⟩ { lwRates 1000 with lateInterestRate := 1000 } pdBigFees (some 60)
     (some 30) (some 60) 0 false false]

/-- `10^30`, the first totalDue of the loan with fees of `10^30`. -/
private def pdFeeDue : Number := ⟨false, 1000000000000000000, 12⟩

/-- At `1012` a regular payment of exactly its totalDue charges more than that amount. -/
private def pdChargeCheck : Bool :=
  match (pdGenesis pdVault2).run (pdBigFeeTxs ++ [.close 1012]) with
  | .ok l =>
    match plPay l 0 .regular pdFeeDue with
    | some (_, _, _, p) => decide (pdFeeDue.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat +
        p.amounts.feePaid.toRat)
    | none => false
  | .error _ => false

private lemma pdChargeCheck_true : pdChargeCheck = true := by native_decide

/-- A LoanPay on a reachable ledger can charge more than its requestedAmount. The regular payment of exactly its
totalDue succeeds and charges the instalment's value on top of it. -/
lemma LendingLedger.payment_charge_le_amount_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) ∧
      amount.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat := by
  have h := pdChargeCheck_true
  unfold pdChargeCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
      exact ⟨l, l', 0, pdFeeDue, loan, p, LendingLedger.Reachable.of_run pdGenesis2 hl, hap, hat, hp,
        of_decide_eq_true h⟩
    · cases h
  · cases h

/-- At `1012` the regular payment of exactly its totalDue pays its first scheduled payment, which charges more than
its totalDue. -/
private def pdSplitCheck : Bool :=
  match (pdGenesis pdVault2).run (pdBigFeeTxs ++ [.close 1012]) with
  | .ok l =>
    match plPay l 0 .regular pdFeeDue with
    | some (loan, _, _, p) =>
      match loan.unimpaired.paymentComponents .regular l.now with
      | .ok pc =>
        match pc.totalDue with
        | .ok due =>
          match (loan.unimpaired.payInstalment l.vault pc due).run with
          | .ok (.ok q) => decide (0 < p.count) && decide (q.totalPaid.toRat < q.amounts.principalPaid.toRat +
              q.amounts.interestPaid.toRat + q.amounts.feePaid.toRat)
          | _ => false
        | .error _ => false
      | .error _ => false
    | none => false
  | .error _ => false

private lemma pdSplitCheck_true : pdSplitCheck = true := by native_decide

/-- A scheduled payment that a LoanPay on a reachable ledger pays can charge more than its totalDue. A
LoanServiceFee more than `10^19` times the instalment makes totalDue drop the instalment's value. -/
lemma LendingLedger.payment_split_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan lk : Loan) (pc : PaymentComponents)
      (q : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      loan.PaysInstalment l.vault amount l.now .regular lk pc q ∧
      q.totalPaid.toRat < q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + q.amounts.feePaid.toRat := by
  have h := pdSplitCheck_true
  unfold pdSplitCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      split at h
      · rename_i pc hpc
        split at h
        · rename_i due hdue
          split at h
          · rename_i q hq
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
            exact ⟨l, l', 0, pdFeeDue, loan, loan.unimpaired, pc, q, LendingLedger.Reachable.of_run pdGenesis2 hl,
              hap, hat, .scheduled hp h.1 .first hpc hdue hq, h.2⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- `2·10^30`, the late totalDue of the loan with fees of `10^30`. -/
private def pdLateDue : Number := ⟨false, 2000000000000000000, 12⟩

/-- At `1201` the late payment of exactly its totalDue charges less than its principal, interest and fee parts, and
less than the value it clears plus the fees and the rounded late interest. -/
private def pdLateCostCheck : Bool :=
  match (pdGenesis pdVault2).run (pdBigFeeTxs ++ [.close 1201]) with
  | .ok l =>
    match plPay l 0 .late pdLateDue with
    | some (loan, _, _, p) =>
      match loanLatePaymentInterest loan.principalOutstanding loan.rates.lateInterestRate l.now
          loan.nextPaymentDueDate with
      | .ok li =>
        match STAmount.roundToNumericType loan.broker.numericType li .to_nearest (some loan.loanScale) with
        | .ok lr => decide (p.totalPaid.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat +
            p.amounts.feePaid.toRat) &&
          decide (p.totalPaid.toRat < loan.totalValueOutstanding.toRat - p.loan.totalValueOutstanding.toRat +
            loan.fees.serviceFee.toRat + loan.fees.latePaymentFee.toRat + lr.toRat)
        | .error _ => false
      | .error _ => false
    | none => false
  | .error _ => false

private lemma pdLateCostCheck_true : pdLateCostCheck = true := by native_decide

/-- A late LoanPay on a reachable ledger can charge less than its parts and its cost. A LatePaymentFee more than
`10^19` times the instalment makes totalDue drop the instalment's value. -/
lemma LendingLedger.latePayment_cost_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault) (li lr : Number),
      l.Reachable ∧ (l.apply (.loanPay i .late amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .late amount l.now).run = .ok (.ok p) ∧
      loanLatePaymentInterest loan.principalOutstanding loan.rates.lateInterestRate l.now loan.nextPaymentDueDate =
        .ok li ∧ STAmount.roundToNumericType loan.broker.numericType li .to_nearest (some loan.loanScale) = .ok lr ∧
      p.totalPaid.toRat < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat + p.amounts.feePaid.toRat ∧
      p.totalPaid.toRat < loan.totalValueOutstanding.toRat - p.loan.totalValueOutstanding.toRat +
        loan.fees.serviceFee.toRat + loan.fees.latePaymentFee.toRat + lr.toRat := by
  have h := pdLateCostCheck_true
  unfold pdLateCostCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      split at h
      · rename_i li hli
        split at h
        · rename_i lr hlr
          obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
          simp only [Bool.and_eq_true] at h
          exact ⟨l, l', 0, pdLateDue, loan, p, li, lr, LendingLedger.Reachable.of_run pdGenesis2 hl, hap, hat, hp,
            hli, hlr, of_decide_eq_true h.1, of_decide_eq_true h.2⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- A deposit of `3·10^9` into the Scale 6 vault, a broker without a fee, and at close time `1001` a loan of `10^9`
at InterestRate 0.001% in 860 payments 92 seconds apart, that allows overpayments. -/
private def pdCheaperTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 3000000000000000 (-6)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 1000000000000000000, -9⟩ (lwRates 1) lwFees (some 92) (some 860) (some 60) 0 false true,
   .close 1093]

/-- `1000000000.029173`, the payoff's totalDue at the first due date. -/
private def pdCheaperDue : Number := ⟨false, 1000000000029173000, -9⟩

/-- At the first due date the full payment of exactly its totalDue charges more than TotalValueOutstanding. -/
private def pdCheaperCheck : Bool :=
  match (pdGenesis pdVault6).run pdCheaperTxs with
  | .ok l =>
    match plPay l 0 .full pdCheaperDue with
    | some (loan, _, _, p) => decide (loan.rates.closeInterestRate = 0 ∧
        loan.fees.closePaymentFee.toRat ≤ loan.fees.serviceFee.toRat ∧
        loan.totalValueOutstanding.toRat + loan.paymentRemaining.toNat * loan.fees.serviceFee.toRat <
          p.totalPaid.toRat)
    | none => false
  | .error _ => false

private lemma pdCheaperCheck_true : pdCheaperCheck = true := by native_decide

/-- An early payoff on a reachable ledger can cost more than the remaining scheduled payments. The loan books less
interest than one period accrues, and the payoff charges that accrual on the principal. -/
lemma LendingLedger.fullPayment_cheaper_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .full amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok p) ∧
      loan.rates.closeInterestRate = 0 ∧ loan.fees.closePaymentFee.toRat ≤ loan.fees.serviceFee.toRat ∧
      loan.totalValueOutstanding.toRat + loan.paymentRemaining.toNat * loan.fees.serviceFee.toRat <
        p.totalPaid.toRat := by
  have h := pdCheaperCheck_true
  unfold pdCheaperCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      obtain ⟨h1, h2, h3⟩ := of_decide_eq_true h
      obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
      exact ⟨l, l', 0, pdCheaperDue, loan, p, LendingLedger.Reachable.of_run pdGenesis6 hl, hap, hat, hp, h1, h2, h3⟩
    · cases h
  · cases h

/-- A deposit of `3·10^9`, a broker with a 10% management fee, and at close time `1001` a loan of `1000` at 10% with
a 100% CloseInterestRate and a ClosePaymentFee of `10^25`, in thirty payments 60 seconds apart. -/
private def pdCloseFeeTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 3000000000000000 (-6)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, some 10000, none, none⟩,
   .loanSet 0 ⟨false, 1000000000000000000, -15⟩ { lwRates 10000 with closeInterestRate := 100000 }
     { lwFees with closePaymentFee := ⟨false, 1000000000000000000, 7⟩ } (some 60) (some 30) (some 60) 0 false false,
   .close 1011]

/-- `2·10^25`, enough for the payoff. -/
private def pdCloseFeeAmount : Number := ⟨false, 2000000000000000000, 7⟩

/-- At `1011` the full payment's feePaid is not ClosePaymentFee plus the management fee. -/
private def pdCloseFeeCheck : Bool :=
  match (pdGenesis pdVault6).run pdCloseFeeTxs with
  | .ok l =>
    match plPay l 0 .full pdCloseFeeAmount with
    | some (loan, _, _, payment) =>
      match loan.periodicRate with
      | .ok rate =>
        match loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining with
        | .ok tpo =>
          match computeFullPaymentInterest tpo rate l.now loan.schedule.paymentInterval loan.previousPaymentDueDate
              loan.schedule.startDate loan.rates.closeInterestRate with
          | .ok fi =>
            match STAmount.roundToNumericType loan.broker.numericType fi .downward (some loan.loanScale) with
            | .ok fi' =>
              match computeManagementFee loan.broker.numericType fi' loan.broker.managementFeeRate loan.loanScale with
              | .ok mf => decide (payment.amounts.feePaid.toRat ≠ loan.fees.closePaymentFee.toRat + mf.toRat)
              | .error _ => false
            | .error _ => false
          | .error _ => false
        | .error _ => false
      | .error _ => false
    | none => false
  | .error _ => false

private lemma pdCloseFeeCheck_true : pdCloseFeeCheck = true := by native_decide

/-- A full LoanPay on a reachable ledger can have feePaid ≠ ClosePaymentFee + managementFee. A ClosePaymentFee of
`10^25` plus a management fee of `100.000003` has 32 digits, and the payoff keeps 19 of them. -/
lemma LendingLedger.fullPayment_broker_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (payment : UnsettledPayment Vault)
      (rate tpo fullInterest fullInterest' managementFee : Number),
      l.Reachable ∧ (l.apply (.loanPay i .full amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .full amount l.now).run = .ok (.ok payment) ∧
      loan.periodicRate = .ok rate ∧
      loanPrincipalFromPeriodicPayment loan.periodicPayment rate loan.paymentRemaining = .ok tpo ∧
      computeFullPaymentInterest tpo rate l.now loan.schedule.paymentInterval loan.previousPaymentDueDate
        loan.schedule.startDate loan.rates.closeInterestRate = .ok fullInterest ∧
      STAmount.roundToNumericType loan.broker.numericType fullInterest .downward (some loan.loanScale) =
        .ok fullInterest' ∧
      computeManagementFee loan.broker.numericType fullInterest' loan.broker.managementFeeRate loan.loanScale =
        .ok managementFee ∧
      payment.amounts.feePaid.toRat ≠ loan.fees.closePaymentFee.toRat + managementFee.toRat := by
  have h := pdCloseFeeCheck_true
  unfold pdCloseFeeCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' payment hpay
      split at h
      · rename_i rate hrate
        split at h
        · rename_i tpo htpo
          split at h
          · rename_i fi hfi
            split at h
            · rename_i fi' hfloor
              split at h
              · rename_i mf hmf
                obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
                exact ⟨l, l', 0, pdCloseFeeAmount, loan, payment, rate, tpo, fi, fi', mf,
                  LendingLedger.Reachable.of_run pdGenesis6 hl, hap, hat, hp, hrate, htpo, hfi, hfloor, hmf,
                  of_decide_eq_true h⟩
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- A deposit of `10^12` into the Scale 2 vault, a broker without a fee, and at close time `1001` a loan of `1001` at
1% with LoanServiceFee `10^17`, in thirty payments 60 seconds apart. -/
private def pdServiceFeeTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-3)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 1001000000000000000, -15⟩ (lwRates 1000)
     { lwFees with serviceFee := ⟨false, 1000000000000000000, -1⟩ } (some 60) (some 30) (some 60) 0 false false,
   .close 1012]

/-- `100000000000000100`, the first totalDue `100000000000000033.4` rounded up to 16 digits. -/
private def pdServiceFeeAmount : Number := ⟨false, 1000000000000001000, -1⟩

/-- At `1012` the first scheduled payment is due more than ⌈PeriodicPayment⌉ + LoanServiceFee. -/
private def pdServiceFeeCheck : Bool :=
  match (pdGenesis pdVault2).run pdServiceFeeTxs with
  | .ok l =>
    match plPay l 0 .regular pdServiceFeeAmount with
    | some (loan, _, _, p) =>
      match loan.unimpaired.paymentComponents .regular l.now,
          STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) with
      | .ok pc, .ok pp' =>
        match pc.totalDue with
        | .ok due => decide (0 < p.count) && decide (loan.unimpaired.paymentRemaining ≠ 1) &&
            decide (pp'.toRat + loan.fees.serviceFee.toRat < due.toRat)
        | .error _ => false
      | _, _ => false
    | none => false
  | .error _ => false

private lemma pdServiceFeeCheck_true : pdServiceFeeCheck = true := by native_decide

/-- A scheduled payment of a LoanPay that is not the last can be due more than ⌈PeriodicPayment⌉ + LoanServiceFee.
With LoanServiceFee `10^17` the 19-digit totalDue rounds ⌈PeriodicPayment⌉ `33.37` up to `33.4`. -/
lemma LendingLedger.regularPayment_amount_fee_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault) (k : Nat)
      (lk : Loan) (pc : PaymentComponents) (due pp' : Number),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) ∧ k < p.count ∧
      loan.ScheduledBefore l.now k lk ∧ lk.paymentComponents .regular l.now = .ok pc ∧ pc.totalDue = .ok due ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ lk.paymentRemaining ≠ 1 ∧ pp'.toRat + loan.fees.serviceFee.toRat < due.toRat := by
  have h := pdServiceFeeCheck_true
  unfold pdServiceFeeCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      split at h
      · rename_i pc pp' hpc hpp
        split at h
        · rename_i due hdue
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hk, hrem⟩, hbad⟩ := h
          obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
          exact ⟨l, l', 0, pdServiceFeeAmount, loan, p, 0, loan.unimpaired, pc, due, pp',
            LendingLedger.Reachable.of_run pdGenesis2 hl, hap, hat, hp, hk, .first, hpc, hdue, hpp, hrem, hbad⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- A deposit of `10^6` into the Scale 8 vault, a broker with a 0.1% management fee, and at close time `1001` the
loan of `190.623` at 12% over 36 monthly payments. -/
private def pdLastTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-9)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, some 100, none, none⟩,
   .loanSet 0 ⟨false, 1906230000000000000, -16⟩ (lwRates 12000) lwFees (some 2592000) (some 36) (some 60) 0 false
     false]

/-- A close to loan 0's next due date, then a LoanPay of exactly its next totalDue. Irreducible, so the run's
equations never unfold the payment. -/
@[irreducible] private def pdStep (l : LendingLedger) : Option LendingLedger :=
  match plLoan l 0 with
  | some loan =>
    match loan.paymentComponents .regular loan.nextPaymentDueDate with
    | .ok pc =>
      match pc.totalDue with
      | .ok due =>
        match (l.apply (.close loan.nextPaymentDueDate)).run with
        | .ok (.ok l₁) =>
          match (l₁.apply (.loanPay 0 .regular due)).run with
          | .ok (.ok l₂) => some l₂
          | _ => none
        | _ => none
      | .error _ => none
    | .error _ => none
  | none => none

private lemma pdStep_reachable {l l' : LendingLedger} (hr : l.Reachable) (h : pdStep l = some l') : l'.Reachable := by
  unfold pdStep at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i l₁ h₁
          split at h
          · rename_i l₂ h₂
            obtain rfl := Option.some.inj h
            exact (hr.apply h₁).apply h₂
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- `n` steps of `pdStep`. -/
private def pdSteps : Nat → LendingLedger → Option LendingLedger
  | 0, l => some l
  | n + 1, l =>
    match pdStep l with
    | some l' => pdSteps n l'
    | none => none

private lemma pdSteps_reachable : ∀ (n : Nat) (l l' : LendingLedger), l.Reachable → pdSteps n l = some l' →
    l'.Reachable := by
  intro n
  induction n with
  | zero =>
    intro l l' hr h
    rw [pdSteps] at h
    obtain rfl := Option.some.inj h
    exact hr
  | succ n ih =>
    intro l l' hr h
    rw [pdSteps] at h
    split at h
    · rename_i l₁ h₁
      exact ih l₁ l' (pdStep_reachable hr h₁) h
    · cases h

/-- After 35 payments of the loan of `190.623`, at its last due date, the last scheduled payment is due more than
⌈PeriodicPayment⌉ + LoanServiceFee, and a LoanPay of exactly that amount succeeds. -/
private def pdLastCheck : Bool :=
  match (pdGenesis pdVault8).run pdLastTxs with
  | .ok l₀ =>
    match pdSteps 35 l₀ with
    | some l₁ =>
      match plLoan l₁ 0 with
      | some loan₁ =>
        match (l₁.apply (.close loan₁.nextPaymentDueDate)).run with
        | .ok (.ok l) =>
          match loan₁.unimpaired.paymentComponents .regular l.now with
          | .ok pc =>
            match pc.totalDue with
            | .ok due =>
              match plPay l 0 .regular due with
              | some (loan, _, _, p) =>
                match loan.unimpaired.paymentComponents .regular l.now,
                    STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward
                      (some loan.loanScale) with
                | .ok pc', .ok pp' =>
                  match pc'.totalDue with
                  | .ok due' => decide (0 < p.count) && decide (p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale) &&
                      decide (pp'.toRat + loan.fees.serviceFee.toRat < due'.toRat)
                  | .error _ => false
                | _, _ => false
              | none => false
            | .error _ => false
          | .error _ => false
        | _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma pdLastCheck_true : pdLastCheck = true := by native_decide

/-- The last scheduled payment of a LoanPay can be due more than ⌈PeriodicPayment⌉ + LoanServiceFee. The loan of
`190.623` owes `6.31645547` after 35 of its 36 monthly payments, ⌈PeriodicPayment⌉ is `6.31645546`. -/
lemma LendingLedger.regularPayment_amount_last_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (p : UnsettledPayment Vault) (k : Nat)
      (lk : Loan) (pc : PaymentComponents) (due pp' : Number),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) ∧ k < p.count ∧
      loan.ScheduledBefore l.now k lk ∧ lk.paymentComponents .regular l.now = .ok pc ∧ pc.totalDue = .ok due ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ p.totalPaid.toRat < 10 ^ 16 * 10 ^ loan.loanScale ∧
      pp'.toRat + loan.fees.serviceFee.toRat < due.toRat := by
  have h := pdLastCheck_true
  unfold pdLastCheck at h
  split at h
  case h_2 => cases h
  rename_i l₀ hl₀
  split at h
  case h_2 => cases h
  rename_i l₁ hl₁
  split at h
  case h_2 => cases h
  rename_i loan₁ _
  split at h
  case h_2 => cases h
  rename_i l hcl
  split at h
  case h_2 => cases h
  split at h
  case h_2 => cases h
  rename_i due₀ _
  split at h
  case h_2 => cases h
  rename_i loan l' loan' p hpay
  split at h
  case h_2 => cases h
  rename_i pc pp' hpc hpp
  split at h
  case h_2 => cases h
  rename_i due hdue
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hk, hfit⟩, hbad⟩ := h
  have hr₁ := pdSteps_reachable 35 l₀ l₁ (LendingLedger.Reachable.of_run pdGenesis8 hl₀) hl₁
  obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
  exact ⟨l, l', 0, due₀, loan, p, 0, loan.unimpaired, pc, due, pp', hr₁.apply hcl, hap, hat, hp, hk, .first, hpc,
    hdue, hpp, hfit, hbad⟩

private def pdVault0 : Vault := ⟨pdRawVault 0, by native_decide, by native_decide⟩

private lemma pdGenesis0 : (pdGenesis pdVault0).Genesis where
  created := ⟨some 0, none, pdSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨pdVault0.wf, pdVault0.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- A deposit of `10^7`, a broker with ManagementFeeRate `mfr`, and at close time `1001` a loan of `principal` at
InterestRate `rate` over `n` monthly payments. -/
private def pdMonthlyTxs (mfr : TenthBips16) (principal : Number) (rate : TenthBips32) (n : UInt32) : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-8)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, some mfr, none, none⟩,
   .loanSet 0 principal (lwRates rate) lwFees (some 2592000) (some n) (some 60) 0 false false]

/-- After `k` payments on schedule, at loan 0's next due date, a LoanPay of exactly its next totalDue succeeds, and
`P` holds for the loan, the loan without its impaired flag and the first scheduled payment it pays. -/
private def pdNextCheck (v : Vault) (txs : List LendingTx) (k : Nat)
    (P : Loan → Loan → UnsettledPayment Vault → Bool) : Bool :=
  match (pdGenesis v).run txs with
  | .ok l₀ =>
    match pdSteps k l₀ with
    | some l₁ =>
      match plLoan l₁ 0 with
      | some loan₁ =>
        match (l₁.apply (.close loan₁.nextPaymentDueDate)).run with
        | .ok (.ok l) =>
          match loan₁.unimpaired.paymentComponents .regular l.now with
          | .ok pc₁ =>
            match pc₁.totalDue with
            | .ok due₁ =>
              match plPay l 0 .regular due₁ with
              | some (loan, _, _, p) =>
                match loan.unimpaired.paymentComponents .regular l.now with
                | .ok pc =>
                  match pc.totalDue with
                  | .ok due =>
                    match (loan.unimpaired.payInstalment l.vault pc due).run with
                    | .ok (.ok q) => decide (0 < p.count) && P loan loan.unimpaired q
                    | _ => false
                  | .error _ => false
                | .error _ => false
              | none => false
            | .error _ => false
          | .error _ => false
        | _ => false
      | none => false
    | none => false
  | .error _ => false

private lemma pdNextCheck_spec {v : Vault} (hg : (pdGenesis v).Genesis) {txs : List LendingTx} {k : Nat}
    {P : Loan → Loan → UnsettledPayment Vault → Bool} (h : pdNextCheck v txs k P = true) :
    ∃ (l l' : LendingLedger) (amount : Number) (loan : Loan) (pc : PaymentComponents) (q : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay 0 .regular amount)).run = .ok (.ok l') ∧ l.LoanAt 0 loan ∧
      loan.PaysInstalment l.vault amount l.now .regular loan.unimpaired pc q ∧ P loan loan.unimpaired q = true := by
  unfold pdNextCheck at h
  split at h
  case h_2 => cases h
  rename_i l₀ hl₀
  split at h
  case h_2 => cases h
  rename_i l₁ hl₁
  split at h
  case h_2 => cases h
  split at h
  case h_2 => cases h
  rename_i l hcl
  split at h
  case h_2 => cases h
  split at h
  case h_2 => cases h
  rename_i due₁ _
  split at h
  case h_2 => cases h
  rename_i loan l' loan' p hpay
  split at h
  case h_2 => cases h
  rename_i pc hpc
  split at h
  case h_2 => cases h
  rename_i due hdue
  split at h
  case h_2 => cases h
  rename_i q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, hP⟩ := h
  have hr₁ := pdSteps_reachable k l₀ l₁ (LendingLedger.Reachable.of_run hg hl₀) hl₁
  obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
  exact ⟨l, l', due₁, loan, pc, q, hr₁.apply hcl, hap, hat, .scheduled hp hk .first hpc hdue hq, hP⟩

/-- The scheduled payment leaves payments, and it takes at least 1 ULP at LoanScale less than PeriodicPayment off
TotalValueOutstanding. -/
private def pdBelow (loan lk : Loan) (q : UnsettledPayment Vault) : Bool :=
  decide (q.loan.paymentRemaining ≠ 0) &&
    decide ((10 : ℚ) ^ loan.loanScale ≤
      loan.periodicPayment.toRat - (lk.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat))

/-- The scheduled payment is the last, and `c` holds for TotalValueOutstanding before it, ⌈PeriodicPayment⌉ and
1 ULP at LoanScale. -/
private def pdLast (c : ℚ → ℚ → ℚ → Bool) (loan lk : Loan) (q : UnsettledPayment Vault) : Bool :=
  match STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) with
  | .ok pp' => decide (q.loan.paymentRemaining = 0) && c lk.totalValueOutstanding.toRat pp'.toRat (10 ^ loan.loanScale)
  | .error _ => false

/-- The loan of `0.048832` at 15% over 3 monthly payments without a management fee: its second payment takes
`0.016679`, more than 1 ULP below PeriodicPayment `0.0166803315…`. -/
private lemma pdBelowCheck_true :
    pdNextCheck pdVault6 (pdMonthlyTxs 0 ⟨false, 4883200000000000000, -20⟩ 15000 3) 1 pdBelow = true := by
  native_decide

/-- The loan of `98763` at 21% over 2 monthly payments with a 6% management fee: its last payment is `50665`,
⌈PeriodicPayment⌉ is `50664`. -/
private lemma pdLastAboveCheck_true :
    pdNextCheck pdVault0 (pdMonthlyTxs 6000 ⟨false, 9876300000000000000, -14⟩ 21000 2) 1
      (pdLast fun T pp _ => decide (0 < T - pp)) = true := by
  native_decide

/-- The loan of `6188` at 9% over 3 monthly payments with a 3% management fee: its last payment is `2092`,
⌈PeriodicPayment⌉ is `2094`. -/
private lemma pdLastBelowCheck_true :
    pdNextCheck pdVault0 (pdMonthlyTxs 3000 ⟨false, 6188000000000000000, -15⟩ 9000 3) 2
      (pdLast fun T pp u => decide (u < pp - T)) = true := by
  native_decide

/-- A scheduled payment that isn't the last can take 1 ULP at LoanScale or more below PeriodicPayment. The second
payment of the loan of `0.048832` takes `0.016679`, PeriodicPayment is `0.0166803315…`. -/
lemma LendingLedger.regularPayment_periodicPayment_below_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan lk : Loan) (pc : PaymentComponents)
      (q : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      loan.PaysInstalment l.vault amount l.now .regular lk pc q ∧ q.loan.paymentRemaining ≠ 0 ∧
      10 ^ loan.loanScale ≤ loan.periodicPayment.toRat -
        (lk.totalValueOutstanding.toRat - q.loan.totalValueOutstanding.toRat) := by
  obtain ⟨l, l', amount, loan, pc, q, hr, hap, hat, hq, hP⟩ := pdNextCheck_spec pdGenesis6 pdBelowCheck_true
  simp only [pdBelow, Bool.and_eq_true, decide_eq_true_eq] at hP
  exact ⟨l, l', 0, amount, loan, loan.unimpaired, pc, q, hr, hap, hat, hq, hP.1, hP.2⟩

/-- The last scheduled payment can be more than ⌈PeriodicPayment⌉. The loan of `98763` owes `50665` for its last
payment, ⌈PeriodicPayment⌉ is `50664`. -/
lemma LendingLedger.regularPayment_periodicPayment_last_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan lk : Loan) (pc : PaymentComponents)
      (q : UnsettledPayment Vault) (pp' : Number),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      loan.PaysInstalment l.vault amount l.now .regular lk pc q ∧ q.loan.paymentRemaining = 0 ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ 0 < lk.totalValueOutstanding.toRat - pp'.toRat := by
  obtain ⟨l, l', amount, loan, pc, q, hr, hap, hat, hq, hP⟩ := pdNextCheck_spec pdGenesis0 pdLastAboveCheck_true
  unfold pdLast at hP
  split at hP
  case h_2 => cases hP
  rename_i pp' hpp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  exact ⟨l, l', 0, amount, loan, loan.unimpaired, pc, q, pp', hr, hap, hat, hq, hP.1, hpp, hP.2⟩

/-- The last scheduled payment can be more than 1 ULP at LoanScale below ⌈PeriodicPayment⌉. The loan of `6188` owes
`2092` for its last payment, ⌈PeriodicPayment⌉ is `2094`. -/
lemma LendingLedger.regularPayment_periodicPayment_last_below_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan lk : Loan) (pc : PaymentComponents)
      (q : UnsettledPayment Vault) (pp' : Number),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      loan.PaysInstalment l.vault amount l.now .regular lk pc q ∧ q.loan.paymentRemaining = 0 ∧
      STAmount.roundToNumericType loan.broker.numericType loan.periodicPayment .upward (some loan.loanScale) =
        .ok pp' ∧ 10 ^ loan.loanScale < pp'.toRat - lk.totalValueOutstanding.toRat := by
  obtain ⟨l, l', amount, loan, pc, q, hr, hap, hat, hq, hP⟩ := pdNextCheck_spec pdGenesis0 pdLastBelowCheck_true
  unfold pdLast at hP
  split at hP
  case h_2 => cases hP
  rename_i pp' hpp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  exact ⟨l, l', 0, amount, loan, loan.unimpaired, pc, q, pp', hr, hap, hat, hq, hP.1, hpp, hP.2⟩

/-- A deposit of `10^13` into the Scale 0 vault, a broker without a fee, and at close time `1001` a loan of `10^12` at
1% over 12 monthly payments that allows overpayments, with LoanServiceFee `10^25` and OverpaymentFee 0.001%. -/
private def pdOverFeeTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-2)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 1000000000000000000, -6⟩ { lwRates 1000 with overpaymentFee := 1 }
     { lwFees with serviceFee := ⟨false, 1000000000000000000, 7⟩ } (some 2592000) (some 12) (some 60) 0 false true]

/-- `10^25 + 10^11`, the first totalDue and an extra part of about `1.6·10^10`. -/
private def pdOverFeeAmount : Number := ⟨false, 1000000000000010000, 7⟩

/-- At the first due date an overpayment of `pdOverFeeAmount` differs from the regular payment of it, and its
feePaid misses the fee of its extra part. -/
private def pdOverFeeCheck : Bool :=
  match (pdGenesis pdVault0).run pdOverFeeTxs with
  | .ok l₀ =>
    match plLoan l₀ 0 with
    | some loan₀ =>
      match (l₀.apply (.close loan₀.nextPaymentDueDate)).run with
      | .ok (.ok l) =>
        match plPay l 0 .overpayment pdOverFeeAmount, (l.apply (.loanPay 0 .regular pdOverFeeAmount)).run with
        | some (loan, l', _, p), .ok (.ok l₂) =>
          match (loan.payInstalments l.vault .regular pdOverFeeAmount l.now).run,
              STAmount.roundToNumericType loan.broker.numericType pdOverFeeAmount .towards_zero
                (some loan.loanScale) with
          | .ok (.ok payment), .ok amount' =>
            match amount'.operator_sub payment.totalPaid .to_nearest with
            | .ok unspent =>
              match STAmount.roundToNumericType loan.broker.numericType
                  (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) with
              | .ok extra =>
                match tenthBipsOfValue extra loan.rates.overpaymentFee .to_nearest,
                    tenthBipsOfValue extra loan.rates.overpaymentInterestRate .to_nearest with
                | .ok f, .ok i =>
                  match STAmount.roundToNumericType loan.broker.numericType f .to_nearest (some loan.loanScale),
                      STAmount.roundToNumericType loan.broker.numericType i .to_nearest (some loan.loanScale) with
                  | .ok fee, .ok i' =>
                    match computeManagementFee loan.broker.numericType i' loan.broker.managementFeeRate
                        loan.loanScale with
                    | .ok mf =>
                      decide (l'.vault.assetsAvailable.toRat ≠ l₂.vault.assetsAvailable.toRat) &&
                        decide (p.amounts.feePaid.toRat ≠ payment.amounts.feePaid.toRat + fee.toRat + mf.toRat)
                    | .error _ => false
                  | _, _ => false
                | _, _ => false
              | .error _ => false
            | .error _ => false
          | _, _ => false
        | _, _ => false
      | _ => false
    | none => false
  | .error _ => false

private lemma pdOverFeeCheck_true : pdOverFeeCheck = true := by native_decide

/-- An overpayment's feePaid can miss the fee of its extra part. With LoanServiceFee `10^25` the fees keep 19
digits, and the fee of about `1.6·10^5` on an extra part of about `1.6·10^10` rounds away. -/
lemma LendingLedger.overpayment_fees_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (payment p : UnsettledPayment Vault)
      (amount' unspent extra f fee interest interest' managementFee : Number),
      l.Reachable ∧ (l.apply (.loanPay i .overpayment amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) ∧
      (loan.payInstalments l.vault .overpayment amount l.now).run = .ok (.ok p) ∧
      (l.apply (.loanPay i .overpayment amount)).run ≠ (l.apply (.loanPay i .regular amount)).run ∧
      STAmount.roundToNumericType loan.broker.numericType amount .towards_zero (some loan.loanScale) = .ok amount' ∧
      amount'.operator_sub payment.totalPaid .to_nearest = .ok unspent ∧
      STAmount.roundToNumericType loan.broker.numericType
        (Number.min unspent payment.loan.totalValueOutstanding) .downward (some loan.loanScale) = .ok extra ∧
      tenthBipsOfValue extra loan.rates.overpaymentFee .to_nearest = .ok f ∧
      STAmount.roundToNumericType loan.broker.numericType f .to_nearest (some loan.loanScale) = .ok fee ∧
      tenthBipsOfValue extra loan.rates.overpaymentInterestRate .to_nearest = .ok interest ∧
      STAmount.roundToNumericType loan.broker.numericType interest .to_nearest (some loan.loanScale) =
        .ok interest' ∧
      computeManagementFee loan.broker.numericType interest' loan.broker.managementFeeRate loan.loanScale =
        .ok managementFee ∧
      p.amounts.feePaid.toRat ≠ payment.amounts.feePaid.toRat + fee.toRat + managementFee.toRat := by
  have h := pdOverFeeCheck_true
  unfold pdOverFeeCheck at h
  split at h
  case h_2 => cases h
  rename_i l₀ hl₀
  split at h
  case h_2 => cases h
  split at h
  case h_2 => cases h
  rename_i l hcl
  split at h
  case h_2 => cases h
  rename_i loan l' loan' p l₂ hpay hreg
  split at h
  case h_2 => cases h
  rename_i payment amount' hp0 hamount
  split at h
  case h_2 => cases h
  rename_i unspent hunspent
  split at h
  case h_2 => cases h
  rename_i extra hextra
  split at h
  case h_2 => cases h
  rename_i f i hf hi
  split at h
  case h_2 => cases h
  rename_i fee i' hfee hi'
  split at h
  case h_2 => cases h
  rename_i mf hmf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hdiff, hbad⟩ := h
  obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
  have hr := (LendingLedger.Reachable.of_run pdGenesis0 hl₀).apply hcl
  refine ⟨l, l', 0, pdOverFeeAmount, loan, payment, p, amount', unspent, extra, f, fee, i, i', mf, hr, hap, hat,
    hp0, hp, ?_, hamount, hunspent, hextra, hf, hfee, hi, hi', hmf, hbad⟩
  intro heq
  rw [hap, hreg] at heq
  obtain rfl := Except.ok.inj (Except.ok.inj heq)
  exact hdiff rfl

end XRPL.Model.Lending
