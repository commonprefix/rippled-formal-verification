import XRPL.Properties.Lending.Loan.Common.PayReachableWitness
import XRPL.Properties.Lending.Loan.Common.ZeroValueWitness
import XRPL.Properties.Lending.Loan.Common.SeparatePaymentsWitness
import XRPL.Properties.Lending.Loan.Common.PayLedger

/-! # Witnesses for LoanPay transactions on reachable ledgers

Runs of the existing ledger fixtures, then one LoanPay transaction, checked by `native_decide`. The loan of
`603946999675283.3` on a Scale 1 vault, the loan of 6 at 14.5% on a Scale 0 vault, and loan D of 3 on the coarsened
vault. A payment amount that a 16-digit asset amount cannot hold is rounded up to one it can. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private pwLoanTxs pwCoverTxs pwDue pwLate from XRPL.Properties.Lending.Loan.Common.PayReachableWitness
open private zvGenesis zvGenesis_genesis zvTxs zvOne from XRPL.Properties.Lending.Loan.Common.ZeroValueWitness
open private spTxs spHalf spWhole from XRPL.Properties.Lending.Loan.Common.SeparatePaymentsWitness

/-- The loan at `i` read with its broker's ledger copy, as every loan transaction reads it. -/
private def plLoan (l : LendingLedger) (i : Nat) : Option Loan :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b => (e.loan.withBroker b).toOption
    | none => none
  | none => none

private lemma plLoan_loanAt {l : LendingLedger} {i : Nat} {loan : Loan} (h : plLoan l i = some loan) :
    l.LoanAt i loan := by
  unfold plLoan at h
  split at h
  · rename_i e he
    split at h
    · rename_i b hb
      refine ⟨e, b, he, hb, ?_⟩
      cases hw : e.loan.withBroker b with
      | error _ => rw [hw] at h; cases h
      | ok loan' => rw [hw] at h; cases h; rfl
    · cases h
  · cases h

/-- A LoanPay of `amount` on loan `i`: the loan read before, the ledger and the loan read after, and the
instalments the payment pays. -/
private def plPay (l : LendingLedger) (i : Nat) (pt : LoanPaymentType) (amount : Number) :
    Option (Loan × LendingLedger × Loan × UnsettledPayment Vault) :=
  match plLoan l i, (l.apply (.loanPay i pt amount)).run with
  | some loan, .ok (.ok l') =>
    match plLoan l' i, (loan.payInstalments l.vault pt amount l.now).run with
    | some loan', .ok (.ok p) => some (loan, l', loan', p)
    | _, _ => none
  | _, _ => none

private lemma plPay_spec {l l' : LendingLedger} {i : Nat} {pt : LoanPaymentType} {amount : Number}
    {loan loan' : Loan} {p : UnsettledPayment Vault} (h : plPay l i pt amount = some (loan, l', loan', p)) :
    (l.apply (.loanPay i pt amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧ l'.LoanAt i loan' ∧
      (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) := by
  unfold plPay at h
  split at h
  · rename_i loan₀ l₀ hl hap
    split at h
    · rename_i loan₀' p₀ hl' hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨hap, plLoan_loanAt hl, plLoan_loanAt hl', hp⟩
    · cases h
  · cases h

/-- `19514390684779360`, the late payment 32 years late, its totalDue `19514390684779359.5` rounded up to 16 digits. -/
private def plLateAmount : Number := ⟨false, 1951439068477936000, -2⟩

/-- At the first due date, the first instalment credits the vault exactly principalPaid + interestPaid. -/
private def plVaultEqualCheck : Bool :=
  match cwGenesis.run (pwLoanTxs ++ [.close pwDue]) with
  | .ok l =>
    match plPay l 0 .regular ⟨false, 8655180199939950000, -5⟩ with
    | some (_, l', _, p) => decide ((l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
        (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) = 0)
    | none => false
  | .error _ => false

private lemma plVaultEqualCheck_true : plVaultEqualCheck = true := by native_decide

/-- A LoanPay on a reachable ledger can credit the vault exactly principalPaid + interestPaid. The first instalment
of the loan of `603946999675283.3`, paid at its due date. -/
lemma LendingLedger.payment_vault_upper_bound_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
        (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) = 0 := by
  have h := plVaultEqualCheck_true
  unfold plVaultEqualCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
      exact ⟨l, l', 0, .regular, _, loan, p, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hap, hat, hp,
        of_decide_eq_true h⟩
    · cases h
  · cases h

/-- 32 years late, the late payment credits the vault `1.99` ULP less than principalPaid + interestPaid at the scale
of AssetsAvailable', and AssetsAvailable plus the payment fits a `Number`. -/
private def plVaultLowerCheck : Bool :=
  match cwGenesis.run (pwLoanTxs ++ [.close pwLate]) with
  | .ok l =>
    match plPay l 0 .late plLateAmount with
    | some (_, l', _, p) =>
      match numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType with
      | .ok e =>
        decide (l.vault.assetsAvailable.toRat + (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) <
            2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) &&
          decide (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat -
            (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) = (199 / 100 : ℚ) * 10 ^ e)
      | .error _ => false
    | none => false
  | .error _ => false

private lemma plVaultLowerCheck_true : plVaultLowerCheck = true := by native_decide

/-- A LoanPay on a reachable ledger can credit the vault `1.99` ULP less than principalPaid + interestPaid. The loan
of `603946999675283.3` paid 32 years late lifts AssetsAvailable' to the scale `10^1`. -/
lemma LendingLedger.payment_vault_lower_bound_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      l.vault.assetsAvailable.toRat + (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent ∧
      numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e ∧
      payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat -
        (l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) = (199 / 100 : ℚ) * 10 ^ e := by
  have h := plVaultLowerCheck_true
  unfold plVaultLowerCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      split at h
      · rename_i e he
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
        exact ⟨l, l', 0, .late, _, loan, p, e, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hap, hat, hp,
          h.1, he, h.2⟩
      · cases h
    · cases h
  · cases h

/-- Right after the default the broker is below minCover, and the late payment of the large loan adds exactly
feePaid to its cover. -/
private def plCoverEqualCheck : Bool :=
  match cwGenesis.run pwCoverTxs with
  | .ok l =>
    match plPay l 0 .late ⟨false, 8655297021245700000, -5⟩ with
    | some (loan, _, loan', p) =>
      decide (loan.broker.hasMinimumCover l.vault.baseExponent = .ok false) &&
        decide (loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat <
          2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) &&
        decide ((loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) -
          p.amounts.feePaid.toRat = 0)
    | none => false
  | .error _ => false

private lemma plCoverEqualCheck_true : plCoverEqualCheck = true := by native_decide

/-- A LoanPay on a reachable ledger can add exactly feePaid to the cover of a broker below minCover. The large loan
paid a minute late with a 10% management fee, after a default left the cover at `0.5`. -/
lemma LendingLedger.payment_fees_upper_bound_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan loan' : Loan)
      (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ loan.broker.hasMinimumCover l.vault.baseExponent = .ok false ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      (loan.broker.numericType.isIntegral = true → loan.broker.coverAvailable.toRat +
        payment.amounts.feePaid.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) ∧
      (loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) - payment.amounts.feePaid.toRat = 0 := by
  have h := plCoverEqualCheck_true
  unfold plCoverEqualCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨hap, hat, hat', hp⟩ := plPay_spec hpay
      exact ⟨l, l', 0, .late, _, loan, loan', p, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hap, hat, hat',
        h1, hp, fun _ => h2, h3⟩
    · cases h
  · cases h

/-- The broker is below minCover, and the late payment 32 years late adds a full ULP less than feePaid to its
cover. -/
private def plCoverLowerCheck : Bool :=
  match cwGenesis.run (pwCoverTxs ++ [.close pwLate]) with
  | .ok l =>
    match plPay l 0 .late plLateAmount with
    | some (loan, _, loan', p) =>
      match numberExponent loan'.broker.coverAvailable l.vault.baseExponent loan.broker.numericType with
      | .ok e =>
        decide (loan.broker.hasMinimumCover l.vault.baseExponent = .ok false) &&
          decide (loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat - loan'.broker.coverAvailable.toRat =
            10 ^ e)
      | .error _ => false
    | none => false
  | .error _ => false

private lemma plCoverLowerCheck_true : plCoverLowerCheck = true := by native_decide

/-- A LoanPay on a reachable ledger can add a full ULP less than feePaid to the cover. The large loan paid 32 years
late with a 10% management fee lifts a cover of `0.5` to the scale `10^0`. -/
lemma LendingLedger.payment_fees_lower_bound_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan loan' : Loan)
      (payment : UnsettledPayment Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ loan.broker.hasMinimumCover l.vault.baseExponent = .ok false ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      numberExponent loan'.broker.coverAvailable l.vault.baseExponent loan.broker.numericType = .ok e ∧
      loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat - loan'.broker.coverAvailable.toRat =
        10 ^ e := by
  have h := plCoverLowerCheck_true
  unfold plCoverLowerCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      split at h
      · rename_i e he
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hap, hat, hat', hp⟩ := plPay_spec hpay
        exact ⟨l, l', 0, .late, _, loan, loan', p, e, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hap, hat,
          hat', h.1, hp, he, h.2⟩
      · cases h
    · cases h
  · cases h

/-- The fifth instalment of the loan of 6 has a value delta of 0, and its late payment keeps TotalValueOutstanding
12 and PrincipalOutstanding 6. -/
private def plZeroValueCheck : Bool :=
  match zvGenesis.run zvTxs with
  | .ok l =>
    match plPay l 0 .late zvOne with
    | some (loan, _, loan', _) =>
      match loan.paymentComponents .late l.now with
      | .ok pc =>
        decide (pc.isFinal = false ∧ pc.totalValueDelta.toRat = 0 ∧
          loan'.paymentRemaining < loan.paymentRemaining ∧
          loan'.principalOutstanding = loan.principalOutstanding ∧
          loan'.totalValueOutstanding.toRat = loan.totalValueOutstanding.toRat)
      | .error _ => false
    | none => false
  | .error _ => false

private lemma plZeroValueCheck_true : plZeroValueCheck = true := by native_decide

/-- A late LoanPay on a reachable ledger can leave TotalValueOutstanding and PrincipalOutstanding as they were. Its
instalment's targets equal the loan's amounts, and the late interest alone changes AssetsAvailable. -/
lemma LendingLedger.payment_decreases_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan loan' : Loan) (pc : PaymentComponents),
      l.Reachable ∧ (l.apply (.loanPay i .late amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ loan.paymentComponents .late l.now = .ok pc ∧ pc.isFinal = false ∧
      pc.totalValueDelta.toRat = 0 ∧ loan'.paymentRemaining < loan.paymentRemaining ∧
      loan'.principalOutstanding = loan.principalOutstanding ∧
      loan'.totalValueOutstanding.toRat = loan.totalValueOutstanding.toRat := by
  have h := plZeroValueCheck_true
  unfold plZeroValueCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      split at h
      · rename_i pc hpc
        obtain ⟨h1, h2, h3⟩ := of_decide_eq_true h
        obtain ⟨hap, hat, hat', -⟩ := plPay_spec hpay
        exact ⟨l, l', 0, zvOne, loan, loan', pc, LendingLedger.Reachable.of_run zvGenesis_genesis hl, hap, hat,
          hat', hpc, h1, h2, h3⟩
      · cases h
    · cases h
  · cases h

/-- Loan D paid as one regular payment of both instalments, and as two LoanPay transactions of one instalment
each. The two runs leave different AssetsAvailable. -/
private def plSplitCheck : Bool :=
  match cwGenesis.run spTxs with
  | .error _ => false
  | .ok l =>
    match plPay l 3 .regular spWhole, plPay l 3 .regular spHalf with
    | some (_, l₁, _, payment), some (_, l₃, _, p₁) =>
      match plPay l₃ 3 .regular spHalf with
      | some (_, l₂, _, p₂) =>
        decide (payment.count = 2) && decide (p₁.count = 1) && decide (p₂.count = 1) &&
          decide (l₂.vault.assetsAvailable.toRat ≠ l₁.vault.assetsAvailable.toRat)
      | none => false
    | _, _ => false

private lemma plSplitCheck_true : plSplitCheck = true := by native_decide

/-- Paid together, loan D's two instalments of 1.5 credit a coarsened reachable vault 3, paid apart 1 each. Loan
and broker match apart from CoverAvailable. -/
lemma LendingLedger.regularPayment_split_witness :
    ∃ (l l₁ : LendingLedger) (i : Nat) (amount : Number) (loan loan₁ : Loan) (payment : UnsettledPayment Vault)
      (l₂ : LendingLedger) (loan₂ : Loan),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l₁) ∧ l.LoanAt i loan ∧
      l₁.LoanAt i loan₁ ∧ (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) ∧
      payment.count = 2 ∧ l.SeparatePayments i payment.count l₂ ∧ l₂.LoanAt i loan₂ ∧
      loan₂.toRawLoan = { loan₁.toRawLoan with broker := loan₂.broker } ∧
      loan₂.broker.toRawLoanBroker =
        { loan₁.broker.toRawLoanBroker with coverAvailable := loan₂.broker.coverAvailable } ∧
      l₂.vault ≠ l₁.vault := by
  have h := plSplitCheck_true
  unfold plSplitCheck at h
  split at h
  · cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i loan l₁ loan₁ payment loanA l₃ loanB p₁ hpay hpay₁
  split at h
  case h_2 => cases h
  rename_i loanC l₂ loan₂ p₂ hpay₂
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hc₁⟩, hc₂⟩, hne⟩ := h
  have hr := LendingLedger.Reachable.of_run cwGenesis_genesis hl
  obtain ⟨hap, hat, hat₁, hp⟩ := plPay_spec hpay
  obtain ⟨hap₁, hatA, -, hp₁⟩ := plPay_spec hpay₁
  obtain ⟨hap₂, hatB, hat₂, hp₂⟩ := plPay_spec hpay₂
  obtain rfl : loan = loanA := (LendingLedger.LoanAt.eq hatA hat).symm
  have hsep : l.SeparatePayments 3 payment.count l₂ := by
    rw [hc]
    exact .step loan spHalf p₁ hat hp₁ hc₁ hap₁ (.step loanC spHalf p₂ hatB hp₂ hc₂ hap₂ (.refl l₂))
  obtain ⟨r, hok, rfl, hv⟩ := LendingLedger.loanPay_loans hap hat hat₁
  obtain ⟨-, -, hraw, hbroker⟩ := Loan.regularPayment_split_loan hr hat hp hok hsep hat₂
  exact ⟨l, l₁, 3, spWhole, loan, r.loan', payment, l₂, loan₂, hr, hap, hat, hat₁, hp, hc, hsep, hat₂, hraw, hbroker,
    fun hv' => hne (by rw [hv', hv])⟩

/-- The coarsened run with loan D of 1.5 at InterestRate 10% in one instalment, due after the vault coarsens. -/
private def plYieldTxs : List LendingTx :=
  cwTxs.take 8 ++
  [.loanSet 0 ⟨false, 1500000000000000000, -18⟩ { cwRates 0 with interestRate := 10000 } cwFees (some 70000000)
     (some 1) (some 60) 0 false false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩]

/-- Loan D's regular payment of 1.9 is credited to the coarsened vault as 1, so AssetsTotal grows by less than the
interest it pays. -/
private def plYieldCheck : Bool :=
  match cwGenesis.run plYieldTxs with
  | .ok l =>
    match plPay l 3 .regular ⟨false, 1900000000000000000, -18⟩ with
    | some (_, l', _, p) =>
      decide (l'.vault.toExact.assetsTotal - l.vault.toExact.assetsTotal < p.amounts.interestPaid.toRat)
    | none => false
  | .error _ => false

private lemma plYieldCheck_true : plYieldCheck = true := by native_decide

/-- A regular LoanPay on a reachable coarsened vault can raise AssetsTotal by less than interestPaid. Loan D's
instalment of 1.9 is credited as 1, so AssetsTotal falls by 0.5 while interestPaid is 0.4. -/
lemma LendingLedger.regularPayment_yield_witness :
    ∃ (l l' : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment) ∧
      l'.vault.toExact.assetsTotal - l.vault.toExact.assetsTotal < payment.amounts.interestPaid.toRat := by
  have h := plYieldCheck_true
  unfold plYieldCheck at h
  split at h
  · rename_i l hl
    split at h
    · rename_i loan l' loan' p hpay
      obtain ⟨hap, hat, -, hp⟩ := plPay_spec hpay
      exact ⟨l, l', 3, _, loan, p, LendingLedger.Reachable.of_run cwGenesis_genesis hl, hap, hat, hp,
        of_decide_eq_true h⟩
    · cases h
  · cases h

end XRPL.Model.Lending
