import XRPL.Properties.Lending.Ledger.Common.PaymentTotal
import XRPL.Properties.Lending.Ledger.Common.PrincipalLeftLedger
import XRPL.Properties.Lending.Loan.Common.NextPayment
import XRPL.Properties.Lending.Loan.Common.Reserved

/-! # An active loan is paid off by its next payments

At one close time, a late loan takes late payments and a loan that is not late takes regular payments. Each pays
exactly the amount due of the loan's next instalment, succeeds under the conditions of `loan_ops_total`, and leaves
fewer payments, so a run of them pays the loan off. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private LendingLedger.Reachable.loan_withBroker from XRPL.Properties.Lending.Ledger.Common.ManageTotal

/-- `L` is reached from `l` by next payments on loan `i`. Each one is of the loan's next payment type and of exactly
the amount due of its next instalment, and succeeds. -/
inductive LendingLedger.PaidFrom (l : LendingLedger) (i : Nat) : LendingLedger → Prop where
  | refl : LendingLedger.PaidFrom l i l
  | step {L L' : LendingLedger} {loan : Loan} {pc : PaymentComponents} {td : Number} :
      LendingLedger.PaidFrom l i L → L.LoanAt i loan →
      loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
      (L.apply (.loanPay i (loan.nextPaymentType L.now) td)).run = .ok (.ok L') → LendingLedger.PaidFrom l i L'

/-- Next payments are a run of payments on the loan. -/
lemma LendingLedger.PaidFrom.reaches {l L : LendingLedger} {i : Nat} (h : l.PaidFrom i L) :
    ∃ txs, LendingLedger.Reaches l txs L ∧ ∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount := by
  induction h with
  | refl => exact ⟨[], .refl, fun _ h => by cases h⟩
  | step _ _ _ _ hok ih =>
    obtain ⟨txs, hreach, hall⟩ := ih
    refine ⟨txs ++ [_], hreach.step _ hok, fun tx htx => ?_⟩
    rcases List.mem_append.mp htx with h | h
    · exact hall tx h
    · rw [List.mem_singleton.mp h]; exact ⟨_, _, rfl⟩

/-- What `loan_ops_total` asks of a payment of loan `i` of exactly `td` besides its checks: the preflight, a vault that
is not coarsened, no negative interest part, a credit or a payoff, and a cover, credit and fee that fit the asset. -/
structure LendingLedger.PaymentConditions (L : LendingLedger) (i : Nat) (loan : Loan) (pt : LoanPaymentType)
    (td : Number) : Prop where
  preflight : (LendingTx.loanPay i pt td).preflight L = .tesSUCCESS
  total : L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent
  parts : ∀ p, (loan.payInstalments L.vault pt td L.now).run = .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat
  credit : ∀ p, (loan.payInstalments L.vault pt td L.now).run = .ok (.ok p) →
    0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0
  cover : loan.broker.coverAvailable.toRat < 10 ^ 96
  creditFits : L.CreditFits i pt td
  feeFits : L.FeeFits i pt td

/-- The terms of `principal_left`: InterestRate at most 80%, a PaymentInterval of at least two hours, or at most 25
years of payments. -/
def Loan.FallingFactorTerms (rates : LoanRates) (schedule : LoanSchedule) : Prop :=
  rates.interestRate.toNat ≤ 80000 ∨ 7200 ≤ schedule.paymentInterval.toNat ∨
    schedule.paymentTotal.toNat * schedule.paymentInterval.toNat ≤ 25 * 31556952

/-- The next payment of an active loan stored on a reachable ledger succeeds, of exactly the amount due of its
next instalment, and leaves the loan stored with fewer payments, its terms, and no more value owed. -/
private lemma LendingLedger.Reachable.next_payment {L : LendingLedger} (hr : L.Reachable)
    (hnd : L.vaultDeleted = false) {i : Nat} {e : LoanEntry} (he : L.loan? i = some e)
    (hp : e.loan.isPending = false) (hrem : e.loan.paymentRemaining ≠ 0)
    (hterms : Loan.FallingFactorTerms e.loan.rates e.loan.schedule)
    (hxrp : L.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14)
    (hcond : ∀ loan pc td, L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
      loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
      L.PaymentConditions i loan (loan.nextPaymentType L.now) td) :
    ∃ (loan : Loan) (pc : PaymentComponents) (td : Number) (L' : LendingLedger) (e' : LoanEntry), L.LoanAt i loan ∧
      loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc ∧ pc.totalDue = .ok td ∧
      (L.apply (.loanPay i (loan.nextPaymentType L.now) td)).run = .ok (.ok L') ∧ L'.loan? i = some e' ∧
      e'.loan.paymentRemaining < e.loan.paymentRemaining ∧ e'.loan.isPending = false ∧
      e'.loan.rates = e.loan.rates ∧ e'.loan.schedule = e.loan.schedule ∧
      e'.loan.totalValueOutstanding.toRat ≤ e.loan.totalValueOutstanding.toRat := by
  obtain ⟨b, loan, hb, hw, hraw⟩ := LendingLedger.Reachable.loan_withBroker hr he
  have hat : L.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  have epr : loan.paymentRemaining = e.loan.paymentRemaining := (congrArg RawLoan.paymentRemaining hraw :)
  have ep : loan.isPending = e.loan.isPending := (congrArg RawLoan.isPending hraw :)
  have erates : loan.rates = e.loan.rates := (congrArg RawLoan.rates hraw :)
  have esched : loan.schedule = e.loan.schedule := (congrArg RawLoan.schedule hraw :)
  have eT : loan.totalValueOutstanding = e.loan.totalValueOutstanding :=
    (congrArg RawLoan.totalValueOutstanding hraw :)
  have elb : loan.broker = b := (congrArg RawLoan.broker hraw :)
  have hrem' : loan.paymentRemaining ≠ 0 := by rw [epr]; exact hrem
  have hp' : loan.isPending = false := by rw [ep]; exact hp
  have hpo := Loan.principal_left_proof L hr i loan hat (by rw [erates, esched]; exact hterms) hrem'
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨-, hnt⟩ := hr.loanAt_scale hat
  have hroom := hr.loopRoom hat (fun h => by have := hxrp h; rw [eT]; linarith)
  obtain ⟨-, -, bL, -, -, -⟩ := hreach.fees_below
  obtain ⟨pc, td, hpc, htd⟩ := hroom.nextPayment_computes L.now hrem' (fun h => by
    rw [hnt] at h; rw [eT]; exact hxrp h) bL
  have hpt : loan.nextPaymentType L.now = .late ∨ loan.nextPaymentType L.now = .regular := by
    unfold Loan.nextPaymentType; split <;> simp
  have hc : loan.canPay (loan.nextPaymentType L.now) = .tesSUCCESS :=
    Loan.canPay_success_proof loan _ hp' (fun h => by rcases hpt with h' | h' <;> rw [h'] at h <;> cases h) hrem'
      hpo
  have hlate : loan.nextPaymentType L.now = .late ↔ loan.isPaymentLate L.now = true := by
    unfold Loan.nextPaymentType; cases loan.isPaymentLate L.now <;> simp
  have hfull : loan.nextPaymentType L.now = .full → loan.paymentRemaining ≠ 1 := by
    intro h; rcases hpt with h' | h' <;> rw [h'] at h <;> cases h
  have hcd := hcond loan pc td hat hrem' hpc htd
  obtain ⟨L', hL'⟩ := LendingLedger.payment_total_proof L hr hnd i e b loan _ pc td td he hb hw hc hlate hfull hpc
    htd le_rfl (fun _ => rfl) hcd.preflight hcd.total hcd.parts hcd.credit
    (fun h => by have := hxrp h; rw [eT]; linarith)
    (by rw [← elb]; exact hcd.cover) hcd.creditFits hcd.feeFits
  obtain ⟨u, hu, hL'u⟩ := LendingLedger.apply_loan rfl hL'
  obtain ⟨e0, b0, loan0, r, he0, hb0, hw0, -, hok, hueq⟩ := LendingLedger.applyLoan_pay_inv L u i _ td hu
  rw [he] at he0
  obtain rfl := Option.some.inj he0
  rw [hb] at hb0
  obtain rfl := Option.some.inj hb0
  rw [hw] at hw0
  obtain rfl := Except.ok.inj hw0
  have hL'i : L'.loan? i = some { e with loan := r.loan' } := by
    rw [hL'u, LendingLedger.loan?_commitLoan, hueq]
    simp [LoanEffect.ofLoan, LendingLedger.loan?_lt he]
  have hkt := Loan.pay_keepsTerms loan _ L.vault td L.now r hok
  refine ⟨loan, pc, td, L', { e with loan := r.loan' }, hat, hpc, htd, hL', hL'i, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← epr]; exact Loan.payment_paymentRemaining_decreases (hok := hok)
  · show r.loan'.isPending = false
    rw [Loan.pay_isPending loan L.vault _ td L.now r hok]; exact hp'
  · show r.loan'.rates = e.loan.rates
    rw [hkt.rates, erates]
  · show r.loan'.schedule = e.loan.schedule
    rw [hkt.schedule, esched]
  · show r.loan'.totalValueOutstanding.toRat ≤ _
    rw [← eT]; exact (Loan.pay_outstanding_le loan L.vault _ td L.now r hok).2.1

/-- Next payments pay a loan off, from any ledger the payments reach that stores it active with the terms and
at most the value it started with. -/
private lemma LendingLedger.payoff_run (l : LendingLedger) (i : Nat) (e₀ : LoanEntry)
    (hterms : Loan.FallingFactorTerms e₀.loan.rates e₀.loan.schedule)
    (hxrp : l.vault.numericType = .native → e₀.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14)
    (hrun : ∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
      loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
      L.PaymentConditions i loan (loan.nextPaymentType L.now) td) :
    ∀ (n : ℕ) (L : LendingLedger) (e : LoanEntry), e.loan.paymentRemaining.toNat = n → l.PaidFrom i L →
      L.Reachable → L.vaultDeleted = false → L.vault.numericType = l.vault.numericType → L.loan? i = some e →
      e.loan.isPending = false → e.loan.rates = e₀.loan.rates → e.loan.schedule = e₀.loan.schedule →
      e.loan.totalValueOutstanding.toRat ≤ e₀.loan.totalValueOutstanding.toRat →
      ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
        e'.loan.paymentRemaining = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L e hn hPF hrL hndL hntL he hp hrates hsched hT
    by_cases h0 : e.loan.paymentRemaining = 0
    · obtain ⟨txs, hreach, hall⟩ := hPF.reaches
      exact ⟨txs, L, e, hreach, hall, he, h0⟩
    obtain ⟨loan, pc, td, L', e', hat, hpc, htd, hL', he', hlt, hp', hrates', hsched', hT'⟩ :=
      hrL.next_payment hndL he hp h0 (by rw [hrates, hsched]; exact hterms)
        (fun h => by rw [hntL] at h; have := hxrp h; linarith)
        (fun loan pc td hat hpr hpc htd => hrun L loan pc td hPF hat hpr hpc htd)
    have hPF' : l.PaidFrom i L' := .step hPF hat hpc htd hL'
    have hnd' : L'.vaultDeleted = false := by
      obtain ⟨u, -, rfl⟩ := LendingLedger.apply_loan rfl hL'
      exact hndL
    exact ih e'.loan.paymentRemaining.toNat (by rw [← hn]; exact UInt32.lt_iff_toNat_lt.mp hlt) L' e' rfl hPF'
      (hrL.apply hL') hnd' (by rw [LendingLedger.apply_numericType hL', hntL]) he' hp' (by rw [hrates', hrates])
      (by rw [hsched', hsched]) (le_trans hT' hT)

/-- Proof body of the paid-off line of `Lending.Reachable.payoff_reachable`. -/
lemma LendingLedger.payoff_reachable_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e) (hp : e.loan.isPending = false)
    (hterms : Loan.FallingFactorTerms e.loan.rates e.loan.schedule)
    (hxrp : l.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14)
    (hrun : ∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
      loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
      L.PaymentConditions i loan (loan.nextPaymentType L.now) td) :
    ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
      (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
      e'.loan.paymentRemaining = 0 :=
  LendingLedger.payoff_run l i e hterms hxrp hrun _ l e rfl .refl hr hnd rfl he hp rfl rfl le_rfl

end XRPL.Model.Lending
