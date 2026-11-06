import XRPL.Properties.Lending.Ledger.Common.PayoffRun
import XRPL.Properties.Lending.Ledger.Common.PaymentTotalWitness

/-! # Reachable late loans no payment can pay off

Three late loans whose late payment of exactly totalDue fails, each for one reason: the coarsened vault of loan C,
the negative interest part of a tiny-rate instalment, and an instalment that is only management fee. A smaller
amount is too little, a larger one makes the same payment, and the other payment types are rejected, so no run of
payments moves the loan. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private niGenesis niTxs niGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness
open private foGenesis foTxs foGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.PaymentTotalWitness

/-- After `txs` loan `j` is late, active and takes no overpayment, and its late payment of exactly totalDue
passes its checks and the conditions asked for, and fails. -/
private def stuckCheck (g : LendingLedger) (txs : List LendingTx) (j : Nat) (total parts credit : Bool) : Bool :=
  match g.run txs with
  | .ok l =>
    match l.loan? j with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          match loan.paymentComponents .late l.now with
          | .ok pc =>
            match pc.totalDue with
            | .ok td =>
              !l.vaultDeleted && decide (b.coverAvailable.toRat < 10 ^ 96) &&
                decide ((LendingTx.loanPay j .late td).preflight l = .tesSUCCESS) &&
                decide (l.vault.numericType = .fractional) &&
                decide (loan.nextPaymentDueDate < l.now) && loan.nextPaymentDueDate != 0 &&
                loan.paymentRemaining != 0 && loan.principalOutstanding != Number.zero &&
                !loan.allowsOverpayment && !loan.isPending && !loan.isImpaired && !td.operator_lt td &&
                decide (loan.rates.interestRate.toNat ≤ 80000) &&
                (!total || decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
                  10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)) &&
                (match (loan.payInstalments l.vault .late td l.now).run with
                  | .ok (.ok p) =>
                    decide (loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 89) &&
                      (!parts || decide (0 ≤ p.amounts.interestPaid.toRat)) &&
                      (!credit || decide (0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨
                        p.loan.paymentRemaining = 0))
                  | _ => true) &&
                (match (loan.latePayment l.vault td l.now).run with
                  | .ok (.ok _) => false
                  | _ => true)
            | .error _ => false
          | .error _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

/-- A run whose check passes gives a reachable late loan that no payment can pay, with the conditions of its
late payment of exactly totalDue that the check asked for. -/
private lemma LendingLedger.stuckCheck_sound {g : LendingLedger} (hg : g.Genesis) {txs : List LendingTx} {j : Nat}
    {total parts credit : Bool} (h : stuckCheck g txs j total parts credit = true) :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? j = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
        e.loan.paymentRemaining ≠ 0 ∧ e.loan.isPending = false ∧
        Loan.FallingFactorTerms e.loan.rates e.loan.schedule ∧ l.vault.numericType = .fractional ∧
        loan.isPaymentLate l.now = true ∧ loan.paymentComponents .late l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (LendingTx.loanPay j .late td).preflight l = .tesSUCCESS ∧
        (total = true → l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
          10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) ∧
        (parts = true → ∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) →
          0 ≤ p.amounts.interestPaid.toRat) ∧
        (credit = true → ∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        loan.broker.coverAvailable.toRat < 10 ^ 96 ∧ l.CreditFits j .late td ∧ l.FeeFits j .late td ∧
        ∀ (pt : LoanPaymentType) (amount : Number) (l' : LendingLedger),
          (l.apply (.loanPay j pt amount)).run ≠ .ok (.ok l') := by
  unfold stuckCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan hw
  split at h
  case h_2 => cases h
  rename_i pc hpc
  split at h
  case h_2 => cases h
  rename_i td htd
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hnd, hca⟩, hpre⟩, hfrac⟩, hlate⟩, hdue⟩, hrem⟩, hpo⟩, hao⟩, hpend⟩, himp⟩, hirr⟩, hrate⟩,
    htot⟩, hinst⟩, hfail⟩ := h
  have hraw := Loan.withBroker_eq hw
  have hlb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]
  have hrem' : loan.paymentRemaining = e.loan.paymentRemaining := (congrArg RawLoan.paymentRemaining hraw :)
  have hpend' : loan.isPending = e.loan.isPending := (congrArg RawLoan.isPending hraw :)
  have hrates : loan.rates = e.loan.rates := (congrArg RawLoan.rates hraw :)
  have hq : ∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) →
      loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 89 ∧
      (parts = true → 0 ≤ p.amounts.interestPaid.toRat) ∧
      (credit = true → 0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨
        p.loan.paymentRemaining = 0) := by
    intro p hp
    rw [hp] at hinst
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hinst
    obtain ⟨⟨hfee, hpa⟩, hcr⟩ := hinst
    refine ⟨hfee, fun h1 => ?_, fun h1 => ?_⟩
    · rcases hpa with h0 | h0
      · rw [h1] at h0; cases h0
      · exact h0
    · rcases hcr with h0 | h0
      · rw [h1] at h0; cases h0
      · exact h0
  have hat : ∀ loan', l.LoanAt j loan' → loan' = loan := by
    intro loan' ⟨e', b', he', hb', hw'⟩
    rw [he] at he'
    obtain rfl := Option.some.inj he'
    rw [hb] at hb'
    obtain rfl := Option.some.inj hb'
    rw [hw] at hw'
    exact (Except.ok.inj hw').symm
  have hfit : l.CreditFits j .late td := by
    intro loan' p _ _ hint
    rw [hfrac] at hint
    cases hint
  have hfeeF : l.FeeFits j .late td := by
    intro loan' p hat' hp
    obtain rfl := hat loan' hat'
    exact Or.inl ⟨hfrac, (hq p hp).1⟩
  refine ⟨l, LendingLedger.Reachable.of_run hg hl, by simpa using hnd, e, b, loan, pc, td, he, hb, hw,
    by rw [← hrem']; exact hrem, by rw [← hpend']; simpa using hpend, Or.inl (by rw [← hrates]; exact hrate),
    hfrac, by simpa [Loan.isPaymentLate] using hlate, hpc, htd, hpre, fun h1 => ?_,
    fun h1 p hp => (hq p hp).2.1 h1, fun h1 p hp => (hq p hp).2.2 h1, by rw [hlb]; exact hca, hfit, hfeeF,
    fun pt amount l' hok => ?_⟩
  · simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at htot
    rcases htot with h0 | h0
    · rw [h1] at h0; cases h0
    · exact h0
  -- every payment of loan `j` fails: the loan is late and its late payment fails at every amount
  obtain ⟨u, hu, -⟩ := LendingLedger.apply_loan rfl hok
  obtain ⟨e', b', loan', r, he', hb', hw', hc, hr, -⟩ := l.applyLoan_pay_inv u j pt amount hu
  rw [he] at he'; cases he'
  rw [hb] at hb'; cases hb'
  rw [hw] at hw'; cases hw'
  have hpend2 : loan.isPending = false := by simpa using hpend
  have himp2 : loan.isImpaired = false := by simpa using himp
  have hao2 : loan.allowsOverpayment = false := by simpa using hao
  cases pt with
  | regular =>
    have := Loan.regularPayment_late_proof loan l.vault amount l.now hrem hpo (fun _ => hdue) hlate
    rw [show (loan.pay l.vault .regular amount l.now) = loan.regularPayment l.vault amount l.now from rfl,
      this] at hr
    cases hr
  | full =>
    have := Loan.fullPayment_late_proof loan l.vault amount l.now hrem hpo (fun _ => hdue) hlate
    rw [show (loan.pay l.vault .full amount l.now) = loan.fullPayment l.vault amount l.now from rfl, this] at hr
    cases hr
  | overpayment =>
    rw [Loan.canPay_overpayment_not_allowed_proof loan hpend2 hao2] at hc
    cases hc
  | late =>
    by_cases hlt : amount.operator_lt td = true
    · have hchecks : loan.PayChecks .late l.now :=
        ⟨hrem, hpo, hdue, ⟨fun _ => hlate, fun _ => rfl⟩, fun h => by cases h⟩
      have := Loan.payment_insufficient_proof loan l.vault amount l.now .late pc td hchecks
        (fun h => by rw [himp2] at h; cases h) hpc htd hlt
      rw [this] at hr
      cases hr
    · have hsame := (Loan.latePayment_single_proof loan l.vault l.now pc td amount td hpc htd
        (by simpa using hlt) (by simpa using hirr)).1
      rw [show (loan.pay l.vault .late amount l.now) = loan.latePayment l.vault amount l.now from rfl,
        hsame] at hr
      rw [hr] at hfail
      cases hfail

/-- Payments that all fail reach no other ledger. A run of payments on loan `j` that each succeed is empty. -/
private lemma LendingLedger.payments_stuck {l : LendingLedger} {j : Nat}
    (hstuck : ∀ (pt : LoanPaymentType) (amount : Number) (l' : LendingLedger),
      (l.apply (.loanPay j pt amount)).run ≠ .ok (.ok l'))
    {txs : List LendingTx} {L : LendingLedger} (hreach : LendingLedger.Reaches l txs L)
    (hpay : ∀ tx ∈ txs, ∃ pt amount, tx = .loanPay j pt amount) : L = l := by
  induction hreach with
  | refl => rfl
  | step tx hprev happ ih =>
    have hmid := ih (fun t ht => hpay t (List.mem_append_left _ ht))
    subst hmid
    obtain ⟨pt, amount, rfl⟩ := hpay tx (List.mem_append_right _ (List.mem_singleton_self _))
    exact absurd happ (hstuck pt amount _)

/-- A stuck late loan gives the conditions of its next payments on every ledger its payments reach, and no run
of payments pays it off. -/
private lemma LendingLedger.stuck_payoff {l : LendingLedger} {j : Nat} {e : LoanEntry} {b : LoanBroker}
    {loan : Loan} {pc : PaymentComponents} {td : Number} {total parts credit : Bool}
    (he : l.loan? j = some e) (hb : l.broker? e.brokerIndex = some b) (hw : e.loan.withBroker b = .ok loan)
    (hrem : e.loan.paymentRemaining ≠ 0) (hlate : loan.isPaymentLate l.now = true)
    (hpc : loan.paymentComponents .late l.now = .ok pc) (htd : pc.totalDue = .ok td)
    (hpre : (LendingTx.loanPay j .late td).preflight l = .tesSUCCESS)
    (htot : total = true → l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hparts : parts = true → ∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) →
      0 ≤ p.amounts.interestPaid.toRat)
    (hcredit : credit = true → ∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) →
      0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0)
    (hca : loan.broker.coverAvailable.toRat < 10 ^ 96) (hfit : l.CreditFits j .late td)
    (hfee : l.FeeFits j .late td)
    (hstuck : ∀ (pt : LoanPaymentType) (amount : Number) (l' : LendingLedger),
      (l.apply (.loanPay j pt amount)).run ≠ .ok (.ok l')) :
    (∀ L loan' pc' td', l.PaidFrom j L → L.LoanAt j loan' → loan'.paymentRemaining ≠ 0 →
      loan'.paymentComponents (loan'.nextPaymentType L.now) L.now = .ok pc' → pc'.totalDue = .ok td' →
      (LendingTx.loanPay j (loan'.nextPaymentType L.now) td').preflight L = .tesSUCCESS ∧
      (total = true → L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent) ∧
      (parts = true → ∀ p, (loan'.payInstalments L.vault (loan'.nextPaymentType L.now) td' L.now).run =
        .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat) ∧
      (credit = true → ∀ p, (loan'.payInstalments L.vault (loan'.nextPaymentType L.now) td' L.now).run =
        .ok (.ok p) → 0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨
          p.loan.paymentRemaining = 0) ∧
      loan'.broker.coverAvailable.toRat < 10 ^ 96 ∧ L.CreditFits j (loan'.nextPaymentType L.now) td' ∧
      L.FeeFits j (loan'.nextPaymentType L.now) td') ∧
    ¬ ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
      (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay j pt amount) ∧ l'.loan? j = some e' ∧
      e'.loan.paymentRemaining = 0 := by
  refine ⟨fun L loan' pc' td' hPF hat _ hpc' htd' => ?_, fun ⟨txs, l', e', hreach, hpay, he', hrem'⟩ => ?_⟩
  · obtain ⟨txs, hreach, hpay⟩ := hPF.reaches
    obtain rfl := LendingLedger.payments_stuck hstuck hreach hpay
    obtain ⟨e', b', he', hb', hw'⟩ := hat
    rw [he] at he'
    obtain rfl := Option.some.inj he'
    rw [hb] at hb'
    obtain rfl := Option.some.inj hb'
    rw [hw] at hw'
    obtain rfl := (Except.ok.inj hw').symm
    have hnt : loan'.nextPaymentType L.now = .late := by simp [Loan.nextPaymentType, hlate]
    rw [hnt] at hpc' ⊢
    rw [hpc] at hpc'
    obtain rfl := Except.ok.inj hpc'
    rw [htd] at htd'
    obtain rfl := Except.ok.inj htd'
    exact ⟨hpre, htot, hparts, hcredit, hca, hfit, hfee⟩
  · obtain rfl := LendingLedger.payments_stuck hstuck hreach hpay
    rw [he] at he'
    obtain rfl := Option.some.inj he'
    exact hrem hrem'

private lemma stuckCheck_coarsened : stuckCheck cwGenesis cwCoarsenedTxs 2 false true true = true := by
  native_decide

private lemma stuckCheck_negative_interest :
    stuckCheck niGenesis (niTxs ++ [.close 1200]) 0 true false true = true := by
  native_decide

private lemma stuckCheck_fee_only :
    stuckCheck foGenesis (foTxs ++ [.close (1001 + 9 * 31536000 + 100)]) 0 true true false = true := by
  native_decide

/-- A late loan on a coarsened vault that no payments pay off. Loan C's late payment of exactly totalDue rounds
to no credit, and every other payment is rejected. -/
lemma LendingLedger.payoff_reachable_witness :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧ ∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
      e.loan.paymentRemaining ≠ 0 ∧ e.loan.isPending = false ∧ Loan.FallingFactorTerms e.loan.rates e.loan.schedule ∧
      (l.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14) ∧
      (∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
        loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
        (LendingTx.loanPay i (loan.nextPaymentType L.now) td).preflight L = .tesSUCCESS ∧
        (∀ p, (loan.payInstalments L.vault (loan.nextPaymentType L.now) td L.now).run = .ok (.ok p) →
          0 ≤ p.amounts.interestPaid.toRat) ∧
        (∀ p, (loan.payInstalments L.vault (loan.nextPaymentType L.now) td L.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        loan.broker.coverAvailable.toRat < 10 ^ 96 ∧ L.CreditFits i (loan.nextPaymentType L.now) td ∧
        L.FeeFits i (loan.nextPaymentType L.now) td) ∧
      ¬ ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
        e'.loan.paymentRemaining = 0 := by
  obtain ⟨l, hr, hnd, e, b, loan, pc, td, he, hb, hw, hrem, hpend, hterms, hfrac, hlate, hpc, htd, hpre, htot,
    hparts, hcredit, hca, hfit, hfee, hstuck⟩ := LendingLedger.stuckCheck_sound cwGenesis_genesis stuckCheck_coarsened
  obtain ⟨hrun, hno⟩ := LendingLedger.stuck_payoff he hb hw hrem hlate hpc htd hpre htot hparts hcredit hca hfit hfee
    hstuck
  refine ⟨l, hr, hnd, 2, e, he, hrem, hpend, hterms, fun hn => absurd (hn.symm.trans hfrac) (by decide),
    fun L loan' pc' td' hPF hat hrem' hpc' htd' => ?_, hno⟩
  obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := hrun L loan' pc' td' hPF hat hrem' hpc' htd'
  exact ⟨h1, h3 rfl, h4 rfl, h5, h6, h7⟩

/-- A late loan with a negative interest part that no payments pay off. The tiny-rate loan is late on its
third instalment, whose late payment of exactly totalDue is rejected, and every other payment is too. -/
lemma LendingLedger.payoff_reachable_negative_interest_witness :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧ ∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
      e.loan.paymentRemaining ≠ 0 ∧ e.loan.isPending = false ∧ Loan.FallingFactorTerms e.loan.rates e.loan.schedule ∧
      (l.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14) ∧
      (∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
        loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
        (LendingTx.loanPay i (loan.nextPaymentType L.now) td).preflight L = .tesSUCCESS ∧
        L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent ∧
        (∀ p, (loan.payInstalments L.vault (loan.nextPaymentType L.now) td L.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        loan.broker.coverAvailable.toRat < 10 ^ 96 ∧ L.CreditFits i (loan.nextPaymentType L.now) td ∧
        L.FeeFits i (loan.nextPaymentType L.now) td) ∧
      ¬ ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
        e'.loan.paymentRemaining = 0 := by
  obtain ⟨l, hr, hnd, e, b, loan, pc, td, he, hb, hw, hrem, hpend, hterms, hfrac, hlate, hpc, htd, hpre, htot,
    hparts, hcredit, hca, hfit, hfee, hstuck⟩ :=
    LendingLedger.stuckCheck_sound niGenesis_genesis stuckCheck_negative_interest
  obtain ⟨hrun, hno⟩ := LendingLedger.stuck_payoff he hb hw hrem hlate hpc htd hpre htot hparts hcredit hca hfit hfee
    hstuck
  refine ⟨l, hr, hnd, 0, e, he, hrem, hpend, hterms, fun hn => absurd (hn.symm.trans hfrac) (by decide),
    fun L loan' pc' td' hPF hat hrem' hpc' htd' => ?_, hno⟩
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hrun L loan' pc' td' hPF hat hrem' hpc' htd'
  exact ⟨h1, h2 rfl, h4 rfl, h5, h6, h7⟩

/-- A late loan with an instalment that is only management fee that no payments pay off. The loan of 2 at
45.5% is late on instalment 9, whose late payment sends everything to the broker and is rejected. -/
lemma LendingLedger.payoff_reachable_fee_only_witness :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧ ∃ (i : Nat) (e : LoanEntry), l.loan? i = some e ∧
      e.loan.paymentRemaining ≠ 0 ∧ e.loan.isPending = false ∧ Loan.FallingFactorTerms e.loan.rates e.loan.schedule ∧
      (l.vault.numericType = .native → e.loan.totalValueOutstanding.toRat < 3 * 10 ^ 14) ∧
      (∀ L loan pc td, l.PaidFrom i L → L.LoanAt i loan → loan.paymentRemaining ≠ 0 →
        loan.paymentComponents (loan.nextPaymentType L.now) L.now = .ok pc → pc.totalDue = .ok td →
        (LendingTx.loanPay i (loan.nextPaymentType L.now) td).preflight L = .tesSUCCESS ∧
        L.vault.assetsAvailable.toRat + L.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ L.vault.baseExponent ∧
        (∀ p, (loan.payInstalments L.vault (loan.nextPaymentType L.now) td L.now).run = .ok (.ok p) →
          0 ≤ p.amounts.interestPaid.toRat) ∧
        loan.broker.coverAvailable.toRat < 10 ^ 96 ∧ L.CreditFits i (loan.nextPaymentType L.now) td ∧
        L.FeeFits i (loan.nextPaymentType L.now) td) ∧
      ¬ ∃ (txs : List LendingTx) (l' : LendingLedger) (e' : LoanEntry), LendingLedger.Reaches l txs l' ∧
        (∀ tx ∈ txs, ∃ pt amount, tx = .loanPay i pt amount) ∧ l'.loan? i = some e' ∧
        e'.loan.paymentRemaining = 0 := by
  obtain ⟨l, hr, hnd, e, b, loan, pc, td, he, hb, hw, hrem, hpend, hterms, hfrac, hlate, hpc, htd, hpre, htot,
    hparts, hcredit, hca, hfit, hfee, hstuck⟩ := LendingLedger.stuckCheck_sound foGenesis_genesis stuckCheck_fee_only
  obtain ⟨hrun, hno⟩ := LendingLedger.stuck_payoff he hb hw hrem hlate hpc htd hpre htot hparts hcredit hca hfit hfee
    hstuck
  refine ⟨l, hr, hnd, 0, e, he, hrem, hpend, hterms, fun hn => absurd (hn.symm.trans hfrac) (by decide),
    fun L loan' pc' td' hPF hat hrem' hpc' htd' => ?_, hno⟩
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := hrun L loan' pc' td' hPF hat hrem' hpc' htd'
  exact ⟨h1, h2 rfl, h3 rfl, h5, h6, h7⟩

end XRPL.Model.Lending
