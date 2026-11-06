import XRPL.Properties.Lending.Loan.Common.Twin
import XRPL.Properties.Lending.Loan.Common.PayYield
import XRPL.Properties.Lending.Loan.Common.Loss
import XRPL.Properties.Lending.Loan.Common.PoolFrame
import XRPL.Properties.Lending.Ledger.Common.PaymentShareValue
import XRPL.Properties.Lending.Ledger.Common.ReservedInv
import XRPL.Properties.Lending.Ledger.Common.BrokerSteps

/-! # A regular payment of several scheduled payments, paid one at a time

Several scheduled payments paid together and paid as separate LoanPay transactions pay the same instalments, so they
leave the same loan and DebtTotal. At base scale they also leave the same vault. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments
  from XRPL.Model.Lending.Loan.LoanPay

/-- `l.SeparatePayments i k l'`: `k` LoanPay transactions on loan `i`, each a regular payment of exactly one
scheduled payment, take `l` to `l'`. No ledger close comes between them. -/
inductive LendingLedger.SeparatePayments (i : Nat) : Nat → LendingLedger → LendingLedger → Prop where
  | refl (l : LendingLedger) : LendingLedger.SeparatePayments i 0 l l
  | step {l l₁ l₂ : LendingLedger} {k : Nat} (loan : Loan) (amount : Number) (p : UnsettledPayment Vault) :
      l.LoanAt i loan → (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) → p.count = 1 →
      (l.apply (.loanPay i .regular amount)).run = .ok (.ok l₁) → LendingLedger.SeparatePayments i k l₁ l₂ →
      LendingLedger.SeparatePayments i (k + 1) l l₂

/-- `n` scheduled instalments, each with its LoanServiceFee, advance loan `a` to loan `b`. -/
inductive Loan.Instalments : Loan → Nat → Loan → Prop where
  | refl (a : Loan) : Loan.Instalments a 0 a
  | step {a b c : Loan} {n : Nat} (pc : PaymentComponents) :
      a.paymentComponents .regular 0 = .ok pc → Loan.doPayment a pc = .ok b → Loan.Instalments b n c →
      Loan.Instalments a (n + 1) c

/-- A loan is its own twin. -/
private lemma Loan.Twin.refl' (a : Loan) : Loan.Twin a a := ⟨rfl, rfl, rfl⟩

/-- Twins of twins are twins. -/
private lemma Loan.Twin.trans' {a b c : Loan} (h₁ : Loan.Twin a b) (h₂ : Loan.Twin b c) : Loan.Twin a c := by
  refine ⟨?_, h₂.numericType.trans h₁.numericType, h₂.managementFeeRate.trans h₁.managementFeeRate⟩
  rw [h₂.raw, h₁.raw]

/-- Twins advanced by the same number of instalments stay twins. -/
private lemma Loan.Instalments.twin {a b : Loan} {n : Nat} (hc : Loan.Instalments a n b) :
    ∀ {a' b' : Loan}, Loan.Twin a a' → Loan.Instalments a' n b' → Loan.Twin b b' := by
  induction hc with
  | refl a =>
    intro a' b' h hc'
    cases hc'
    exact h
  | step pc hpc hdo _ ih =>
    intro a' b' h hc'
    cases hc' with
    | step pc' hpc' hdo' hrest' =>
      rw [Loan.paymentComponents_twin h, hpc] at hpc'
      obtain rfl := Except.ok.inj hpc'
      exact ih (Loan.doPayment_twin h pc hdo hdo') hrest'

/-- The first instalment of a run of instalments, and the rest. -/
private lemma Loan.Instalments.head {a c : Loan} {n : Nat} (hc : Loan.Instalments a (n + 1) c) :
    ∃ b, Loan.Instalments a 1 b ∧ Loan.Instalments b n c := by
  cases hc with
  | step pc hpc hdo hrest => exact ⟨_, .step pc hpc hdo (.refl _), hrest⟩

/-- The next scheduled instalment with its LoanServiceFee is the first instalment of a regular payment. -/
private lemma Loan.scheduled_paymentComponents {a : Loan} {pc : PaymentComponents}
    (h : Loan.scheduledComponents a = .ok pc) :
    a.paymentComponents .regular 0 = .ok { pc with untrackedManagementFee := a.fees.serviceFee } := by
  simp [Loan.paymentComponents, h]

/-- The instalment loop advances the loan by one instalment per scheduled payment it counts. -/
private lemma UnsettledPayment.payInstalments_chain {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p' →
      ∃ m, p'.count = payment.count + m ∧ Loan.Instalments payment.loan m p'.loan := by
  intro n
  induction n with
  | zero =>
    intro payment p' h
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    exact ⟨0, rfl, .refl _⟩
  | succ n ih =>
    intro payment p' h
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · exact ⟨0, rfl, .refl _⟩
    · exact ⟨0, rfl, .refl _⟩
    all_goals
      have hpc := Loan.scheduled_paymentComponents ‹Loan.scheduledComponents payment.loan = _›
      have hdo := ‹Loan.doPayment payment.loan _ = _›
    · exact ⟨1, rfl, .step _ hpc hdo (.refl _)⟩
    · obtain ⟨m, hm, hc⟩ := ih _ p' ‹UnsettledPayment.payInstalments _ n amount = _›
      exact ⟨m + 1, by rw [hm]; dsimp only; omega, .step _ hpc hdo hc⟩

/-- What a regular payment on a reachable ledger does to the loan, its broker and the vault, read exactly. -/
structure Loan.RegularPaid (l : LendingLedger) (loan : Loan) (payment : UnsettledPayment Vault)
    (r : LoanWithAmounts Vault) : Prop where
  instalments : Loan.Instalments loan.unimpaired payment.count payment.loan
  twin : Loan.Twin payment.loan r.loan'
  unimpaired : r.loan'.isImpaired = false
  broker : r.loan'.broker.toRawLoanBroker = { loan.broker.toRawLoanBroker with
    debtTotal := r.loan'.broker.debtTotal, coverAvailable := r.loan'.broker.coverAvailable }
  principal : loan.principalOutstanding.toRat - r.loan'.principalOutstanding.toRat =
    payment.amounts.principalPaid.toRat
  interest : loan.toExact.interestDue - r.loan'.toExact.interestDue = payment.amounts.interestPaid.toRat
  principal_nonneg : 0 ≤ payment.amounts.principalPaid.toRat
  interest_nonneg : 0 ≤ payment.amounts.interestPaid.toRat
  debt : loan.broker.debtTotal.toRat - r.loan'.broker.debtTotal.toRat = payment.amounts.principalPaid.toRat
  deployed : l.vault.assetsDeployed.toRat - r.pool'.assetsDeployed.toRat = payment.amounts.principalPaid.toRat
  yield : l.vault.yieldUnrealized.toRat - r.pool'.yieldUnrealized.toRat = payment.amounts.interestPaid.toRat
  loss : r.pool'.lossUnrealized.toRat =
    l.vault.lossUnrealized.toRat - (if loan.isImpaired then loan.principalOutstanding.toRat else 0)
  reserved : r.pool'.assetsReserved = l.vault.assetsReserved
  settings : Vault.KeepsSettings l.vault r.pool'
  available : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
    r.pool'.assetsAvailable.toRat = l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat)

/-- What a regular payment on a reachable ledger does, read exactly. -/
lemma Loan.regularPaid {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan} (hat : l.LoanAt i loan)
    {amount : Number} {payment : UnsettledPayment Vault} {r : LoanWithAmounts Vault}
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hok : (loan.regularPayment l.vault amount l.now).run = .ok (.ok r)) : Loan.RegularPaid l loan payment r := by
  have hok' : (loan.pay l.vault .regular amount l.now).run = .ok (.ok r) := hok
  have hls := (hr.loanAt_scale hat).1
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hrange : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0 := by rw [hls]; omega

  -- the loop advanced the loan without the impaired flag by one instalment per scheduled payment
  obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan l.vault amount l.now payment hpay
  obtain ⟨m, hm, hchain⟩ := UnsettledPayment.payInstalments_chain amount _ _ _ hloop
  simp only [Nat.zero_add] at hm
  rw [← hm] at hchain

  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan l.vault .regular amount l.now payment hpay
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault .regular amount l.now r hok'
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨_, _, _, _, _, _, broker', -, -, -, hbroker, hloan, -, -⟩ := UnsettledPayment.settle_ok payment r hs
  have hraw := (RawLoan.to_lawful_ok hloan).1
  have hbraw := (RawLoanBroker.to_lawful_ok hbroker).1
  have hrb : r.loan'.broker = broker' := (congrArg RawLoan.broker hraw :)
  have hpb : payment.loan.broker = loan.broker := hst.broker
  have htwin : Loan.Twin payment.loan r.loan' := by
    refine ⟨by rw [hraw], ?_, ?_⟩
    · rw [hrb, show broker'.numericType = broker'.toRawLoanBroker.numericType from rfl, hbraw]
    · rw [hrb, show broker'.managementFeeRate = broker'.toRawLoanBroker.managementFeeRate from rfl, hbraw]
  have hid : r.loan'.toExact.interestDue = payment.loan.toExact.interestDue :=
    Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hraw :)
      (congrArg RawLoan.principalOutstanding hraw :) (congrArg RawLoan.managementFeeOutstanding hraw :)

  obtain ⟨hP, hAD, hDT⟩ := Loan.payment_principal_proof loan amount .regular r l hr i hat payment hpay hok'
  have hI := Loan.regularPayment_interest loan l.vault amount l.now payment hrange hpay
  obtain ⟨hP0, hI0, -⟩ := Loan.pay_parts_nonneg loan amount .regular r l.vault l.now payment hpay hok'
  have hY := Loan.payment_yield_proof loan amount .regular r l hr i hat hok' (hr.pay_yield_lt hat hok')
  change r.pool'.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat - _ at hY
  refine ⟨hchain, htwin, ?_, ?_, hP, by rw [hid, hI], hP0, hI0, hDT, hAD, by rw [hY, hid, hI]; ring, ?_,
    (Loan.pay_debt loan l.vault .regular amount l.now r hok').2,
    Loan.regularPayment_keepsSettings loan l.vault amount l.now r hok, ?_⟩
  · rw [show r.loan'.isImpaired = r.loan'.toRawLoan.isImpaired from rfl, hraw]
    exact hst.isImpaired
  · rw [hrb, hbraw, hpb]
  · cases himp : loan.isImpaired
    · rw [(Loan.pay_lossStep loan l.vault .regular amount l.now r hok').2.1 himp]; simp
    · have hL := Loan.payment_unimpairs_proof loan amount .regular r l hr i hat himp hok'
      change r.pool'.lossUnrealized.toRat = l.vault.lossUnrealized.toRat - loan.principalOutstanding.toRat at hL
      rw [hL]; simp
  · intro htotal
    obtain ⟨hAT, -⟩ := Loan.regularPayment_yield_proof loan amount r l hr i hat payment hpay hok htotal hr.yield_lt
    change r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat -
      (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat) = _ at hAT
    linarith

/-- The ledger after a payment holds the paid loan in the same slot, read with the broker it wrote. -/
private lemma LendingLedger.loanAt_commitPay {l : LendingLedger} {i : Nat} {e : LoanEntry} {b : LoanBroker}
    (loan' : Loan) (v' : Vault) (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).LoanAt i loan' := by
  refine ⟨{ e with loan := loan' }, loan'.broker, ?_, ?_, ?_⟩
  · rw [LendingLedger.loan?_commitLoan]
    simp only [LoanEffect.ofLoan, if_pos (LendingLedger.loan?_lt he)]
    rfl
  · rw [LendingLedger.broker?_commitLoan l _ b hb]
    simp [LoanEffect.ofLoan]
  · unfold Loan.withBroker RawLoan.to_lawful
    rw [dif_pos ⟨loan'.wf, loan'.valid⟩]

/-- A separate payment on a reachable ledger: the next ledger is reachable and holds the paid loan and the paid
vault. -/
private lemma LendingLedger.separate_step {l l₁ : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) {amount : Number} {p : UnsettledPayment Vault}
    (hp : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p))
    (happly : (l.apply (.loanPay i .regular amount)).run = .ok (.ok l₁)) :
    ∃ r : LoanWithAmounts Vault, l₁.Reachable ∧ l₁.LoanAt i r.loan' ∧ l₁.vault = r.pool' ∧
      Loan.RegularPaid l loan p r := by
  have hr₁ := hr.apply happly
  obtain ⟨e, loan₁, r, he, hat₁, -, hok, rfl, -⟩ := LendingLedger.loanPay_parts happly
  obtain ⟨e₂, b₂, he₂, hb₂, hw₂⟩ := hat₁
  obtain rfl := hat.unique he₂ hb₂ hw₂
  rw [he] at he₂
  obtain rfl := Option.some.inj he₂
  exact ⟨r, hr₁, LendingLedger.loanAt_commitPay r.loan' r.pool' he hb₂, rfl, Loan.regularPaid hr hat hp hok⟩

/-- What `k` separate payments do, against the loan `M` read before them, the loan `S` read after them and the
loan `N` that the same `k` instalments leave. -/
structure LendingLedger.SeparatePaid (k : Nat) (l l' : LendingLedger) (M N S : Loan) : Prop where
  twin : Loan.Twin N S.unimpaired
  unimpaired : k ≠ 0 ∨ M.isImpaired = false → S.isImpaired = false
  broker : S.broker.toRawLoanBroker = { M.broker.toRawLoanBroker with
    debtTotal := S.broker.debtTotal, coverAvailable := S.broker.coverAvailable }
  principal_le : S.principalOutstanding.toRat ≤ M.principalOutstanding.toRat
  interest_le : S.toExact.interestDue ≤ M.toExact.interestDue
  debt : M.broker.debtTotal.toRat - S.broker.debtTotal.toRat =
    M.principalOutstanding.toRat - S.principalOutstanding.toRat
  deployed : l.vault.assetsDeployed.toRat - l'.vault.assetsDeployed.toRat =
    M.principalOutstanding.toRat - S.principalOutstanding.toRat
  yield : l.vault.yieldUnrealized.toRat - l'.vault.yieldUnrealized.toRat = M.toExact.interestDue - S.toExact.interestDue
  loss : l'.vault.lossUnrealized.toRat =
    l.vault.lossUnrealized.toRat - (if M.isImpaired = true ∧ k ≠ 0 then M.principalOutstanding.toRat else 0)
  reserved : l'.vault.assetsReserved = l.vault.assetsReserved
  settings : Vault.KeepsSettings l.vault l'.vault
  available : l.vault.assetsAvailable.toRat + ((M.principalOutstanding.toRat - S.principalOutstanding.toRat) +
      (M.toExact.interestDue - S.toExact.interestDue)) < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
    l'.vault.assetsAvailable.toRat = l.vault.assetsAvailable.toRat +
      ((M.principalOutstanding.toRat - S.principalOutstanding.toRat) + (M.toExact.interestDue - S.toExact.interestDue))

/-- Separate payments read against the instalments they pay. Each one pays the next instalment and settles it
on its own. -/
private lemma LendingLedger.SeparatePayments.paid {i k : Nat} {l l' : LendingLedger}
    (hsep : l.SeparatePayments i k l') :
    ∀ {M N₀ N S : Loan}, l.Reachable → l.LoanAt i M → Loan.Twin N₀ M.unimpaired →
      Loan.Instalments N₀ k N → l'.LoanAt i S → LendingLedger.SeparatePaid k l l' M N S := by
  induction hsep with
  | refl l =>
    intro M N₀ N S _ hat htw hc hat'
    obtain ⟨e, b, he, hb, hw⟩ := hat'
    obtain rfl := hat.unique he hb hw
    cases hc
    exact ⟨htw, fun h => h.resolve_left (by simp), rfl, le_refl _, le_refl _, by ring, by ring, by ring,
      by simp, rfl, Vault.KeepsSettings.refl _, fun _ => by ring⟩
  | @step l l₁ l₂ k loan₀ a p hat₀ hp hc happly _ ih =>
    intro M N₀ N S hr hat htw hchain hat'
    obtain ⟨e, b, he, hb, hw⟩ := hat₀
    obtain rfl := hat.unique he hb hw
    obtain ⟨r₁, hr₁, hat₁, hv₁, hf⟩ := LendingLedger.separate_step hr hat hp happly
    -- the first instalment leaves twins, and the rest of the run starts from them
    have h1 := hf.instalments
    rw [hc] at h1
    obtain ⟨N₁, hN₁, hrest⟩ := hchain.head
    have htw₁ : Loan.Twin N₁ r₁.loan'.unimpaired := by
      rw [Loan.unimpaired_of_not _ hf.unimpaired]
      exact Loan.Twin.trans' (hN₁.twin htw h1) hf.twin
    have hs := ih hr₁ hat₁ htw₁ hrest hat'
    have hbe : r₁.pool'.baseExponent = l.vault.baseExponent := hf.settings.baseExponent_eq
    have hsD := hs.deployed
    have hsY := hs.yield
    have hsL := hs.loss
    have hsR := hs.reserved
    have hsS := hs.settings
    have hsA := hs.available
    rw [hv₁] at hsD hsY hsL hsR hsS hsA
    have hP := hf.principal
    have hI := hf.interest
    have hP0 := hf.principal_nonneg
    have hI0 := hf.interest_nonneg
    have hPS := hs.principal_le
    have hIS := hs.interest_le
    refine ⟨hs.twin, fun _ => hs.unimpaired (Or.inr hf.unimpaired), ?_, by linarith, by linarith,
      by linarith [hf.debt, hs.debt], by linarith [hf.deployed], by linarith [hf.yield], ?_,
      hsR.trans hf.reserved, hf.settings.trans hsS, ?_⟩
    · rw [hs.broker, hf.broker]
    · rw [hsL, if_neg (by simp [hf.unimpaired]), hf.loss]
      simp
    · intro htotal
      have h₁ := hf.available (by linarith)
      have h₂ := hsA (by rw [h₁, hbe]; linarith)
      rw [h₂, h₁]
      linarith

/-- Two vaults with the same five balances and the same settings are the same vault. -/
private lemma Vault.eq_of_balances {v w : Vault} (h1 : v.assetsAvailable.toRat = w.assetsAvailable.toRat)
    (h2 : v.assetsDeployed.toRat = w.assetsDeployed.toRat) (h3 : v.assetsReserved = w.assetsReserved)
    (h4 : v.lossUnrealized.toRat = w.lossUnrealized.toRat) (h5 : v.yieldUnrealized.toRat = w.yieldUnrealized.toRat)
    (hs : Vault.KeepsSettings w v) : v = w := by
  have e1 := v.wf.assetsAvailable_norm.toRat_inj w.wf.assetsAvailable_norm h1
  have e2 := v.wf.assetsDeployed_norm.toRat_inj w.wf.assetsDeployed_norm h2
  have e4 := v.wf.lossUnrealized_norm.toRat_inj w.wf.lossUnrealized_norm h4
  have e5 := v.wf.yieldUnrealized_norm.toRat_inj w.wf.yieldUnrealized_norm h5
  obtain ⟨hnt, hsc, hst, ham, hsch, hee, hoc, hdb⟩ := hs
  obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩, _, _⟩ := v
  obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩, _, _⟩ := w
  simp only at e1 e2 h3 e4 e5 hnt hsc hst ham hsch hee hoc hdb
  subst e1 e2 h3 e4 e5 hnt hsc hst ham hsch hee hoc hdb
  rfl

/-- The loan after a regular payment of k scheduled payments and after k separate payments. Both are the
loan the same k instalments leave, with the broker each run wrote. -/
lemma Loan.regularPayment_split_loan {l l' : LendingLedger} (hr : l.Reachable) {i : Nat} {loan loan' : Loan}
    (hat : l.LoanAt i loan) {amount : Number} {payment : UnsettledPayment Vault} {r : LoanWithAmounts Vault}
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hok : (loan.regularPayment l.vault amount l.now).run = .ok (.ok r))
    (hsep : l.SeparatePayments i payment.count l') (hat' : l'.LoanAt i loan') :
    Loan.RegularPaid l loan payment r ∧ LendingLedger.SeparatePaid payment.count l l' loan payment.loan loan' ∧
      loan'.toRawLoan = { r.loan'.toRawLoan with broker := loan'.broker } ∧
      loan'.broker.toRawLoanBroker =
        { r.loan'.broker.toRawLoanBroker with coverAvailable := loan'.broker.coverAvailable } := by
  have hf := Loan.regularPaid hr hat hpay hok
  have hs := hsep.paid hr hat (Loan.Twin.refl' _) hf.instalments hat'
  obtain ⟨-, -, -, -, hc⟩ := Loan.payInstalments_ok loan l.vault .regular amount l.now payment hpay
  have htw := hs.twin
  rw [Loan.unimpaired_of_not _ (hs.unimpaired (Or.inl (by omega)))] at htw
  have hrraw := hf.twin.raw
  have hlraw := htw.raw
  refine ⟨hf, hs, by rw [hlraw, hrraw], ?_⟩

  -- the two runs take the same principal off DebtTotal
  have hPO : loan'.principalOutstanding = r.loan'.principalOutstanding := by
    rw [show loan'.principalOutstanding = loan'.toRawLoan.principalOutstanding from rfl, hlraw,
      show r.loan'.principalOutstanding = r.loan'.toRawLoan.principalOutstanding from rfl, hrraw]
  have hdt : loan'.broker.debtTotal = r.loan'.broker.debtTotal := by
    apply loan'.broker.wf.debtTotal_norm.toRat_inj r.loan'.broker.wf.debtTotal_norm
    have := hs.debt
    have := hf.debt
    have := hf.principal
    rw [hPO] at *
    linarith
  rw [hs.broker, hf.broker, hdt]

/-- Proof body of `regularPayment_split`. -/
lemma Loan.regularPayment_split_proof (loan : Loan) (amount : Number) (r : LoanWithAmounts Vault)
    (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (l' : LendingLedger) (loan' : Loan)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hok : (loan.regularPayment l.vault amount l.now).run = .ok (.ok r))
    (hsep : l.SeparatePayments i payment.count l') (hat' : l'.LoanAt i loan')
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    loan'.toRawLoan = { r.loan'.toRawLoan with broker := loan'.broker } ∧
      loan'.broker.toRawLoanBroker =
        { r.loan'.broker.toRawLoanBroker with coverAvailable := loan'.broker.coverAvailable } ∧
      l'.vault = r.pool' := by
  obtain ⟨hf, hs, hraw, hbroker⟩ := Loan.regularPayment_split_loan hr hat hpay hok hsep hat'
  refine ⟨hraw, hbroker, ?_⟩
  obtain ⟨-, -, -, -, hc⟩ := Loan.payInstalments_ok loan l.vault .regular amount l.now payment hpay

  have hPO : loan'.principalOutstanding = r.loan'.principalOutstanding := by
    rw [show loan'.principalOutstanding = loan'.toRawLoan.principalOutstanding from rfl, hraw]
  have hID : loan'.toExact.interestDue = r.loan'.toExact.interestDue := by
    apply Loan.toExact_interestDue_congr
    · rw [show loan'.totalValueOutstanding = loan'.toRawLoan.totalValueOutstanding from rfl, hraw]
    · exact hPO
    · rw [show loan'.managementFeeOutstanding = loan'.toRawLoan.managementFeeOutstanding from rfl, hraw]
  have hP := hf.principal
  have hI := hf.interest
  rw [← hPO] at hP
  rw [← hID] at hI

  -- so the same balances, and the separate payments stay at base scale
  have hAA := hs.available (by linarith)
  have hAA' := hf.available htotal
  have hLU := hs.loss
  rw [if_congr (show (loan.isImpaired = true ∧ payment.count ≠ 0) ↔ loan.isImpaired = true from
    ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩) rfl rfl] at hLU
  have hks := hs.settings
  have hkf := hf.settings
  apply Vault.eq_of_balances (by linarith) (by linarith [hs.deployed, hf.deployed])
    (hs.reserved.trans hf.reserved.symm) (by rw [hLU, hf.loss]) (by linarith [hs.yield, hf.yield])
  exact ⟨hks.1.trans hkf.1.symm, hks.2.trans hkf.2.symm, hks.3.trans hkf.3.symm, hks.4.trans hkf.4.symm,
    hks.5.trans hkf.5.symm, hks.6.trans hkf.6.symm, hks.7.trans hkf.7.symm, hks.8.trans hkf.8.symm⟩

end XRPL.Model.Lending
