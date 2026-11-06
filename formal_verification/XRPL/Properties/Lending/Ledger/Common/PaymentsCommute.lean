import XRPL.Properties.Lending.Ledger.Common.Isolation
import XRPL.Properties.Lending.Ledger.Common.PaymentCoarsening
import XRPL.Properties.Lending.Loan.Common.SeparatePayments
import XRPL.Properties.Lending.Loan.Common.TwinPay

/-! # Payments on two loans in either order

A payment's amounts depend only on its own loan and its broker's asset and management fee rate, so at base scale
both orders leave the same vault and DebtTotal. Only CoverAvailable can differ: each payment decides from the broker
before it whether its fee goes to the cover. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Vault.eq_of_balances from XRPL.Properties.Lending.Loan.Common.SeparatePayments
open private LendingLedger.keepsLoan_of_loanTx from XRPL.Properties.Lending.Ledger.Common.Isolation

/-- What a payment of `loan` on a reachable ledger `l` does, read exactly: `p` is the instalments it pays and `r`
the settled result. -/
structure Loan.Paid (l : LendingLedger) (loan : Loan) (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault) :
    Prop where
  raw : r.loan'.toRawLoan = { p.loan.toRawLoan with broker := r.loan'.broker }
  broker : r.loan'.broker.toRawLoanBroker = { loan.broker.toRawLoanBroker with
    debtTotal := r.loan'.broker.debtTotal, coverAvailable := r.loan'.broker.coverAvailable }
  debt : loan.broker.debtTotal.toRat - r.loan'.broker.debtTotal.toRat = p.amounts.principalPaid.toRat
  deployed : l.vault.assetsDeployed.toRat - r.pool'.assetsDeployed.toRat = p.amounts.principalPaid.toRat
  yield : r.pool'.yieldUnrealized.toRat =
    l.vault.yieldUnrealized.toRat - (loan.toExact.interestDue - p.loan.toExact.interestDue)
  loss : r.pool'.lossUnrealized.toRat =
    l.vault.lossUnrealized.toRat - (if loan.isImpaired then loan.principalOutstanding.toRat else 0)
  reserved : r.pool'.assetsReserved = l.vault.assetsReserved
  settings : Vault.KeepsSettings l.vault r.pool'
  principal_nonneg : 0 ≤ p.amounts.principalPaid.toRat
  interest_nonneg : 0 ≤ p.amounts.interestPaid.toRat
  available : l.vault.assetsAvailable.toRat +
      (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
    r.pool'.assetsAvailable.toRat = l.vault.assetsAvailable.toRat +
      (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat)

/-- What a payment on a reachable ledger does, read exactly. At base scale the vault credits principalPaid +
interestPaid in full. -/
lemma Loan.paid {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan} (hat : l.LoanAt i loan)
    {pt : LoanPaymentType} {amount : Number} {p : UnsettledPayment Vault} {r : LoanWithAmounts Vault}
    (hpay : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p))
    (hok : (loan.pay l.vault pt amount l.now).run = .ok (.ok r)) (hks : Vault.KeepsSettings l.vault r.pool') :
    Loan.Paid l loan p r := by
  obtain ⟨-, -, hst, -, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now p hpay
  obtain ⟨q, hq, hs⟩ := Loan.pay_ok loan l.vault pt amount l.now r hok
  rw [hpay] at hq
  obtain rfl := Except.ok.inj (Except.ok.inj hq)
  obtain ⟨_, _, _, _, _, _, broker', -, -, -, hbroker, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hraw := (RawLoan.to_lawful_ok hloan).1
  have hbraw := (RawLoanBroker.to_lawful_ok hbroker).1
  have hrb : r.loan'.broker = broker' := (congrArg RawLoan.broker hraw :)
  have hpb : p.loan.broker = loan.broker := hst.broker
  have hid : r.loan'.toExact.interestDue = p.loan.toExact.interestDue :=
    Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hraw :)
      (congrArg RawLoan.principalOutstanding hraw :) (congrArg RawLoan.managementFeeOutstanding hraw :)

  obtain ⟨-, hAD, hDT⟩ := Loan.payment_principal_proof loan amount pt r l hr i hat p hpay hok
  obtain ⟨hP0, hI0, -⟩ := Loan.pay_parts_nonneg loan amount pt r l.vault l.now p hpay hok
  have hY := Loan.payment_yield_proof loan amount pt r l hr i hat hok (hr.pay_yield_lt hat hok)
  change r.pool'.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat - _ at hY
  refine ⟨by rw [hrb]; exact hraw, by rw [hrb, hbraw, hpb], hDT, hAD, by rw [hY, hid], ?_,
    (Loan.pay_debt loan l.vault pt amount l.now r hok).2, hks, hP0, hI0, ?_⟩
  · cases himp : loan.isImpaired
    · rw [(Loan.pay_lossStep loan l.vault pt amount l.now r hok).2.1 himp]; simp
    · have hL := Loan.payment_unimpairs_proof loan amount pt r l hr i hat himp hok
      change r.pool'.lossUnrealized.toRat = l.vault.lossUnrealized.toRat - loan.principalOutstanding.toRat at hL
      rw [hL]; simp

  -- at base scale the credit is the whole of principalPaid + interestPaid, already in base units
  intro htotal
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
  obtain ⟨g1, g2⟩ := Loan.payInstalments_onGrid loan l.vault pt amount l.now p (by rw [hls]; omega) hpay
  rw [hls] at g1 g2
  obtain ⟨pp, hpp⟩ := g1.nat hP0
  obtain ⟨ip, hip⟩ := g2.nat hI0
  obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
  have hsumv : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat =
      ((pp + ip : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by rw [hpp, hip]; push_cast; ring
  have hall : a + (pp + ip) < 10 ^ 16 := by
    rw [ha, hsumv, ← add_mul] at htotal
    have : ((a + (pp + ip) : ℕ) : ℚ) < 10 ^ 16 := by
      push_cast; exact lt_of_mul_lt_mul_right (by push_cast at htotal; linarith) hp10.le
    exact_mod_cast this
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((pp + ip : ℕ) : ℤ) l.vault.baseExponent
    (by constructor <;> omega) (by unfold minExponent maxExponent; omega)
  have hsum : ∃ w : Number, w.isNormalized ∧ 0 ≤ w.toRat ∧
      w.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat :=
    ⟨w, hw, by rw [hwv]; positivity, by rw [hwv, hsumv]; push_cast; ring⟩
  have hroom : l.vault.assetsAvailable.toRat + (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) ≤
      (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent := by
    have h1 : ((a + (pp + ip) : ℕ) : ℚ) + 1 ≤ 10 ^ 16 := by
      have : a + (pp + ip) + 1 ≤ 10 ^ 16 := by omega
      exact_mod_cast this
    have hpow : (10 : ℚ) ^ (16 + l.vault.baseExponent) = 10 ^ 16 * 10 ^ l.vault.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    rw [hpow, ha, hsumv, ← add_mul]
    have := mul_le_mul_of_nonneg_right h1 hp10.le
    push_cast at this ⊢
    linarith
  obtain ⟨hA', -⟩ := Loan.payment_vault_at_base loan l.vault amount l.now pt r p a hnt hr.availableStored hpay hok
    hsum ha hroom
  rw [hA', hsumv, mul_div_assoc, div_self hp10.ne', mul_one,
    show ((pp + ip : ℕ) : ℚ) = (((pp + ip : ℕ) : ℤ) : ℚ) by push_cast; ring, Int.floor_intCast]

/-- A loan read with another copy of its broker, of the same asset and management fee rate, is a twin. -/
private lemma LendingLedger.KeepsLoan.twin {L L' : LendingLedger} (hR : L.Reachable) (hR' : L'.Reachable) {i : Nat}
    {e : LoanEntry} (hk : L.KeepsLoan L' i e) (he : L.loan? i = some e) {A A' : Loan} (hat : L.LoanAt i A)
    (hat' : L'.LoanAt i A') : Loan.Twin A A' := by
  obtain ⟨e₁, b, he₁, hb, hw⟩ := hat
  rw [he] at he₁
  obtain rfl := Option.some.inj he₁
  obtain ⟨e₂, b₂, he₂, hb₂, hw₂⟩ := hat'
  rw [hk.loan] at he₂
  obtain rfl := Option.some.inj he₂
  obtain ⟨b', hb', hm⟩ := hk.broker b hb
  rw [hb₂] at hb'
  obtain rfl := Option.some.inj hb'
  have hraw := Loan.withBroker_eq hw
  have hraw' := Loan.withBroker_eq hw₂
  have hlb : A.broker = b := by rw [show A.broker = A.toRawLoan.broker from rfl, hraw]
  have hlb' : A'.broker = b₂ := by rw [show A'.broker = A'.toRawLoan.broker from rfl, hraw']
  exact ⟨by rw [hraw', hraw], by rw [hlb', hlb, hR'.scaleInv.brokers _ b₂ hb₂, hk.settings.numericType,
    hR.scaleInv.brokers _ b hb], by rw [hlb', hlb, hm]⟩

/-- Twins pay the same amounts, and the loans they leave are twins. -/
private lemma Loan.Twin.pay_same {A A' : Loan} (ht : Loan.Twin A A') {v v' : Vault} {pt : LoanPaymentType}
    {amount : Number} {now : UInt32} {p p' : UnsettledPayment Vault}
    (hp : (A.payInstalments v pt amount now).run = .ok (.ok p))
    (hp' : (A'.payInstalments v' pt amount now).run = .ok (.ok p')) :
    Loan.Twin p.loan p'.loan ∧ p'.amounts = p.amounts := by
  obtain ⟨-, hu, -, -, -⟩ := Loan.payInstalments_ok A' v' pt amount now p' hp'
  obtain ⟨q, hq, htw, ha, -⟩ := Loan.payInstalments_twin ht v v' p'.pool pt amount now p hu hp
  rw [hp'] at hq
  obtain rfl := Except.ok.inj (Except.ok.inj hq)
  exact ⟨htw, ha⟩

/-- Twins carry the same impairment and the same principal. -/
private lemma Loan.Twin.impaired {A A' : Loan} (ht : Loan.Twin A A') :
    A'.isImpaired = A.isImpaired ∧ A'.principalOutstanding = A.principalOutstanding :=
  ⟨(congrArg RawLoan.isImpaired ht.raw :), (congrArg RawLoan.principalOutstanding ht.raw :)⟩

/-- principalPaid + interestPaid of a payment. -/
private abbrev UnsettledPayment.credit (p : UnsettledPayment Vault) : ℚ :=
  p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat

/-- What a payment on loan `i` then a payment on loan `j` do, read against the two loans `A`, `B` and the two
payments `pA`, `pB` that each would make first. -/
private structure LendingLedger.PairPaid (l lab : LendingLedger) (i j : Nat) (eA eB : LoanEntry) (A B : Loan)
    (pA pB : UnsettledPayment Vault) : Prop where
  available : lab.vault.assetsAvailable.toRat = l.vault.assetsAvailable.toRat + pA.credit + pB.credit
  deployed : lab.vault.assetsDeployed.toRat =
    l.vault.assetsDeployed.toRat - pA.amounts.principalPaid.toRat - pB.amounts.principalPaid.toRat
  yield : lab.vault.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat -
    (A.toExact.interestDue - pA.loan.toExact.interestDue) - (B.toExact.interestDue - pB.loan.toExact.interestDue)
  loss : lab.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat -
    (if A.isImpaired then A.principalOutstanding.toRat else 0) -
    (if B.isImpaired then B.principalOutstanding.toRat else 0)
  reserved : lab.vault.assetsReserved = l.vault.assetsReserved
  settings : Vault.KeepsSettings l.vault lab.vault
  broker_other : ∀ k, k ≠ eA.brokerIndex → k ≠ eB.brokerIndex → lab.broker? k = l.broker? k
  broker : ∀ k b₀, l.broker? k = some b₀ → (k = eA.brokerIndex ∨ k = eB.brokerIndex) → ∃ b,
    lab.broker? k = some b ∧
    b.toRawLoanBroker = { b₀.toRawLoanBroker with debtTotal := b.debtTotal, coverAvailable := b.coverAvailable } ∧
    b.debtTotal.toRat = b₀.debtTotal.toRat - ((if k = eA.brokerIndex then pA.amounts.principalPaid.toRat else 0) +
      (if k = eB.brokerIndex then pB.amounts.principalPaid.toRat else 0))
  loan_other : ∀ k, k ≠ i → k ≠ j → lab.loan? k = l.loan? k
  loan_first : ∃ X : Loan, lab.loan? i = some { eA with loan := X } ∧
    X.toRawLoan = { pA.loan.toRawLoan with broker := X.broker }
  loan_second : ∃ Y : Loan, lab.loan? j = some { eB with loan := Y } ∧
    Y.toRawLoan = { pB.loan.toRawLoan with broker := Y.broker }

/-- The broker a paid loan reads is the stored one. -/
private lemma LendingLedger.LoanAt.broker {l : LendingLedger} {i : Nat} {e : LoanEntry} {loan : Loan}
    (hat : l.LoanAt i loan) (he : l.loan? i = some e) : l.broker? e.brokerIndex = some loan.broker := by
  obtain ⟨e₁, b, he₁, hb, hw⟩ := hat
  rw [he] at he₁
  obtain rfl := Option.some.inj he₁
  rw [hb, show loan.broker = loan.toRawLoan.broker from rfl, Loan.withBroker_eq hw]

/-- A payment on loan `i` then a payment on loan `j`, at base scale, read against the payments each loan would
make first on `l`. -/
private lemma LendingLedger.pay_pair {l la lab : LendingLedger} (hr : l.Reachable) {i j : Nat} (hij : i ≠ j)
    {pt pt' : LoanPaymentType} {a a' : Number}
    (ha : (l.apply (.loanPay i pt a)).run = .ok (.ok la)) (hab : (la.apply (.loanPay j pt' a')).run = .ok (.ok lab))
    {eA eB : LoanEntry} {A B : Loan} {pA pB : UnsettledPayment Vault} (heA : l.loan? i = some eA)
    (heB : l.loan? j = some eB) (hatA : l.LoanAt i A) (hatB : l.LoanAt j B)
    (hpA : (A.payInstalments l.vault pt a l.now).run = .ok (.ok pA))
    (hpB : (B.payInstalments l.vault pt' a' l.now).run = .ok (.ok pB))
    (hroom : l.vault.assetsAvailable.toRat + pA.credit + pB.credit < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    LendingLedger.PairPaid l lab i j eA eB A B pA pB := by
  have hra := hr.apply ha
  obtain ⟨eA₁, A₁, rA, heA₁, hatA₁, -, hokA, rfl, hksA⟩ := LendingLedger.loanPay_parts ha
  rw [heA] at heA₁
  obtain rfl := Option.some.inj heA₁
  obtain ⟨e₁, b₁, he₁, hb₁, hw₁⟩ := hatA₁
  obtain rfl := hatA.unique he₁ hb₁ hw₁
  have hfA := Loan.paid hr hatA hpA hokA hksA
  -- the second payment reads loan `j` as it was, with a broker of the same terms
  obtain ⟨hk, -⟩ := LendingLedger.keepsLoan_of_loanTx heB rfl (by simp [LendingTx.loanIndex?, hij]) ha
  obtain ⟨eB₁, B₁, rB, heB₁, hatB₁, -, hokB, rfl, hksB⟩ := LendingLedger.loanPay_parts hab
  rw [hk.loan] at heB₁
  obtain rfl := Option.some.inj heB₁
  have htw := LendingLedger.KeepsLoan.twin hr hra hk heB hatB hatB₁
  obtain ⟨pB₁, hpB₁, -⟩ := Loan.pay_ok B₁ _ pt' a' _ rB hokB
  rw [hk.now] at hpB₁
  obtain ⟨htwp, hamt⟩ := htw.pay_same hpB hpB₁
  rw [← hk.now] at hpB₁
  have hfB := Loan.paid hra hatB₁ hpB₁ hokB hksB
  have hPB0 := hfB.principal_nonneg
  have hIB0 := hfB.interest_nonneg
  rw [hamt] at hPB0 hIB0
  have hbeA : rA.pool'.baseExponent = l.vault.baseExponent := hksA.baseExponent_eq
  have hD₁ := hfA.deployed
  have hD₂ := hfB.deployed
  rw [hamt] at hD₂
  change rA.pool'.assetsDeployed.toRat - rB.pool'.assetsDeployed.toRat = _ at hD₂

  unfold UnsettledPayment.credit at hroom
  have hAA₁ := hfA.available (by linarith [hfA.principal_nonneg, hfA.interest_nonneg])
  have hAA₂ := hfB.available (by
    show rA.pool'.assetsAvailable.toRat + _ < 10 ^ 16 * 10 ^ rA.pool'.baseExponent
    rw [hAA₁, hbeA, hamt]; linarith)
  rw [hamt] at hAA₂
  have hY₂ := hfB.yield
  rw [htw.interestDue_eq, htwp.interestDue_eq] at hY₂
  have hL₂ := hfB.loss
  rw [htw.impaired.1, htw.impaired.2] at hL₂

  have hbA := hatA.broker heA
  have hbB₁ := hatB₁.broker hk.loan
  have hla : ∀ k, (l.commitLoan (LoanEffect.ofLoan i eA rA.loan' rA.pool')).broker? k =
      if k = eA.brokerIndex then some rA.loan'.broker else l.broker? k :=
    LendingLedger.broker?_commitLoan l _ _ hbA
  have hlab : ∀ k, ((l.commitLoan (LoanEffect.ofLoan i eA rA.loan' rA.pool')).commitLoan
      (LoanEffect.ofLoan j eB rB.loan' rB.pool')).broker? k =
      if k = eB.brokerIndex then some rB.loan'.broker
      else (l.commitLoan (LoanEffect.ofLoan i eA rA.loan' rA.pool')).broker? k :=
    LendingLedger.broker?_commitLoan _ _ _ hbB₁
  have hDA := hfA.debt
  have hDB := hfB.debt
  rw [hamt] at hDB

  have hiA := LendingLedger.loan?_lt heA
  have hjB := LendingLedger.loan?_lt hk.loan
  have hloa : ∀ k, (l.commitLoan (LoanEffect.ofLoan i eA rA.loan' rA.pool')).loan? k =
      if k = i then some { eA with loan := rA.loan' } else l.loan? k := by
    intro k
    rw [LendingLedger.loan?_commitLoan,
      if_pos (show (LoanEffect.ofLoan i eA rA.loan' rA.pool').loanIndex < l.loans.length from hiA)]
    rfl
  have hloab : ∀ k, ((l.commitLoan (LoanEffect.ofLoan i eA rA.loan' rA.pool')).commitLoan
      (LoanEffect.ofLoan j eB rB.loan' rB.pool')).loan? k =
      if k = j then some { eB with loan := rB.loan' }
      else (l.commitLoan (LoanEffect.ofLoan i eA rA.loan' rA.pool')).loan? k := by
    intro k
    rw [LendingLedger.loan?_commitLoan,
      if_pos (show (LoanEffect.ofLoan j eB rB.loan' rB.pool').loanIndex < _ from hjB)]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hfB.reserved.trans hfA.reserved, hfA.settings.trans hfB.settings, ?_, ?_, ?_, ?_, ?_⟩
  · show rB.pool'.assetsAvailable.toRat = _
    unfold UnsettledPayment.credit
    rw [hAA₂]
    show rA.pool'.assetsAvailable.toRat + _ = _
    rw [hAA₁]
  · show rB.pool'.assetsDeployed.toRat = _
    linarith
  · show rB.pool'.yieldUnrealized.toRat = _
    rw [hY₂]
    show rA.pool'.yieldUnrealized.toRat - _ = _
    rw [hfA.yield]
  · show rB.pool'.lossUnrealized.toRat = _
    rw [hL₂]
    show rA.pool'.lossUnrealized.toRat - _ = _
    rw [hfA.loss]
  · intro k hkA hkB
    rw [hlab, if_neg hkB, hla, if_neg hkA]
  · intro k b₀ hb₀ hkAB
    rw [hlab, hla]
    by_cases hkB : k = eB.brokerIndex
    · -- the second payment wrote this broker, from the copy it read
      subst hkB
      rw [if_pos rfl]
      refine ⟨_, rfl, ?_, ?_⟩
      · rw [hfB.broker]
        rw [hla] at hbB₁
        by_cases hkA : eB.brokerIndex = eA.brokerIndex
        · rw [if_pos hkA] at hbB₁
          obtain hbr := Option.some.inj hbB₁
          rw [← hbr, hfA.broker]
          rw [hkA, hbA] at hb₀
          rw [← Option.some.inj hb₀]
        · rw [if_neg hkA, hb₀] at hbB₁
          rw [← Option.some.inj hbB₁]
      · rw [hla] at hbB₁
        by_cases hkA : eB.brokerIndex = eA.brokerIndex
        · rw [if_pos hkA] at hbB₁
          obtain hbr := Option.some.inj hbB₁
          rw [if_pos hkA, if_pos rfl]
          rw [hkA, hbA] at hb₀
          obtain rfl := Option.some.inj hb₀
          rw [← hbr] at hDB
          linarith
        · rw [if_neg hkA, hb₀] at hbB₁
          obtain hbr := Option.some.inj hbB₁
          rw [if_neg hkA, if_pos rfl]
          rw [← hbr] at hDB
          linarith
    · -- only the first payment wrote this broker
      have hkA : k = eA.brokerIndex := hkAB.resolve_right hkB
      subst hkA
      rw [if_neg hkB, if_pos rfl]
      rw [hbA] at hb₀
      obtain rfl := Option.some.inj hb₀
      refine ⟨_, rfl, hfA.broker, ?_⟩
      rw [if_pos rfl, if_neg hkB]
      linarith
  · intro k hki hkj
    rw [hloab, if_neg hkj, hloa, if_neg hki]
  · refine ⟨rA.loan', ?_, hfA.raw⟩
    rw [hloab, if_neg hij, hloa, if_pos rfl]
  · refine ⟨rB.loan', ?_, ?_⟩
    · rw [hloab, if_pos rfl]
    · rw [hfB.raw, htwp.raw]

/-- Two vaults that keep the settings of a third keep each other's. -/
private lemma Vault.KeepsSettings.cross {v w w' : Vault} (h : Vault.KeepsSettings v w)
    (h' : Vault.KeepsSettings v w') : Vault.KeepsSettings w' w :=
  ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm, h.3.trans h'.3.symm, h.4.trans h'.4.symm, h.5.trans h'.5.symm,
    h.6.trans h'.6.symm, h.7.trans h'.7.symm, h.8.trans h'.8.symm⟩

/-- Proof body of `Lending.payments_comm`. -/
lemma LendingLedger.payments_comm_proof (l la lb lab lba : LendingLedger) (hr : l.Reachable) (i j : Nat)
    (hij : i ≠ j) (pt pt' : LoanPaymentType) (a a' : Number)
    (ha : (l.apply (.loanPay i pt a)).run = .ok (.ok la)) (hab : (la.apply (.loanPay j pt' a')).run = .ok (.ok lab))
    (hb : (l.apply (.loanPay j pt' a')).run = .ok (.ok lb)) (hba : (lb.apply (.loanPay i pt a)).run = .ok (.ok lba))
    (htotal : lab.vault.assetsAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ lab.vault.baseExponent) :
    lab.vault = lba.vault ∧
      (∀ k, lab.broker? k = lba.broker? k ∨ ∃ b b', lab.broker? k = some b ∧ lba.broker? k = some b' ∧
        b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable }) ∧
      (∀ k, lab.loan? k = lba.loan? k ∨ ∃ e e', lab.loan? k = some e ∧ lba.loan? k = some e' ∧
        e'.brokerIndex = e.brokerIndex ∧ e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.broker }) := by
  obtain ⟨eA, A, rA, heA, hatA, -, hokA, hla, hksA⟩ := LendingLedger.loanPay_parts ha
  obtain ⟨pA, hpA, -⟩ := Loan.pay_ok A l.vault pt a l.now rA hokA
  obtain ⟨eB, B, rB, heB, hatB, -, hokB, -, -⟩ := LendingLedger.loanPay_parts hb
  obtain ⟨pB, hpB, -⟩ := Loan.pay_ok B l.vault pt' a' l.now rB hokB

  -- AssetsAvailable' below `10^16` base units means each payment of the order `i` then `j` was at base scale
  have hra := hr.apply ha
  obtain ⟨-, B₁, rB₁, -, hatB₁, -, hokB₁, -, -⟩ := LendingLedger.loanPay_parts hab
  obtain ⟨pB₁, hpB₁, -⟩ := Loan.pay_ok B₁ la.vault pt' a' la.now rB₁ hokB₁
  obtain ⟨hk, -⟩ := LendingLedger.keepsLoan_of_loanTx heB rfl (by simp [LendingTx.loanIndex?, hij]) ha
  have htw := LendingLedger.KeepsLoan.twin hr hra hk heB hatB hatB₁
  rw [hk.now] at hpB₁
  obtain ⟨-, hamt⟩ := htw.pay_same hpB hpB₁
  rw [← hk.now] at hpB₁
  have hbeab := LendingLedger.apply_baseExponent hab
  have hbea := LendingLedger.apply_baseExponent ha
  have hB := LendingLedger.pay_below_line hra hab hatB₁ hpB₁ (by rw [← hbeab]; exact htotal)
  rw [hamt] at hB
  obtain ⟨hPB0, hIB0, -⟩ := Loan.pay_parts_nonneg B a' pt' rB l.vault l.now pB hpB hokB
  have hA := LendingLedger.pay_below_line hr ha hatA hpA (by rw [← hbea]; linarith)
  have hAA := (Loan.paid hr hatA hpA hokA hksA).available hA
  have hroom : l.vault.assetsAvailable.toRat + pA.credit + pB.credit <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
    unfold UnsettledPayment.credit
    rw [hla] at hB hbea
    change rA.pool'.assetsAvailable.toRat + _ < 10 ^ 16 * 10 ^ rA.pool'.baseExponent at hB
    rw [hAA, show rA.pool'.baseExponent = l.vault.baseExponent from hbea] at hB
    linarith
  have hAB := LendingLedger.pay_pair hr hij ha hab heA heB hatA hatB hpA hpB hroom
  have hBA := LendingLedger.pay_pair hr (Ne.symm hij) hb hba heB heA hatB hatA hpB hpA
    (by unfold UnsettledPayment.credit at hroom ⊢; linarith)
  refine ⟨?_, ?_, ?_⟩

  -- the vault: the same five balances and the same settings
  · refine Vault.eq_of_balances ?_ ?_ (hAB.reserved.trans hBA.reserved.symm) ?_ ?_
      (hAB.settings.cross hBA.settings)
    · rw [hAB.available, hBA.available]; ring
    · rw [hAB.deployed, hBA.deployed]; ring
    · rw [hAB.loss, hBA.loss]; ring
    · rw [hAB.yield, hBA.yield]; ring

  -- the brokers: the same DebtTotal, each payment's principal taken off once
  · intro k
    by_cases hk : k = eA.brokerIndex ∨ k = eB.brokerIndex
    · right
      obtain ⟨b₀, hb₀⟩ : ∃ b₀, l.broker? k = some b₀ := by
        rcases hk with rfl | rfl
        · exact ⟨_, hatA.broker heA⟩
        · exact ⟨_, hatB.broker heB⟩
      obtain ⟨b, hb, hbraw, hbdt⟩ := hAB.broker k b₀ hb₀ hk
      obtain ⟨b', hb', hb'raw, hb'dt⟩ := hBA.broker k b₀ hb₀ hk.symm
      have hdt : b'.debtTotal = b.debtTotal :=
        b'.wf.debtTotal_norm.toRat_inj b.wf.debtTotal_norm (by rw [hb'dt, hbdt]; ring)
      refine ⟨b, b', hb, hb', ?_⟩
      rw [hb'raw, hbraw, hdt]
    · left
      push Not at hk
      rw [hAB.broker_other k hk.1 hk.2, hBA.broker_other k hk.2 hk.1]

  -- the loans: the same loan, read with each order's copy of its broker
  · intro k
    by_cases hki : k = i
    · subst hki
      right
      obtain ⟨X, hX, hXraw⟩ := hAB.loan_first
      obtain ⟨X', hX', hX'raw⟩ := hBA.loan_second
      exact ⟨_, _, hX, hX', rfl, by rw [hX'raw, hXraw]⟩
    by_cases hkj : k = j
    · subst hkj
      right
      obtain ⟨Y, hY, hYraw⟩ := hAB.loan_second
      obtain ⟨Y', hY', hY'raw⟩ := hBA.loan_first
      exact ⟨_, _, hY, hY', rfl, by rw [hY'raw, hYraw]⟩
    left
    rw [hAB.loan_other k hki hkj, hBA.loan_other k hkj hki]

end XRPL.Model.Lending
