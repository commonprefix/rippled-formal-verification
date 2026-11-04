import XRPL.Properties.Lending.Ledger.Common.PaymentSettles
import XRPL.Properties.Lending.Loan.Common.DueLoop

/-! # A payment that passes its checks succeeds

A payment of at least the amount due of its first instalment, an overpayment of exactly that amount, on a loan
stored on a reachable ledger, pays its instalments: a late or full payment its one instalment, a regular payment or
an overpayment the scheduled instalments its amount covers. It then settles while the vault is not coarsened, no
interest part is negative, and the vault gets principal or interest or the loan is paid off. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A loan stored on a reachable ledger has what the instalment loop needs to compute its next instalment, while
160 times an XRP loan's TotalValueOutstanding stays below `10^17` drops. -/
lemma LendingLedger.Reachable.loopRoom {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan)
    (hxrp : l.vault.numericType = .native → 160 * loan.totalValueOutstanding.toRat + 1 ≤ 10 ^ 17) :
    loan.LoopRoom := by
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
  have hbase := Vault.baseExponent_scale_range l.vault
  obtain ⟨hlo, -, hint⟩ := hreach.loanScale_facts
  have hs0 : loan.loanScale ≤ 0 := by rw [hls]; exact hbase.2
  have hp1 : (10 : ℚ) ^ loan.loanScale ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hs0
  have hT := Loan.Reachable.totalValue_le hreach
  have hT' : loan.totalValueOutstanding.toRat ≤ 10 ^ 16 + 1 :=
    le_trans hT (mul_le_of_le_one_right (by norm_num) hp1)
  have hroom := hreach.paymentRoom
  have hasset : loan.broker.numericType = .fractional ∨ loan.broker.numericType = .native ∨
      loan.broker.numericType = .int64 := by rw [hnt]; exact hr.holdsAsset
  obtain ⟨bS, hS0, -, -, -, -⟩ := hreach.fees_below
  obtain ⟨e, b, he, -, hw⟩ := hat
  have hraw := Loan.withBroker_eq hw
  have hsched : loan.schedule = e.loan.schedule := (congrArg RawLoan.schedule hraw :)
  obtain ⟨s, hls'⟩ := hr.loansInv
  have hmat := hls'.mature i e he
  have hred : s.redemptionDate.toNat < 2 ^ 32 := s.redemptionDate.toNat_lt
  have hprle := UInt32.le_iff_toNat_le.mp (Loan.Reachable.paymentRemaining_le loan t hreach)
  have hclock : loan.paymentRemaining.toNat * loan.schedule.paymentInterval.toNat < 2 ^ 32 := by
    rw [hsched] at hprle ⊢
    have h1 := Nat.mul_le_mul_right e.loan.schedule.paymentInterval.toNat hprle
    rw [Nat.mul_comm e.loan.schedule.paymentTotal.toNat] at h1
    unfold loanRedemptionBuffer at hmat
    generalize e.loan.schedule.paymentInterval.toNat * e.loan.schedule.paymentTotal.toNat = A at h1 hmat
    generalize loan.paymentRemaining.toNat * e.loan.schedule.paymentInterval.toNat = B at h1 ⊢
    omega
  -- the payments left are worth less than twice TotalValueOutstanding on XRP or an MPT
  have hfits : loan.broker.numericType.isIntegral = true → 2 ≤ loan.paymentRemaining.toNat →
      80 * ((loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat) + 1 ≤
        loan.broker.numericType.maxValue.toNat := by
    intro hintg h2
    have hrem : loan.paymentRemaining ≠ 0 := fun h0 => by rw [h0] at h2; simp at h2
    obtain ⟨pp', hpp'⟩ := hreach.scheduleComputes.payment hrem
    have hneeds := hreach.needsAllPayments hrem pp' hpp'
    have hppN := loan.wf.periodicPayment_norm
    have hpp0 : 0 < loan.periodicPayment.toRat := loan.exact.periodicPayment_pos
    have hle : loan.periodicPayment.toRat ≤ pp'.toRat :=
      (STAmount.roundToNumericType_int_grid _ hintg _ _ .upward _ hppN hpp0.le (Or.inr (Or.inl rfl)) hpp').2.2.1 rfl
    have hprq : (2 : ℚ) ≤ loan.paymentRemaining.toNat := by exact_mod_cast h2
    have hlt : (loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat <
        2 * loan.totalValueOutstanding.toRat := by nlinarith
    rcases hasset with h | h | h
    · rw [h] at hintg; cases hintg
    · have hx := hxrp (by rw [← hnt, h])
      rw [h]
      have : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
      rw [this]
      linarith
    · rw [h]
      have : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
      rw [this]
      linarith
  exact ⟨⟨by omega, hint, hreach.interestDue_nonneg⟩, hs0, hT', hreach.scheduleComputes,
    fun h2 => le_trans (hroom.periodic h2) (by nlinarith), hclock, hasset, hfits, bS, hS0⟩

/-- A LoanPay that passes its preflight pays an amount above zero that the vault's asset holds exactly. -/
lemma LendingTx.loanPay_preflight_ok {l : LendingLedger} {i : Nat} {pt : LoanPaymentType} {amount : Number}
    (h : (LendingTx.loanPay i pt amount).preflight l = .tesSUCCESS) :
    amount.isNormalized ∧ 0 < amount.toRat ∧ STAmount.isRounded l.vault.numericType amount = false := by
  simp only [LendingTx.preflight] at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, isPositiveInput, decide_eq_true_eq] at hc
  obtain ⟨⟨hN, hpos⟩, heq⟩ := hc
  refine ⟨hN, ?_, ?_⟩
  · have := (operator_lt_iff Number.zero amount Number.zero_isNormalized hN).mp hpos
    rwa [Number.toRat_zero] at this
  · unfold STAmount.isRounded
    cases hcv : STAmount.equalAfterNumberConvert l.vault.numericType amount with
    | error e => rw [hcv] at heq; simp [Except.toOption] at heq
    | ok b => rw [hcv] at heq; simp [Except.toOption] at heq; simp [heq]

/-- Proof body of the payment line of `Lending.loan_ops_total`. -/
lemma LendingLedger.payment_total_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (i : Nat) (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pt : LoanPaymentType) (pc : PaymentComponents)
    (td amount : Number) (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b)
    (hw : e.loan.withBroker b = .ok loan) (hc : loan.canPay pt = .tesSUCCESS)
    (hlate : pt = .late ↔ loan.isPaymentLate l.now = true) (hfull : pt = .full → loan.paymentRemaining ≠ 1)
    (hpc : loan.paymentComponents pt l.now = .ok pc) (htd : pc.totalDue = .ok td)
    (hamt : td.toRat ≤ amount.toRat) (hover : pt = .overpayment → amount = td)
    (hpre : (LendingTx.loanPay i pt amount).preflight l = .tesSUCCESS)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hparts : ∀ p, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) →
      0 ≤ p.amounts.interestPaid.toRat)
    (hcredit : ∀ p, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p) →
      0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0)
    (hxrp : l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14)
    (hca : b.coverAvailable.toRat < 10 ^ 96) (hfit : l.CreditFits i pt amount) (hfee : l.FeeFits i pt amount) :
    ∃ l', (l.apply (.loanPay i pt amount)).run = .ok (.ok l') := by
  have hat : l.LoanAt i loan := ⟨e, b, he, hb, hw⟩
  have hxrp' : l.vault.numericType = .native → 160 * loan.totalValueOutstanding.toRat + 1 ≤ 10 ^ 17 :=
    fun h => by have := hxrp h; linarith
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat
  have hbase := Vault.baseExponent_scale_range l.vault
  have hs0 : loan.loanScale ≤ 0 := by rw [hls]; exact hbase.2
  obtain ⟨hlo, -, hint⟩ := hreach.loanScale_facts
  have hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair l.vault).run = .ok (.ok r) :=
    fun himp => hr.manageUnimpair_ok hat himp
  obtain ⟨-, hrem, -⟩ := Loan.canPay_active hc
  have hdd := Loan.Reachable.nextPaymentDueDate_ne_zero loan t hreach hrem
  obtain ⟨hamtN, hamt0, hrep⟩ := LendingTx.loanPay_preflight_ok hpre
  have hnl : pt ≠ .late → loan.isPaymentLate l.now = false := by
    intro hpt
    cases h : loan.isPaymentLate l.now
    · rfl
    · exact absurd (hlate.mpr h) hpt
  obtain ⟨q, hq, hqF, hqi⟩ : ∃ q, (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok q) ∧
      0 ≤ q.amounts.feePaid.toRat ∧ 0 ≤ q.loan.toExact.interestDue := by
    cases pt with
    | late =>
      obtain ⟨q, hq, hqF⟩ := Loan.latePayInstalments_due hreach hs0 l.vault l.now hc (hlate.mp rfl) hunimpair pc td
        amount hpc htd hamtN hamt
      exact ⟨q, hq, hqF, Loan.payInstalments_interestDue loan l.vault .late amount l.now q (by decide) (by omega) hint
        hreach.interestDue_nonneg hq⟩
    | full =>
      obtain ⟨q, hq, hqF⟩ := Loan.fullPayInstalments_due hreach hs0 l.vault l.now hc (hnl (by decide)) (hfull rfl)
        hunimpair pc td amount hpc htd hamtN hamt
      exact ⟨q, hq, hqF, Loan.payInstalments_interestDue loan l.vault .full amount l.now q (by decide) (by omega) hint
        hreach.interestDue_nonneg hq⟩
    | regular =>
      obtain ⟨q, hq, hqF, -, -⟩ := Loan.regularPayInstalments_due loan (hr.loopRoom hat hxrp') l.vault l.now hc hdd
        (hnl (by decide)) hunimpair pc td amount hpc htd hamtN hamt
      exact ⟨q, hq, hqF, Loan.payInstalments_interestDue loan l.vault .regular amount l.now q (by decide) (by omega)
        hint hreach.interestDue_nonneg hq⟩
    | overpayment =>
      obtain rfl := hover rfl
      obtain ⟨q, hq, hqr, hqF⟩ := Loan.overPayInstalments_due loan (hr.loopRoom hat hxrp') l.vault l.now hc hdd
        (hnl (by decide)) hunimpair pc amount hpc htd hamtN hamt0.le (by rw [hnt]; exact hrep)
      exact ⟨q, hq, hqF, Loan.payInstalments_interestDue loan l.vault .regular amount l.now q (by decide) (by omega)
        hint hreach.interestDue_nonneg hqr⟩
  exact hr.pay_of_instalments hnd he hb hw pt amount hc hpre q hq hqi htotal (hparts q hq) hqF (hcredit q hq) hca hfit
    hfee

end XRPL.Model.Lending
