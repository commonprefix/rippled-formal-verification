import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Loan.LoanValid
import XRPL.Properties.Protocol.Common.FixedWidth

/-! # LoanPay read in two stages

A payment first pays its instalments, then settles the summed amounts with the vault and the broker. The
definitions here name the two stages so the payment theorems can state their conditions on them. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.lateComponents Loan.fullComponents Loan.unimpairIfImpaired
  Loan.payScheduledInstalments UnsettledPayment.applyOverpayment UnsettledPayment.payInstalments
  Loan.doPayment Loan.settlePayment Loan.paySingleInstalment validatePostPayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- The payment a LoanPay transaction makes for its payment type. -/
def Loan.pay {α : Type} [AssetPool α] (loan : Loan) (pool : α) (paymentType : LoanPaymentType)
    (amount : Number) (now : UInt32) : TerExcept (LoanWithAmounts α) :=
  match paymentType with
  | .regular => loan.regularPayment pool amount now
  | .late => loan.latePayment pool amount now
  | .full => loan.fullPayment pool amount now
  | .overpayment => loan.overpayment pool amount now

/-- An instalment other than the last that passed had a payment left, and its next due date fits the ledger
clock. -/
lemma Loan.doPayment_ok_checks (l : Loan) (pc : PaymentComponents) (r : Loan) (hf : pc.isFinal = false)
    (h : Loan.doPayment l pc = .ok r) :
    1 ≤ l.paymentRemaining ∧ l.nextPaymentDueDate.toNat + l.schedule.paymentInterval.toNat < 2 ^ 32 := by
  unfold Loan.doPayment at h
  simp only [hf, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i c1 hc1
  split at h
  · cases h
  rename_i c2 hc2
  exact ⟨(UInt32.subChecked_eq_ok.mp hc1).1, (UInt32.addChecked_eq_ok.mp hc2).1⟩

/-- One instalment before it is settled, late, full or a single scheduled one: the amount check, then the loan
advanced by the instalment. -/
def Loan.payInstalment {α : Type} [AssetPool α] (loan : Loan) (pool : α) (pc : PaymentComponents)
    (amount : Number) : TerExcept (UnsettledPayment α) := do
  let totalDue ← pc.totalDue
  if amount.operator_lt totalDue then
    throw .tecINSUFFICIENT_PAYMENT
  let scheduledInterest ← loan.interestDue
  let amounts ← pc.paidAmounts
  let loan' ← Loan.doPayment loan pc
  return { loan := loan', pool := pool, amounts := amounts, totalPaid := totalDue, count := 1,
           scheduledInterest := scheduledInterest }

/-- The instalments a payment pays before it settles with the vault and the broker. It returns the
paid loan, the vault after the unimpair, the summed amounts and the interestDue before the payment. -/
def Loan.payInstalments {α : Type} [AssetPool α] (loan : Loan) (pool : α) (paymentType : LoanPaymentType)
    (amount : Number) (now : UInt32) : TerExcept (UnsettledPayment α) :=
  match paymentType with
  | .regular => Loan.payScheduledInstalments loan pool amount now
  | .overpayment => do
    let payment ← Loan.payScheduledInstalments loan pool amount now
    UnsettledPayment.applyOverpayment payment amount
  | .late => do
    if loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero then
      throw .tecKILLED
    if loan.nextPaymentDueDate == 0 then throw .tecINTERNAL
    if !(loan.isPaymentLate now) then throw .tecTOO_SOON
    let ⟨loan, pool⟩ ← Loan.unimpairIfImpaired loan pool
    let pc ← Loan.lateComponents loan now
    loan.payInstalment pool pc amount
  | .full => do
    if loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero then
      throw .tecKILLED
    if loan.nextPaymentDueDate == 0 then throw .tecINTERNAL
    if loan.isPaymentLate now then throw .tecEXPIRED
    if loan.paymentRemaining ≤ 1 then throw .tecKILLED
    let ⟨loan, pool⟩ ← Loan.unimpairIfImpaired loan pool
    let pc ← Loan.fullComponents loan now
    loan.payInstalment pool pc amount

/-- The first instalment a payment pays: the next scheduled one with LoanServiceFee, the late one, or
the full payoff. -/
def Loan.paymentComponents (loan : Loan) (paymentType : LoanPaymentType) (now : UInt32) :
    Except Error PaymentComponents :=
  match paymentType with
  | .regular | .overpayment => do
    let pc ← Loan.scheduledComponents loan
    return { pc with untrackedManagementFee := loan.fees.serviceFee }
  | .late => Loan.lateComponents loan now
  | .full => Loan.fullComponents loan now

/-- The payment passes the checks before the unimpair: the loan is not paid off and has a due date, a late payment
comes after NextPaymentDueDate and the other payments at or before it, and a full payment is not the last. -/
structure Loan.PayChecks (loan : Loan) (paymentType : LoanPaymentType) (now : UInt32) : Prop where
  remaining : loan.paymentRemaining ≠ 0
  principal : loan.principalOutstanding ≠ Number.zero
  due : loan.nextPaymentDueDate ≠ 0
  date : paymentType = .late ↔ loan.nextPaymentDueDate < now
  full : paymentType = .full → loan.paymentRemaining ≠ 1

/-- The balance change a payment makes to the vault: the credit joins AssetsAvailable, principalPaid
leaves AssetsDeployed, and YieldUnrealized follows the change of interestDue. -/
def UnsettledPayment.change (payment : UnsettledPayment Vault) (toPool yieldDelta : Number) :
    PoolBalanceChange :=
  { cash := toPool, deployed := payment.amounts.principalPaid.operator_neg, yield := yieldDelta }

/-- The amounts the settlement computes before it updates the vault: the credit `toPool`, `yieldDelta` =
interestDue' − interestDue, the fee `toBroker`, the new CoverAvailable `cover'` and DebtTotal `debtTotal'`. -/
structure UnsettledPayment.SettleSums (payment : UnsettledPayment Vault)
    (toPool yieldDelta toBroker cover' debtTotal' : Number) : Prop where
  parts : (payment.amounts.principalPaid.signum < 0 || payment.amounts.interestPaid.signum < 0 ||
    payment.amounts.feePaid.signum < 0) = false
  yield : ∃ interestDue', payment.loan.interestDue = .ok interestDue' ∧
    interestDue'.operator_sub payment.scheduledInterest .to_nearest = .ok yieldDelta
  toPool : ∃ totalPaid credit,
    payment.amounts.principalPaid.operator_add payment.amounts.interestPaid .to_nearest = .ok totalPaid ∧
    sumRoundAndSubtract payment.pool.assetsAvailable totalPaid payment.pool.baseExponent
      payment.loan.broker.numericType .downward = .ok credit ∧
    credit.toNumber .to_nearest = .ok toPool
  fee : (payment.loan.broker.hasMinimumCover payment.pool.baseExponent = .ok true ∧
      toBroker = payment.amounts.feePaid ∧ cover' = payment.loan.broker.coverAvailable) ∨
    (payment.loan.broker.hasMinimumCover payment.pool.baseExponent = .ok false ∧
      ∃ feeToCover, sumRoundAndSubtract payment.loan.broker.coverAvailable payment.amounts.feePaid
          payment.pool.baseExponent payment.loan.broker.numericType .downward = .ok feeToCover ∧
        feeToCover.toNumber .to_nearest = .ok toBroker ∧
        payment.loan.broker.coverAvailable.operator_add toBroker .to_nearest = .ok cover')
  debt : payment.loan.broker.debtTotal.operator_sub payment.amounts.principalPaid .to_nearest = .ok debtTotal'

/-! ## The two stages put together -/

private lemma ite_bind' {m : Type → Type} [Monad m] {α β : Type} (c : Prop) [Decidable c] (x y : m α)
    (f : α → m β) : ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

private lemma throw_bind' {α β : Type} (e : TER) (f : α → TerExcept β) :
    ((throw e : TerExcept α) >>= f) = throw e := rfl

/-- Every payment pays its instalments, then settles them. -/
lemma Loan.pay_run {α : Type} [AssetPool α] (loan : Loan) (pool : α) (paymentType : LoanPaymentType)
    (amount : Number) (now : UInt32) :
    (loan.pay pool paymentType amount now).run =
      (do let p ← loan.payInstalments pool paymentType amount now
          Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run := by
  cases paymentType
  · rfl
  · simp only [Loan.pay, Loan.payInstalments, Loan.latePayment, Loan.payInstalment, Loan.paySingleInstalment,
      bind_assoc, pure_bind, ite_bind', throw_bind']
  · simp only [Loan.pay, Loan.payInstalments, Loan.fullPayment, Loan.payInstalment, Loan.paySingleInstalment,
      bind_assoc, pure_bind, ite_bind', throw_bind']
  · simp only [Loan.pay, Loan.payInstalments, Loan.overpayment, bind_assoc]

/-- A payment whose instalments pass settles them with the vault and the broker. -/
lemma Loan.pay_settle (loan : Loan) (v : Vault) (paymentType : LoanPaymentType) (amount : Number)
    (now : UInt32) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment)) :
    (loan.pay v paymentType amount now).run =
      (Loan.settlePayment payment.loan payment.pool payment.amounts payment.scheduledInterest).run := by
  rw [Loan.pay_run]
  simp only [ExceptT.run] at hpay
  unfold_ter
  simp [hpay]

/-- The settlement once its amounts are computed: the vault update, the broker and loan re-checks, then
the pool re-check. -/
lemma UnsettledPayment.SettleSums.run_eq {payment : UnsettledPayment Vault}
    {toPool yieldDelta toBroker cover' debtTotal' : Number}
    (hsums : payment.SettleSums toPool yieldDelta toBroker cover' debtTotal') :
    (Loan.settlePayment payment.loan payment.pool payment.amounts payment.scheduledInterest).run =
      (do
        let pool' ← AssetPool.adjustBalances payment.pool (payment.change toPool yieldDelta)
        let broker' ← ({ payment.loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := cover' }
            : RawLoanBroker).to_lawful
        let loan' ← ({ payment.loan.toRawLoan with broker := broker' } : RawLoan).to_lawful
        validatePostPayment payment.pool
          { loan' := loan', pool' := pool', amountToPool := toPool, amountToBroker := toBroker } :
        TerExcept _).run := by
  obtain ⟨i', hi', hyd⟩ := hsums.yield
  obtain ⟨tp, credit, htp, hcredit, hto⟩ := hsums.toPool
  simp only [Loan.settlePayment]
  unfold_ter
  rcases hsums.fee with ⟨hc, rfl, rfl⟩ | ⟨hc, fc, hfc, hfb, hcov⟩
  · simp [hsums.parts, Vault.pool_amounts, Vault.pool_baseExponent, hc, hi', hyd, htp, hcredit, hto, hsums.debt,
      UnsettledPayment.change]
  · simp [hsums.parts, Vault.pool_amounts, Vault.pool_baseExponent, hc, hi', hyd, htp, hcredit, hto, hsums.debt,
      hfc, hfb, hcov, UnsettledPayment.change]

/-- `Number.operator_ne` is false exactly on equal numbers. -/
lemma Number.operator_ne_false_iff_eq' (x y : Number) : x.operator_ne y = false ↔ x = y := by
  unfold Number.operator_ne
  rw [← Number.operator_eq_iff_eq]
  cases x.operator_eq y <;> simp

lemma Loan.principal_operator_eq_zero (loan : Loan) (hpo : loan.principalOutstanding ≠ Number.zero) :
    loan.principalOutstanding.operator_eq Number.zero = false := by
  rw [Bool.eq_false_iff]; intro h; exact hpo ((Number.operator_eq_iff_eq _ _).mp h)

/-- The paid-off check fires exactly when PaymentRemaining = 0 or PrincipalOutstanding = 0. -/
lemma Loan.paid_off_iff (loan : Loan) :
    (loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero) = true ↔
      loan.paymentRemaining = 0 ∨ loan.principalOutstanding = Number.zero := by
  rw [Bool.or_eq_true, beq_iff_eq, Number.operator_eq_iff_eq]

lemma Loan.not_paid_off (loan : Loan) (hr : loan.paymentRemaining ≠ 0)
    (hpo : loan.principalOutstanding ≠ Number.zero) :
    (loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero) = false := by
  have h1 : (loan.paymentRemaining == 0) = false := by simpa using hr
  rw [h1, loan.principal_operator_eq_zero hpo]; rfl

/-- A loan with a due date passes the due date check. Reachable loans with payments left have one. -/
lemma Loan.nextPaymentDueDate_ne_zero (loan : Loan) (hdue : loan.nextPaymentDueDate ≠ 0) :
    (loan.nextPaymentDueDate == 0) = false := by
  simpa using hdue

/-- The due date check never fires on a loan that passed the paid-off check, when payments left mean a due date. -/
lemma Loan.due_date_set (loan : Loan) (hdue : loan.paymentRemaining ≠ 0 → loan.nextPaymentDueDate ≠ 0)
    (h : ¬(loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero) = true) :
    ¬(loan.nextPaymentDueDate == 0) = true := by
  have hr : loan.paymentRemaining ≠ 0 := fun h0 => h ((Loan.paid_off_iff loan).mpr (Or.inl h0))
  rw [Loan.nextPaymentDueDate_ne_zero loan (hdue hr)]; decide

/-- A lawful loan's interestDue computes. -/
lemma Loan.interestDue_ok (loan : Loan) : ∃ i, loan.interestDue = .ok i := by
  have h := loan.valid.interest_nonneg
  unfold RawLoan.interestNonneg at h
  split at h
  · exact ⟨_, by assumption⟩
  · exact absurd h (by decide)

lemma Loan.PayChecks.not_late {loan : Loan} {paymentType : LoanPaymentType} {now : UInt32}
    (h : loan.PayChecks paymentType now) (hpt : paymentType ≠ .late) : ¬ loan.nextPaymentDueDate < now :=
  fun hl => hpt (h.date.mpr hl)

lemma Loan.PayChecks.more_than_one {loan : Loan} {now : UInt32} (h : loan.PayChecks .full now) :
    ¬ loan.paymentRemaining ≤ 1 := by
  have hr := h.remaining
  have h1 := h.full rfl
  intro hle
  rw [UInt32.le_iff_toNat_le] at hle
  have : loan.paymentRemaining.toNat ≠ 0 := by
    intro h0; exact hr (UInt32.toNat_inj.mp (by simpa using h0))
  have : loan.paymentRemaining.toNat ≠ 1 := by
    intro h0; exact h1 (UInt32.toNat_inj.mp (by simpa using h0))
  simp at hle; omega

/-! ## The unimpair -/

private lemma RawLoan.wf_unimpaired (rl : RawLoan) (h : rl.WF) : ({ rl with isImpaired := false } : RawLoan).WF :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12⟩

private lemma RawLoan.valid_unimpaired (rl : RawLoan) (h : rl.Valid) :
    ({ rl with isImpaired := false } : RawLoan).Valid :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17, h.18, h.19,
    h.20, h.21, h.22, h.23⟩

/-- The loan without the impaired flag. -/
def Loan.unimpaired (loan : Loan) : Loan :=
  { toRawLoan := { loan.toRawLoan with isImpaired := false }
    wf := RawLoan.wf_unimpaired _ loan.wf
    valid := RawLoan.valid_unimpaired _ loan.valid }

private lemma Loan.unimpaired_to_lawful (loan : Loan) :
    ({ loan.toRawLoan with isImpaired := false } : RawLoan).to_lawful = .ok loan.unimpaired := by
  unfold RawLoan.to_lawful
  rw [dif_pos ⟨RawLoan.wf_unimpaired _ loan.wf, RawLoan.valid_unimpaired _ loan.valid⟩]
  rfl

lemma Loan.unimpaired_of_not (loan : Loan) (h : loan.isImpaired = false) : loan.unimpaired = loan := by
  obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩, _, _⟩ := loan
  simp only at h
  subst h
  rfl

lemma Loan.unimpairIfImpaired_not (loan : Loan) (v : Vault) (h : loan.isImpaired = false) :
    (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := loan, pool' := v }) := by
  simp [Loan.unimpairIfImpaired, h]

lemma Loan.unimpairIfImpaired_impaired (loan : Loan) (v : Vault) (h : loan.isImpaired = true) :
    (Loan.unimpairIfImpaired loan v).run =
      (match AssetPool.adjustBalances v { loss := loan.principalOutstanding.operator_neg } with
       | .error e => .error e
       | .ok (.error t) => .ok (.error t)
       | .ok (.ok v1) => .ok (.ok { loan' := loan.unimpaired, pool' := v1 })) := by
  simp only [Loan.unimpairIfImpaired, h, ↓reduceIte, Loan.manageUnimpair, Loan.changeImpairment]
  unfold_ter
  simp only [Bool.false_eq_true, ↓reduceIte, Loan.unimpaired_to_lawful]
  rcases AssetPool.adjustBalances v { loss := loan.principalOutstanding.operator_neg } with e | t | v1 <;> rfl

private lemma Loan.manageUnimpair_ok (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.manageUnimpair v).run = .ok (.ok r)) :
    AssetPool.adjustBalances v { loss := loan.principalOutstanding.operator_neg } = .ok (.ok r.pool') ∧
      r.loan' = loan.unimpaired := by
  simp only [Loan.manageUnimpair, Loan.changeImpairment] at h
  unfold_ter at h
  simp only [Bool.false_eq_true, ↓reduceIte, Loan.unimpaired_to_lawful] at h
  rcases hadj : AssetPool.adjustBalances v { loss := loan.principalOutstanding.operator_neg } with e | t | v1 <;>
    rw [hadj] at h
  · cases h
  · cases h
  · obtain rfl : { loan' := loan.unimpaired, pool' := v1 } = r := by injection h with h; injection h
    exact ⟨rfl, rfl⟩

/-- When the unimpair of an impaired loan passes, the payment goes on with the loan without the impaired
flag. -/
lemma Loan.unimpairIfImpaired_ok (loan : Loan) (v : Vault)
    (hunimpair : loan.isImpaired = true → ∃ r, (loan.manageUnimpair v).run = .ok (.ok r)) :
    ∃ v1, (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := loan.unimpaired, pool' := v1 }) := by
  cases himp : loan.isImpaired
  · refine ⟨v, ?_⟩
    rw [Loan.unimpairIfImpaired_not loan v himp, Loan.unimpaired_of_not loan himp]
  · obtain ⟨r, hr⟩ := hunimpair himp
    obtain ⟨hadj, -⟩ := Loan.manageUnimpair_ok loan v r hr
    refine ⟨r.pool', ?_⟩
    rw [Loan.unimpairIfImpaired_impaired loan v himp, hadj]

/-- The instalment amounts never read the impaired flag. -/
lemma Loan.scheduledComponents_unimpaired (loan : Loan) :
    Loan.scheduledComponents loan.unimpaired = Loan.scheduledComponents loan := rfl

lemma Loan.lateComponents_unimpaired (loan : Loan) (now : UInt32) :
    Loan.lateComponents loan.unimpaired now = Loan.lateComponents loan now := rfl

lemma Loan.fullComponents_unimpaired (loan : Loan) (now : UInt32) :
    Loan.fullComponents loan.unimpaired now = Loan.fullComponents loan now := rfl

lemma Loan.interestDue_unimpaired (loan : Loan) : loan.unimpaired.interestDue = loan.interestDue := rfl

end XRPL.Model.Lending
