import XRPL.Properties.Lending.Ledger.Common.LoanTxResults
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.DefaultCredit
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Loan.Common.ManageCover

/-! # Impair, unimpair and default through the ledger

Proof bodies of the `LoanManage` headlines. Each one reads the action a successful `l.apply` ran on the loan at
`i` and reuses the proof on the model operation. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- The default `hdef` names is the one a successful LoanManage ran on the loan read at `i`. The ledger after holds
its vault and reads its loan at `i`. -/
private lemma default_named {l l' : LendingLedger} {i : Nat} {loan : Loan} {r : LoanWithAmounts Vault}
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) (hat : l.LoanAt i loan)
    (hdef : (loan.manageDefault l.vault).run = .ok (.ok r)) :
    l'.vault = r.pool' ∧ l'.LoanAt i r.loan' := by
  obtain ⟨_, loan₀, r₀, -, hat₀, -, hdef₀, -, hv, hat', -⟩ := LendingLedger.loanDefault_ok h
  rw [hat₀.eq hat, hdef] at hdef₀
  have hr : r₀ = r := (Except.ok.inj (Except.ok.inj hdef₀)).symm
  rw [hr] at hv hat'
  exact ⟨hv, hat'⟩

/-- A ledger with broker `b₁` put in the slot of broker `b` reads `b₁` there. -/
private lemma broker?_set {l : LendingLedger} {j : Nat} {b b₁ : LoanBroker} (hb : l.broker? j = some b) :
    ({ l with brokers := l.brokers.set j (some b₁) } : LendingLedger).broker? j = some b₁ := by
  unfold LendingLedger.broker? at hb ⊢
  have hj : j < l.brokers.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hb
    cases hb
  simp [hj]

variable {l l' : LendingLedger} {i : Nat}

/-- Proof body of the loan part of `Lending.default_updates`. -/
lemma LendingLedger.manageDefault_closes_proof (h : (l.apply (.loanManage i .default)).run = .ok (.ok l'))
    {loan' : Loan} (hat' : l'.LoanAt i loan') :
    loan'.principalOutstanding = Number.zero ∧ loan'.totalValueOutstanding = Number.zero ∧
      loan'.managementFeeOutstanding = Number.zero ∧ loan'.paymentRemaining = 0 ∧
      loan'.nextPaymentDueDate = 0 ∧ loan'.isDefault = true := by
  obtain ⟨_, _, r, -, -, -, hdef, -, -, hat'₀, -⟩ := LendingLedger.loanDefault_ok h
  rw [hat'.eq hat'₀]
  exact Loan.manageDefault_closes_proof _ _ r hdef

/-- Proof body of `Lending.manageDefault_coverAvailable`. -/
lemma LendingLedger.manageDefault_coverAvailable_proof (h : (l.apply (.loanManage i .default)).run = .ok (.ok l'))
    {loan loan' : Loan} (hat : l.LoanAt i loan) (hat' : l'.LoanAt i loan') {r : LoanWithAmounts Vault}
    (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = loan.broker.coverAvailable.toRat - r.amountToPool.toRat) :
    loan'.broker.coverAvailable.toRat = loan.broker.coverAvailable.toRat - r.amountToPool.toRat := by
  rw [hat'.eq (default_named h hat hdef).2]
  exact Loan.manageDefault_coverAvailable_proof _ _ r hdef hexact

/-- Proof body of `Lending.manageDefault_cover_upper_bound`. -/
lemma LendingLedger.manageDefault_cover_upper_bound_proof (h : (l.apply (.loanManage i .default)).run = .ok (.ok l'))
    {loan : Loan} (hat : l.LoanAt i loan) {minimumCover liquidationAmount : Number} {r : LoanWithAmounts Vault}
    (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount) :
    r.amountToPool.toRat -
      min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat ≤ 0 := by
  obtain ⟨-, -⟩ := default_named h hat hdef
  exact Loan.manageDefault_cover_upper_bound_proof _ _ _ _ r hdef hmin hliq

/-- Proof body of the loan and LossUnrealized part of `Lending.impair_updates`. -/
lemma LendingLedger.manageImpair_loss_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .impair)).run = .ok (.ok l')) {loan loan' : Loan} (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') :
    loan'.toRawLoan = { loan.toRawLoan with isImpaired := true } ∧
      l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat + loan.principalOutstanding.toRat ∧
      l'.vault.toRawVault = { l.vault.toRawVault with lossUnrealized := l'.vault.lossUnrealized } := by
  obtain ⟨_, _, r, -, hat₀, -, hok, -, hv, hat'₀, -⟩ := LendingLedger.loanImpair_ok h
  rw [hat₀.eq hat] at hok
  rw [hat'.eq hat'₀, hv]
  exact Loan.manageImpair_loss_proof _ _ _ r hok hr.availableStored (hr.impair_fits hat)

/-- Proof body of `Lending.manageUnimpair_loss`. -/
lemma LendingLedger.manageUnimpair_loss_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .unimpair)).run = .ok (.ok l')) {loan loan' : Loan} (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') :
    loan'.toRawLoan = { loan.toRawLoan with isImpaired := false } ∧
      l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat - loan.principalOutstanding.toRat ∧
      l'.vault.toRawVault = { l.vault.toRawVault with lossUnrealized := l'.vault.lossUnrealized } := by
  obtain ⟨_, _, r, -, hat₀, -, hok, -, hv, hat'₀, -⟩ := LendingLedger.loanUnimpair_ok h
  rw [hat₀.eq hat] at hok
  rw [hat'.eq hat'₀, hv]
  exact Loan.manageUnimpair_loss_proof _ _ r hok hr.availableStored (hr.unimpair_fits hat)

/-- Proof body of the vault part of `Lending.default_updates`. -/
lemma LendingLedger.manageDefault_vault_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan)
    {r : LoanWithAmounts Vault} (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hsupply : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) :
    l'.vault.toExact.assetsTotal =
        l.vault.toExact.assetsTotal - (loan.principalOutstanding.toRat - r.amountToPool.toRat) ∧
      l'.vault.assetsAvailable.toRat = l.vault.assetsAvailable.toRat + r.amountToPool.toRat := by
  rw [(default_named h hat hdef).1]
  exact LendingLedger.manageDefault_vault_exact_proof l hr i loan hat r hdef hsupply

/-- A default -> YieldUnrealized' = YieldUnrealized − interestDue. -/
lemma LendingLedger.manageDefault_yield_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan) :
    l'.vault.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat - loan.toExact.interestDue := by
  obtain ⟨_, _, r, -, hat₀, -, hdef, -, hv, -⟩ := LendingLedger.loanDefault_ok h
  rw [hat₀.eq hat] at hdef
  rw [hv]
  exact Loan.manageDefault_yield_proof _ _ r hdef (hr.yield_fits hat hr.yield_lt)

/-- Defaulting an impaired loan -> LossUnrealized' = LossUnrealized − PrincipalOutstanding. -/
lemma LendingLedger.manageDefault_loss_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan)
    (himp : loan.isImpaired = true) :
    l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat - loan.principalOutstanding.toRat := by
  obtain ⟨_, _, r, -, hat₀, -, hdef, -, hv, -⟩ := LendingLedger.loanDefault_ok h
  rw [hat₀.eq hat] at hdef
  rw [hv]
  exact Loan.manageDefault_loss_proof _ _ r hdef himp (hr.unimpair_fits hat)

/-- A default -> AssetsDeployed and DebtTotal each drop by PrincipalOutstanding. -/
lemma LendingLedger.manageDefault_principal_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) {loan loan' : Loan} (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') :
    l.vault.assetsDeployed.toRat - l'.vault.assetsDeployed.toRat = loan.principalOutstanding.toRat ∧
      loan.broker.debtTotal.toRat - loan'.broker.debtTotal.toRat = loan.principalOutstanding.toRat := by
  obtain ⟨_, _, r, -, hat₀, -, hdef, -, hv, hat'₀, -⟩ := LendingLedger.loanDefault_ok h
  rw [hat₀.eq hat] at hdef
  rw [hat'.eq hat'₀, hv]
  exact Loan.manageDefault_principal_proof _ _ r hdef (hr.deployed_fits hat) (hr.debt_fits hat)

/-- Proof body of the lower bound part of `Lending.manageDefault_cover`. -/
lemma LendingLedger.manageDefault_cover_lower_bound_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan)
    {minimumCover liquidationAmount : Number} {r : LoanWithAmounts Vault}
    (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∀ e, numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e →
      min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat -
        r.amountToPool.toRat < 10 ^ e := by
  rw [(default_named h hat hdef).1]
  exact LendingLedger.loanDefault_cover_lower_bound l hr i loan hat _ _ r hdef hmin hliq htotal

/-- Proof body of the nonnegative part of `Lending.manageDefault_cover`. -/
lemma LendingLedger.manageDefault_cover_nonneg_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan)
    {r : LoanWithAmounts Vault} (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    0 ≤ r.amountToPool.toRat := by
  obtain ⟨-, -⟩ := default_named h hat hdef
  exact LendingLedger.loanDefault_cover_nonneg l hr i loan hat r hdef htotal

/-- Proof body of the monotone part of `Lending.manageDefault_cover`. The ledger `l` with the larger cover is the
reachable one, `l₁` is `l` with the smaller broker `b₁` in the loan's broker slot. -/
lemma LendingLedger.manageDefault_cover_monotone_proof (hr : l.Reachable)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) {e : LoanEntry} (he : l.loan? i = some e)
    {b b₁ : LoanBroker} (hb : l.broker? e.brokerIndex = some b)
    (hb₁ : b₁.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b₁.coverAvailable })
    (hle : b₁.coverAvailable.toRat ≤ b.coverAvailable.toRat) {l₁ l₁' : LendingLedger}
    (hl₁ : l₁ = { l with brokers := l.brokers.set e.brokerIndex (some b₁) })
    (h₁ : (l₁.apply (.loanManage i .default)).run = .ok (.ok l₁'))
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    l.vault.toExact.assetsTotal - l'.vault.toExact.assetsTotal ≤
      l₁.vault.toExact.assetsTotal - l₁'.vault.toExact.assetsTotal := by
  subst hl₁
  obtain ⟨_, loan, r₂, -, hat, -, hdef₂, -, hv₂, -⟩ := LendingLedger.loanDefault_ok h
  obtain ⟨_, loan₁, r₁, -, hat₁, -, hdef₁, -, hv₁, -⟩ := LendingLedger.loanDefault_ok h₁
  obtain ⟨e₂, he₂, hb₂, hraw⟩ := hat.stored
  obtain ⟨e₃, he₃, hb₃, hraw₁⟩ := hat₁.stored
  -- both ledgers store the entry `e` at `i`, and read it with `b` and `b₁`
  have hee₂ : e₂ = e := Option.some.inj (he₂.symm.trans he)
  have hee₃ : e₃ = e := Option.some.inj (he₃.symm.trans he)
  rw [hee₂] at hb₂ hraw
  rw [hee₃] at hb₃ hraw₁
  have hbr : loan.broker = b := Option.some.inj (hb₂.symm.trans hb)
  have hbr₁ : loan₁.broker = b₁ := Option.some.inj (hb₃.symm.trans (broker?_set hb))
  have hloan : loan.toRawLoan = { loan₁.toRawLoan with broker := loan.broker } := by
    rw [hraw₁]
    exact hraw
  have hbroker : loan.broker.toRawLoanBroker =
      { loan₁.broker.toRawLoanBroker with coverAvailable := loan.broker.coverAvailable } := by
    rw [hbr, hbr₁, hb₁]
  have hle' : loan₁.broker.coverAvailable.toRat ≤ loan.broker.coverAvailable.toRat := by
    rw [hbr, hbr₁]
    exact hle
  rw [hv₂, hv₁]
  exact LendingLedger.loanDefault_cover_monotone l hr i loan hat loan₁ r₁ r₂ hloan hbroker hle' hdef₁ hdef₂
    htotal

end XRPL.Model.Lending
