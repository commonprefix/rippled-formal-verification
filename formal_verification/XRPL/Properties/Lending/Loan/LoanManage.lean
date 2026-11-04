import XRPL.Properties.Lending.Loan.Common.ManageLedger
import XRPL.Properties.Lending.Loan.Common.ManageLedgerWitness

/-! # `LoanManage`: impair, unimpair and default

What impair, unimpair and default write to the loan, the vault and the broker, how impair and default move the share
value, and the cover a default pays (`r.amountToPool`). Each theorem takes a successful LoanManage on the loan at `i`
from the ledger `l` to `l'`, which reads `loan` on `l` and `loan'` on `l'`. `r` is the result of the impair or default
on `loan`, with `r.pool'` the vault after it. shareValue = (AssetsTotal − LossUnrealized) / SharesTotal, read
exactly. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault RawVault)

variable (l : LendingLedger)

/-- Default -> loan marked defaulted and closed, AssetsTotal falls by PrincipalOutstanding − defaultCovered,
AssetsAvailable grows by defaultCovered, and shareValue falls by that loss per share, less the LossUnrealized freed. -/
theorem Lending.default_updates (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (loan' : Loan) (hat' : l'.LoanAt i loan') (r : LoanWithAmounts Vault)
    (hdef : (loan.manageDefault l.vault).run = .ok (.ok r)) :
    (loan'.principalOutstanding = Number.zero ∧ loan'.totalValueOutstanding = Number.zero ∧
      loan'.managementFeeOutstanding = Number.zero ∧ loan'.paymentRemaining = 0 ∧
      loan'.nextPaymentDueDate = 0 ∧ loan'.isDefault = true) ∧
    -- the last three lines: the MPT supply limit, an MPT vault and its broker hold less than `2^63` units
    -- together, the model does not track the two pseudo-account balances
    ((l.vault.numericType = NumericType.int64 →
        l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) →
      l'.vault.toExact.assetsTotal =
          l.vault.toExact.assetsTotal - (loan.principalOutstanding.toRat - r.amountToPool.toRat) ∧
        l'.vault.assetsAvailable.toRat = l.vault.assetsAvailable.toRat + r.amountToPool.toRat) ∧
    (loan.isImpaired = false →
      (l.vault.numericType = NumericType.int64 →
          l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) →
        l.vault.shareValue - r.pool'.shareValue =
          (loan.principalOutstanding.toRat - r.amountToPool.toRat) / l.vault.toExact.sharesTotal) ∧
    -- holds for any default, not only of an impaired loan
    ((l.vault.numericType = NumericType.int64 →
        l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) →
      r.pool'.shareValue - l.vault.shareValue =
        (l.vault.lossUnrealized.toRat - r.pool'.lossUnrealized.toRat -
          (loan.principalOutstanding.toRat - r.amountToPool.toRat)) / l.vault.toExact.sharesTotal) :=
  ⟨LendingLedger.manageDefault_closes_proof h hat', LendingLedger.manageDefault_vault_proof hr h hat hdef,
    LendingLedger.default_share_value_exact_proof l hr i loan hat r hdef,
    LendingLedger.default_impaired_share_value_exact_proof l hr i loan hat r hdef⟩

/-- Default -> CoverAvailable' = CoverAvailable − defaultCovered.
`hexact` - the new CoverAvailable fits a Number -/
theorem Lending.manageDefault_coverAvailable (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan) (loan' : Loan)
    (hat' : l'.LoanAt i loan') (r : LoanWithAmounts Vault) (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = loan.broker.coverAvailable.toRat - r.amountToPool.toRat) :
    loan'.broker.coverAvailable.toRat = loan.broker.coverAvailable.toRat - r.amountToPool.toRat :=
  LendingLedger.manageDefault_coverAvailable_proof h hat hat' hdef hexact

/-- Witness: a reachable run where they differ. A LoanServiceFee of `10^12` paid into a cover below its minimum
leaves `1000000000001` at the scale `10^-10`, and a default of `1.0000000001` leaves `10^12`. -/
theorem Lending.manageDefault_coverAvailable_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan) (r : LoanWithAmounts Vault),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      l'.LoanAt i loan' ∧ (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      loan'.broker.coverAvailable.toRat ≠ loan.broker.coverAvailable.toRat - r.amountToPool.toRat :=
  LendingLedger.manageDefault_coverAvailable_witness

/-- Default -> defaultCovered − min(liquidationAmount, PrincipalOutstanding, CoverAvailable) ≤ 0. -/
theorem Lending.manageDefault_cover_upper_bound (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (minimumCover liquidationAmount : Number) (r : LoanWithAmounts Vault)
    (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount) :
    r.amountToPool.toRat -
      min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat ≤ 0 :=
  LendingLedger.manageDefault_cover_upper_bound_proof h hat hdef hmin hliq

/-- Witness: a run where they are equal. A loan of 100 with a liquidation amount of 1000 and 5000 of
cover is covered in full. -/
theorem Lending.manageDefault_cover_upper_bound_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan) (minimumCover liquidationAmount : Number)
      (r : LoanWithAmounts Vault),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      r.amountToPool.toRat -
        min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat = 0 :=
  LendingLedger.manageDefault_cover_upper_bound_witness

/-- Impair -> loan marked impaired and no other loan field changes, LossUnrealized grows by PrincipalOutstanding and
no other vault field changes, and shareValue drops by that loss over SharesTotal. -/
theorem Lending.impair_updates (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanManage i .impair)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan) (loan' : Loan)
    (hat' : l'.LoanAt i loan') (r : LoanWithPool Vault) (hok : (loan.manageImpair l.vault l.now).run = .ok (.ok r)) :
    (loan'.toRawLoan = { loan.toRawLoan with isImpaired := true } ∧
      l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat + loan.principalOutstanding.toRat ∧
      l'.vault.toRawVault = { l.vault.toRawVault with lossUnrealized := l'.vault.lossUnrealized }) ∧
    l.vault.shareValue - r.pool'.shareValue =
      (r.pool'.lossUnrealized.toRat - l.vault.lossUnrealized.toRat) / l.vault.toExact.sharesTotal :=
  ⟨LendingLedger.manageImpair_loss_proof hr h hat hat',
    Loan.impair_share_value_proof loan l.vault l.now r hok hr.availableStored⟩

/-- Unimpair -> loan marked unimpaired and no other loan field changes, LossUnrealized' = LossUnrealized −
PrincipalOutstanding and no other vault field changes. -/
theorem Lending.manageUnimpair_loss (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanManage i .unimpair)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (loan' : Loan) (hat' : l'.LoanAt i loan') :
    loan'.toRawLoan = { loan.toRawLoan with isImpaired := false } ∧
      l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat - loan.principalOutstanding.toRat ∧
      l'.vault.toRawVault = { l.vault.toRawVault with lossUnrealized := l'.vault.lossUnrealized } :=
  LendingLedger.manageUnimpair_loss_proof hr h hat hat'

/-- Default -> defaultCovered is less than 1 ULP under min(liquidationAmount, PrincipalOutstanding, CoverAvailable),
never negative, and more cover never makes the vault lose more. -/
theorem Lending.manageDefault_cover (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (minimumCover liquidationAmount : Number) (r : LoanWithAmounts Vault)
    (hdef : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount) :
    -- all three lines: the vault is not coarsened
    (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      ∀ e, numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e →
        min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat -
          r.amountToPool.toRat < 10 ^ e) ∧
    (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      0 ≤ r.amountToPool.toRat) ∧
    -- `l₁` is `l` with a broker `b₁` of less cover in the loan's broker slot
    (∀ (e : LoanEntry) (b b₁ : LoanBroker) (l₁ l₁' : LendingLedger), l.loan? i = some e →
      l.broker? e.brokerIndex = some b →
      b₁.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b₁.coverAvailable } →
      b₁.coverAvailable.toRat ≤ b.coverAvailable.toRat →
      l₁ = { l with brokers := l.brokers.set e.brokerIndex (some b₁) } →
      (l₁.apply (.loanManage i .default)).run = .ok (.ok l₁') →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent →
      l.vault.toExact.assetsTotal - l'.vault.toExact.assetsTotal ≤
        l₁.vault.toExact.assetsTotal - l₁'.vault.toExact.assetsTotal) :=
  ⟨LendingLedger.manageDefault_cover_lower_bound_proof hr h hat hdef hmin hliq,
    LendingLedger.manageDefault_cover_nonneg_proof hr h hat hdef,
    fun _ _ _ _ _ he hb hb₁ hle hl₁ h₁ => LendingLedger.manageDefault_cover_monotone_proof hr h he hb hb₁ hle hl₁ h₁⟩

/-- Witness: a run where min(liquidationAmount, PrincipalOutstanding, CoverAvailable) − defaultCovered = 9.9999 ULP. On
the coarsened vault AssetsAvailable is `999999999999999.9`, and loan B's default pays the vault `-0.9`. -/
theorem Lending.manageDefault_cover_lower_bound_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan) (minimumCover liquidationAmount : Number)
      (r : LoanWithAmounts Vault) (e : Int),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      numberExponent l'.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e ∧
      min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat -
        r.amountToPool.toRat = (99999 / 10000 : ℚ) * 10 ^ e :=
  LendingLedger.manageDefault_cover_lower_bound_witness

/-- Witness: a run where defaultCovered < 0. On the coarsened vault AssetsAvailable is `999999999999999.9`, and the
default of loan B pays the vault `-0.9`. -/
theorem Lending.manageDefault_cover_nonneg_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan : Loan) (r : LoanWithAmounts Vault),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧ r.amountToPool.toRat < 0 :=
  LendingLedger.manageDefault_cover_nonneg_witness

/-- Witness: a run where a larger CoverAvailable makes AssetsTotal − AssetsTotal' larger. On the coarsened vault loan
B with its cover of `0.1` loses 1.9 of AssetsTotal, and the same loan on a broker with `0.09` of cover loses 1. -/
theorem Lending.manageDefault_cover_monotone_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (e : LoanEntry) (b b₁ : LoanBroker) (l₁ l₁' : LendingLedger),
      l.Reachable ∧ (l.apply (.loanManage i .default)).run = .ok (.ok l') ∧ l.loan? i = some e ∧
      l.broker? e.brokerIndex = some b ∧
      b₁.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b₁.coverAvailable } ∧
      b₁.coverAvailable.toRat ≤ b.coverAvailable.toRat ∧
      l₁ = { l with brokers := l.brokers.set e.brokerIndex (some b₁) } ∧
      (l₁.apply (.loanManage i .default)).run = .ok (.ok l₁') ∧
      l₁.vault.toExact.assetsTotal - l₁'.vault.toExact.assetsTotal <
        l.vault.toExact.assetsTotal - l'.vault.toExact.assetsTotal :=
  LendingLedger.manageDefault_cover_monotone_witness

end XRPL.Model
