import XRPL.Properties.Lending.Ledger.Common.ShareValueWitness
import XRPL.Properties.Lending.Ledger.Common.VaultOutflow
import XRPL.Properties.Lending.Loan.Common.ShareValue
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.DefaultCoverWitness
import XRPL.Properties.Lending.Ledger.Common.PayoffWitness
import XRPL.Properties.Lending.Ledger.Common.DefaultCredit
import XRPL.Properties.Lending.Ledger.Common.PaymentShareBound
import XRPL.Properties.Lending.Ledger.Common.PaymentShareLarge

/-! # Share value around payments and default

shareValue = (AssetsTotal − LossUnrealized) / SharesTotal, read exactly. defaultCovered is the cover a default
pays the vault. The actions run on a reachable ledger's vault, on the loan stored at `i` read with its broker.
`l.PaysLoan i fits l' paid` is a run from `l` to `l'` that never defaults the loan at `i`, where `paid` sums
AssetsAvailable' − AssetsAvailable over its payments of that loan, and each payment satisfies `fits`. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault RawVault)

variable (l : LendingLedger)

/-- Payment -> shareValue' − shareValue ≥ 0, where shareValue = (AssetsTotal − LossUnrealized) / SharesTotal. -/
theorem Lending.payment_share_value (hr : l.Reachable) (l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType)
    (amount : Number) (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan : Loan)
    (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    -- the vault is not coarsened after the payment: AssetsAvailable' stays below 10^16 base units (FV_M4_25)
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    l.vault.toRawVault.shareValue ≤ l'.vault.toRawVault.shareValue :=
  LendingLedger.payment_share_value_proof l hr l' i paymentType amount h loan hat payment hpay htotal

/-- Witness: a run where shareValue' − shareValue < 0. On a coarsened vault an instalment of 1.5 without interest is
credited as 1. -/
theorem Lending.payment_share_value_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (paymentType : LoanPaymentType) (amount : Number) (loan : Loan)
      (payment : UnsettledPayment Vault),
      l.Reachable ∧ (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧
      (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment) ∧
      l'.vault.toRawVault.shareValue < l.vault.toRawVault.shareValue :=
  LendingLedger.payment_share_value_falls_reachable

/-- Loan paid off -> Σ (AssetsAvailable' − AssetsAvailable) over its payments ≥ PrincipalRequested. The run from `l`
never defaults the loan, and PrincipalOutstanding is PrincipalRequested until the first payment. -/
theorem Lending.Reachable.payoff_returns_principal (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (l' : LendingLedger) (paid : ℚ)
    -- each payment of the loan keeps AssetsAvailable plus its credit below `10^16` base units
    (hrun : l.PaysLoan i (fun l₁ paymentType amount => l₁.PaymentFits i paymentType amount) l' paid)
    (hoff : ∃ e, l'.loan? i = some e ∧ e.loan.paymentRemaining = 0) :
    loan.principalOutstanding.toRat ≤ paid :=
  LendingLedger.payoff_returns_principal_proof l hr i loan hat l' paid hrun hoff

/-- Witness: a run where the sum < PrincipalRequested. On a coarsened vault loan D of 3 is paid off with two
instalments of 1.5 that are each credited as 1. -/
theorem Lending.Reachable.payoff_returns_principal_attained :
    ∃ (l : LendingLedger) (i : Nat) (loan : Loan) (l' : LendingLedger) (paid : ℚ),
      l.Reachable ∧ l.LoanAt i loan ∧ l.PaysLoan i (fun _ _ _ => True) l' paid ∧
      (∃ e, l'.loan? i = some e ∧ e.loan.paymentRemaining = 0) ∧ paid < loan.principalOutstanding.toRat :=
  LendingLedger.payoff_short_run_reachable

/-- Default with min(liquidationAmount, CoverAvailable) ≥ PrincipalOutstanding -> defaultCovered = PrincipalOutstanding
and AssetsTotal' = AssetsTotal, liquidationAmount = DebtTotal × CoverRateMinimum × CoverRateLiquidation rounded up. -/
theorem Lending.default_fully_covered (hr : l.Reachable) (i : Nat) (loan : Loan) (hat : l.LoanAt i loan)
    (minimumCover liquidationAmount : Number) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hcov : loan.principalOutstanding.toRat ≤ min liquidationAmount.toRat loan.broker.coverAvailable.toRat)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) : -- the vault is not coarsened
    r.amountToPool.toRat = loan.principalOutstanding.toRat ∧
      r.pool'.toExact.assetsTotal = l.vault.toExact.assetsTotal :=
  LendingLedger.default_fully_covered_proof l hr i loan hat minimumCover liquidationAmount r hok hmin hliq hcov htotal

/-- Witness: a run where AssetsTotal' < AssetsTotal. On the coarsened vault AssetsAvailable is `999999999999999.9`,
loan B of 1 is covered in full, yet the cover pays only `0.1` and AssetsTotal drops by `0.9`. -/
theorem Lending.default_fully_covered_attained :
    ∃ (l : LendingLedger) (i : Nat) (loan : Loan) (minimumCover liquidationAmount : Number)
      (r : LoanWithAmounts Vault),
      l.Reachable ∧ l.LoanAt i loan ∧ (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      loan.principalOutstanding.toRat ≤ min liquidationAmount.toRat loan.broker.coverAvailable.toRat ∧
      r.amountToPool.toRat < loan.principalOutstanding.toRat ∧
      r.pool'.toExact.assetsTotal < l.vault.toExact.assetsTotal :=
  LendingLedger.default_fully_covered_loss_reachable

/-- VaultWithdraw or VaultClawback -> it pays at most AssetsAvailable and AssetsDeployed is unchanged. -/
theorem Lending.lent_out_protected (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (htx : (∃ holder amount, tx = .vaultWithdraw holder amount) ∨ ∃ holder assets, tx = .vaultClawback holder assets)
    (h : (l.apply tx).run = .ok (.ok l')) :
    0 ≤ l'.vault.assetsAvailable.toRat ∧ l'.vault.assetsAvailable.toRat ≤ l.vault.assetsAvailable.toRat ∧
      l'.vault.assetsDeployed = l.vault.assetsDeployed :=
  LendingLedger.lent_out_protected_proof l l' tx hr hr.holdsAsset.maxValue_le htx h

end XRPL.Model
