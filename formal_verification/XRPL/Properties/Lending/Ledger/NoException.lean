import XRPL.Properties.Lending.Ledger.Common.NoExceptionVaultDeposit
import XRPL.Properties.Lending.Ledger.Common.NoExceptionVaultDepositWitness
import XRPL.Properties.Lending.Ledger.Common.NoExceptionVaultWithdraw
import XRPL.Properties.Lending.Ledger.Common.NoExceptionVaultWithdrawWitness
import XRPL.Properties.Lending.Ledger.Common.NoExceptionBrokerSet
import XRPL.Properties.Lending.Ledger.Common.NoExceptionBrokerCover
import XRPL.Properties.Lending.Ledger.Common.NoExceptionBrokerDebit
import XRPL.Properties.Lending.Ledger.Common.NoExceptionBrokerWitness
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSet
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanSetWitness
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanManage
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayOverpayment
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayWitness
import XRPL.Properties.Lending.Ledger.Lawful

/-! # Every transaction returns a result code

On a reachable ledger a transaction ends in a result code, never in a model error (a C++ exception, `tefEXCEPTION`).
Where C++ throws, the theorem carries the hypothesis that keeps it out and an `_attained` witness shows the error. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (WithdrawAmount VaultAmounts computeClawback)

variable (l : LendingLedger)

/-- VaultDeposit on a reachable ledger, AssetsTotal plus the amount within the largest amount of the asset -> a
result code, never an exception. -/
theorem Lending.vaultDeposit_no_exception (hr : l.Reachable) (h : Nat) (amount : STAmount) (isDonation : Bool)
    -- the Open limit check builds AssetsTotal + amount as an amount of the asset (FV_M4_52)
    (hrange : l.vault.toExact.assetsTotal + amount.toRat ≤ l.vault.numericType.maxAmount) :
    ∃ r, (l.apply (.vaultDeposit h amount isDonation)).run = .ok r :=
  LendingLedger.vaultDeposit_no_exception_proof l hr h amount isDonation hrange

/-- Witness for `vaultDeposit_no_exception`: on a reachable XRP ledger a deposit that takes AssetsTotal above the
largest XRP amount ends in an error. -/
theorem Lending.vaultDeposit_no_exception_attained :
    ∃ (l : LendingLedger) (h : Nat) (amount : STAmount) (isDonation : Bool),
      l.Reachable ∧
      l.vault.numericType = NumericType.native ∧
      (LendingTx.vaultDeposit h amount isDonation).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < l.vault.toExact.assetsTotal + amount.toRat ∧
      (l.apply (.vaultDeposit h amount isDonation)).run = .error .outOfRange :=
  LendingLedger.vaultDeposit_exception_xrp_witness

/-- Witness for `vaultDeposit_no_exception`: the same on a reachable MPT ledger. -/
theorem Lending.vaultDeposit_no_exception_mpt_attained :
    ∃ (l : LendingLedger) (h : Nat) (amount : STAmount) (isDonation : Bool),
      l.Reachable ∧
      l.vault.numericType = NumericType.int64 ∧
      (LendingTx.vaultDeposit h amount isDonation).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < l.vault.toExact.assetsTotal + amount.toRat ∧
      (l.apply (.vaultDeposit h amount isDonation)).run = .error .overflow :=
  LendingLedger.vaultDeposit_exception_mpt_witness

/-- VaultWithdraw on a reachable ledger, on XRP the shares redeemed worth at most `10^17` drops -> a result code,
never an exception. -/
theorem Lending.vaultWithdraw_no_exception (hr : l.Reachable) (h : Nat) (amount : WithdrawAmount)
    -- the shares are priced as an XRP amount before the holder's shares are checked (FV_M2_25)
    (hxrp : l.vault.numericType = NumericType.native → ∀ shares : STAmount, amount = .vaultShares shares →
      l.vault.idealAssetsWithdraw (l.isSoleShareholder h) shares.toRat ≤ 10 ^ 17) :
    ∃ r, (l.apply (.vaultWithdraw h amount)).run = .ok r :=
  LendingLedger.vaultWithdraw_no_exception_proof l hr h amount
    ((VaultDepositNoException.reachable_sharesSum hr).sharesOf_le hr.sharesNonneg h) hxrp

/-- Witness for `vaultWithdraw_no_exception`: on a reachable XRP ledger an account without shares redeems shares
worth more than `10^17` drops and the withdrawal ends in an error. -/
theorem Lending.vaultWithdraw_no_exception_attained :
    ∃ (l : LendingLedger) (h : Nat) (shares : STAmount),
      l.Reachable ∧
      l.vault.numericType = NumericType.native ∧
      (LendingTx.vaultWithdraw h (.vaultShares shares)).preflight l = .tesSUCCESS ∧
      (10 : ℚ) ^ 17 < l.vault.idealAssetsWithdraw (l.isSoleShareholder h) shares.toRat ∧
      (l.apply (.vaultWithdraw h (.vaultShares shares))).run = .error .outOfRange := by
  obtain ⟨l, h, shares, hr, hnt, -, hpre, hworth, herr⟩ := LendingLedger.vaultWithdraw_out_of_range_witness
  exact ⟨l, h, shares, hr, hnt, hpre, hworth, herr⟩

/-- VaultClawback of assets on a reachable ledger -> a result code, never an exception. -/
theorem Lending.vaultClawback_no_exception (hr : l.Reachable) (h : Nat) (assets : STAmount)
    -- the holder owns the shares the clawback destroys, which C++ accountSend checks
    (hheld : ∀ (hs : STAmount) (amounts : VaultAmounts),
      STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
      (computeClawback l.vault assets hs (l.isSoleShareholder h)).run = .ok (.ok amounts) →
      amounts.shares.toRat ≤ (l.sharesOf h).toRat)
    -- an MPT vault holds less than `10^16` units: above it a full clawback fails its re-check (FV_M4_36, FV_M4_38)
    (htotal : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∃ r, (l.apply (.vaultClawback h assets)).run = .ok r :=
  LendingLedger.vaultClawback_no_exception_proof l hr h assets
    ⟨(VaultDepositNoException.reachable_sharesSum hr).sharesOf_whole h, (hr.sharesNonneg.sharesOf h).2,
      (VaultDepositNoException.reachable_sharesSum hr).sharesOf_le hr.sharesNonneg h⟩ hheld htotal

/-- Witness for `vaultClawback_no_exception`: on a reachable ledger a clawback from a holder that owns the shares
destroyed ends in an error, the failed re-check of FV_M4_36 and FV_M4_38. -/
theorem Lending.vaultClawback_no_exception_attained :
    ∃ (l : LendingLedger) (h : Nat) (assets : STAmount),
      l.Reachable ∧
      (∀ (hs : STAmount) (amounts : VaultAmounts), STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
        (computeClawback l.vault assets hs (l.isSoleShareholder h)).run = .ok (.ok amounts) →
        amounts.shares.toRat ≤ (l.sharesOf h).toRat) ∧
      (l.apply (.vaultClawback h assets)).run = .error .notLawful := by
  obtain ⟨l, h, assets, hr, -, hheld, herr⟩ := Lending.transactions_lawful_attained
  exact ⟨l, h, assets, hr, hheld, herr⟩

/-- VaultClawback of shares on a reachable ledger -> a result code, never an exception. -/
theorem Lending.vaultBurnShares_no_exception (hr : l.Reachable) (h : Nat) (amount : STAmount) :
    ∃ r, (l.apply (.vaultBurnShares h amount)).run = .ok r :=
  LendingLedger.vaultBurnShares_no_exception_proof l hr h amount
    ⟨(VaultDepositNoException.reachable_sharesSum hr).sharesOf_whole h, (hr.sharesNonneg.sharesOf h).2,
      (VaultDepositNoException.reachable_sharesSum hr).sharesOf_le hr.sharesNonneg h⟩

/-- VaultSet on a reachable ledger -> a result code, never an exception. -/
theorem Lending.vaultSet_no_exception (hr : l.Reachable) (assetsMaximum : Option Number)
    (blockDeposit : Option Bool) : ∃ r, (l.apply (.vaultSet assetsMaximum blockDeposit)).run = .ok r :=
  LendingLedger.vaultSet_no_exception_proof l hr assetsMaximum blockDeposit

/-- VaultDelete -> a result code, never an exception. -/
theorem Lending.vaultDelete_no_exception : ∃ r, (l.apply .vaultDelete).run = .ok r :=
  LendingLedger.vaultDelete_no_exception_proof l

/-- LoanBrokerSet that creates a broker on a reachable ledger -> a result code, never an exception. -/
theorem Lending.loanBrokerCreate_no_exception (hr : l.Reachable) (tx : LoanBrokerSetCreate) :
    ∃ r, (l.apply (.loanBrokerCreate tx)).run = .ok r :=
  LendingLedger.loanBrokerCreate_no_exception_proof l hr tx

/-- LoanBrokerSet that updates a broker on a reachable ledger -> a result code, never an exception. -/
theorem Lending.loanBrokerUpdate_no_exception (hr : l.Reachable) (i : Nat) (debtMaximum : Option Number) :
    ∃ r, (l.apply (.loanBrokerUpdate i debtMaximum)).run = .ok r :=
  LendingLedger.loanBrokerUpdate_no_exception_proof l hr i debtMaximum

/-- LoanBrokerCoverDeposit on a reachable ledger, CoverAvailable plus the amount within the largest amount of the
asset -> a result code, never an exception. -/
theorem Lending.loanBrokerCoverDeposit_no_exception (hr : l.Reachable) (i : Nat) (amount : STAmount)
    -- the Open limit check builds CoverAvailable + amount as an amount of the asset (FV_M3_10)
    (hrange : ∀ b, l.broker? i = some b →
      b.coverAvailable.toRat + amount.toRat ≤ l.vault.numericType.maxAmount)
    -- an IOU: proven up to `10^89`
    (hiou : l.vault.numericType.isIntegral = false → ∀ b, l.broker? i = some b →
      b.coverAvailable.toRat + amount.toRat ≤ iouProofCap) :
    ∃ r, (l.apply (.loanBrokerCoverDeposit i amount)).run = .ok r :=
  LendingLedger.loanBrokerCoverDeposit_no_exception_proof l hr i amount hrange hiou

/-- Witness for `loanBrokerCoverDeposit_no_exception`: on a reachable XRP ledger a deposit that takes CoverAvailable
above the largest XRP amount ends in an error. -/
theorem Lending.loanBrokerCoverDeposit_no_exception_attained :
    ∃ (l : LendingLedger) (i : Nat) (amount : STAmount) (b : LoanBroker),
      l.Reachable ∧
      l.vault.numericType = NumericType.native ∧
      l.broker? i = some b ∧
      (LendingTx.loanBrokerCoverDeposit i amount).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < b.coverAvailable.toRat + amount.toRat ∧
      (l.apply (.loanBrokerCoverDeposit i amount)).run = .error .outOfRange :=
  LendingLedger.loanBrokerCoverDeposit_exception_witness

/-- Witness for `loanBrokerCoverDeposit_no_exception`: the same on a reachable MPT ledger. -/
theorem Lending.loanBrokerCoverDeposit_no_exception_mpt_attained :
    ∃ (l : LendingLedger) (i : Nat) (amount : STAmount) (b : LoanBroker),
      l.Reachable ∧
      l.vault.numericType = NumericType.int64 ∧
      l.broker? i = some b ∧
      (LendingTx.loanBrokerCoverDeposit i amount).preflight l = .tesSUCCESS ∧
      l.vault.numericType.maxAmount < b.coverAvailable.toRat + amount.toRat ∧
      (l.apply (.loanBrokerCoverDeposit i amount)).run = .error .overflow :=
  LendingLedger.loanBrokerCoverDeposit_exception_witness_mpt

/-- LoanBrokerCoverWithdraw on a reachable ledger -> a result code, never an exception. -/
theorem Lending.loanBrokerCoverWithdraw_no_exception (hr : l.Reachable) (i : Nat) (amount : STAmount)
    -- CoverAvailable is a balance of the asset
    (hcover : ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount)
    -- an IOU: proven up to `10^89`
    (hiou : l.vault.numericType.isIntegral = false → amount.toRat ≤ iouProofCap ∧
      ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ iouProofCap) :
    ∃ r, (l.apply (.loanBrokerCoverWithdraw i amount)).run = .ok r :=
  LendingLedger.loanBrokerCoverWithdraw_no_exception_proof l hr i amount hcover hiou

/-- LoanBrokerCoverClawback on a reachable ledger -> a result code, never an exception. -/
theorem Lending.loanBrokerCoverClawback_no_exception (hr : l.Reachable) (i : Nat) (amount : Option STAmount)
    -- the asset stores CoverAvailable. C++ associateAsset keeps an IOU cover so
    (hrep : ∀ b, l.broker? i = some b → STAmount.isRounded b.numericType b.coverAvailable = false)
    -- an IOU: proven up to `10^89`
    (hiou : l.vault.numericType.isIntegral = false →
      ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ iouProofCap) :
    ∃ r, (l.apply (.loanBrokerCoverClawback i amount)).run = .ok r :=
  LendingLedger.loanBrokerCoverClawback_no_exception_proof l hr i amount hrep hiou

/-- LoanBrokerDelete on a reachable ledger -> a result code, never an exception. -/
theorem Lending.loanBrokerDelete_no_exception (hr : l.Reachable) (i : Nat)
    -- CoverAvailable is a balance of the asset
    (hcover : ∀ b, l.broker? i = some b → b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount) :
    ∃ r, (l.apply (.loanBrokerDelete i)).run = .ok r :=
  LendingLedger.loanBrokerDelete_no_exception_proof l hr i hcover

/-- LoanSet on a reachable ledger, on XRP or an MPT the total value of the loan within the largest amount of the
asset, on an MPT also the vault total -> a result code, never an exception. -/
theorem Lending.loanSet_no_exception (hr : l.Reachable) (i : Nat) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
    (twoStep allowsOverpayment : Bool)
    -- LoanCount does not wrap. C++ LoanSequence stops a broker before `2^32` loans
    (hcount : ∀ b, l.broker? i = some b → b.loanCount + 1 ≠ 0)
    -- an MPT total of `2^63` or `2^63 + 1` is stored rounded down. On XRP the stored total is the exact sum
    (htotal : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat)
    -- PeriodicPayment × PaymentTotal is rounded to an amount of the asset before any check on it (FV_M4_51)
    (hvalue : l.vault.numericType.isIntegral = true → ∀ rate periodicPayment : Number,
      loanPeriodicRate rates.interestRate (paymentInterval.getD defaultPaymentInterval) = .ok rate →
      loanPeriodicPayment principal rate (paymentTotal.getD defaultPaymentTotal) = .ok periodicPayment →
      periodicPayment.toRat * (paymentTotal.getD defaultPaymentTotal).toNat ≤ l.vault.numericType.maxValue.toNat) :
    ∃ r, (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment)).run = .ok r :=
  LendingLedger.loanSet_no_exception_proof l hr i principal rates fees paymentInterval paymentTotal gracePeriod
    startDate twoStep allowsOverpayment hcount htotal hvalue

/-- Witness for `loanSet_no_exception`: on a reachable XRP ledger a LoanSet whose PeriodicPayment × PaymentTotal is
above the largest XRP amount ends in an error. -/
theorem Lending.loanSet_no_exception_attained :
    ∃ (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32) (twoStep allowsOverpayment : Bool)
      (rate periodicPayment : Number),
      l.Reachable ∧
      (∀ b, l.broker? i = some b → b.loanCount + 1 ≠ 0) ∧
      l.vault.numericType = NumericType.native ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat ∧
      loanPeriodicRate rates.interestRate (paymentInterval.getD defaultPaymentInterval) = .ok rate ∧
      loanPeriodicPayment principal rate (paymentTotal.getD defaultPaymentTotal) = .ok periodicPayment ∧
      (l.vault.numericType.maxValue.toNat : ℚ) < periodicPayment.toRat * (paymentTotal.getD defaultPaymentTotal).toNat ∧
      (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .error .outOfRange :=
  LendingLedger.loanSet_value_exception_witness

/-- Witness for `loanSet_no_exception`: the same on a reachable MPT ledger. -/
theorem Lending.loanSet_no_exception_mpt_attained :
    ∃ (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32) (twoStep allowsOverpayment : Bool)
      (rate periodicPayment : Number),
      l.Reachable ∧
      (∀ b, l.broker? i = some b → b.loanCount + 1 ≠ 0) ∧
      l.vault.numericType = NumericType.int64 ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat ∧
      loanPeriodicRate rates.interestRate (paymentInterval.getD defaultPaymentInterval) = .ok rate ∧
      loanPeriodicPayment principal rate (paymentTotal.getD defaultPaymentTotal) = .ok periodicPayment ∧
      (l.vault.numericType.maxValue.toNat : ℚ) < periodicPayment.toRat * (paymentTotal.getD defaultPaymentTotal).toNat ∧
      (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run = .error .overflow :=
  LendingLedger.loanSet_value_exception_mpt_witness

/-- LoanAccept on a reachable ledger -> a result code, never an exception. -/
theorem Lending.loanAccept_no_exception (hr : l.Reachable) (i : Nat) :
    ∃ r, (l.apply (.loanAccept i)).run = .ok r :=
  LendingLedger.loanAccept_no_exception_proof l hr i

/-- LoanDelete on a reachable ledger -> a result code, never an exception. -/
theorem Lending.loanDelete_no_exception (hr : l.Reachable) (i : Nat)
    -- a pending loan on an MPT or an IOU: the vault account holds AssetsAvailable and the reserved principal, so
    -- their sum is an amount of the asset. On XRP the total the vault stored bounds the sum
    (hroom : l.vault.numericType ≠ NumericType.native → ∀ e, l.loan? i = some e → e.loan.isPending = true →
      l.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat ≤ l.vault.numericType.maxAmount) :
    ∃ r, (l.apply (.loanDelete i)).run = .ok r :=
  LendingLedger.loanDelete_no_exception_proof l hr i hroom

/-- LoanManage on a reachable ledger -> a result code, never an exception. -/
theorem Lending.loanManage_no_exception (hr : l.Reachable) (i : Nat) (action : LoanManageAction)
    -- default: CoverAvailable is a balance of the asset, and on an MPT or an IOU AssetsAvailable plus the cover
    -- paid is an amount of it. On XRP the total the vault stored bounds the sum
    (hcover : action = .default → ∀ e b, l.loan? i = some e → l.broker? e.brokerIndex = some b →
      b.coverAvailable.toRat ≤ l.vault.numericType.maxAmount ∧
      (l.vault.numericType ≠ NumericType.native →
        l.vault.assetsAvailable.toRat + min e.loan.principalOutstanding.toRat b.coverAvailable.toRat ≤
          l.vault.numericType.maxAmount))
    -- default on an IOU: proven while the vault holds less than `10^16` base units
    (hiou : action = .default → l.vault.numericType = .fractional →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∃ r, (l.apply (.loanManage i action)).run = .ok r :=
  LendingLedger.loanManage_no_exception_proof l hr i action hcover hiou

/-- LoanPay on a reachable ledger, on XRP the late interest within the largest XRP amount, on XRP or an MPT the
vault total after the payment within the largest amount -> a result code, never an exception. -/
theorem Lending.loanPay_no_exception (hr : l.Reachable) (i : Nat) (pt : LoanPaymentType) (amount : Number)
    -- a late payment on XRP: the late interest is rounded to an XRP amount before the payment check (FV_M4_53)
    (hlate : l.vault.numericType = .native → pt = .late → ∀ loan, l.LoanAt i loan →
      loan.lateInterestExact l.now + 2 ≤ 10 ^ 17)
    -- a full payment on an IOU: proven for a ClosePaymentFee below `10^90`
    (hcfi : l.vault.numericType = .fractional → pt = .full → ∀ loan, l.LoanAt i loan →
      loan.fees.closePaymentFee.toRat < 10 ^ 90)
    -- the cover is a balance of the asset, and the fee fits beside it
    (hca : ∀ loan, l.LoanAt i loan → loan.broker.coverAvailable.toRat < 10 ^ 96)
    -- on XRP or an MPT the vault update stores AssetsAvailable + AssetsDeployed after the payment as an amount of
    -- the asset (FV_M4_59)
    (hfit : l.CreditFits i pt amount) (hfee : l.FeeFits i pt amount)
    -- an IOU: proven for AssetsAvailable below `10^88`
    (hAA : l.vault.numericType = .fractional → l.vault.assetsAvailable.toRat < 10 ^ 88)
    -- an overpayment on XRP: proven for loans up to about `3·10^15` drops
    (hxrp : l.vault.numericType = .native → pt = .overpayment → ∀ loan, l.LoanAt i loan →
      20 * ((loan.paymentRemaining.toNat : ℚ) * loan.periodicPayment.toRat) +
        16 * loan.totalValueOutstanding.toRat + 100 ≤ 10 ^ 17) :
    ∃ r, (l.apply (.loanPay i pt amount)).run = .ok r :=
  LendingLedger.loanPay_no_exception_full_proof l hr i pt amount hlate hcfi hca hfit hfee hAA hxrp

/-- Witness for `loanPay_no_exception`: on a reachable XRP ledger a late payment whose late interest is above the
largest XRP amount ends in an error, while every other condition holds. -/
theorem Lending.loanPay_no_exception_attained :
    ∃ (l : LendingLedger) (i : Nat) (amount : Number) (loan : Loan),
      l.Reachable ∧
      l.LoanAt i loan ∧
      l.vault.numericType = NumericType.native ∧
      (LendingTx.loanPay i .late amount).preflight l = .tesSUCCESS ∧
      loan.nextPaymentDueDate < l.now ∧
      loan.paymentRemaining = 1 ∧
      loan.broker.coverAvailable.toRat < 10 ^ 96 ∧
      l.CreditFits i .late amount ∧
      l.FeeFits i .late amount ∧
      (10 : ℚ) ^ 17 < loan.lateInterestExact l.now ∧
      (l.apply (.loanPay i .late amount)).run = .error .outOfRange :=
  LendingLedger.loanPay_late_out_of_range_witness

/-- Witness for `loanPay_no_exception`: on a reachable XRP ledger a late payment that takes AssetsAvailable +
AssetsDeployed above the largest XRP amount ends in an error, while every other condition holds (FV_M4_59). -/
theorem Lending.loanPay_no_exception_total_attained :
    ∃ (l : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (q : UnsettledPayment SingleAssetVault.Vault),
      l.Reachable ∧
      l.LoanAt i loan ∧
      l.vault.numericType = NumericType.native ∧
      (LendingTx.loanPay i .late amount).preflight l = .tesSUCCESS ∧
      loan.nextPaymentDueDate < l.now ∧
      loan.paymentRemaining = 1 ∧
      loan.broker.coverAvailable.toRat < 10 ^ 96 ∧
      loan.lateInterestExact l.now + 2 ≤ 10 ^ 17 ∧
      l.FeeFits i .late amount ∧
      (loan.payInstalments l.vault .late amount l.now).run = .ok (.ok q) ∧
      l.vault.assetsAvailable.toRat + q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + 1 ≤ 10 ^ 17 ∧
      (10 : ℚ) ^ 17 < l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + q.amounts.interestPaid.toRat ∧
      (l.apply (.loanPay i .late amount)).run = .error .outOfRange :=
  LendingLedger.loanPay_total_out_of_range_witness

/-- Witness for `loanPay_no_exception`: on a reachable MPT ledger a late payment that takes AssetsAvailable +
AssetsDeployed above the largest MPT amount ends in an error, while every other condition holds. -/
theorem Lending.loanPay_no_exception_mpt_attained :
    ∃ (l : LendingLedger) (i : Nat) (amount : Number) (loan : Loan) (q : UnsettledPayment SingleAssetVault.Vault),
      l.Reachable ∧
      l.LoanAt i loan ∧
      l.vault.numericType = NumericType.int64 ∧
      (LendingTx.loanPay i .late amount).preflight l = .tesSUCCESS ∧
      loan.nextPaymentDueDate < l.now ∧
      loan.broker.coverAvailable.toRat < 10 ^ 96 ∧
      l.FeeFits i .late amount ∧
      (loan.payInstalments l.vault .late amount l.now).run = .ok (.ok q) ∧
      l.vault.assetsAvailable.toRat + q.amounts.principalPaid.toRat + q.amounts.interestPaid.toRat + 1 ≤
        l.vault.numericType.maxValue.toNat ∧
      (l.vault.numericType.maxValue.toNat : ℚ) <
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + q.amounts.interestPaid.toRat ∧
      (l.apply (.loanPay i .late amount)).run = .error .overflow :=
  LendingLedger.loanPay_total_out_of_range_mpt_witness

end XRPL.Model
