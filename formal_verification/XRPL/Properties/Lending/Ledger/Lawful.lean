import XRPL.Properties.Lending.Ledger.Common.RecheckBroker
import XRPL.Properties.Lending.Ledger.Common.RecheckPay
import XRPL.Properties.Lending.Ledger.Common.FullClawbackWitness

/-! # Every transaction passes its lawfulness re-check

Every vault, broker and loan operation ends by re-checking the objects it writes. On a reachable ledger the
re-check never fails, given the C++ checks and balances the model runs elsewhere or not at all, except a full
VaultClawback on a large MPT vault (FV_M4_36, FV_M4_38). -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (VaultAmounts WithdrawAmount computeDeposit computeWithdraw computeClawback)

variable (l : LendingLedger)

/-- All vault, loan broker and loan transactions and ledger closes on a reachable ledger -> never fail the lawfulness
check after the transaction. -/
theorem Lending.transactions_lawful (hr : l.Reachable) :
    -- LoanSet: LoanCount does not wrap. C++ LoanSequence stops a broker before `2^32` loans
    (∀ (i : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool),
      (∀ b, l.broker? i = some b → b.loanCount + 1 ≠ 0) →
      (l.apply (.loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
        allowsOverpayment)).run ≠ .error .notLawful) ∧
    (∀ i : Nat, (l.apply (.loanAccept i)).run ≠ .error .notLawful) ∧
    (∀ (i : Nat) (paymentType : LoanPaymentType) (amount : Number),
      (l.apply (.loanPay i paymentType amount)).run ≠ .error .notLawful) ∧
    (∀ (i : Nat) (action : LoanManageAction), (l.apply (.loanManage i action)).run ≠ .error .notLawful) ∧
    (∀ i : Nat, (l.apply (.loanDelete i)).run ≠ .error .notLawful) ∧
    (∀ tx : LoanBrokerSetCreate, (l.apply (.loanBrokerCreate tx)).run ≠ .error .notLawful) ∧
    (∀ (i : Nat) (debtMaximum : Option Number), (l.apply (.loanBrokerUpdate i debtMaximum)).run ≠ .error .notLawful) ∧
    (∀ (i : Nat) (amount : STAmount), (l.apply (.loanBrokerCoverDeposit i amount)).run ≠ .error .notLawful) ∧
    (∀ (i : Nat) (amount : STAmount), (l.apply (.loanBrokerCoverWithdraw i amount)).run ≠ .error .notLawful) ∧
    -- LoanBrokerCoverClawback: the asset stores CoverAvailable. C++ associateAsset keeps an IOU cover so, and an MPT
    -- cover stays within the asset's maximum
    (∀ (i : Nat) (amount : Option STAmount),
      (∀ b, l.broker? i = some b → STAmount.isRounded b.numericType b.coverAvailable = false) →
      (l.apply (.loanBrokerCoverClawback i amount)).run ≠ .error .notLawful) ∧
    (∀ i : Nat, (l.apply (.loanBrokerDelete i)).run ≠ .error .notLawful) ∧
    -- VaultDeposit: the new shares keep SharesTotal within the share MPT maximum, which C++ accountSend enforces and
    -- the model does not run
    (∀ (h : Nat) (amount : STAmount) (isDonation : Bool),
      (∀ ra amounts, (l.vault.roundedDepositAmount amount).run = .ok (.ok ra) →
        (computeDeposit l.vault ra isDonation).run = .ok (.ok amounts) →
        (l.vault.toExact.sharesTotal : ℚ) + amounts.shares.toRat ≤ 2 ^ 63 - 1) →
      (l.apply (.vaultDeposit h amount isDonation)).run ≠ .error .notLawful) ∧
    -- VaultWithdraw: the holder's shares are within SharesTotal, which C++ keeps for the share MPT
    (∀ (h : Nat) (amount : WithdrawAmount), (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat →
      (l.apply (.vaultWithdraw h amount)).run ≠ .error .notLawful) ∧
    -- VaultClawback of assets: the holder's shares are a whole number within SharesTotal, and the holder owns the
    -- shares destroyed (C++ accountSend). An MPT vault holds less than `10^16` units: from about 10^18 units the price
    -- of all the shares can miss the cash (FV_M4_36, FV_M4_38)
    (∀ (h : Nat) (assets : STAmount),
      ((l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧ (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) →
      (∀ (hs : STAmount) (amounts : VaultAmounts), STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
        (computeClawback l.vault assets hs (l.isSoleShareholder h)).run = .ok (.ok amounts) →
        amounts.shares.toRat ≤ (l.sharesOf h).toRat) →
      (l.vault.numericType = NumericType.int64 →
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) →
      (l.apply (.vaultClawback h assets)).run ≠ .error .notLawful) ∧
    -- VaultClawback of shares: the holder's shares are a whole number within SharesTotal, which C++ keeps for the
    -- share MPT
    (∀ (h : Nat) (amount : STAmount),
      ((l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧ (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) →
      (l.apply (.vaultBurnShares h amount)).run ≠ .error .notLawful) ∧
    (∀ (assetsMaximum : Option Number) (blockDeposit : Option Bool),
      (l.apply (.vaultSet assetsMaximum blockDeposit)).run ≠ .error .notLawful) ∧
    (l.apply .vaultDelete).run ≠ .error .notLawful ∧
    ∀ time : UInt32, (l.apply (.close time)).run ≠ .error .notLawful :=
  ⟨LendingLedger.loanSet_ne_notLawful l hr, LendingLedger.loanAccept_ne_notLawful l hr,
    LendingLedger.pay_ne_notLawful l hr, LendingLedger.loanManage_ne_notLawful l hr,
    LendingLedger.loanDelete_ne_notLawful l hr, LendingLedger.loanBrokerCreate_ne_notLawful l,
    LendingLedger.loanBrokerUpdate_ne_notLawful l, LendingLedger.loanBrokerCoverDeposit_ne_notLawful l hr,
    LendingLedger.loanBrokerCoverWithdraw_ne_notLawful l, LendingLedger.loanBrokerCoverClawback_ne_notLawful l hr,
    LendingLedger.loanBrokerDelete_ne_notLawful l, LendingLedger.vaultDeposit_ne_notLawful l hr,
    LendingLedger.vaultWithdraw_ne_notLawful l hr, LendingLedger.vaultClawback_ne_notLawful l hr,
    LendingLedger.vaultBurnShares_ne_notLawful l hr,
    LendingLedger.vaultSet_ne_notLawful l, LendingLedger.vaultDelete_ne_notLawful l, LendingLedger.close_ne_notLawful l⟩

/-- Witness: a run where a full VaultClawback would leave AssetsAvailable > 0 with SharesTotal = 0. The MPT vault,
grown past 10^18 units by late interest, prices a full clawback one unit short of its cash. -/
theorem Lending.transactions_lawful_attained :
    ∃ (l : LendingLedger) (h : Nat) (assets : STAmount), l.Reachable ∧
      ((l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧ (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) ∧
      (∀ (hs : STAmount) (amounts : VaultAmounts), STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
        (computeClawback l.vault assets hs (l.isSoleShareholder h)).run = .ok (.ok amounts) →
        amounts.shares.toRat ≤ (l.sharesOf h).toRat) ∧
      (l.apply (.vaultClawback h assets)).run = .error .notLawful :=
  LendingLedger.vaultClawback_lawful_witness

end XRPL.Model
