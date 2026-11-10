import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultCreate
import XRPL.Model.Vault.VaultDelete
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultSet
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverClawback
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverDeposit
import XRPL.Model.Lending.LoanBroker.LoanBrokerCoverWithdraw
import XRPL.Model.Lending.LoanBroker.LoanBrokerDelete
import XRPL.Model.Lending.LoanBroker.LoanBrokerSet
import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Model.Lending.Loan.LoanDelete
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending1_1.AssetPool
import XRPL.Properties.Lending.Loan.Common.PayDefs

/-! # Lending ledger

A slice of the ledger with one vault, its share holders, the loan brokers on it and their loans.
A transaction runs its preflight, its checks and then its operation, like C++ `preflight`,
`preclaim` and `doApply`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault WithdrawAmount)

/-- A loan and the index of its broker in `LendingLedger.brokers`. -/
structure LoanEntry where
  brokerIndex : Nat
  loan : Loan

/-- One vault, the shares each holder owns, the brokers on the vault and their loans, at a ledger
close time. Deleting a broker or a loan leaves `none` in its place, so indices stay stable. -/
structure LendingLedger where
  vault : Vault
  shares : List Number
  brokers : List (Option LoanBroker)
  loans : List (Option LoanEntry)
  now : UInt32
  -- set by `vaultDelete`, after which the vault no longer exists
  vaultDeleted : Bool := false

/-- The transactions on a lending ledger. `close` moves the ledger close time forward, and after
`vaultDelete` every other transaction finds no vault. -/
inductive LendingTx where
  | vaultDeposit (holder : Nat) (amount : STAmount) (isDonation : Bool)
  | vaultWithdraw (holder : Nat) (amount : WithdrawAmount)
  | vaultClawback (holder : Nat) (assets : STAmount)
  | vaultBurnShares (holder : Nat) (amount : STAmount)
  | vaultSet (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool)
  | vaultDelete
  | loanBrokerCreate (tx : LoanBrokerSetCreate)
  | loanBrokerUpdate (broker : Nat) (debtMaximum : Option Number)
  | loanBrokerCoverDeposit (broker : Nat) (amount : STAmount)
  | loanBrokerCoverWithdraw (broker : Nat) (amount : STAmount)
  | loanBrokerCoverClawback (broker : Nat) (amount : Option STAmount)
  | loanBrokerDelete (broker : Nat)
  | loanSet (broker : Nat) (principal : Number) (rates : LoanRates) (fees : LoanFees)
      (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32)
      (twoStep allowsOverpayment : Bool)
  | loanAccept (loan : Nat)
  | loanDelete (loan : Nat)
  | loanManage (loan : Nat) (action : LoanManageAction)
  | loanPay (loan : Nat) (paymentType : LoanPaymentType) (amount : Number)
  | close (time : UInt32)

/-- A vault transaction that changes the vault and at most one holder's shares (not `vaultDelete`). -/
def LendingTx.isVault : LendingTx → Bool
  | .vaultDeposit .. | .vaultWithdraw .. | .vaultClawback .. | .vaultBurnShares .. | .vaultSet .. => true
  | _ => false

/-- A loan broker transaction. -/
def LendingTx.isBroker : LendingTx → Bool
  | .loanBrokerCreate .. | .loanBrokerUpdate .. | .loanBrokerCoverDeposit ..
  | .loanBrokerCoverWithdraw .. | .loanBrokerCoverClawback .. | .loanBrokerDelete .. => true
  | _ => false

/-- A loan transaction. -/
def LendingTx.isLoan : LendingTx → Bool
  | .loanSet .. | .loanAccept .. | .loanDelete .. | .loanManage .. | .loanPay .. => true
  | _ => false

/-- The shares holder `h` owns. -/
def LendingLedger.sharesOf (l : LendingLedger) (h : Nat) : Number :=
  l.shares.getD h Number.zero

/-- Set the shares of holder `h`, adding holders up to `h` when needed. -/
def LendingLedger.setShares (l : LendingLedger) (h : Nat) (n : Number) : LendingLedger :=
  let padded := l.shares ++ List.replicate (h + 1 - l.shares.length) Number.zero
  { l with shares := padded.set h n }

/-- The broker at `i`, if it exists. -/
def LendingLedger.broker? (l : LendingLedger) (i : Nat) : Option LoanBroker :=
  (l.brokers[i]?).join

/-- The loan at `i`, if it exists. -/
def LendingLedger.loan? (l : LendingLedger) (i : Nat) : Option LoanEntry :=
  (l.loans[i]?).join

/-- Holder `h` owns every share of the vault (C++ sole shareholder). -/
def LendingLedger.isSoleShareholder (l : LendingLedger) (h : Nat) : Bool :=
  (l.sharesOf h).operator_ne Number.zero && (l.sharesOf h).operator_eq l.vault.sharesTotal

/-- The loan with its broker replaced by the ledger's current copy. A loan keeps a copy of its
broker, and another loan on the same broker may have changed it since. -/
def Loan.withBroker (loan : Loan) (broker : LoanBroker) : Except Error Loan :=
  RawLoan.to_lawful { loan.toRawLoan with broker := broker }

/-- `loan` is the loan stored at `i`, read with its broker's current copy, as every loan transaction reads it. -/
def LendingLedger.LoanAt (l : LendingLedger) (i : Nat) (loan : Loan) : Prop :=
  ∃ e b, l.loan? i = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan

/-- A stored amount of the numeric type `nt`: an integral amount at offset `0` within the type's
maximum, or an IOU zero or 16-digit mantissa with the exponent in range. -/
def isCanonicalAmount (s : STAmount) (nt : NumericType) : Bool :=
  s.mNumericType == nt &&
    if nt.isIntegral then s.mOffset == 0 && decide (s.mValue.toNat ≤ nt.maxValue.toNat)
    else s.mValue == 0 ||
      (decide (10 ^ 15 ≤ s.mValue.toNat) && decide (s.mValue.toNat < 10 ^ 16) &&
        decide (-96 ≤ s.mOffset) && decide (s.mOffset ≤ 80))

/-- A stored amount above zero. -/
def isPositiveAmount (s : STAmount) : Bool := !s.mIsNegative && s.mValue != 0

/-- A `Number` from a transaction: normalized and at least `0`. -/
def isNonnegativeInput (n : Number) : Bool :=
  decide n.isNormalized && Number.zero.operator_le n

/-- A `Number` from a transaction: normalized and above `0`. -/
def isPositiveInput (n : Number) : Bool :=
  decide n.isNormalized && Number.zero.operator_lt n

/-- The C++ `preflight` checks on the transaction's own fields. Here an amount must also have the expected numeric
type (temBAD_AMOUNT). C++ checks the asset in preclaim (tecWRONG_ASSET) and rejects an XRP clawback in preflight. -/
def LendingTx.preflight (l : LendingLedger) : LendingTx → TER
  | .vaultDeposit _ amount _ =>
    if isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount then .tesSUCCESS
    else .temBAD_AMOUNT
  | .vaultWithdraw _ (.vaultAssets amount) =>
    if isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount then .tesSUCCESS
    else .temBAD_AMOUNT
  | .vaultWithdraw _ (.vaultShares shares) =>
    if isCanonicalAmount shares .int64 && isPositiveAmount shares then .tesSUCCESS else .temBAD_AMOUNT
  | .vaultClawback _ assets =>
    if !(isCanonicalAmount assets l.vault.numericType && !assets.mIsNegative) then .temBAD_AMOUNT
    -- XRP has no issuer, so nobody can claw it back. C++ gives tecNO_PERMISSION when the amount is left out.
    else if assets.mNumericType == NumericType.native then .temMALFORMED
    else .tesSUCCESS
  | .vaultBurnShares _ amount =>
    if isCanonicalAmount amount .int64 && !amount.mIsNegative then .tesSUCCESS else .temBAD_AMOUNT
  | .vaultSet assetsMaximum blockDeposit unblockDeposit =>
    let maximumOk := match assetsMaximum with
      | none => true
      | some m => isNonnegativeInput m
    if !maximumOk then .temMALFORMED
    else if blockDeposit && unblockDeposit then .temINVALID_FLAG
    else .tesSUCCESS
  | .loanBrokerCreate tx =>
    let debtMaximumOk := match tx.debtMaximum with
      | none => true
      | some d => isNonnegativeInput d && d.operator_le debtMaximumCap
    let coverMinimum := tx.coverRateMinimum.getD 0
    let coverLiquidation := tx.coverRateLiquidation.getD 0
    if debtMaximumOk && tx.managementFeeRate.getD 0 ≤ maxManagementFeeRate &&
        coverMinimum ≤ maxCoverRate && coverLiquidation ≤ maxCoverRate &&
        (coverMinimum == 0) == (coverLiquidation == 0) then .tesSUCCESS
    else .temINVALID
  | .loanBrokerUpdate _ debtMaximum =>
    match debtMaximum with
    | some d => if isNonnegativeInput d && d.operator_le debtMaximumCap then .tesSUCCESS else .temINVALID
    | none => .tesSUCCESS
  | .loanBrokerCoverDeposit _ amount | .loanBrokerCoverWithdraw _ amount =>
    if isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount then .tesSUCCESS
    else .temBAD_AMOUNT
  | .loanBrokerCoverClawback _ amount =>
    match amount with
    | some a =>
      -- XRP has no issuer, so nobody can claw it back
      if isCanonicalAmount a l.vault.numericType && !a.mIsNegative && a.mNumericType != NumericType.native then
        .tesSUCCESS
      else .temBAD_AMOUNT
    | none => .tesSUCCESS
  | .loanSet _ principal rates fees paymentInterval paymentTotal gracePeriod _ _ _ =>
    let interval := paymentInterval.getD defaultPaymentInterval
    let grace := gracePeriod.getD defaultGracePeriod
    if isPositiveInput principal && isNonnegativeInput fees.originationFee &&
        fees.originationFee.operator_le principal && isNonnegativeInput fees.serviceFee &&
        isNonnegativeInput fees.latePaymentFee && isNonnegativeInput fees.closePaymentFee &&
        rates.interestRate ≤ maxLoanRate && rates.lateInterestRate ≤ maxLoanRate &&
        rates.closeInterestRate ≤ maxLoanRate && rates.overpaymentInterestRate ≤ maxLoanRate &&
        rates.overpaymentFee ≤ maxLoanRate && 0 < paymentTotal.getD defaultPaymentTotal &&
        minPaymentInterval ≤ interval && defaultGracePeriod ≤ grace && grace ≤ interval then
      .tesSUCCESS
    else .temINVALID
  | .loanPay _ _ amount =>
    if isPositiveInput amount &&
        (STAmount.equalAfterNumberConvert l.vault.numericType amount).toOption == some true then
      .tesSUCCESS
    else .temBAD_AMOUNT
  | _ => .tesSUCCESS

/-- Store `x` at slot `i`, or add it when `i` is past the end. -/
def storeSlot {α : Type} (xs : List (Option α)) (i : Nat) (x : Option α) : List (Option α) :=
  if i < xs.length then xs.set i x else xs ++ [x]

/-- What a vault transaction changes: the vault and the shares of at most one holder. -/
structure VaultEffect where
  vault : Vault
  holderShares : Option (Nat × Number)

/-- What a broker transaction changes: one broker slot. `none` deletes the broker. -/
structure BrokerEffect where
  index : Nat
  broker : Option LoanBroker

/-- What a loan transaction changes: the vault, the loan's broker and one loan slot. `none` deletes
the loan. -/
structure LoanEffect where
  vault : Vault
  brokerIndex : Nat
  broker : LoanBroker
  loanIndex : Nat
  loan : Option LoanEntry

/-- Apply a vault transaction. A holder that owns every share waives the unrealized loss. -/
def LendingLedger.applyVault (l : LendingLedger) : LendingTx → TerExcept VaultEffect
  | .vaultDeposit h amount isDonation =>
    if hpos : 0 < amount.toRat then do
      let r ← l.vault.deposit amount isDonation l.now hpos
      let minted ← r.shares.toNumber .to_nearest
      let shares' ← (l.sharesOf h).operator_add minted .to_nearest
      return { vault := r.vault', holderShares := some (h, shares') }
    else throw .temBAD_AMOUNT
  | .vaultWithdraw h amount =>
    if hpos : 0 < amount.amount.toRat then do
      let held := l.sharesOf h
      let r ← l.vault.withdraw amount (l.isSoleShareholder h) l.now hpos (some held)
      let burned ← r.shares.toNumber .to_nearest
      let shares' ← held.operator_sub burned .to_nearest
      return { vault := r.vault', holderShares := some (h, shares') }
    else throw .temBAD_AMOUNT
  | .vaultClawback h assets =>
    if hnn : 0 ≤ assets.toRat then do
      let held := l.sharesOf h
      let holderShares ← STAmount.ofNumber .int64 held .to_nearest
      let r ← l.vault.clawback assets holderShares (l.isSoleShareholder h) hnn
      let destroyed ← r.shares.toNumber .to_nearest
      if held.operator_lt destroyed then throw .tecINSUFFICIENT_FUNDS
      let shares' ← held.operator_sub destroyed .to_nearest
      return { vault := r.vault', holderShares := some (h, shares') }
    else throw .temBAD_AMOUNT
  | .vaultBurnShares h amount => do
    let holderShares ← STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest
    let _ ← l.vault.canBurnShares amount holderShares
    let vault' ← l.vault.burnShares holderShares
    return { vault := vault', holderShares := some (h, Number.zero) }
  | .vaultSet assetsMaximum blockDeposit unblockDeposit => do
    let ter ← l.vault.canVaultUpdate assetsMaximum blockDeposit unblockDeposit
    if !ter.isTesSuccess then throw ter
    let vault' ← l.vault.update assetsMaximum blockDeposit unblockDeposit
    return { vault := vault', holderShares := none }
  | _ => throw .temMALFORMED

/-- Delete the vault. The brokers are linked to the vault, so C++ `VaultDelete::doApply` rejects the
delete while any broker is left. -/
def LendingLedger.applyVaultDelete (l : LendingLedger) : TerExcept LendingLedger := do
  if l.vaultDeleted then throw .tecNO_ENTRY
  let ter ← l.vault.canVaultDelete
  if !ter.isTesSuccess then throw ter
  if l.vault.assetsReserved.operator_ne Number.zero then throw .tecHAS_OBLIGATIONS
  if l.brokers.any Option.isSome then throw .tecHAS_OBLIGATIONS
  return { l with vaultDeleted := true }

/-- Apply a loan broker transaction. -/
def LendingLedger.applyBroker (l : LendingLedger) : LendingTx → TerExcept BrokerEffect
  | .loanBrokerCreate tx => do
    let ter ← LoanBroker.canCreate l.vault tx.debtMaximum l.vault.numericType
    if !ter.isTesSuccess then throw ter
    let broker ← LoanBroker.create tx l.vault.numericType
    return { index := l.brokers.length, broker := some broker }
  | .loanBrokerUpdate i debtMaximum => do
    let some broker := l.broker? i | throw .tecNO_ENTRY
    let ter ← broker.canUpdate l.vault debtMaximum
    if !ter.isTesSuccess then throw ter
    let broker' ← broker.update debtMaximum
    return { index := i, broker := some broker' }
  | .loanBrokerCoverDeposit i amount => do
    let some broker := l.broker? i | throw .tecNO_ENTRY
    let ter ← broker.canCoverDeposit l.vault amount
    if !ter.isTesSuccess then throw ter
    let r ← broker.coverDeposit l.vault amount
    return { index := i, broker := some r.loanBroker' }
  | .loanBrokerCoverWithdraw i amount => do
    let some broker := l.broker? i | throw .tecNO_ENTRY
    let ter ← broker.canCoverWithdraw l.vault amount
    if !ter.isTesSuccess then throw ter
    let r ← broker.coverWithdraw l.vault amount
    return { index := i, broker := some r.loanBroker' }
  | .loanBrokerCoverClawback i amount => do
    let some broker := l.broker? i | throw .tecNO_ENTRY
    let ter ← broker.canCoverClawback l.vault amount
    if !ter.isTesSuccess then throw ter
    let r ← broker.coverClawback l.vault amount
    return { index := i, broker := some r.loanBroker' }
  | .loanBrokerDelete i => do
    let some broker := l.broker? i | throw .tecNO_ENTRY
    let ter ← broker.canDelete l.vault
    if !ter.isTesSuccess then throw ter
    -- C++ sends the cover back to the owner as an amount of the asset, which throws above the asset's maximum
    let _ ← broker.roundedCoverAvailable
    return { index := i, broker := none }
  | _ => throw .temMALFORMED

/-- The effect of a new loan on broker `i`, stored at slot `n`. -/
def LoanEffect.ofCreate (i n : Nat) (r : LoanWithDisbursement Vault) : LoanEffect :=
  { vault := r.pool', brokerIndex := i, broker := r.loan'.broker, loanIndex := n
    loan := some { brokerIndex := i, loan := r.loan' } }

/-- The effect of an operation on the loan at `i` that keeps it. -/
def LoanEffect.ofLoan (i : Nat) (e : LoanEntry) (loan' : Loan) (vault' : Vault) : LoanEffect :=
  { vault := vault', brokerIndex := e.brokerIndex, broker := loan'.broker, loanIndex := i
    loan := some { e with loan := loan' } }

/-- Run a management action. -/
def Loan.manage (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32) :
    TerExcept (LoanWithPool Vault) :=
  match action with
  | .impair => loan.manageImpair v now
  | .unimpair => loan.manageUnimpair v
  | .default => do
    let r ← loan.manageDefault v
    return r.toLoanWithPool

/-- The rest of a LoanSet once the LoanSet checks returned `checks`: a rejection stops it, otherwise
the loan is created on `broker`. -/
def LendingLedger.loanSetChecked (l : LendingLedger) (i : Nat) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (twoStep allowsOverpayment : Bool)
    (checks : Except Error TER) : TerExcept LoanEffect :=
  match checks with
  | .error e => ExceptT.mk (.error e)
  | .ok ter =>
    if !ter.isTesSuccess then throw ter
    else LoanEffect.ofCreate i l.loans.length <$>
      Loan.create broker l.vault principal rates fees schedule allowsOverpayment twoStep

/-- A LoanSet on broker `i` with the schedule its fields build. C++ checks that the schedule fits before
it reads the broker or the vault. -/
def LendingLedger.applyLoanSet (l : LendingLedger) (i : Nat) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (twoStep allowsOverpayment : Bool) : TerExcept LoanEffect :=
  match schedule.checkTimeAvailability with
  | .error e => ExceptT.mk (.error e)
  | .ok scheduleTer =>
    if !scheduleTer.isTesSuccess then throw scheduleTer
    else match l.broker? i with
      | none => throw .tecNO_ENTRY
      | some broker =>
        let checks := Loan.canCreate broker l.vault principal fees schedule l.now twoStep
        l.loanSetChecked i broker principal rates fees schedule twoStep allowsOverpayment checks

/-- Apply a loan transaction. Every operation on an existing loan first gives it the ledger's
current copy of its broker. -/
def LendingLedger.applyLoan (l : LendingLedger) : LendingTx → TerExcept LoanEffect
  | .loanSet i principal rates fees paymentInterval paymentTotal gracePeriod startDate twoStep
      allowsOverpayment =>
    let schedule := LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now twoStep
    l.applyLoanSet i principal rates fees schedule twoStep allowsOverpayment
  | .loanAccept i => do
    let some e := l.loan? i | throw .tecNO_ENTRY
    let some broker := l.broker? e.brokerIndex | throw .tecNO_ENTRY
    let loan ← e.loan.withBroker broker
    let ter ← loan.canAccept l.vault l.now
    if !ter.isTesSuccess then throw ter
    let r ← loan.accept l.vault
    return LoanEffect.ofLoan i e r.loan' r.pool'
  | .loanDelete i => do
    let some e := l.loan? i | throw .tecNO_ENTRY
    let some broker := l.broker? e.brokerIndex | throw .tecNO_ENTRY
    let loan ← e.loan.withBroker broker
    let ter := loan.canDelete
    if !ter.isTesSuccess then throw ter
    let r ← loan.delete l.vault
    return { vault := r.pool', brokerIndex := e.brokerIndex, broker := r.broker', loanIndex := i, loan := none }
  | .loanManage i action => do
    let some e := l.loan? i | throw .tecNO_ENTRY
    let some broker := l.broker? e.brokerIndex | throw .tecNO_ENTRY
    let loan ← e.loan.withBroker broker
    let ter ← loan.canManage action l.now
    if !ter.isTesSuccess then throw ter
    let r ← loan.manage action l.vault l.now
    return LoanEffect.ofLoan i e r.loan' r.pool'
  | .loanPay i paymentType amount => do
    let some e := l.loan? i | throw .tecNO_ENTRY
    let some broker := l.broker? e.brokerIndex | throw .tecNO_ENTRY
    let loan ← e.loan.withBroker broker
    let ter := loan.canPay paymentType
    if !ter.isTesSuccess then throw ter
    let r ← loan.pay l.vault paymentType amount l.now
    return LoanEffect.ofLoan i e r.loan' r.pool'
  | _ => throw .temMALFORMED

/-- Write a vault effect into the ledger. -/
def LendingLedger.commitVault (l : LendingLedger) (u : VaultEffect) : LendingLedger :=
  match u.holderShares with
  | none => { l with vault := u.vault }
  | some (h, n) => { l with vault := u.vault }.setShares h n

/-- Write a broker effect into the ledger. -/
def LendingLedger.commitBroker (l : LendingLedger) (u : BrokerEffect) : LendingLedger :=
  { l with brokers := storeSlot l.brokers u.index u.broker }

/-- Write a loan effect into the ledger. -/
def LendingLedger.commitLoan (l : LendingLedger) (u : LoanEffect) : LendingLedger :=
  { l with
    vault := u.vault
    brokers := l.brokers.set u.brokerIndex (some u.broker)
    loans := storeSlot l.loans u.loanIndex u.loan }

/-- Run a transaction that passed its preflight: its checks and operation, by kind. -/
def LendingLedger.applyChecked (l : LendingLedger) (tx : LendingTx) : TerExcept LendingLedger :=
  match tx with
  | .close time => pure { l with now := max l.now time }
  | .vaultDelete => l.applyVaultDelete
  | _ =>
    if l.vaultDeleted then throw .tecNO_ENTRY
    else if tx.isVault then l.commitVault <$> l.applyVault tx
    else if tx.isBroker then l.commitBroker <$> l.applyBroker tx
    else l.commitLoan <$> l.applyLoan tx

/-- Apply a transaction: its preflight, then its checks and operation. `.ok (.error ter)` is a
rejection that leaves the ledger as it was, `.error` a failure of the model. -/
def LendingLedger.apply (l : LendingLedger) (tx : LendingTx) : TerExcept LendingLedger :=
  let ter := tx.preflight l
  if !ter.isTesSuccess then throw ter else l.applyChecked tx

/-- Apply the transactions in order. A rejected transaction leaves the ledger as it was. -/
def LendingLedger.run (l : LendingLedger) : List LendingTx → Except Error LendingLedger
  | [] => .ok l
  | tx :: txs => do
    match ← (l.apply tx).run with
    | .error _ => l.run txs
    | .ok l' => l'.run txs

end XRPL.Model.Lending
