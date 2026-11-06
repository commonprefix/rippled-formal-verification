import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Lending.Loan.Common.ManageExits

/-! # `LoanManage` exits

The exits of `canManage` and of impair, unimpair and default, in check order. A later exit assumes the earlier
checks passed. On a loan whose schedule fits, the grace period end never passes the largest ledger time. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable (loan : Loan) (action : LoanManageAction) (now : UInt32)

/-- The exits of `canManage`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Loan.canManage_exits :
    (loan.isPending = true → loan.canManage action now = .ok .tecNO_PERMISSION) ∧
    (loan.isDefault = true → loan.canManage action now = .ok .tecNO_PERMISSION) ∧
    (loan.isImpaired = true → loan.canManage .impair now = .ok .tecNO_PERMISSION) ∧
    (loan.isImpaired = false → loan.canManage .unimpair now = .ok .tecNO_PERMISSION) ∧
    (loan.paymentRemaining = 0 → loan.canManage action now = .ok .tecNO_PERMISSION) ∧
    (loan.isPending = false → loan.isDefault = false → loan.paymentRemaining ≠ 0 →
      loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat ≤ maxTime.toNat →
      now.toNat ≤ loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat →
      loan.canManage .default now = .ok .tecTOO_SOON) ∧
    (loan.isPending = false → loan.isDefault = false → loan.paymentRemaining ≠ 0 →
      (action = .impair → loan.isImpaired = false) → (action = .unimpair → loan.isImpaired = true) →
      loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat ≤ maxTime.toNat →
      (action = .default → loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat < now.toNat) →
      loan.canManage action now = .ok .tesSUCCESS) :=
  ⟨Loan.canManage_pending_proof loan action now, Loan.canManage_defaulted_proof loan action now,
    Loan.canManage_already_impaired_proof loan now, Loan.canManage_not_impaired_proof loan now,
    Loan.canManage_paid_off_proof loan action now, Loan.canManage_default_too_soon_proof loan now,
    Loan.canManage_success_proof loan action now⟩

/-- Error codes: success, tecNO_PERMISSION or tecTOO_SOON. -/
theorem Loan.canManage_error_codes :
    loan.canManage action now = .ok .tesSUCCESS ∨ loan.canManage action now = .ok .tecNO_PERMISSION ∨
      loan.canManage action now = .ok .tecTOO_SOON :=
  Loan.canManage_error_codes_proof loan action now

/-- Success ⟺ the loan is active and not paid off, an impair needs a loan that isn't impaired, an unimpair an
impaired one, and a default now > NextPaymentDueDate + GracePeriod. -/
theorem Loan.canManage_lawful_iff
    (hfit : loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat ≤ maxTime.toNat) :
    loan.canManage action now = .ok .tesSUCCESS ↔
      loan.isPending = false ∧ loan.isDefault = false ∧ loan.paymentRemaining ≠ 0 ∧
        (action = .impair → loan.isImpaired = false) ∧ (action = .unimpair → loan.isImpaired = true) ∧
        (action = .default → loan.nextPaymentDueDate.toNat + loan.schedule.gracePeriod.toNat < now.toNat) :=
  Loan.canManage_lawful_iff_proof loan action now hfit

open XRPL.Model.SingleAssetVault (Vault RawVault)

variable (v : Vault)

/-- The exits of impair, unimpair and default, in the order each runs its checks. Each line assumes the checks before
it passed. -/
theorem Loan.manage_exits :
    (now ≤ loan.nextPaymentDueDate → (loan.manageImpair v now).run = .ok (.error .tecTOO_SOON)) ∧
    -- `lu'` - the new LossUnrealized, `ad'` - the new AssetsDeployed
    (∀ aa' ad' lu' ar' yu' : Number, loan.nextPaymentDueDate < now →
      Vault.AdjustSums v { loss := loan.principalOutstanding } aa' ad' lu' ar' yu' → lu'.operator_gt ad' = true →
      (loan.manageImpair v now).run = .ok (.error .tecLIMIT_EXCEEDED)) ∧
    (∀ raw : RawVault, loan.nextPaymentDueDate < now →
      (v.adjustBalances { loss := loan.principalOutstanding }).run = .ok (.ok raw) →
      ∃ v' loan', (loan.manageImpair v now).run = .ok (.ok { loan' := loan', pool' := v' }) ∧
        v'.toRawVault = raw ∧ loan'.toRawLoan = { loan.toRawLoan with isImpaired := true }) ∧
    -- `lu'` - the new LossUnrealized
    (∀ aa' ad' lu' ar' yu' : Number,
      Vault.AdjustSums v { loss := loan.principalOutstanding.operator_neg } aa' ad' lu' ar' yu' → lu'.signum < 0 →
      (loan.manageUnimpair v).run = .ok (.error .tefBAD_LEDGER)) ∧
    (∀ raw : RawVault, (v.adjustBalances { loss := loan.principalOutstanding.operator_neg }).run = .ok (.ok raw) →
      ∃ v' loan', (loan.manageUnimpair v).run = .ok (.ok { loan' := loan', pool' := v' }) ∧
        v'.toRawVault = raw ∧ loan'.toRawLoan = { loan.toRawLoan with isImpaired := false }) ∧
    -- the default lines: `defaultCovered` - the cover the default pays. Here `lu'` - the new LossUnrealized
    (∀ interestDue defaultCovered aa' ad' lu' ar' yu' : Number, loan.interestDue = .ok interestDue →
      loan.defaultCover v = .ok defaultCovered → loan.isImpaired = true →
      Vault.AdjustSums v
        { cash := defaultCovered
          deployed := loan.principalOutstanding.operator_neg
          yield := interestDue.operator_neg
          loss := loan.principalOutstanding.operator_neg } aa' ad' lu' ar' yu' →
      lu'.signum < 0 → (loan.manageDefault v).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `ad'` - the new AssetsDeployed
    (∀ interestDue defaultCovered aa' ad' lu' ar' yu' : Number, loan.interestDue = .ok interestDue →
      loan.defaultCover v = .ok defaultCovered →
      Vault.AdjustSums v (loan.defaultChange interestDue defaultCovered) aa' ad' lu' ar' yu' → ad'.signum < 0 →
      (loan.manageDefault v).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `yu'` - the new YieldUnrealized
    (∀ interestDue defaultCovered aa' ad' lu' ar' yu' : Number, loan.interestDue = .ok interestDue →
      loan.defaultCover v = .ok defaultCovered →
      Vault.AdjustSums v (loan.defaultChange interestDue defaultCovered) aa' ad' lu' ar' yu' → yu'.signum < 0 →
      (loan.manageDefault v).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `lu'` - the new LossUnrealized, `ad'` - the new AssetsDeployed
    (∀ interestDue defaultCovered aa' ad' lu' ar' yu' : Number, loan.interestDue = .ok interestDue →
      loan.defaultCover v = .ok defaultCovered → loan.isImpaired = false →
      Vault.AdjustSums v
        { cash := defaultCovered
          deployed := loan.principalOutstanding.operator_neg
          yield := interestDue.operator_neg } aa' ad' lu' ar' yu' →
      0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum →
      lu'.operator_gt ad' = true → (loan.manageDefault v).run = .ok (.error .tecLIMIT_EXCEEDED)) ∧
    -- `raw` - the vault the update writes
    (∀ (interestDue defaultCovered debtTotal' coverAvailable' : Number) (raw : RawVault) (v' : Vault)
        (broker' : LoanBroker),
      loan.interestDue = .ok interestDue → loan.defaultCover v = .ok defaultCovered →
      (v.adjustBalances (loan.defaultChange interestDue defaultCovered)).run = .ok (.ok raw) →
      raw.to_lawful = .ok v' →
      loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok debtTotal' →
      loan.broker.coverAvailable.operator_sub defaultCovered .to_nearest = .ok coverAvailable' →
      (loan.defaultedBroker debtTotal' coverAvailable').to_lawful = .ok broker' →
      ∃ loan', (loan.manageDefault v).run =
          .ok (.ok { loan' := loan', pool' := v', amountToPool := defaultCovered, amountToBroker := Number.zero }) ∧
        loan'.toRawLoan = loan.defaultedLoan broker') :=
  ⟨Loan.manageImpair_not_late_proof loan v now, Loan.manageImpair_limit_exceeded_proof loan v now,
    Loan.manageImpair_success_proof loan v now, Loan.manageUnimpair_bad_ledger_proof loan v,
    Loan.manageUnimpair_success_proof loan v, Loan.manageDefault_impaired_bad_ledger_proof loan v,
    Loan.manageDefault_deployed_bad_ledger_proof loan v, Loan.manageDefault_yield_bad_ledger_proof loan v,
    Loan.manageDefault_limit_exceeded_proof loan v, Loan.manageDefault_success_proof loan v⟩

/-- The only rejections of an impair, an unimpair and a default. -/
theorem Loan.manage_error_codes (ter : TER) :
    ((loan.manageImpair v now).run = .ok (.error ter) → ter = .tecTOO_SOON ∨ ter = .tecLIMIT_EXCEEDED) ∧
    ((loan.manageUnimpair v).run = .ok (.error ter) → ter = .tefBAD_LEDGER) ∧
    ((loan.manageDefault v).run = .ok (.error ter) → ter = .tefBAD_LEDGER ∨ ter = .tecLIMIT_EXCEEDED) :=
  ⟨Loan.manageImpair_error_codes_proof loan v now ter, Loan.manageUnimpair_error_codes_proof loan v ter,
    Loan.manageDefault_error_codes_proof loan v ter⟩

end XRPL.Model.Lending
