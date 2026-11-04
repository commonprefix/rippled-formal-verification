import XRPL.Properties.Lending.Loan.Common.SetDefs
import XRPL.Properties.Lending.Common.PoolBalances

/-! # The vault phase a new loan needs

A LoanSet that passed its checks found the vault open for the schedule: no phase, or the investment
phase with the last payment due at least 60 seconds before RedemptionDate. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault VaultSchedule)

open private checkPrecisionFields canFundLoan from XRPL.Model.Lending.Loan.LoanSet

/-- The vault check passes only when the vault lends for the schedule. -/
private lemma canFundLoan_fitsVault (v : Vault) (schedule : LoanSchedule) (t : UInt32) (nt : NumericType)
    (h : canFundLoan v schedule t nt = .ok .tesSUCCESS) : schedule.FitsVault v t := by
  unfold canFundLoan at h
  simp only [Vault.pool_phase, Vault.pool_redemptionDate] at h
  cases hp : v.phase t with
  | noPhase => exact Or.inl hp
  | subscription => rw [hp] at h; cases h
  | redemption => rw [hp] at h; cases h
  | investment =>
    refine Or.inr ⟨hp, fun s hs => ?_⟩
    rw [hp, hs] at h
    simp only [Option.map_some, Option.getD_some, bind, Except.bind, pure, Except.pure] at h
    by_contra hlate
    rw [if_pos (by simp; omega)] at h
    cases h

/-- A passing LoanSet check passed the vault check. -/
lemma Loan.canCreate_canFundLoan (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool)
    (h : Loan.canCreate broker v p fees schedule t twoStep = .ok .tesSUCCESS) :
    canFundLoan v schedule t broker.numericType = .ok .tesSUCCESS := by
  unfold Loan.canCreate at h
  generalize schedule.checkTimeAvailability = st at h
  cases hf : canFundLoan v schedule t broker.numericType with
  | error e =>
    rw [hf] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h; exact absurd ‹_› (by decide)
    · split at h
      · cases h
      · cases h
  | ok vt =>
    rw [hf] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h; exact absurd ‹_› (by decide)
    · split at h
      · cases h
      · split at h
        · cases h; exact absurd ‹_› (by decide)
        · rename_i hvt
          exact congrArg Except.ok ((TER.isTesSuccess_iff vt).mp (by simpa using hvt))

/-- A passing LoanSet check means the vault lends for the schedule. -/
lemma Loan.canCreate_fitsVault (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t : UInt32) (twoStep : Bool)
    (h : Loan.canCreate broker v p fees schedule t twoStep = .ok .tesSUCCESS) : schedule.FitsVault v t :=
  canFundLoan_fitsVault v schedule t _ (Loan.canCreate_canFundLoan broker v p fees schedule t twoStep h)
end XRPL.Model.Lending
