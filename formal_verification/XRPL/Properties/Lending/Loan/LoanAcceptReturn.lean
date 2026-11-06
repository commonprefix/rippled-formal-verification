import XRPL.Properties.Lending.Loan.Common.GuardProofs
import XRPL.Properties.Lending.Loan.Common.AcceptExits

/-! # `LoanAccept` exits

The exits of `canAccept` and `accept`, one line per exit. Each line assumes the checks that run before it
passed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable (loan : Loan) (v : Vault) (t : UInt32)

/-- The exits of `canAccept`, one line per exit. Each line assumes the checks that run before it passed. -/
theorem Loan.canAccept_exits :
    (loan.isPending = false → loan.canAccept v t = .ok .tecNO_PERMISSION) ∧
    (loan.isPending = true → loan.schedule.startDate ≤ t → loan.canAccept v t = .ok .tecEXPIRED) ∧
    (loan.isPending = true → t < loan.schedule.startDate → v.phase t = .subscription →
      loan.canAccept v t = .ok .tecTOO_SOON) ∧
    (loan.isPending = true → v.phase t = .redemption → loan.canAccept v t = .ok .tecEXPIRED) ∧
    (∀ interestDue : Number, loan.isPending = true → t < loan.schedule.startDate →
      (v.phase t = .noPhase ∨ v.phase t = .investment) → loan.interestDue = .ok interestDue →
      v.exceedsOpenLimit interestDue = .ok true → loan.canAccept v t = .ok .tecLIMIT_EXCEEDED) ∧
    (∀ interestDue : Number, loan.isPending = true → t < loan.schedule.startDate →
      (v.phase t = .noPhase ∨ v.phase t = .investment) → loan.interestDue = .ok interestDue →
      v.exceedsOpenLimit interestDue = .ok false → loan.canAccept v t = .ok .tesSUCCESS) :=
  ⟨Loan.canAccept_not_pending_proof loan v t, Loan.canAccept_start_passed_proof loan v t,
    Loan.canAccept_subscription_proof loan v t, Loan.canAccept_redemption_proof loan v t,
    fun interestDue hp ht hphase => Loan.canAccept_open_zone_proof loan v t hp ht hphase interestDue,
    fun interestDue hp ht hphase => Loan.canAccept_success_proof loan v t hp ht hphase interestDue⟩

/-- Error codes: success, tecNO_PERMISSION, tecEXPIRED, tecTOO_SOON or tecLIMIT_EXCEEDED. -/
theorem Loan.canAccept_error_codes (ter : TER) (hok : loan.canAccept v t = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecNO_PERMISSION ∨ ter = .tecEXPIRED ∨ ter = .tecTOO_SOON ∨
      ter = .tecLIMIT_EXCEEDED :=
  Loan.canAccept_error_codes_proof loan v t ter hok

/-- Success ⟺ the loan is pending, now < StartDate, the phase allows it, and its interestDue
fits the Open limit. -/
theorem Loan.canAccept_lawful_iff (interestDue : Number) (hi : loan.interestDue = .ok interestDue)
    (exceeds : Bool) (hopen : v.exceedsOpenLimit interestDue = .ok exceeds) :
    loan.canAccept v t = .ok .tesSUCCESS ↔
      loan.isPending = true ∧ t < loan.schedule.startDate ∧
        (v.phase t = .noPhase ∨ v.phase t = .investment) ∧ exceeds = false :=
  Loan.canAccept_lawful_iff_proof loan v t interestDue hi exceeds hopen

/-! ## `Loan.accept` -/

open XRPL.Model.SingleAssetVault (RawVault)

/-- The exits of `accept`, one line per exit. Each line assumes the checks that run before it passed. -/
theorem Loan.accept_exits :
    -- `ar'` - the new AssetsReserved
    (∀ interestDue aa' ad' lu' ar' yu' : Number, loan.interestDue = .ok interestDue →
      Vault.AdjustSums v (loan.acceptChange interestDue) aa' ad' lu' ar' yu' → ar'.signum < 0 →
      (loan.accept v).run = .ok (.error .tefBAD_LEDGER)) ∧
    -- `raw` - the updated vault
    (∀ (interestDue : Number) (raw : RawVault) (v' : Vault) (loan' : Loan), loan.interestDue = .ok interestDue →
      (v.adjustBalances (loan.acceptChange interestDue)).run = .ok (.ok raw) → raw.to_lawful = .ok v' →
      ({ loan.toRawLoan with isPending := false } : RawLoan).to_lawful = .ok loan' →
      (loan.accept v).run = .ok (.ok { loan' := loan', pool' := v' })) :=
  ⟨Loan.accept_bad_ledger_proof loan v, Loan.accept_success_proof loan v⟩

/-- The only accept rejection is tefBAD_LEDGER. -/
theorem Loan.accept_error_codes (ter : TER) (hok : (loan.accept v).run = .ok (.error ter)) :
    ter = .tefBAD_LEDGER :=
  Loan.accept_error_codes_proof loan v ter hok

end XRPL.Model.Lending
