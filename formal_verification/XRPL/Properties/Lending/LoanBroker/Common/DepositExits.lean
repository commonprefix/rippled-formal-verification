import XRPL.Properties.Lending.LoanBroker.Common.CoverAccuracy

/-! # Proof bodies for the `LoanBroker.coverDeposit` exits

Proofs for the deposit exits. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- **Proof body of `roundedCoverAmount_precision_loss`.** -/
lemma LoanBroker.roundedCoverAmount_precision_loss_proof (lb : LoanBroker) (amount r : STAmount)
    (hdown : roundToCoverScale lb.numericType lb.coverAvailable amount .downward = .ok r)
    (hz : r.signum = 0) :
    lb.roundedCoverAmount amount = .ok (.rejected .tecPRECISION_LOSS) := by
  simp [LoanBroker.roundedCoverAmount, hdown, hz]

/-- **Proof body of `roundedCoverAmount_rounded`.** -/
lemma LoanBroker.roundedCoverAmount_rounded_proof (lb : LoanBroker) (amount r : STAmount)
    (hdown : roundToCoverScale lb.numericType lb.coverAvailable amount .downward = .ok r)
    (hnz : r.signum ≠ 0) :
    lb.roundedCoverAmount amount = .ok (.rounded r) := by
  simp [LoanBroker.roundedCoverAmount, hdown, hnz]

/-- **Proof body of `roundedCoverAmount_rejected_code`.** -/
lemma LoanBroker.roundedCoverAmount_rejected_code_proof (lb : LoanBroker) (amount : STAmount)
    (ter : TER) (hok : lb.roundedCoverAmount amount = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS := by
  unfold LoanBroker.roundedCoverAmount at hok
  dsimp only at hok
  cases h : roundToCoverScale lb.numericType lb.coverAvailable amount .downward with
  | error e => rw [h, err_bind] at hok; exact absurd hok (by simp)
  | ok r =>
    rw [h, ok_bind] at hok
    by_cases hs : (r.signum == 0) = true
    · simpa [hs] using hok.symm
    · simp [hs] at hok

/-- **Proof body of `coverDeposit_rejected`.** -/
lemma LoanBroker.coverDeposit_rejected_proof (lb : LoanBroker) (amount : STAmount) (ter : TER)
    (hrej : lb.roundedCoverAmount amount = .ok (.rejected ter)) :
    lb.coverDeposit amount = .ok (.error .tecINTERNAL) := by
  simp [LoanBroker.coverDeposit, hrej]

/-- **Proof body of `coverDeposit_success`.** -/
lemma LoanBroker.coverDeposit_success_proof (lb : LoanBroker) (amount r : STAmount)
    (rN c' : Number) (hrounded : lb.roundedCoverAmount amount = .ok (.rounded r))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat)
    (hnum : r.toNumber .to_nearest = .ok rN)
    (hadd : lb.coverAvailable.operator_add rN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, lb.coverDeposit amount = .ok (.ok ⟨r, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  have hcr := (LoanBroker.roundedCoverAmount_exactCanonical lb amount r hc hrounded).1
  have hr0 := LoanBroker.roundedCoverAmount_nonneg lb amount r hc.iouCanonical hnn hrounded
  obtain ⟨hv, hrn⟩ := STAmount.toNumber_exact_of r rN hcr hnum
  obtain ⟨lb', htl, hraw⟩ := LoanBroker.credit_lawful lb rN c' hrn (by rw [hv]; exact hr0) hadd
  refine ⟨lb', ?_, hraw⟩
  simp [LoanBroker.coverDeposit, LoanBroker.applyCoverTransaction, hrounded, hnum, hadd, htl]

/-- **Proof body of `coverDeposit_error_codes`.** -/
lemma LoanBroker.coverDeposit_error_codes_proof (lb : LoanBroker) (amount : STAmount)
    (ter : TER) (hok : lb.coverDeposit amount = .ok (.error ter)) : ter = .tecINTERNAL := by
  unfold LoanBroker.coverDeposit at hok
  obtain ⟨rr, _, hok⟩ := bind_ok_peel _ _ _ hok
  cases rr with
  | rejected t => simp at hok; exact hok.symm
  | rounded r =>
    simp only [except_pure_eq, ok_bind] at hok
    obtain ⟨res, _, hok⟩ := bind_ok_peel _ _ _ hok
    simp at hok

end XRPL.Model.Lending
