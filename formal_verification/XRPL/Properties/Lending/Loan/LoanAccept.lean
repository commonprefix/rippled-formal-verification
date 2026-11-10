import XRPL.Properties.Lending.Loan.Common.AcceptDeleteLedger
import XRPL.Properties.Lending.Loan.Common.AcceptCoverWitness

/-! # `LoanAccept` properties

What accepting a pending loan moves in the vault. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault)

/-- Accept -> AssetsReserved falls by PrincipalOutstanding = amountToBorrower + OriginationFee, YieldUnrealized grows by
interestDue, nothing else in the vault or broker changes. -/
theorem Lending.accept_releases (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanAccept i)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (interestDue : Number) (hi : loan.interestDue = .ok interestDue)
    -- `r` - the accept the LoanAccept runs, `r.amountToBorrower` is what the vault sends the borrower
    (r : LoanWithDisbursement Vault) (hacc : (loan.accept l.vault).run = .ok (.ok r)) :
    l'.vault.assetsReserved.toRat = l.vault.assetsReserved.toRat - loan.principalOutstanding.toRat ∧
      l'.vault.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat + interestDue.toRat ∧
      { l'.vault.toRawVault with
          assetsReserved := l.vault.assetsReserved
          yieldUnrealized := l.vault.yieldUnrealized } = l.vault.toRawVault ∧
      loan'.broker = loan.broker ∧
      r.amountToBorrower.toRat + loan.fees.originationFee.toRat = loan.principalOutstanding.toRat ∧
      l.vault.assetsReserved.toRat - l'.vault.assetsReserved.toRat =
        r.amountToBorrower.toRat + loan.fees.originationFee.toRat :=
  let ⟨h1, h2, h3, h4⟩ := LendingLedger.accept_releases_proof hr h hat hat' hi
  ⟨h1, h2, h3, h4, LendingLedger.accept_amountToBorrower_proof hr h hat hat' hi r hacc⟩

/-- Create pending then accept -> the same vault, broker and loan as an active create with that StartDate.
`hclose` - an active LoanSet starts the loan at the close time, so the ledger closes at StartDate first -/
theorem Lending.createPending_accept (l : LendingLedger) (hr : l.Reachable) (l₁ l₂ lc : LendingLedger) (j : Nat)
    (principal : Number) (rates : LoanRates) (fees : LoanFees)
    (paymentInterval paymentTotal gracePeriod : Option UInt32) (startDate : UInt32) (allowsOverpayment : Bool)
    (hset : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate true
      allowsOverpayment)).run = .ok (.ok l₁))
    (haccept : (l₁.apply (.loanAccept l.loans.length)).run = .ok (.ok l₂))
    (hclose : (l.apply (.close startDate)).run = .ok (.ok lc)) :
    ∃ lA, (lc.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate false
      allowsOverpayment)).run = .ok (.ok lA) ∧
      lA.vault = l₂.vault ∧ lA.brokers = l₂.brokers ∧ lA.loans = l₂.loans :=
  LendingLedger.createPending_accept_proof hr hset haccept hclose

/-- LoanAccept from a broker at or above minCover -> the broker after it is still at or above minCover. -/
theorem Lending.accept_keeps_minimum_cover (l l' : LendingLedger) (i : Nat)
    (h : (l.apply (.loanAccept i)).run = .ok (.ok l')) (loan loan' : Loan) (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok true) :
    loan'.broker.hasMinimumCover l'.vault.baseExponent = .ok true := by
  obtain ⟨-, loan₀, r, -, hat₀, -, hacc, -, hv, hat₁, -, -⟩ := LendingLedger.loanAccept_ok h
  obtain rfl := hat.eq hat₀
  obtain rfl := hat'.eq hat₁
  rw [Loan.accept_broker loan _ r hacc, hv, (Loan.accept_keepsSettings loan _ r hacc).baseExponent_eq]
  exact hcover

/-- Witness: a run where LoanAccept succeeds from a broker below minCover. A broker at 10% minimum cover holds 100 for
loan A of 600 and pending loan B of 400, the default of A takes all 100, then B is accepted with minCover 40. -/
theorem Lending.accept_keeps_minimum_cover_attained :
    ∃ (l l' : LendingLedger) (i : Nat) (loan loan' : Loan),
      l.Reachable ∧ (l.apply (.loanAccept i)).run = .ok (.ok l') ∧ l.LoanAt i loan ∧ l'.LoanAt i loan' ∧
      loan.broker.hasMinimumCover l.vault.baseExponent = .ok false ∧
      loan'.broker.hasMinimumCover l'.vault.baseExponent = .ok false :=
  LendingLedger.accept_keeps_minimum_cover_witness

end XRPL.Model
