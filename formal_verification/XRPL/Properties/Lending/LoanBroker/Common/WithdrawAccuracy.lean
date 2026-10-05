import XRPL.Properties.Lending.LoanBroker.Common.WithdrawExits
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-! # Proof bodies for the `LoanBroker.coverWithdraw` theorems

The withdrawal converts the requested amount to a `Number` and subtracts it with
19-digit rounding. The amount is not rounded first, so the debit is exact when
the true difference fits a `Number`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

/-- **Proof body of `coverWithdraw_amount`.** -/
lemma LoanBroker.coverWithdraw_amount_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res)) :
    res.amount' = amount :=
  LoanBroker.applyCoverTransaction_amount' lb _ amount res
    (LoanBroker.coverWithdraw_ok_inv lb amount res hok)

/-- **Proof body of `coverWithdraw_debit`.** -/
lemma LoanBroker.coverWithdraw_debit_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - amount.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = amount.toRat := by
  have happ := LoanBroker.coverWithdraw_ok_inv lb amount res hok
  rw [(LoanBroker.applyCoverTransaction_debit_value lb amount res happ hc hexact).1]
  ring

/-- **Proof body of `coverWithdraw_debit_integral`.** -/
lemma LoanBroker.coverWithdraw_debit_integral_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ amount.toRat) (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = amount.toRat := by
  have happ := LoanBroker.coverWithdraw_ok_inv lb amount res hok
  obtain ⟨hv, _⟩ :=
    LoanBroker.applyCoverTransaction_debit_integral lb amount res happ hint hsz hnn hcint hbound
  rw [hv]; ring

/-- **Proof body of `coverWithdraw_decreases_cover`.** -/
lemma LoanBroker.coverWithdraw_decreases_cover_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable := by
  have happ := LoanBroker.coverWithdraw_ok_inv lb amount res hok
  obtain ⟨m, c', hm, hsub, _, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb amount res happ
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of amount m hc hm
  show res.loanBroker'.toRawLoanBroker.coverAvailable.toRat ≤ lb.coverAvailable.toRat
  rw [hraw]
  exact operator_sub_le_of_le_normalized _ _ _ _ lb.wf.coverAvailable_norm hmn hsub
    lb.wf.coverAvailable_norm (by rw [hmv]; linarith)

/-- **Proof body of `coverWithdraw_total`.** -/
lemma LoanBroker.coverWithdraw_total_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS) (hc : amount.ExactCanonical) :
    ∃ res, lb.coverWithdraw amount = .ok (.ok res) ∧ res.amount' = amount := by
  obtain ⟨e, aN, c', _, _, hn, hlt, hs, _⟩ :=
    LoanBroker.canCoverWithdraw_success_inv lb pool amount hcan
  obtain ⟨_, han⟩ := STAmount.toNumber_exact_of amount aN hc hn
  obtain ⟨lb', htl, _⟩ := LoanBroker.debit_lawful lb aN c' han hlt hs
  refine ⟨{ amount' := amount, loanBroker' := lb' }, ?_, rfl⟩
  simp [LoanBroker.coverWithdraw, LoanBroker.applyCoverTransaction, hn, hs, htl]

/-- **Proof body of `coverWithdraw_keeps_minimum`.** -/
lemma LoanBroker.coverWithdraw_keeps_minimum_proof (lb : LoanBroker) (pool : α)
    (amount : STAmount) (res : LoanBrokerCoverResult) (e : Int)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) :
    res.loanBroker'.HasMinimumCover e := by
  obtain ⟨e', aN, c', _, he, hn, _, hs, hm⟩ :=
    LoanBroker.canCoverWithdraw_success_inv lb pool amount hcan
  rw [hexp, Except.ok.injEq] at he
  subst he
  have happ := LoanBroker.coverWithdraw_ok_inv lb amount res hok
  obtain ⟨m, c'', hm', hs', _, hraw⟩ :=
    LoanBroker.applyCoverTransaction_debit_inv lb amount res happ
  rw [hn, Except.ok.injEq] at hm'
  subst hm'
  rw [hs, Except.ok.injEq] at hs'
  subst hs'
  unfold LoanBroker.HasMinimumCover
  rw [hraw]
  exact hm

/-- **Proof body of `coverWithdraw_all`.** -/
lemma LoanBroker.coverWithdraw_all_proof (lb : LoanBroker) (pool : α) (e : Int) (s : STAmount)
    (hdebt : lb.debtTotal = Number.zero)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s)
    (hnz : s.mValue ≠ 0) (hrep : s.toRat = lb.toExact.coverAvailable)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e) :
    lb.canCoverWithdraw pool s = .ok .tesSUCCESS ∧
      ∃ res, lb.coverWithdraw s = .ok (.ok res) ∧ res.loanBroker'.toExact.coverAvailable = 0 := by
  have hcn := lb.wf.coverAvailable_norm
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hrep' : s.toRat = lb.coverAvailable.toRat := hrep
  have hc : s.ExactCanonical := STAmount.ofNumber_exactCanonical _ _ .to_nearest s hcn hcov0 hs hnz
  have hcap : lb.coverAvailable.toRat < 10 ^ 96 := by
    rw [← hrep']; exact lt_of_le_of_lt (le_abs_self _) (STAmount.ExactCanonical.abs_lt s hc)
  -- the whole cover already sits at the cover scale, so it passes the scale check
  have hcheck := canApplyToBrokerCover_whole _ _ _ hs hnz
  -- the amount converts exactly, and taking it leaves zero
  obtain ⟨aN, hnum, hav, han⟩ := STAmount.toNumber_exact_canonical s .to_nearest hc
  have hge : lb.coverAvailable.operator_lt aN = false :=
    (operator_lt_eq_false_iff _ _ hcn han).mpr (by rw [hav, hrep'])
  obtain ⟨c', hsub⟩ := Number.operator_sub_ok_of_lt lb.coverAvailable aN .to_nearest hcn han
    hcov0 hcap (by rw [hav, hrep']; exact hcov0) (by rw [hav, hrep']; exact hcap)
  have hc'0 : c'.toRat = 0 := by
    rw [Number.roundsToRepresentable_eq c' (lb.coverAvailable.toRat - aN.toRat)
      (operator_sub_rounded_to_nearest _ _ _ hcn han hsub) Number.zero Number.zero_isNormalized
      (by rw [Number.toRat_zero, hav, hrep']; ring), hav, hrep']
    ring
  have hcn' : c'.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ _ hcn han hsub
  -- with no debt the minimum cover is zero, which the empty cover still meets
  have hmin : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover e =
      .ok true := by
    show (do
        let minimumCover ← minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e
        return minimumCover.operator_le c') = Except.ok true
    rw [hdebt, minimumBrokerCover_zero_debt]
    simp only [ok_bind, pure_eq, Except.ok.injEq]
    exact (operator_le_iff _ _ Number.zero_isNormalized hcn').mpr
      (by rw [Number.toRat_zero, hc'0])
  have hcan := LoanBroker.canCoverWithdraw_success_proof lb pool s e aN c' hcheck hexp hnum hge
    hsub hmin
  refine ⟨hcan, ?_⟩
  obtain ⟨res, hok, _⟩ := LoanBroker.coverWithdraw_total_proof lb pool s hcan hc
  have hdeb := LoanBroker.coverWithdraw_debit_proof lb s res hok hc
    ⟨Number.zero, Number.zero_isNormalized, by
      rw [Number.toRat_zero]; show (0 : ℚ) = lb.coverAvailable.toRat - s.toRat; rw [hrep']; ring⟩
  refine ⟨res, hok, ?_⟩
  have : lb.toExact.coverAvailable = s.toRat := hrep.symm
  linarith

end XRPL.Model.Lending
