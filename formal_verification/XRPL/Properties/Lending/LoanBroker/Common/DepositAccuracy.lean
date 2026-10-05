import XRPL.Properties.Lending.LoanBroker.Common.CoverAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-! # Proof bodies for the `LoanBroker.coverDeposit` theorems

Proofs for the theorems in `LoanBrokerCoverDeposit.lean`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- **Proof body of `coverDeposit_credit`.** -/
lemma LoanBroker.coverDeposit_credit_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = res.amount'.toRat := by
  have hc := (LoanBroker.coverDeposit_amount_exactCanonical lb amount res hok hc).1
  obtain ⟨r, _, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  have hamt : res.amount' = r :=
    LoanBroker.applyCoverTransaction_amount' lb _ r res happ
  rw [hamt] at hc hexact ⊢
  rw [(LoanBroker.applyCoverTransaction_credit_value lb r res happ hc hexact).1]
  ring

/-- **Proof body of `coverDeposit_credit_integral`.** -/
lemma LoanBroker.coverDeposit_credit_integral_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable + amount.toRat < 2 ^ 63) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = amount.toRat := by
  have hamt := LoanBroker.coverDeposit_amount_integral lb amount res hok hint.is_integral
  rw [← hamt]
  apply LoanBroker.coverDeposit_credit_proof lb amount res hok (Or.inr ⟨hint, hsz⟩)
  rw [hamt]
  have hden := Rat.den_one_add _ _ hcint (STAmount.IntegralCanonical.den_eq_one _ hint)
  have hcov : 0 ≤ lb.toExact.coverAvailable := lb.exact.coverAvailable_nonneg
  have habs := STAmount.IntegralCanonical.abs_toRat_le_of_mValue_le amount hint hsz
  exact Number.exists_of_int _ hden (by linarith [neg_abs_le amount.toRat]) hbound

/-- **Proof body of `coverDeposit_credit_le_amount`.** -/
lemma LoanBroker.coverDeposit_credit_le_amount_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable + res.amount'.toRat) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable ≤ amount.toRat := by
  rw [LoanBroker.coverDeposit_credit_proof lb amount res hok hc hexact]
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  have hamt : res.amount' = r :=
    LoanBroker.applyCoverTransaction_amount' lb _ r res happ
  rw [hamt]
  obtain ⟨e, hexp⟩ := LoanBroker.roundedCoverAmount_exponent lb amount r hrr
  exact (LoanBroker.roundedCoverAmount_bounds_proof lb amount r e hc.iouCanonical hexp hrr).1

/-- **Proof body of `coverDeposit_increases_cover`.** -/
lemma LoanBroker.coverDeposit_increases_cover_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat) :
    lb.toExact.coverAvailable ≤ res.loanBroker'.toExact.coverAvailable := by
  have hcr := (LoanBroker.coverDeposit_amount_exactCanonical lb amount res hok hc).1
  have hr0 := (LoanBroker.coverDeposit_amount_bounds lb amount res hok hc hnn).1
  obtain ⟨r, _, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  obtain ⟨m, c', hm, hadd, hamt, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  rw [hamt] at hcr hr0
  obtain ⟨hmv, hmn⟩ := STAmount.toNumber_exact_of r m hcr hm
  show lb.coverAvailable.toRat ≤ res.loanBroker'.toRawLoanBroker.coverAvailable.toRat
  rw [hraw]
  exact operator_add_ge_of_ge_normalized _ _ _ _ lb.wf.coverAvailable_norm hmn hadd
    lb.wf.coverAvailable_norm (by rw [hmv]; linarith)

/-- **Proof body of `coverDeposit_total`.** -/
lemma LoanBroker.coverDeposit_total_proof (lb : LoanBroker) (amount r : STAmount)
    (hrounded : lb.roundedCoverAmount amount = .ok (.rounded r)) (hc : amount.ExactCanonical)
    (hnn : 0 ≤ amount.toRat) (hcap : lb.toExact.coverAvailable + r.toRat < 10 ^ 96) :
    ∃ res, lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = r := by
  have hcr := (LoanBroker.roundedCoverAmount_exactCanonical lb amount r hc hrounded).1
  have hr0 := LoanBroker.roundedCoverAmount_nonneg lb amount r hc.iouCanonical hnn hrounded
  obtain ⟨m, hm, hmv, hmn⟩ := STAmount.toNumber_exact_canonical r .to_nearest hcr
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hcn := lb.wf.coverAvailable_norm
  have hm0 : 0 ≤ m.toRat := by rw [hmv]; exact hr0
  change lb.coverAvailable.toRat + r.toRat < 10 ^ 96 at hcap
  obtain ⟨c', hadd⟩ := Number.operator_add_ok_of_lt lb.coverAvailable m .to_nearest hcn hmn hcov0
    (by linarith) hm0 (by rw [hmv]; linarith)
  obtain ⟨lb', htl, _⟩ := LoanBroker.credit_lawful lb m c' hmn hm0 hadd
  refine ⟨{ amount' := r, loanBroker' := lb' }, ?_, rfl⟩
  simp [LoanBroker.coverDeposit, LoanBroker.applyCoverTransaction, hrounded, hm, hadd, htl]

/-- **Proof body of `coverDeposit_keeps_minimum`.** -/
lemma LoanBroker.coverDeposit_keeps_minimum_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat) (hmin : lb.HasMinimumCover e) :
    res.loanBroker'.HasMinimumCover e := by
  have hf := LoanBroker.coverDeposit_fixed_fields lb amount res hok
  exact LoanBroker.hasMinimumCover_of_cover_le lb res.loanBroker' e hf.numericType hf.debtTotal
    hf.coverRateMinimum
    (LoanBroker.coverDeposit_increases_cover_proof lb amount res hok hc hnn) hmin

/-- **Proof body of `coverDeposit_empty`.** -/
lemma LoanBroker.coverDeposit_empty_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hzero : lb.coverAvailable = Number.zero)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hat : amount.mNumericType = lb.numericType) :
    res.amount' = amount ∧ res.loanBroker'.toExact.coverAvailable = amount.toRat := by
  obtain ⟨q, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  have hq := (LoanBroker.roundedCoverAmount_rounded_inv lb amount q hrr).1
  unfold roundToCoverScale at hq
  obtain ⟨e, he, hq⟩ := bind_ok_peel _ _ _ hq
  have hamt := LoanBroker.applyCoverTransaction_amount' lb _ q res happ
  -- an empty cover leaves the amount alone
  have hsame : q = amount := by
    refine STAmount.roundToExponent_ok_eq_self amount q e .downward ?_ hq
    rcases id hc with hia | ⟨hia, _⟩
    · -- an empty IOU cover sits at scale `10^-100`, below every IOU amount
      have hnt : lb.numericType = .fractional := by rw [← hat]; exact hia.is_fractional
      rw [hzero, hnt] at he
      unfold numberExponent at he
      rw [STAmount.ofNumber_fractional_zero] at he
      have he100 : e = -100 := by
        simp only [ok_bind, pure_eq, Except.ok.injEq] at he
        exact he.symm
      refine Or.inr (Or.inr ?_)
      have := hia.exp_lo
      show e ≤ amount.mOffset
      omega
    · exact Or.inl hia.is_integral
  rw [hsame] at hamt
  refine ⟨hamt, ?_⟩
  -- the empty cover plus the amount is the amount
  have h0 : lb.toExact.coverAvailable = 0 := by
    show lb.coverAvailable.toRat = 0
    rw [hzero, Number.toRat_zero]
  obtain ⟨aN, _, hav, han⟩ := STAmount.toNumber_exact_canonical amount .to_nearest hc
  have hup := LoanBroker.coverDeposit_credit_proof lb amount res hok hc
    ⟨aN, han, by rw [hamt, hav, h0]; ring⟩
  rw [hamt] at hup
  linarith

end XRPL.Model.Lending
