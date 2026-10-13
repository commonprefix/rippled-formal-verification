import XRPL.Properties.Lending.LoanBroker.Common.WithdrawExits
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Lending.LoanBroker.Common.CoverUnit

/-! # Proof bodies for the `LoanBroker.coverWithdraw` theorems

Proofs for the theorems in `LoanBrokerCoverWithdraw.lean`. -/

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

/-- A withdrawal lowers `coverAvailable` by exactly the requested amount when the difference fits
a `Number`. -/
lemma LoanBroker.coverWithdraw_debit_request (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable - amount.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = amount.toRat := by
  have happ := LoanBroker.coverWithdraw_ok_inv lb amount res hok
  rw [(LoanBroker.applyCoverTransaction_debit_value lb amount res happ hc hexact).1]
  ring

/-- **Proof body of `coverWithdraw_debit`.** -/
lemma LoanBroker.coverWithdraw_debit_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat := by
  rw [LoanBroker.coverWithdraw_amount_proof lb amount res hok] at hexact ⊢
  exact LoanBroker.coverWithdraw_debit_request lb amount res hok hc hexact

/-- **Proof body of `coverWithdraw_debit_le_amount`.** -/
lemma LoanBroker.coverWithdraw_debit_le_amount_proof (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hc : amount.ExactCanonical)
    (hexact : ∃ w : Number, w.isNormalized ∧
      w.toRat = lb.toExact.coverAvailable - res.amount'.toRat) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≤ amount.toRat := by
  rw [LoanBroker.coverWithdraw_debit_proof lb amount res hok hc hexact,
    LoanBroker.coverWithdraw_amount_proof lb amount res hok]

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

/-- **Proof body of `coverWithdraw_decrease_possible`.** The amount is one unit at the cover scale. -/
lemma LoanBroker.coverWithdraw_decrease_possible_proof (lb : LoanBroker) (pool : α) (s : STAmount)
    (e : Int) (minimumCover : Number)
    (hexp : AssetPool.exponent pool lb.numericType = .ok e)
    (hmin : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover)
    (hs : STAmount.ofNumber lb.numericType lb.coverAvailable .to_nearest = .ok s) (hnz : s.mValue ≠ 0)
    (hunit : (-81 : Int) ≤ s.exponent)
    (hroom : minimumCover.toRat + (10 : ℚ) ^ s.exponent ≤ lb.toExact.coverAvailable) :
    ∃ (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverWithdraw pool amount = .ok .tesSUCCESS ∧ lb.coverWithdraw amount = .ok (.ok res) ∧
        res.loanBroker'.toExact.coverAvailable < lb.toExact.coverAvailable := by
  have hcn := lb.wf.coverAvailable_norm
  have hcov0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  have hcov : lb.toExact.coverAvailable = lb.coverAvailable.toRat := rfl
  have hmn := minimumBrokerCover_isNormalized _ _ _ _ _ hmin
  have hm0 := LoanBroker.minimumCover_nonneg lb pool e minimumCover hexp hmin
  have hcap := LoanBroker.cover_lt_cap_of_ofNumber lb s hs hnz
  have hp : (0 : ℚ) < (10 : ℚ) ^ s.exponent := zpow_pos (by norm_num) _
  obtain ⟨u, huc, _, _, huv, hcheck⟩ := LoanBroker.coverUnit_exists lb s hs hnz hunit
  obtain ⟨w, hwn, hwv⟩ := LoanBroker.coverUnit_sub_exact lb s hs hnz hunit (by linarith)
  -- the unit converts exactly, and CoverAvailable covers it
  obtain ⟨uN, hnum, huNv, huNn⟩ := STAmount.toNumber_exact_canonical u .to_nearest huc
  have hge : lb.coverAvailable.operator_lt uN = false :=
    (operator_lt_eq_false_iff _ _ hcn huNn).mpr (by rw [huNv, huv]; linarith)
  obtain ⟨c', hsub⟩ := Number.operator_sub_ok_of_lt lb.coverAvailable uN .to_nearest hcn huNn hcov0 hcap
    (by rw [huNv, huv]; exact hp.le)
    (by rw [huNv]; exact lt_of_le_of_lt (le_abs_self _) (STAmount.ExactCanonical.abs_lt u huc))
  -- taking the unit is exact, and leaves at least the minimum cover
  have hc'v : c'.toRat = lb.coverAvailable.toRat - (10 : ℚ) ^ s.exponent := by
    rw [Number.roundsToRepresentable_eq c' _ (operator_sub_rounded_to_nearest _ _ _ hcn huNn hsub) w hwn
      (by rw [hwv, huNv, huv, hcov]), huNv, huv]
  have hcn' : c'.isNormalized := operator_sub_isNormalized_to_nearest_sz _ _ _ hcn huNn hsub
  have hmin' : ({ lb.toRawLoanBroker with coverAvailable := c' } : RawLoanBroker).hasMinimumCover e =
      .ok true := by
    show (do
        let minimumCover ← minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e
        return minimumCover.operator_le c') = Except.ok true
    rw [hmin]
    simp only [ok_bind, pure_eq, Except.ok.injEq]
    exact (operator_le_iff _ _ hmn hcn').mpr (by rw [hc'v]; linarith)
  have hcan := LoanBroker.canCoverWithdraw_success_proof lb pool u e uN c' hcheck hexp hnum hge hsub hmin'
  obtain ⟨lb', hok, hraw⟩ := LoanBroker.coverWithdraw_success_proof lb u uN c' huc hnum hge hsub
  refine ⟨u, ⟨u, lb'⟩, hcan, hok, ?_⟩
  show lb'.toRawLoanBroker.coverAvailable.toRat < lb.coverAvailable.toRat
  rw [hraw]
  show c'.toRat < lb.coverAvailable.toRat
  rw [hc'v]
  linarith

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
  have hdeb := LoanBroker.coverWithdraw_debit_request lb s res hok hc
    ⟨Number.zero, Number.zero_isNormalized, by
      rw [Number.toRat_zero]; show (0 : ℚ) = lb.coverAvailable.toRat - s.toRat; rw [hrep']; ring⟩
  refine ⟨res, hok, ?_⟩
  have : lb.toExact.coverAvailable = s.toRat := hrep.symm
  linarith

end XRPL.Model.Lending
