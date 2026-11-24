import Batteries.Tactic.OpenPrivate
import XRPL.Properties.Lending.Ledger.Common.NoExceptionLoanPayRoom
import XRPL.Properties.Lending.Loan.Common.PayExits

/-! # What the instalment loop leaves for an overpayment

The loop keeps its sums normalized and within the instalments it paid, keeps PeriodicPayment, and leaves a loan with
payments to make the room its next instalment needs. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.doPayment_periodicPayment from XRPL.Properties.Lending.Loan.Common.OverpaymentReduces
open private rn_ge from XRPL.Properties.Lending.Loan.Common.SetLawful
open private Number.add_count PaymentAmounts.add_count from XRPL.Properties.Lending.Loan.Common.DueLoop

local notation "ε" => Number.nearestError

/-- The instalment loop computes on a `PayRoom` loan as in `payInstalments_computes_room`. Its sums stay normalized
and within the instalments paid, PeriodicPayment is kept, and a loan with payments left keeps the room. -/
lemma UnsettledPayment.payInstalments_bounds_room {α : Type} (amount : Number) :
    ∀ (n : Nat) (p : UnsettledPayment α), p.loan.PayRoom → p.count + n ≤ 100 → p.totalPaid.isNormalized →
      |p.totalPaid.toRat| ≤ p.count * (2 * 10 ^ 99) → p.amounts.Norm →
      |p.amounts.principalPaid.toRat| ≤ p.count * (2 * 10 ^ 99) →
      |p.amounts.interestPaid.toRat| ≤ p.count * (2 * 10 ^ 99) →
      |p.amounts.feePaid.toRat| ≤ p.count * (2 * 10 ^ 99) → 0 ≤ p.amounts.feePaid.toRat →
      ∃ p', UnsettledPayment.payInstalments p n amount = .ok p' ∧ 0 ≤ p'.amounts.feePaid.toRat ∧
        p.totalPaid.toRat ≤ p'.totalPaid.toRat ∧ p.count ≤ p'.count ∧ p'.totalPaid.isNormalized ∧
        p'.amounts.Norm ∧ |p'.amounts.principalPaid.toRat| ≤ p'.count * (2 * 10 ^ 99) ∧
        |p'.amounts.interestPaid.toRat| ≤ p'.count * (2 * 10 ^ 99) ∧
        |p'.amounts.feePaid.toRat| ≤ p'.count * (2 * 10 ^ 99) ∧ p'.count ≤ p.count + n ∧
        p'.loan.periodicPayment = p.loan.periodicPayment ∧ (p'.loan.paymentRemaining ≠ 0 → p'.loan.PayRoom) := by
  intro n
  induction n with
  | zero =>
    intro p hroom _ htN _ hN hpl hil hfl hF
    exact ⟨p, by rw [UnsettledPayment.payInstalments]; rfl, hF, le_rfl, le_rfl, htN, hN, hpl, hil, hfl, le_rfl, rfl,
      fun _ => hroom⟩
  | succ n ih =>
    intro p hroom hcnt htN htl hN hpl hil hfl hF
    have hcq : p.count ≤ 100 := by omega
    rw [UnsettledPayment.payInstalments]
    by_cases hpr0 : (p.loan.paymentRemaining == 0) = true
    · simp only [hpr0, ↓reduceIte, pure, Except.pure]
      exact ⟨p, rfl, hF, le_rfl, le_rfl, htN, hN, hpl, hil, hfl, Nat.le_add_right _ _, rfl, fun _ => hroom⟩
    have hpr : p.loan.paymentRemaining ≠ 0 := by simpa using hpr0
    obtain ⟨pc, hpc, b1, b2, b3, h1, h2, h3, hu⟩ := hroom.components hpr
    obtain ⟨bS, hS0⟩ := hroom.fee
    have hd1 : pc.totalValueDelta.operator_add pc.untrackedInterest .to_nearest = .ok pc.totalValueDelta := by
      rw [hu]; exact Number.operator_add_zero_right _ _
    obtain ⟨due, hdue⟩ := Number.Below.add_ok (by norm_num) (b1.mono (by norm_num)) bS
    have bdue := Number.Below.add (b1.mono (by norm_num)) bS hdue
    have hdue0 := Number.operator_add_nonneg _ _ _ b1.1 bS.1 hdue (by linarith)
    have hdue' : ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents).totalDue =
        .ok due := by
      unfold PaymentComponents.totalDue
      simp only [hd1, hdue, bind, Except.bind]
    have hdl : |due.toRat| < 10 ^ 99 := lt_of_lt_of_le bdue.2 (by norm_num)
    obtain ⟨tp', htp', htp'N, htp'l⟩ := Number.add_count htN bdue.1 htl hdl hcq
    have htp'ge : p.totalPaid.toRat ≤ tp'.toRat := by
      have := rn_ge (Number.operator_add_rounded_to_nearest _ _ _ htN bdue.1 htp') p.totalPaid htN (by linarith)
      exact this
    by_cases hlt : amount.operator_lt tp' = true
    · simp only [hpr0, Bool.false_eq_true, ↓reduceIte, hpc, hdue', htp', hlt, bind, Except.bind, pure,
        Except.pure]
      exact ⟨p, rfl, hF, le_rfl, le_rfl, htN, hN, hpl, hil, hfl, Nat.le_add_right _ _, rfl, fun _ => hroom⟩
    obtain ⟨inst, hinst⟩ := PaymentComponents.paidAmounts_ok_of_below
      ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents)
      (b1.mono (by norm_num)) (b2.mono (by norm_num)) (b3.mono (by norm_num))
      (by show pc.untrackedInterest.Below 180; rw [hu]; exact ⟨Number.zero_isNormalized, by simp [Number.toRat_zero]⟩)
      (bS.mono (by norm_num))
    obtain ⟨vap, id, hvap, hid, hip, hfp, hpp⟩ := PaymentComponents.paidAmounts_ok_inv _ inst hinst
    have bvap := Number.Below.sub b1 b2 hvap
    have bid := Number.Below.sub bvap (b3.mono (by norm_num)) hid
    have bip : inst.interestPaid.Below 99 := by
      have := Number.Below.add (bid.mono (by norm_num : 19 ≤ 98)) (show pc.untrackedInterest.Below 98 by
        rw [hu]; exact ⟨Number.zero_isNormalized, by simp [Number.toRat_zero]⟩) hip
      exact this
    have bfp : inst.feePaid.Below 98 := Number.Below.add (b3.mono (by norm_num)) bS hfp
    have hfp0 : 0 ≤ inst.feePaid.toRat := Number.operator_add_nonneg _ _ _ b3.1 bS.1 hfp (by linarith)
    have bpp : inst.principalPaid.Below 17 := by rw [hpp]; exact b2
    have hne := Loan.doPayment_scheduled_ne_notLawful p.loan hroom.shape pc
      ({ pc with untrackedManagementFee := p.loan.fees.serviceFee } : PaymentComponents) hpc hpr ⟨rfl, rfl, rfl, rfl⟩
    have hT0 : 0 ≤ p.loan.totalValueOutstanding.toRat := p.loan.exact.totalValueOutstanding_nonneg
    have hP0 : 0 ≤ p.loan.principalOutstanding.toRat := p.loan.exact.principalOutstanding_nonneg
    have hM0 : 0 ≤ p.loan.managementFeeOutstanding.toRat := p.loan.exact.managementFeeOutstanding_nonneg
    have hi := hroom.shape.3
    have hTv := hroom.value
    have hb17 : (10 : ℚ) ^ 16 + 1 < 10 ^ 17 := by norm_num
    obtain ⟨l', hl'⟩ := Loan.doPayment_ok_of_below p.loan _ hne
      (fun hf => Loan.scheduledComponents_two_le _ _ hpc hpr hf) (b1.mono (by norm_num)) (b2.mono (by norm_num))
      (b3.mono (by norm_num)) ⟨p.loan.wf.totalValueOutstanding_norm, by rw [abs_of_nonneg hT0]; linarith⟩
      ⟨p.loan.wf.principalOutstanding_norm, by
        have : p.loan.principalOutstanding.toRat ≤ p.loan.totalValueOutstanding.toRat := by
          have : 0 ≤ p.loan.totalValueOutstanding.toRat - p.loan.principalOutstanding.toRat -
            p.loan.managementFeeOutstanding.toRat := hi
          linarith
        rw [abs_of_nonneg hP0]; linarith⟩
      ⟨p.loan.wf.managementFeeOutstanding_norm, by
        have : p.loan.managementFeeOutstanding.toRat ≤ p.loan.totalValueOutstanding.toRat := by
          have : 0 ≤ p.loan.totalValueOutstanding.toRat - p.loan.principalOutstanding.toRat -
            p.loan.managementFeeOutstanding.toRat := hi
          linarith
        rw [abs_of_nonneg hM0]; linarith⟩
    obtain ⟨am', ham', ham'N, hapl, hail, hafl, haf0⟩ := PaymentAmounts.add_count (c := p.count) hN
      ⟨bpp.1, bip.1, bfp.1⟩ hcq hpl hil hfl (lt_of_lt_of_le bpp.2 (by norm_num))
      (lt_of_lt_of_le bip.2 (by norm_num)) (lt_of_lt_of_le bfp.2 (by norm_num))
    have hF' := haf0 hF hfp0
    by_cases hfin : pc.isFinal = true
    · simp only [hpr0, Bool.false_eq_true, ↓reduceIte, hpc, hdue', htp', hlt, hinst, hl', ham', bind,
        Except.bind, pure, Except.pure]
      simp only [hfin, ↓reduceIte]
      exact ⟨_, rfl, hF', htp'ge, Nat.le_succ _, htp'N, ham'N, by simpa using hapl, by simpa using hail,
        by simpa using hafl, by simp only; omega, Loan.doPayment_periodicPayment _ _ _ hl',
        fun h => absurd (Loan.doPayment_final _ _ _ hfin hl') h⟩
    have hf : pc.isFinal = false := by simpa using hfin
    have hroom' := hroom.next pc _ hpc hf hpr hl'
    obtain ⟨p', hp', hF'', hge, hcge, hp'N, hp'A, hp'P, hp'I, hp'Fe, hp'c, hp'pp, hp'room⟩ :=
      ih { p with loan := l', amounts := am', totalPaid := tp', count := p.count + 1 }
      hroom' (by simp only; omega) htp'N (by simpa using htp'l) ham'N (by simpa using hapl) (by simpa using hail)
      (by simpa using hafl) hF'
    simp only [hpr0, Bool.false_eq_true, ↓reduceIte, hpc, hdue', htp', hlt, hinst, hl', ham', bind,
      Except.bind, pure, Except.pure]
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨p', hp', hF'', le_trans htp'ge hge, le_trans (Nat.le_succ _) hcge, hp'N, hp'A, hp'P, hp'I, hp'Fe,
      by simp only at hp'c; omega, hp'pp.trans (Loan.doPayment_periodicPayment _ _ _ hl'), hp'room⟩

end XRPL.Model.Lending
