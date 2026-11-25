import XRPL.Properties.Lending.LoanBroker.Common.CoverReduction
import XRPL.Properties.Vault.Proofs.Support.WithdrawPayout
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg

/-! # The debit of a cover withdrawal or clawback

A withdrawal and a clawback clamp their amount toward zero onto the grid of `coverAvailable` minus the amount, never
finer than the base exponent. The debit is whole base units, not negative and never more than the amount. -/

namespace XRPL.Model.Protocol

/-- A debit clamped onto the grid of the difference is canonical or zero, between zero and the amount,
and a whole number of units at the base exponent. -/
lemma clampToSumExponent_debit_facts (cover : Number) (amount debit : STAmount) (b : Int)
    (hc : amount.CanonicalOrZero) (hnn : 0 ≤ amount.toRat) (hb : (-96 : ℤ) ≤ b ∧ b ≤ 80)
    (hint : amount.integral = true → b ≤ 0)
    (hok : clampToSumExponent cover amount.operator_neg b = .ok debit) :
    debit.CanonicalOrZero ∧ 0 ≤ debit.toRat ∧ debit.toRat ≤ amount.toRat ∧
      ∃ k : ℕ, debit.toRat = (k : ℚ) * 10 ^ b := by
  have hn := STAmount.CanonicalOrZero.operator_neg hc
  obtain ⟨hdc, -, hd0⟩ := clampToSumExponent_canonicalOrZero cover _ debit b hn hb.1 hb.2 hok
  have hle := clampToSumExponent_le_abs cover _ debit b hn hb.1 hb.2 hok
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hnn] at hle
  exact ⟨hdc, hd0, hle, clampToSumExponent_units cover _ debit b hn hb.1 hb.2
    (by rw [STAmount.operator_neg_integral]; exact hint) hok⟩

/-- A nonzero IOU debit is the amount floored onto the grid of the difference, an exponent at or above
the base exponent. -/
lemma clampToSumExponent_debit_floor (cover : Number) (amount debit : STAmount) (b : Int)
    (hc : amount.CanonicalOrZero) (hfr : amount.integral = false) (hnn : 0 ≤ amount.toRat)
    (hb : (-96 : ℤ) ≤ b ∧ b ≤ 80) (hnz : debit.mValue ≠ 0)
    (hok : clampToSumExponent cover amount.operator_neg b = .ok debit) :
    ∃ (amountNum : Number) (e : Int), amount.operator_neg.toNumber .to_nearest = .ok amountNum ∧
      postSumExponent cover amountNum b amount.operator_neg.numericType = .ok e ∧ b ≤ e ∧
      debit.toRat = (⌊amount.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e := by
  have hn := STAmount.CanonicalOrZero.operator_neg hc
  obtain ⟨amountNum, e, hnum, hps, hge, hv⟩ := clampToSumExponent_frac_floor cover _ debit b
    (hn.fracCanonZero ((STAmount.operator_neg_integral amount).trans hfr)) hb.1 hb.2 hnz hok
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hnn] at hv
  exact ⟨amountNum, e, hnum, hps, hge, hv⟩

/-- An XRP or MPT debit clamped onto the grid of the difference is the amount itself: canonical, with
the same count of units and the same magnitude. -/
lemma clampToSumExponent_neg_integral (cover : Number) (amount debit : STAmount) (b : Int)
    (hic : amount.IntegralCanonical) (hok : clampToSumExponent cover amount.operator_neg b = .ok debit) :
    debit.IntegralCanonical ∧ debit.mValue = amount.mValue ∧ debit.toRat = |amount.toRat| := by
  rw [clampToSumExponent_integral _ _ _ ((STAmount.operator_neg_integral amount).trans hic.is_integral),
    Except.ok.injEq] at hok
  obtain ⟨-, -, hval, hrat⟩ := clamp_magnitude amount.operator_neg
  rw [hok] at hval hrat
  refine ⟨?_, by rw [hval, STAmount.operator_neg_mValue], by rw [hrat, STAmount.operator_neg_toRat, abs_neg]⟩
  rw [← hok]
  split
  · exact hic.operator_neg.operator_neg
  · exact hic.operator_neg

/-- Negating a positive amount and taking the magnitude back gives the amount. -/
lemma STAmount.abs_operator_neg_of_pos (a : STAmount) (hpos : 0 < a.toRat) :
    (if a.operator_neg.negative then a.operator_neg.operator_neg else a.operator_neg) = a := by
  have hnz : a.mValue ≠ 0 := fun h0 => hpos.ne' ((STAmount.toRat_eq_zero_iff a).mpr h0)
  have hneg := STAmount.mIsNegative_false_of_pos a hpos
  cases a
  simp_all [STAmount.operator_neg, STAmount.negative]

end XRPL.Model.Protocol
