import XRPL.Model.Lending.LoanBroker.LoanBrokerDelete
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding

/-! # Proof bodies for the `LoanBroker.roundedCoverAvailable` theorems

Proofs for the theorems in `LoanBrokerDelete.lean`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A zero `coverAvailable` converts to a zero IOU amount. -/
private lemma roundedCoverAvailable_zero_iou (lb : LoanBroker) (s : STAmount)
    (hm : lb.coverAvailable.mantissa_ = 0)
    (hok : STAmount.ofNumber .fractional lb.coverAvailable .to_nearest = .ok s) : s.mValue = 0 := by
  rw [Number.eq_zero_of_mantissa_zero _ lb.wf.coverAvailable_norm hm,
    STAmount.ofNumber_fractional_zero, Except.ok.injEq] at hok
  rw [← hok]

/-- **Proof body of `roundedCoverAvailable_within_half`.** -/
lemma LoanBroker.roundedCoverAvailable_within_half_proof (lb : LoanBroker) (s : STAmount)
    (hok : lb.roundedCoverAvailable = .ok s) (hnz : s.mValue ≠ 0) :
    |s.toRat - lb.toExact.coverAvailable| ≤ (1 / 2 : ℚ) * (10 : ℚ) ^ s.exponent := by
  unfold LoanBroker.roundedCoverAvailable at hok
  have hneg := LoanBroker.coverAvailable_negative_false lb
  show |s.toRat - lb.coverAvailable.toRat| ≤ _
  cases hnt : lb.numericType with
  | integral mv mo ms msh =>
    rw [hnt] at hok
    have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
    have hoff : s.exponent = 0 :=
      (STAmount.ofNumber_integral_canonical _ _ _ s hint hok).1.offset_zero
    rw [hoff, zpow_zero, mul_one]
    exact STAmount.ofNumber_integral_within_half _ _ s hint lb.wf.coverAvailable_norm hneg hok
  | fractional =>
    rw [hnt] at hok
    by_cases hm : lb.coverAvailable.mantissa_ = 0
    · exact absurd (roundedCoverAvailable_zero_iou lb s hm hok) hnz
    · exact STAmount.ofNumber_iou_to_nearest_within_half _ s lb.wf.coverAvailable_norm hm hok hnz

/-- **Proof body of `roundedCoverAvailable_exact`.** -/
lemma LoanBroker.roundedCoverAvailable_exact_proof (lb : LoanBroker) (s : STAmount)
    (hok : lb.roundedCoverAvailable = .ok s)
    (hrep : ∃ a : STAmount, a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧
      a.toRat = lb.toExact.coverAvailable) :
    s.toRat = lb.toExact.coverAvailable := by
  unfold LoanBroker.roundedCoverAvailable at hok
  obtain ⟨a, hac, hat, hav⟩ := hrep
  rw [← hav]
  exact STAmount.ofNumber_to_nearest_eq_of_canonical _ _ s a lb.wf.coverAvailable_norm
    lb.exact.coverAvailable_nonneg hac hat hav.symm hok

end XRPL.Model.Lending
