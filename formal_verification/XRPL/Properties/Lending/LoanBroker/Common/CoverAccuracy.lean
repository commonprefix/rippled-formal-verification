import XRPL.Properties.Lending.LoanBroker.Common.CoverReduction
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero

/-! # Proof bodies for the `roundedCoverAmount` theorems

Also the facts about the amount a deposit credits. The cover scale is the exponent
of `coverAvailable` written as an `STAmount`: `0` for XRP and MPT, `-100` for an
empty IOU cover, otherwise in `[-96, 80]`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- A `.rounded` result is the amount rounded down to the cover scale, and it is
nonzero. -/
lemma LoanBroker.roundedCoverAmount_rounded_inv (lb : LoanBroker) (amount r : STAmount)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) :
    roundToCoverScale lb.numericType lb.coverAvailable amount .downward = .ok r ∧
      r.signum ≠ 0 := by
  unfold LoanBroker.roundedCoverAmount at hok
  dsimp only at hok
  cases h : roundToCoverScale lb.numericType lb.coverAvailable amount .downward with
  | error e => rw [h, err_bind] at hok; exact absurd hok (by simp)
  | ok r' =>
    rw [h, ok_bind] at hok
    by_cases hs : (r'.signum == 0) = true
    · simp [hs] at hok
    · have hr : r' = r := by simpa [hs] using hok
      subst hr
      exact ⟨rfl, by simpa using hs⟩

/-- A deposit credits a nonzero amount. -/
lemma LoanBroker.coverDeposit_amount_nonzero (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res)) :
    res.amount'.mValue ≠ 0 := by
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  have hsg := (LoanBroker.roundedCoverAmount_rounded_inv lb amount r hrr).2
  rw [LoanBroker.applyCoverTransaction_amount' lb _ r res happ]
  intro h0
  apply hsg
  unfold STAmount.signum
  rw [show (r.mValue == 0) = true from beq_iff_eq.mpr h0, if_pos rfl]

/-- **Proof body of `roundedCoverAmount_integral`.** -/
lemma LoanBroker.roundedCoverAmount_integral_proof (lb : LoanBroker) (amount r : STAmount)
    (hint : amount.integral = true)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) : r = amount := by
  obtain ⟨hround, _⟩ := LoanBroker.roundedCoverAmount_rounded_inv lb amount r hok
  unfold roundToCoverScale at hround
  cases he : numberExponent lb.coverAvailable lb.numericType with
  | error err => rw [he, err_bind] at hround; exact absurd hround (by simp)
  | ok e =>
    rw [he, ok_bind] at hround
    exact STAmount.roundToExponent_ok_eq_self amount r e .downward (Or.inl hint) hround

/-- A `.rounded` result is the amount itself, or the amount truncated onto the
`10 ^ e` grid of the cover scale. -/
private lemma LoanBroker.roundedCoverAmount_grid (lb : LoanBroker) (amount r : STAmount) (e : Int)
    (hcanon : amount.integral = false → amount.IOUCanonical)
    (hexp : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) :
    r = amount ∨ r.toRat = (⌊amount.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e := by
  by_cases hint : amount.integral = true
  · exact Or.inl (LoanBroker.roundedCoverAmount_integral_proof lb amount r hint hok)
  have hfr : amount.integral = false := by simpa using hint
  have hc := hcanon hfr
  obtain ⟨hround, hnz⟩ := LoanBroker.roundedCoverAmount_rounded_inv lb amount r hok
  rw [roundToCoverScale_eq _ _ _ _ e hexp] at hround
  -- an amount already on a grid at least as fine as the cover scale passes unchanged
  by_cases hge : amount.exponent ≥ e
  · exact Or.inl (STAmount.roundToExponent_ok_eq_self amount r e .downward (Or.inr (Or.inr hge))
      hround)
  -- otherwise the amount is truncated onto the `10 ^ e` grid
  right
  have hlt : amount.exponent < e := not_le.mp hge
  have hrange : (-96 : ℤ) ≤ e ∧ e ≤ 80 := by
    rcases numberExponent_range _ _ e hexp with h100 | hr
    · have := hc.exp_lo
      have hem : amount.exponent = amount.mOffset := rfl
      omega
    · exact hr
  have hmv : r.mValue ≠ 0 := by
    intro h0
    apply hnz
    simp [STAmount.signum, h0]
  exact STAmount.roundToExponent_rounded amount r e .downward hc hrange.1 hrange.2 hmv hround

/-- **Proof body of `roundedCoverAmount_bounds`.** -/
lemma LoanBroker.roundedCoverAmount_bounds_proof (lb : LoanBroker) (amount r : STAmount) (e : Int)
    (hcanon : amount.integral = false → amount.IOUCanonical)
    (hexp : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) :
    r.toRat ≤ amount.toRat ∧ amount.toRat - r.toRat < 10 ^ e := by
  have hpow : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  rcases LoanBroker.roundedCoverAmount_grid lb amount r e hcanon hexp hok with h | hgrid
  · subst h; exact ⟨le_refl _, by rw [sub_self]; exact hpow⟩
  have hfl := Int.floor_le (amount.toRat / 10 ^ e)
  have hlt1 := Int.lt_floor_add_one (amount.toRat / 10 ^ e)
  have hdiv : amount.toRat / 10 ^ e * 10 ^ e = amount.toRat := by field_simp
  constructor
  · rw [hgrid]
    calc (⌊amount.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e ≤ amount.toRat / 10 ^ e * 10 ^ e :=
          mul_le_mul_of_nonneg_right hfl hpow.le
      _ = amount.toRat := hdiv
  · rw [hgrid]
    have : amount.toRat / 10 ^ e * 10 ^ e < ((⌊amount.toRat / 10 ^ e⌋ : ℚ) + 1) * 10 ^ e :=
      mul_lt_mul_of_pos_right hlt1 hpow
    rw [hdiv] at this
    linarith

/-- The cover scale is known once the amount has been rounded. -/
lemma LoanBroker.roundedCoverAmount_exponent (lb : LoanBroker) (amount r : STAmount)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) :
    ∃ e, numberExponent lb.coverAvailable lb.numericType = .ok e := by
  obtain ⟨hround, _⟩ := LoanBroker.roundedCoverAmount_rounded_inv lb amount r hok
  unfold roundToCoverScale at hround
  cases he : numberExponent lb.coverAvailable lb.numericType with
  | error err => rw [he, err_bind] at hround; exact absurd hround (by simp)
  | ok e => exact ⟨e, rfl⟩

/-- A nonnegative amount rounds to a nonnegative amount. -/
lemma LoanBroker.roundedCoverAmount_nonneg (lb : LoanBroker) (amount r : STAmount)
    (hcanon : amount.integral = false → amount.IOUCanonical) (hnn : 0 ≤ amount.toRat)
    (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) : 0 ≤ r.toRat := by
  obtain ⟨e, hexp⟩ := LoanBroker.roundedCoverAmount_exponent lb amount r hok
  rcases LoanBroker.roundedCoverAmount_grid lb amount r e hcanon hexp hok with h | hgrid
  · rw [h]; exact hnn
  · rw [hgrid]
    have hpow : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    have hfl : (0 : ℤ) ≤ ⌊amount.toRat / 10 ^ e⌋ := Int.floor_nonneg.mpr (div_nonneg hnn hpow.le)
    exact mul_nonneg (by exact_mod_cast hfl) hpow.le

/-- A canonical amount rounds to a canonical amount of the same type. -/
lemma LoanBroker.roundedCoverAmount_exactCanonical (lb : LoanBroker) (amount r : STAmount)
    (hc : amount.ExactCanonical) (hok : lb.roundedCoverAmount amount = .ok (.rounded r)) :
    r.ExactCanonical ∧ r.mNumericType = amount.mNumericType := by
  by_cases hint : amount.integral = true
  · rw [LoanBroker.roundedCoverAmount_integral_proof lb amount r hint hok]
    exact ⟨hc, rfl⟩
  have hiou := hc.iouCanonical (by simpa using hint)
  obtain ⟨hround, hnz⟩ := LoanBroker.roundedCoverAmount_rounded_inv lb amount r hok
  obtain ⟨e, hexp⟩ := LoanBroker.roundedCoverAmount_exponent lb amount r hok
  rw [roundToCoverScale_eq _ _ _ _ e hexp] at hround
  obtain ⟨hnt, hr⟩ := STAmount.roundToExponent_fczr amount r e .downward
    ⟨hiou.is_fractional, Or.inl hiou⟩ hround
  refine ⟨?_, by rw [hnt, hiou.is_fractional]⟩
  rcases hr with hr | h0
  · exact Or.inl hr
  · exact absurd (by simp [STAmount.signum, h0]) hnz

/-- A deposit of an XRP or MPT amount credits the amount itself. -/
lemma LoanBroker.coverDeposit_amount_integral (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hint : amount.integral = true) : res.amount' = amount := by
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  rw [LoanBroker.applyCoverTransaction_amount' lb _ r res happ]
  exact LoanBroker.roundedCoverAmount_integral_proof lb amount r hint hrr

/-- A deposit at a known cover scale takes the amount rounded down to that
scale. -/
lemma LoanBroker.coverDeposit_amount_of_exp (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int)
    (hexp : numberExponent lb.coverAvailable lb.numericType = .ok e)
    (hok : lb.coverDeposit amount = .ok (.ok res)) :
    amount.roundToExponent e .downward = .ok res.amount' := by
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  rw [LoanBroker.applyCoverTransaction_amount' lb _ r res happ]
  rw [← roundToCoverScale_eq _ _ _ _ e hexp]
  exact (LoanBroker.roundedCoverAmount_rounded_inv lb amount r hrr).1

/-- A deposit of a canonical amount credits a canonical amount of the same type. -/
lemma LoanBroker.coverDeposit_amount_exactCanonical (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) :
    res.amount'.ExactCanonical ∧ res.amount'.mNumericType = amount.mNumericType := by
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  rw [LoanBroker.applyCoverTransaction_amount' lb _ r res happ]
  exact LoanBroker.roundedCoverAmount_exactCanonical lb amount r hc hrr

/-- A deposit of a canonical nonnegative amount credits a nonnegative amount no
larger than the request. -/
lemma LoanBroker.coverDeposit_amount_bounds (lb : LoanBroker) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : lb.coverDeposit amount = .ok (.ok res))
    (hc : amount.ExactCanonical) (hnn : 0 ≤ amount.toRat) :
    0 ≤ res.amount'.toRat ∧ res.amount'.toRat ≤ amount.toRat := by
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
  rw [LoanBroker.applyCoverTransaction_amount' lb _ r res happ]
  obtain ⟨e, hexp⟩ := LoanBroker.roundedCoverAmount_exponent lb amount r hrr
  exact ⟨LoanBroker.roundedCoverAmount_nonneg lb amount r hc.iouCanonical hnn hrr,
    (LoanBroker.roundedCoverAmount_bounds_proof lb amount r e hc.iouCanonical hexp hrr).1⟩

end XRPL.Model.Lending
