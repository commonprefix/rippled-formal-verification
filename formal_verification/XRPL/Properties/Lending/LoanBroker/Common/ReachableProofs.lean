import XRPL.Properties.Lending.LoanBroker.Common.ReachableDefs
import XRPL.Properties.Lending.LoanBroker.Common.Create
import XRPL.Properties.Lending.LoanBroker.Common.DeleteAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.DepositAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy

/-! # Reachability induction proofs

Proof bodies for the `LoanBroker.ReachableFrom` corollaries in `Reachable.lean`,
`LoanBrokerDelete.lean` and `LoanBrokerCover.lean`. Each is an induction on a
history from `ReachableDefs.lean`, with one case per operation. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- `update` only changes `debtMaximum`: it keeps the fixed fields and
`coverAvailable`. -/
private lemma LoanBroker.update_fixed_fields (lb lb' : LoanBroker) (dm : Option Number)
    (hok : lb.update dm = .ok lb') :
    LoanBroker.SameFixedFields lb lb' ∧ lb'.coverAvailable = lb.coverAvailable := by
  rw [LoanBroker.update_eq] at hok
  have h := (RawLoanBroker.to_lawful_ok hok).1
  have e1 := congrArg RawLoanBroker.numericType h
  have e2 := congrArg RawLoanBroker.debtTotal h
  have e3 := congrArg RawLoanBroker.loanCount h
  have e4 := congrArg RawLoanBroker.managementFeeRate h
  have e5 := congrArg RawLoanBroker.coverRateMinimum h
  have e6 := congrArg RawLoanBroker.coverRateLiquidation h
  have e7 := congrArg RawLoanBroker.coverAvailable h
  exact ⟨⟨e1, e2, e3, e4, e5, e6⟩, e7⟩

/-- No operation changes the numeric type, `debtTotal`, `loanCount` or the rates:
a broker reachable from `start` keeps all of them. -/
private lemma LoanBroker.ReachableFrom.fixed_fields (start lb : LoanBroker)
    (hr : LoanBroker.ReachableFrom start lb) : LoanBroker.SameFixedFields start lb := by
  induction hr with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | update lb lb' dm _ hok ih =>
    exact ih.trans (LoanBroker.update_fixed_fields lb lb' dm hok).1
  | coverDeposit lb amount res _ hok ih =>
    exact ih.trans (LoanBroker.coverDeposit_fixed_fields lb amount res hok)
  | coverWithdraw lb amount res _ hok ih =>
    exact ih.trans (LoanBroker.coverWithdraw_fixed_fields lb amount res hok)
  | coverClawback lb α pool amount res _ hok ih =>
    exact ih.trans (LoanBroker.coverClawback_fixed_fields lb pool amount res hok)

/-- **Proof body of `Reachable.debtTotal_zero`.** -/
lemma LoanBroker.Reachable.debtTotal_zero_proof (lb : LoanBroker) (hr : lb.Reachable) :
    lb.debtTotal = Number.zero := by
  obtain ⟨tx, nt, start, hc, hrf⟩ := hr
  rw [(LoanBroker.ReachableFrom.fixed_fields start lb hrf).debtTotal]
  exact (LoanBroker.create_no_exposure_proof tx nt start hc).1

/-- **Proof body of `Reachable.loanCount_zero`.** -/
lemma LoanBroker.Reachable.loanCount_zero_proof (lb : LoanBroker) (hr : lb.Reachable) :
    lb.loanCount = 0 := by
  obtain ⟨tx, nt, start, hc, hrf⟩ := hr
  rw [(LoanBroker.ReachableFrom.fixed_fields start lb hrf).loanCount]
  exact (LoanBroker.create_no_exposure_proof tx nt start hc).2.2

/-- **Proof body of `ReachableFrom.creation_rates`.** -/
lemma LoanBroker.ReachableFrom.creation_rates_proof (tx : LoanBrokerSetCreate) (nt : NumericType)
    (start lb : LoanBroker) (hc : LoanBroker.create tx nt = .ok start)
    (hr : LoanBroker.ReachableFrom start lb) :
    lb.managementFeeRate = tx.managementFeeRate.getD 0 ∧
      lb.coverRateMinimum = tx.coverRateMinimum.getD 0 ∧
      lb.coverRateLiquidation = tx.coverRateLiquidation.getD 0 := by
  have hf := LoanBroker.ReachableFrom.fixed_fields start lb hr
  unfold LoanBroker.create at hc
  have h := (RawLoanBroker.to_lawful_ok hc).1
  refine ⟨?_, ?_, ?_⟩
  · rw [hf.managementFeeRate]; show start.toRawLoanBroker.managementFeeRate = _; rw [h]; rfl
  · rw [hf.coverRateMinimum]; show start.toRawLoanBroker.coverRateMinimum = _; rw [h]; rfl
  · rw [hf.coverRateLiquidation]; show start.toRawLoanBroker.coverRateLiquidation = _; rw [h]; rfl

/-- Every step of a whole-cover history is an ordinary LoanBroker operation. -/
private lemma LoanBroker.WholeCoverFrom.reachableFrom (start lb : LoanBroker)
    (hr : LoanBroker.WholeCoverFrom start lb) : LoanBroker.ReachableFrom start lb := by
  induction hr with
  | refl => exact .refl
  | update lb lb' dm _ hok ih => exact .update lb lb' dm ih hok
  | coverDeposit lb amount res _ hok _ _ _ _ ih => exact .coverDeposit lb amount res ih hok
  | coverWithdraw lb amount res _ hok _ _ _ ih => exact .coverWithdraw lb amount res ih hok
  | coverClawback lb α pool amount res _ hok _ _ _ ih =>
    exact .coverClawback lb α pool amount res ih hok

/-- A whole-number `coverAvailable` below `2^63` stays whole after a debit of a
canonical whole amount. -/
private lemma whole_after_debit (lb : LoanBroker) (a : STAmount) (res : LoanBrokerCoverResult)
    (happ : lb.applyCoverTransaction .debit a = .ok res) (hic : a.IntegralCanonical)
    (hsz : a.mValue.toNat ≤ 2 ^ 63 - 1) (ha0 : 0 ≤ a.toRat)
    (hw : lb.toExact.coverAvailable.den = 1 ∧ lb.toExact.coverAvailable < 2 ^ 63) :
    res.loanBroker'.toExact.coverAvailable.den = 1 ∧
      res.loanBroker'.toExact.coverAvailable < 2 ^ 63 := by
  obtain ⟨hv, _⟩ :=
    LoanBroker.applyCoverTransaction_debit_integral lb a res happ hic hsz ha0 hw.1 hw.2
  have hden := Rat.den_one_sub _ _ hw.1 (STAmount.IntegralCanonical.den_eq_one a hic)
  rw [hv, hden]
  exact ⟨rfl, by linarith [hw.2]⟩

/-- `coverAvailable` stays a whole number below `2^63` while every cover amount
is a nonnegative canonical XRP or MPT amount and every deposit keeps the sum
below `2^63`. -/
lemma LoanBroker.WholeCoverFrom.whole (start lb : LoanBroker)
    (hstart : start.toExact.coverAvailable.den = 1 ∧ start.toExact.coverAvailable < 2 ^ 63)
    (hr : LoanBroker.WholeCoverFrom start lb) :
    lb.toExact.coverAvailable.den = 1 ∧ lb.toExact.coverAvailable < 2 ^ 63 := by
  induction hr with
  | refl => exact hstart
  | update lb lb' dm _ hok ih =>
    have hc := (LoanBroker.update_fixed_fields lb lb' dm hok).2
    show lb'.coverAvailable.toRat.den = 1 ∧ lb'.coverAvailable.toRat < 2 ^ 63
    rw [hc]; exact ih
  | coverDeposit lb amount res _ hok hic hsz _ hlt ih =>
    have hup := LoanBroker.coverDeposit_credit_integral_proof lb amount res hok hic hsz ih.1 hlt
    have hv : res.loanBroker'.toExact.coverAvailable =
        lb.toExact.coverAvailable + amount.toRat := by linarith
    rw [hv]
    exact ⟨Rat.den_one_add _ _ ih.1 (STAmount.IntegralCanonical.den_eq_one amount hic), hlt⟩
  | coverWithdraw lb amount res _ hok hic hsz ha0 ih =>
    exact whole_after_debit lb amount res (LoanBroker.coverWithdraw_ok_inv lb amount res hok) hic
      hsz ha0 ih
  | coverClawback lb α pool amount res _ hok hic hsz ha0 ih =>
    obtain ⟨claw, _, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
    have hamt : res.amount' = claw :=
      LoanBroker.applyCoverTransaction_amount' lb _ claw res happ
    rw [hamt] at hic hsz ha0
    exact whole_after_debit lb claw res happ hic hsz ha0 ih

/-- **Proof body of `WholeCoverFrom.roundedCoverAvailable_exact`.** -/
lemma LoanBroker.WholeCoverFrom.roundedCoverAvailable_exact_proof (start lb : LoanBroker)
    (s : STAmount) (hint : start.numericType.isIntegral = true)
    (hstart : start.toExact.coverAvailable.den = 1 ∧ start.toExact.coverAvailable < 2 ^ 63)
    (hr : LoanBroker.WholeCoverFrom start lb) (hok : lb.roundedCoverAvailable = .ok s) :
    s.toRat = lb.toExact.coverAvailable := by
  have hw := LoanBroker.WholeCoverFrom.whole start lb hstart hr
  have hnt : lb.numericType = start.numericType :=
    (LoanBroker.ReachableFrom.fixed_fields start lb
      (LoanBroker.WholeCoverFrom.reachableFrom start lb hr)).numericType
  unfold LoanBroker.roundedCoverAvailable at hok
  exact STAmount.ofNumber_integral_exact _ _ _ s (by rw [hnt]; exact hint)
    lb.wf.coverAvailable_norm hw.1 hok

/-- **Proof body of `ReachableFromIn.cover_eq`.** -/
lemma LoanBroker.ReachableFromIn.cover_eq_proof (start : LoanBroker) (unit : ℚ)
    (lb : LoanBroker) (n : ℕ) (applied requested : ℚ)
    (hr : LoanBroker.ReachableFromIn start unit lb n applied requested) :
    lb.toExact.coverAvailable = start.toExact.coverAvailable + applied := by
  induction hr with
  | refl => rw [add_zero]
  | update lb lb' n a q dm _ hok ih =>
    have hc := (LoanBroker.update_fixed_fields lb lb' dm hok).2
    show lb'.coverAvailable.toRat = _
    rw [hc]; exact ih
  | coverDeposit lb n a q amount res _ hok hc hexact _ ih =>
    have h := LoanBroker.coverDeposit_credit_proof lb amount res hok hc hexact
    linarith
  | coverWithdraw lb n a q amount res _ hok hc hexact ih =>
    have h := LoanBroker.coverWithdraw_debit_proof lb amount res hok hc hexact
    linarith
  | coverClawback lb n a q α pool amount res e m _ hok hac ha0 hnz he hm hfit hcan hexact _ ih =>
    have hcnz := LoanBroker.coverClawback_amount_nonzero lb pool _ res hcan hok
    obtain ⟨mag, hmn, hmv, hcl⟩ :=
      LoanBroker.coverClawback_request lb pool amount res e m hok hac hnz he hm hfit
    have hc := STAmount.ofNumber_exactCanonical _ mag .to_nearest _ hmn
      (by rw [hmv]; exact ha0) hcl hcnz
    have h := LoanBroker.coverClawback_debit_of_canonical lb pool (some amount) res hok hc hexact
    linarith

/-- The net amount the operations moved is within `n` rounding units of the net
amount they were asked to move. -/
private lemma LoanBroker.ReachableFromIn.applied_near (start : LoanBroker) (unit : ℚ)
    (lb : LoanBroker) (n : ℕ) (applied requested : ℚ) (hu0 : 0 ≤ unit)
    (hr : LoanBroker.ReachableFromIn start unit lb n applied requested) :
    |applied - requested| ≤ n * unit := by
  induction hr with
  | refl => simp
  | update lb lb' n a q dm _ _ ih => exact ih
  | coverDeposit lb n a q amount res _ hok hc _ hunit ih =>
    obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb amount res hok
    obtain ⟨_, _, _, _, hamt, _⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
    obtain ⟨e, he⟩ := LoanBroker.roundedCoverAmount_exponent lb amount r hrr
    obtain ⟨hle, hlt⟩ :=
      LoanBroker.roundedCoverAmount_bounds_proof lb amount r e hc.iouCanonical he hrr
    have hu := hunit e he
    have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    have hstep : |r.toRat - amount.toRat| ≤ unit := by rw [abs_le]; constructor <;> linarith
    have hsplit : a + r.toRat - (q + amount.toRat) = (a - q) + (r.toRat - amount.toRat) := by
      ring
    rw [hamt, hsplit]; push_cast; rw [add_mul, one_mul]
    linarith [abs_add_le (a - q) (r.toRat - amount.toRat)]
  | coverWithdraw lb n a q amount res _ _ _ _ ih =>
    rw [show a - amount.toRat - (q - amount.toRat) = a - q by ring]
    push_cast; rw [add_mul, one_mul]
    linarith
  | coverClawback lb n a q α pool amount res e m _ hok hac ha0 hnz he hm hfit hcan _ hunit ih =>
    have hcnz := LoanBroker.coverClawback_amount_nonzero lb pool _ res hcan hok
    obtain ⟨mag, hmn, hmv, hcl⟩ :=
      LoanBroker.coverClawback_request lb pool amount res e m hok hac hnz he hm hfit
    have hhalf := STAmount.ofNumber_to_nearest_within_half _ mag res.amount' hmn
      (by rw [hmv]; exact ha0) hcl hcnz
    rw [hmv, abs_sub_comm] at hhalf
    have hsplit : a - res.amount'.toRat - (q - amount.toRat) =
        (a - q) + (amount.toRat - res.amount'.toRat) := by ring
    rw [hsplit]; push_cast; rw [add_mul, one_mul]
    linarith [abs_add_le (a - q) (amount.toRat - res.amount'.toRat)]

/-- **Proof body of `ReachableFromIn.cover_within`.** -/
lemma LoanBroker.ReachableFromIn.cover_within_proof (start : LoanBroker) (unit : ℚ)
    (lb : LoanBroker) (n : ℕ) (applied requested : ℚ) (hu0 : 0 ≤ unit)
    (hr : LoanBroker.ReachableFromIn start unit lb n applied requested) :
    |lb.toExact.coverAvailable - (start.toExact.coverAvailable + requested)| ≤ n * unit := by
  rw [LoanBroker.ReachableFromIn.cover_eq_proof start unit lb n applied requested hr,
    show start.toExact.coverAvailable + applied - (start.toExact.coverAvailable + requested) =
      applied - requested by ring]
  exact LoanBroker.ReachableFromIn.applied_near start unit lb n applied requested hu0 hr

end XRPL.Model.Lending
