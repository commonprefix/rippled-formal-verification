import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber

/-! # Witnesses for the `LoanBroker.coverDeposit` theorems

Concrete deposit runs showing where the deposit theorems' hypotheses are needed, checked
by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Lending1_1
open XRPL.Model.SingleAssetVault (Vault)

/-- An IOU broker holding `10^15` of cover, so one unit of the cover scale is `1`. -/
def wbUnitScale : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 1000000000000000000, -3⟩, loanCount := 0 }

def wbUnitScaleL : LoanBroker := ⟨wbUnitScale, by native_decide, by native_decide⟩

/-- The deposit, `1.999999999999999`, all 16 digits after the leading one below the cover scale. -/
def waUnitScale : STAmount := STAmount.unchecked .fractional 1999999999999999 (-15) false

/-- The amount is rounded, and loses at least `1 - 10^-15` of a unit of the cover scale. -/
def roundsByAlmostUnit (lb : LoanBroker) (amount : STAmount) : Bool :=
  match numberExponent lb.coverAvailable lb.numericType, lb.roundedCoverAmount amount with
  | .ok e, .ok (.rounded r) => decide ((1 - 1 / 10 ^ 15 : ℚ) * 10 ^ e ≤ amount.toRat - r.toRat)
  | _, _ => false

private lemma roundsByAlmostUnit_witness : roundsByAlmostUnit wbUnitScaleL waUnitScale = true := by
  native_decide

/-- Rounding a deposit to the cover scale can drop all but `10^-15` of a unit. -/
lemma LoanBroker.roundedCoverAmount_bounds_witness :
    ∃ (lb : LoanBroker) (amount r : STAmount) (e : Int),
      (amount.integral = false → amount.IOUCanonical) ∧
      numberExponent lb.coverAvailable lb.numericType = .ok e ∧
      lb.roundedCoverAmount amount = .ok (.rounded r) ∧
      (1 - 1 / 10 ^ 15 : ℚ) * 10 ^ e ≤ amount.toRat - r.toRat := by
  have h := roundsByAlmostUnit_witness
  unfold roundsByAlmostUnit at h
  split at h
  · rename_i e r he hr
    exact ⟨_, _, r, e, fun _ => ⟨rfl, by decide, by decide, by decide, by decide⟩, he, hr,
      of_decide_eq_true h⟩
  · exact absurd h (by decide)

/-- An IOU broker holding `6.6 * 10^12` of cover. -/
def wbOvercredit : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 6600000000000000000, -6⟩, loanCount := 0 }

def wbOvercreditL : LoanBroker := ⟨wbOvercredit, by native_decide, by native_decide⟩

/-- The deposit, `9999999999999999 * 10^15`. -/
def waOvercredit : STAmount := STAmount.unchecked .fractional 9999999999999999 15 false

/-- The deposit succeeds unrounded and credits more than it deposits. -/
def overcredits (lb : LoanBroker) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok res) =>
    res.amount' == amount &&
      decide (amount.toRat < res.loanBroker'.coverAvailable.toRat - lb.coverAvailable.toRat)
  | _ => false

private lemma overcredits_witness : overcredits wbOvercreditL waOvercredit = true := by native_decide

/-- A deposit can raise `coverAvailable` by more than the deposited amount. -/
lemma LoanBroker.coverDeposit_credit_le_amount_witness :
    ∃ (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult),
      amount.IOUCanonical ∧ lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      amount.toRat < res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable := by
  have h := overcredits_witness
  unfold overcredits at h
  split at h
  · rename_i res hres
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨_, _, res, ⟨rfl, by decide, by decide, by decide, by decide⟩, hres, h.1, h.2⟩
  · exact absurd h (by decide)

/-- The deposit succeeds, withdrawing the credited amount passes its checks, and the cover ends
above where it started. -/
def depositWithdrawGains (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok r1) =>
    match r1.loanBroker'.canCoverWithdraw pool r1.amount',
        r1.loanBroker'.coverWithdraw r1.amount' with
    | .ok .tesSUCCESS, .ok (.ok r2) =>
      decide (lb.coverAvailable.toRat < r2.loanBroker'.coverAvailable.toRat)
    | _, _ => false
  | _ => false

private lemma depositWithdrawGains_witness :
    depositWithdrawGains wbOvercreditL wvPoolL waOvercredit = true := by
  native_decide

/-- Withdrawing the amount a deposit credited can leave `coverAvailable` above where it
started. -/
lemma LoanBroker.coverDeposit_coverWithdraw_restores_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res res' : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧
      res.loanBroker'.canCoverWithdraw pool res.amount' = .ok .tesSUCCESS ∧
      res.loanBroker'.coverWithdraw res.amount' = .ok (.ok res') ∧ amount.ExactCanonical ∧
      lb.toExact.coverAvailable < res'.loanBroker'.toExact.coverAvailable := by
  have h := depositWithdrawGains_witness
  unfold depositWithdrawGains at h
  split at h
  · rename_i r1 h1
    split at h
    · rename_i r2 h2 h3
      exact ⟨_, _, _, r1, r2, h1, h2, h3, Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩,
        of_decide_eq_true h⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The deposit succeeds, clawing back the credited amount passes its checks, and the cover ends
above where it started. -/
def depositClawbackGains (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok r1) =>
    match r1.loanBroker'.canCoverClawback pool (some r1.amount'),
        r1.loanBroker'.coverClawback pool (some r1.amount') with
    | .ok .tesSUCCESS, .ok (.ok r2) =>
      decide (0 ≤ amount.toRat) &&
        decide (lb.coverAvailable.toRat < r2.loanBroker'.coverAvailable.toRat)
    | _, _ => false
  | _ => false

private lemma depositClawbackGains_witness :
    depositClawbackGains wbOvercreditL wvPoolL waOvercredit = true := by
  native_decide

/-- With no debt, clawing back the amount a deposit credited can leave `coverAvailable` above
where it started. -/
lemma LoanBroker.coverDeposit_coverClawback_restores_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res res' : LoanBrokerCoverResult),
      lb.debtTotal = Number.zero ∧ lb.coverDeposit amount = .ok (.ok res) ∧
      res.loanBroker'.canCoverClawback pool (some res.amount') = .ok .tesSUCCESS ∧
      res.loanBroker'.coverClawback pool (some res.amount') = .ok (.ok res') ∧
      amount.ExactCanonical ∧ 0 ≤ amount.toRat ∧ amount.mNumericType = lb.numericType ∧
      lb.toExact.coverAvailable < res'.loanBroker'.toExact.coverAvailable := by
  have h := depositClawbackGains_witness
  unfold depositClawbackGains at h
  split at h
  · rename_i r1 h1
    split at h
    · rename_i r2 h2 h3
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
      exact ⟨_, _, _, r1, r2, rfl, h1, h2, h3,
        Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, h.1, rfl, h.2⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- An IOU broker holding `9.999999999999999` of cover. -/
def wbDecade : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 9999999999999999000, -18⟩, loanCount := 0 }

def wbDecadeL : LoanBroker := ⟨wbDecade, by native_decide, by native_decide⟩

/-- The deposit, `10^-15`. -/
def waDecade : STAmount := STAmount.unchecked .fractional 1000000000000000 (-30) false

/-- The deposit is credited unrounded, and withdrawing it afterwards is
rejected. -/
def depositNotWithdrawable (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok res) =>
    res.amount' == amount &&
      match res.loanBroker'.canCoverWithdraw pool amount with
      | .ok .tecPRECISION_LOSS => true
      | _ => false
  | _ => false

private lemma depositNotWithdrawable_witness :
    depositNotWithdrawable wbDecadeL wvPoolL waDecade = true := by native_decide

/-- An amount a deposit credits can be rejected as a withdrawal right after,
once `coverAvailable` has crossed a power of ten. -/
lemma LoanBroker.coverDeposit_withdrawable_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      res.loanBroker'.canCoverWithdraw pool amount = .ok .tecPRECISION_LOSS := by
  have h := depositNotWithdrawable_witness
  unfold depositNotWithdrawable at h
  split at h
  · rename_i res hres
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hamt, h2⟩ := h
    split at h2
    · rename_i hw
      exact ⟨_, _, _, res, hres, hamt, hw⟩
    · exact absurd h2 (by decide)
  · exact absurd h (by decide)

/-- The deposit is credited unrounded, and clawing it back afterwards is
rejected. -/
def depositNotClawable (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok res) =>
    res.amount' == amount &&
      match res.loanBroker'.canCoverClawback pool (some amount) with
      | .ok .tecPRECISION_LOSS => true
      | _ => false
  | _ => false

private lemma depositNotClawable_witness :
    depositNotClawable wbDecadeL wvPoolL waDecade = true := by native_decide

/-- An amount a deposit credits can be rejected as a clawback right after, once
`coverAvailable` has crossed a power of ten. -/
lemma LoanBroker.coverDeposit_clawable_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.amount' = amount ∧
      res.loanBroker'.canCoverClawback pool (some amount) = .ok .tecPRECISION_LOSS := by
  have h := depositNotClawable_witness
  unfold depositNotClawable at h
  split at h
  · rename_i res hres
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hamt, h2⟩ := h
    split at h2
    · rename_i hw
      exact ⟨_, _, _, res, hres, hamt, hw⟩
    · exact absurd h2 (by decide)
  · exact absurd h (by decide)

/-- An IOU broker holding `9999999999999999` of cover. -/
def wbFullDigits : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 9999999999999999000, -3⟩, loanCount := 0 }

def wbFullDigitsL : LoanBroker := ⟨wbFullDigits, by native_decide, by native_decide⟩

/-- The deposit, `9999999999999999`. -/
def waFullDigits : STAmount := STAmount.unchecked .fractional 9999999999999999 0 false

/-- The deposit succeeds and leaves a 17-digit `coverAvailable`. -/
def depositRounds (lb : LoanBroker) (amount : STAmount) : Bool :=
  match lb.coverDeposit amount with
  | .ok (.ok res) => STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable
  | _ => false

private lemma depositRounds_witness : depositRounds wbFullDigitsL waFullDigits = true := by
  native_decide

/-- A deposit can leave `coverAvailable` off the asset grid. -/
lemma LoanBroker.coverDeposit_associateAsset_witness :
    ∃ (lb : LoanBroker) (amount : STAmount) (res : LoanBrokerCoverResult),
      lb.coverDeposit amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded := by
  have h := depositRounds_witness
  unfold depositRounds at h
  split at h
  · rename_i res hres
    exact ⟨_, _, res, hres, Or.inr (Or.inr h)⟩
  · exact absurd h (by decide)

/-- An IOU broker holding `9.99999999999999` of cover, scale `10^-15`. -/
def wbOrder : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 9999999999999990000, -18⟩, loanCount := 0 }

def wbOrderL : LoanBroker := ⟨wbOrder, by native_decide, by native_decide⟩

/-- The first deposit, `10^-14`. It lifts the cover to `10`, scale `10^-14`. -/
def waOrderA : STAmount := STAmount.unchecked .fractional 1000000000000000 (-29) false

/-- The second deposit, `1.3 * 10^-14`. At scale `10^-14` it rounds down to `10^-14`. -/
def waOrderB : STAmount := STAmount.unchecked .fractional 1300000000000000 (-29) false

/-- Both orders of the two deposits succeed, and they end at a different cover. -/
def depositOrderDependent (lb : LoanBroker) (a b : STAmount) : Bool :=
  match lb.coverDeposit a, lb.coverDeposit b with
  | .ok (.ok r1), .ok (.ok s1) =>
    match r1.loanBroker'.coverDeposit b, s1.loanBroker'.coverDeposit a with
    | .ok (.ok r2), .ok (.ok s2) =>
      decide (r2.loanBroker'.coverAvailable.toRat ≠ s2.loanBroker'.coverAvailable.toRat)
    | _, _ => false
  | _, _ => false

private lemma depositOrderDependent_witness : depositOrderDependent wbOrderL waOrderA waOrderB = true := by
  native_decide

/-- An IOU broker holding `5 * 10^15` of cover, so one unit of the cover scale is `1`. -/
def wbSplit : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 5000000000000000000, -3⟩, loanCount := 0 }

def wbSplitL : LoanBroker := ⟨wbSplit, by native_decide, by native_decide⟩

/-- The first part, `6 * 10^15`. It lifts the cover to `1.1 * 10^16`, where one unit is `10`. -/
def waSplitDepositA : STAmount := STAmount.unchecked .fractional 6000000000000000 0 false

/-- The second part, `1000000000000001`. At the coarser scale it rounds down to `10^15`. -/
def waSplitDepositB : STAmount := STAmount.unchecked .fractional 1000000000000001 0 false

/-- Both parts at once, `7000000000000001`. -/
def waSplitDepositC : STAmount := STAmount.unchecked .fractional 7000000000000001 0 false

/-- All three deposits succeed, the sum of the parts is the whole, the first part and the whole are
added exactly, and the two parts end at a different cover and take a different total than the
whole at once. -/
def depositSplitDiffers (lb : LoanBroker) (a b c : STAmount) : Bool :=
  match lb.coverDeposit a, lb.coverDeposit c with
  | .ok (.ok r1), .ok (.ok s) =>
    match r1.loanBroker'.coverDeposit b with
    | .ok (.ok r2) =>
      decide (c.toRat = a.toRat + b.toRat) &&
        decide (r1.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat + a.toRat) &&
        decide (s.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat + c.toRat) &&
        decide (r2.loanBroker'.coverAvailable.toRat ≠ s.loanBroker'.coverAvailable.toRat) &&
        decide (r1.amount'.toRat + r2.amount'.toRat ≠ s.amount'.toRat)
    | _ => false
  | _, _ => false

private lemma depositSplitDiffers_witness :
    depositSplitDiffers wbSplitL waSplitDepositA waSplitDepositB waSplitDepositC = true := by
  native_decide

/-- Two deposits can end at a different `coverAvailable`, and take a different total, than one
deposit of their sum. -/
lemma LoanBroker.coverDeposit_split_witness :
    ∃ (lb : LoanBroker) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult) (e : Int),
      lb.coverDeposit a = .ok (.ok r1) ∧ r1.loanBroker'.coverDeposit b = .ok (.ok r2) ∧
      lb.coverDeposit c = .ok (.ok s) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧ c.ExactCanonical ∧ c.toRat = a.toRat + b.toRat ∧
      numberExponent lb.coverAvailable lb.numericType = .ok e ∧
      e ≤ a.exponent ∧ e ≤ b.exponent ∧ e ≤ c.exponent ∧
      (∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + a.toRat) ∧
      (∃ w : Number, w.isNormalized ∧ w.toRat = lb.toExact.coverAvailable + c.toRat) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable ∧
      r1.amount'.toRat + r2.amount'.toRat ≠ s.amount'.toRat := by
  have h := depositSplitDiffers_witness
  unfold depositSplitDiffers at h
  split at h
  · rename_i r1 s h1 h3
    split at h
    · rename_i r2 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hsum, hx1⟩, hx2⟩, hne⟩, htot⟩ := h
      exact ⟨_, _, _, _, r1, r2, s, 0, h1, h2, h3,
        Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩,
        Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩,
        Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, hsum, by native_decide,
        by decide, by decide, by decide,
        ⟨r1.loanBroker'.coverAvailable, r1.loanBroker'.wf.coverAvailable_norm, hx1⟩,
        ⟨s.loanBroker'.coverAvailable, s.loanBroker'.wf.coverAvailable_norm, hx2⟩, hne, htot⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Two deposits in the two orders can end at a different cover. -/
lemma LoanBroker.coverDeposit_comm_witness :
    ∃ (lb : LoanBroker) (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult),
      lb.coverDeposit a = .ok (.ok r1) ∧ r1.loanBroker'.coverDeposit b = .ok (.ok r2) ∧
      lb.coverDeposit b = .ok (.ok s1) ∧ s1.loanBroker'.coverDeposit a = .ok (.ok s2) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s2.loanBroker'.toExact.coverAvailable := by
  have h := depositOrderDependent_witness
  unfold depositOrderDependent at h
  split at h
  · rename_i r1 s1 h1 h3
    split at h
    · rename_i r2 s2 h2 h4
      simp only [decide_eq_true_eq] at h
      exact ⟨_, _, _, r1, r2, s1, s2, h1, h2, h3, h4, h⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
