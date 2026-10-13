import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber

/-! # Witnesses for the `LoanBroker.coverClawback` theorems

Concrete clawback runs showing where the clawback theorems' hypotheses are needed, checked
by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Lending1_1
open XRPL.Model.SingleAssetVault (Vault)

/-- A broker with a `debtTotal` of `5` at a 10% minimum and `10^16` of cover. -/
def wbBelowMinimum : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 10000
  , coverRateLiquidation := 10000, debtTotal := ⟨false, 5000000000000000000, -18⟩
  , debtMaximum := Number.zero, coverAvailable := ⟨false, 1000000000000000000, -2⟩
  , loanCount := 1 }

def wbBelowMinimumL : LoanBroker := ⟨wbBelowMinimum, by native_decide, by native_decide⟩

/-- A full clawback passes its checks and leaves less than the minimum cover. -/
def clawsBelowMinimum (lb : LoanBroker) (pool : Vault) : Bool :=
  match lb.canCoverClawback pool none, lb.coverClawback pool none,
      AssetPool.exponent pool lb.numericType with
  | .ok .tesSUCCESS, .ok (.ok res), .ok e =>
    match minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e with
    | .ok m => decide (res.loanBroker'.coverAvailable.toRat < m.toRat)
    | _ => false
  | _, _, _ => false

private lemma clawsBelowMinimum_witness : clawsBelowMinimum wbBelowMinimumL wvPoolL = true := by
  native_decide

/-- A clawback whose checks passed can leave `coverAvailable` below the minimum cover. -/
lemma LoanBroker.coverClawback_keeps_minimum_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (res : LoanBrokerCoverResult) (e : Int) (minimumCover : Number),
      lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      lb.coverClawback pool none = .ok (.ok res) ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      res.loanBroker'.toExact.coverAvailable < minimumCover.toRat := by
  have h := clawsBelowMinimum_witness
  unfold clawsBelowMinimum at h
  split at h
  · rename_i res e hcan hok hexp
    split at h
    · rename_i m hm
      exact ⟨_, _, res, e, m, hcan, hok, hexp, hm, of_decide_eq_true h⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- A broker with a `debtTotal` of `5` at a 10% minimum and `1234567890123458` of cover. The minimum
cover is `0.5`, so the cover above it is `1234567890123457.5`, which rounds up. -/
def wbHalfAbove : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 10000
  , coverRateLiquidation := 10000, debtTotal := ⟨false, 5000000000000000000, -18⟩
  , debtMaximum := Number.zero, coverAvailable := ⟨false, 1234567890123458000, -3⟩
  , loanCount := 1 }

def wbHalfAboveL : LoanBroker := ⟨wbHalfAbove, by native_decide, by native_decide⟩

/-- The same broker with `1234567890123457` of cover. The cover above the minimum is
`1234567890123456.5`, which rounds down. -/
def wbHalfBelow : RawLoanBroker := { wbHalfAbove with coverAvailable := ⟨false, 1234567890123457000, -3⟩ }

def wbHalfBelowL : LoanBroker := ⟨wbHalfBelow, by native_decide, by native_decide⟩

/-- The request, `2 * 10^15`, above the cover above the minimum. -/
def waAboveCap : STAmount := STAmount.unchecked .fractional 2000000000000000 0 false

/-- A clawback of `amount` returns a nonzero amount exactly half a unit from `target`, computed from
the request and the cover above the minimum. It is above `target` when `up` is set and below it
otherwise. -/
def clawsHalfUnit (lb : LoanBroker) (pool : Vault) (amount : Option STAmount)
    (target : Number → ℚ) (up : Bool) : Bool :=
  match AssetPool.exponent pool lb.numericType with
  | .ok e =>
    match minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e with
    | .ok minimumCover =>
      match lb.coverAvailable.operator_sub minimumCover .downward,
          lb.roundedCoverClawback pool amount with
      | .ok maxClaw, .ok (.rounded claw) =>
        decide (claw.mValue ≠ 0) &&
          decide ((bif up then claw.toRat - target maxClaw else target maxClaw - claw.toRat) =
            (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent)
      | _, _ => false
    | _ => false
  | _ => false

/-- The run that `clawsHalfUnit` checks. -/
private lemma clawsHalfUnit_run (lb : LoanBroker) (pool : Vault) (amount : Option STAmount)
    (target : Number → ℚ) (up : Bool) (h : clawsHalfUnit lb pool amount target up = true) :
    ∃ (e : Int) (minimumCover maxClaw : Number) (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      lb.roundedCoverClawback pool amount = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      (bif up then claw.toRat - target maxClaw else target maxClaw - claw.toRat) =
        (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent := by
  unfold clawsHalfUnit at h
  split at h
  · rename_i e hexp
    split at h
    · rename_i minimumCover hmin
      split at h
      · rename_i maxClaw claw hsub hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨e, minimumCover, maxClaw, claw, hexp, hmin, hsub, hok, h.1, h.2⟩
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

private lemma clawsAllHalfUnitUp_witness :
    clawsHalfUnit wbHalfAboveL wvPoolL none (·.toRat) true = true := by
  native_decide

private lemma clawsAllHalfUnitDown_witness :
    clawsHalfUnit wbHalfBelowL wvPoolL none (·.toRat) false = true := by
  native_decide

private lemma clawsCappedHalfUnitUp_witness :
    clawsHalfUnit wbHalfAboveL wvPoolL (some waAboveCap) (min waAboveCap.toRat ·.toRat) true =
      true := by
  native_decide

private lemma clawsCappedHalfUnitDown_witness :
    clawsHalfUnit wbHalfBelowL wvPoolL (some waAboveCap) (min waAboveCap.toRat ·.toRat) false =
      true := by
  native_decide

/-- The request `waAboveCap` is a nonzero canonical amount. -/
private lemma waAboveCap_facts :
    waAboveCap.isZero = false ∧ waAboveCap.ExactCanonical ∧ 0 ≤ waAboveCap.toRat :=
  ⟨by native_decide, Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, by native_decide⟩

/-- A full clawback can round the cover above the minimum up by half a unit in its last digit. -/
lemma LoanBroker.roundedCoverClawback_all_upper_bound_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      lb.roundedCoverClawback pool none = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      claw.toRat - maxClaw.toRat = (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent := by
  obtain ⟨e, m, x, c, h⟩ := clawsHalfUnit_run _ _ _ _ _ clawsAllHalfUnitUp_witness
  exact ⟨_, _, e, m, x, c, h⟩

/-- A full clawback can round the cover above the minimum down by half a unit in its last digit. -/
lemma LoanBroker.roundedCoverClawback_all_lower_bound_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (e : Int) (minimumCover maxClaw : Number) (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      lb.roundedCoverClawback pool none = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      maxClaw.toRat - claw.toRat = (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent := by
  obtain ⟨e, m, x, c, h⟩ := clawsHalfUnit_run _ _ _ _ _ clawsAllHalfUnitDown_witness
  exact ⟨_, _, e, m, x, c, h⟩

/-- A request above the cap can be capped and then rounded up by half a unit in its last digit. -/
lemma LoanBroker.roundedCoverClawback_capped_upper_bound_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a : STAmount) (e : Int) (minimumCover maxClaw : Number)
      (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      a.isZero = false ∧ a.ExactCanonical ∧ 0 ≤ a.toRat ∧
      lb.roundedCoverClawback pool (some a) = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      claw.toRat - min a.toRat maxClaw.toRat = (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent := by
  obtain ⟨e, m, x, c, hexp, hmin, hsub, hok, hnz, hhalf⟩ :=
    clawsHalfUnit_run _ _ _ _ _ clawsCappedHalfUnitUp_witness
  exact ⟨_, _, _, e, m, x, c, hexp, hmin, hsub, waAboveCap_facts.1, waAboveCap_facts.2.1,
    waAboveCap_facts.2.2, hok, hnz, hhalf⟩

/-- A request above the cap can be capped and then rounded down by half a unit in its last digit. -/
lemma LoanBroker.roundedCoverClawback_capped_lower_bound_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a : STAmount) (e : Int) (minimumCover maxClaw : Number)
      (claw : STAmount),
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      lb.coverAvailable.operator_sub minimumCover .downward = .ok maxClaw ∧
      a.isZero = false ∧ a.ExactCanonical ∧ 0 ≤ a.toRat ∧
      lb.roundedCoverClawback pool (some a) = .ok (.rounded claw) ∧
      claw.mValue ≠ 0 ∧
      min a.toRat maxClaw.toRat - claw.toRat = (1 / 2 : ℚ) * (10 : ℚ) ^ claw.exponent := by
  obtain ⟨e, m, x, c, hexp, hmin, hsub, hok, hnz, hhalf⟩ :=
    clawsHalfUnit_run _ _ _ _ _ clawsCappedHalfUnitDown_witness
  exact ⟨_, _, _, e, m, x, c, hexp, hmin, hsub, waAboveCap_facts.1, waAboveCap_facts.2.1,
    waAboveCap_facts.2.2, hok, hnz, hhalf⟩

/-- An IOU broker holding a 17-digit cover `19999999999999998`, with no debt. -/
def wbAboveCover : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 1999999999999999800, -2⟩, loanCount := 0 }

def wbAboveCoverL : LoanBroker := ⟨wbAboveCover, by native_decide, by native_decide⟩

/-- A full clawback passes its checks and then fails the lawfulness check. -/
def clawsAboveCover (lb : LoanBroker) (pool : Vault) : Bool :=
  match lb.canCoverClawback pool none, lb.coverClawback pool none with
  | .ok .tesSUCCESS, .error .notLawful => true
  | _, _ => false

private lemma clawsAboveCover_witness : clawsAboveCover wbAboveCoverL wvPoolL = true := by
  native_decide

/-- A clawback that passes its checks can still leave an unlawful broker. -/
lemma LoanBroker.coverClawback_lawful_total_witness :
    ∃ (lb : LoanBroker) (pool : Vault),
      lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      lb.coverClawback pool none = .error .notLawful := by
  have h := clawsAboveCover_witness
  unfold clawsAboveCover at h
  split at h
  · rename_i hcan hok
    exact ⟨_, _, hcan, hok⟩
  · exact absurd h (by decide)

/-- The clawback passes its checks, takes the whole nonzero request of the vault asset, and
`coverAvailable` drops by more than the request. -/
def clawbackOverdebits (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverClawback pool (some amount), lb.coverClawback pool (some amount) with
  | .ok .tesSUCCESS, .ok (.ok res) =>
    res.amount' == amount && !amount.isZero && decide (0 ≤ amount.toRat) &&
      decide (amount.toRat < lb.coverAvailable.toRat - res.loanBroker'.coverAvailable.toRat)
  | _, _ => false

private lemma clawbackOverdebits_witness :
    clawbackOverdebits wbLargeCoverL wvPoolL waSmallAmount = true := by
  native_decide

/-- A clawback from a large cover can pass its checks and lower `coverAvailable` by more than
the requested amount. -/
lemma LoanBroker.coverClawback_debit_le_amount_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a : STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      lb.coverClawback pool (some a) = .ok (.ok res) ∧
      a.ExactCanonical ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat ∧ a.isZero = false ∧
      res.amount' = a ∧
      a.toRat < lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable := by
  have h := clawbackOverdebits_witness
  unfold clawbackOverdebits at h
  split at h
  · rename_i res hcan hres
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨⟨hamt, hz⟩, h0⟩, hlt⟩ := h
    exact ⟨_, _, _, res, hcan, hres, Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩,
      rfl, h0, hz, hamt, hlt⟩
  · exact absurd h (by decide)

/-- The clawback passes its checks, a deposit would round the clawed amount to the cover scale,
and `coverAvailable` moves by a different on-ledger amount than it claws. -/
def clawbackAppliedDeltaDiffers (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverClawback pool (some amount), lb.coverClawback pool (some amount) with
  | .ok .tesSUCCESS, .ok (.ok res) =>
    match lb.roundedCoverAmount res.amount',
        lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest with
    | .ok (.rounded amount''), .ok deltaCover =>
      match STAmount.ofNumber lb.numericType deltaCover .to_nearest with
      | .ok deltaAmount =>
        decide (0 ≤ amount.toRat) && !amount''.operator_eq res.amount' &&
          !deltaAmount.operator_eq res.amount'
      | _ => false
    | _, _ => false
  | _, _ => false

private lemma clawbackAppliedDeltaDiffers_witness :
    clawbackAppliedDeltaDiffers wbLargeCoverL wvPoolL waSmallAmount = true := by
  native_decide

/-- A clawback takes its amount without rounding it to the cover scale, so `coverAvailable` can
move by a different on-ledger amount than it claws. -/
lemma LoanBroker.coverClawback_applied_delta_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : Option STAmount) (amount'' : STAmount)
      (res : LoanBrokerCoverResult) (deltaCover : Number) (deltaAmount : STAmount),
      lb.canCoverClawback pool amount = .ok .tesSUCCESS ∧
      lb.coverClawback pool amount = .ok (.ok res) ∧
      (∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat) ∧
      lb.roundedCoverAmount res.amount' = .ok (.rounded amount'') ∧
      amount''.operator_eq res.amount' = false ∧
      lb.coverAvailable.operator_sub res.loanBroker'.coverAvailable .to_nearest = .ok deltaCover ∧
      STAmount.ofNumber lb.numericType deltaCover .to_nearest = .ok deltaAmount ∧
      deltaAmount.operator_eq res.amount' = false := by
  have h := clawbackAppliedDeltaDiffers_witness
  unfold clawbackAppliedDeltaDiffers at h
  split at h
  · rename_i res hcan hok
    split at h
    · rename_i amount'' deltaCover hround hsub
      split at h
      · rename_i deltaAmount hda
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
        obtain ⟨⟨h0, hround'⟩, hdelta⟩ := h
        refine ⟨_, _, _, amount'', res, deltaCover, deltaAmount, hcan, hok, fun a ha _ => ?_,
          hround, hround', hsub, hda, hdelta⟩
        rw [Option.mem_def, Option.some_inj] at ha
        subst ha
        exact ⟨Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, h0⟩
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- An IOU broker holding `10^16` of cover, with no debt. -/
def wbGridCover : RawLoanBroker :=
  { numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0
  , coverRateLiquidation := 0, debtTotal := Number.zero, debtMaximum := Number.zero
  , coverAvailable := ⟨false, 1000000000000000000, -2⟩, loanCount := 0 }

def wbGridCoverL : LoanBroker := ⟨wbGridCover, by native_decide, by native_decide⟩

/-- The clawback, `7.5`. -/
def waHalfClaw : STAmount := STAmount.unchecked .fractional 7500000000000000 (-15) false

/-- The clawback succeeds and leaves a 17-digit `coverAvailable`. -/
def clawbackRounds (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.coverClawback pool (some amount) with
  | .ok (.ok res) => STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable
  | _ => false

private lemma clawbackRounds_witness : clawbackRounds wbGridCoverL wvPoolL waHalfClaw = true := by
  native_decide

/-- A clawback can leave `coverAvailable` off the asset grid. -/
lemma LoanBroker.coverClawback_associateAsset_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult),
      lb.coverClawback pool amount = .ok (.ok res) ∧ res.loanBroker'.assetsRounded := by
  have h := clawbackRounds_witness
  unfold clawbackRounds at h
  split at h
  · rename_i res hres
    exact ⟨_, _, _, res, hres, Or.inr (Or.inr h)⟩
  · exact absurd h (by decide)

/-- The clawback passes its checks, and depositing the clawed amount back does not
restore the cover. -/
def reclaimShort (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverClawback pool (some amount), lb.coverClawback pool (some amount) with
  | .ok .tesSUCCESS, .ok (.ok r1) =>
    match r1.loanBroker'.coverDeposit r1.amount' with
    | .ok (.ok r2) => decide (r2.loanBroker'.coverAvailable.toRat ≠ lb.coverAvailable.toRat)
    | _ => false
  | _, _ => false

private lemma reclaimShort_witness : reclaimShort wbMillionL wvPoolL waBelowUnit = true := by
  native_decide

/-- Depositing back the amount a clawback took can leave `coverAvailable` below
where it started. -/
lemma LoanBroker.coverClawback_coverDeposit_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : STAmount) (r1 r2 : LoanBrokerCoverResult),
      lb.canCoverClawback pool (some amount) = .ok .tesSUCCESS ∧
      lb.coverClawback pool (some amount) = .ok (.ok r1) ∧
      r1.loanBroker'.coverDeposit r1.amount' = .ok (.ok r2) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ lb.toExact.coverAvailable := by
  have h := reclaimShort_witness
  unfold reclaimShort at h
  split at h
  · rename_i r1 h1 h2
    split at h
    · rename_i r2 h3
      exact ⟨_, _, _, r1, r2, h1, h2, h3, of_decide_eq_true h⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Every clawback passes its checks with the whole request under the cap, and clawing `a` twice
ends at a different cover than clawing `c = a + a` at once. -/
def clawbackSplitDiffers (lb : LoanBroker) (pool : Vault) (a c : STAmount) : Bool :=
  match AssetPool.exponent pool lb.numericType with
  | .ok e =>
    match minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e with
    | .ok m =>
      match lb.canCoverClawback pool (some a), lb.coverClawback pool (some a) with
      | .ok .tesSUCCESS, .ok (.ok r1) =>
        match r1.loanBroker'.canCoverClawback pool (some a),
            r1.loanBroker'.coverClawback pool (some a) with
        | .ok .tesSUCCESS, .ok (.ok r2) =>
          match lb.canCoverClawback pool (some c), lb.coverClawback pool (some c) with
          | .ok .tesSUCCESS, .ok (.ok s) =>
            decide (0 ≤ a.toRat) && decide (0 ≤ c.toRat) &&
              decide (c.toRat = a.toRat + a.toRat) &&
              decide (c.toRat ≤ lb.coverAvailable.toRat - m.toRat) &&
              decide (r2.loanBroker'.coverAvailable.toRat ≠ s.loanBroker'.coverAvailable.toRat)
          | _, _ => false
        | _, _ => false
      | _, _ => false
    | .error _ => false
  | .error _ => false

private lemma clawbackSplitDiffers_witness :
    clawbackSplitDiffers wbLargeCoverL wvPoolL waSplitPart waSplitWhole = true := by
  native_decide

/-- Two clawbacks under the cap can end at a different `coverAvailable` than one clawback of their
sum. -/
lemma LoanBroker.coverClawback_split_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult)
      (e : Int) (minimumCover : Number),
      lb.coverClawback pool (some a) = .ok (.ok r1) ∧
      r1.loanBroker'.coverClawback pool (some b) = .ok (.ok r2) ∧
      lb.coverClawback pool (some c) = .ok (.ok s) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧ c.ExactCanonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧
      c.mNumericType = lb.numericType ∧
      0 ≤ a.toRat ∧ 0 ≤ b.toRat ∧ 0 ≤ c.toRat ∧
      a.isZero = false ∧ b.isZero = false ∧ c.isZero = false ∧
      c.toRat = a.toRat + b.toRat ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      c.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat ∧
      lb.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS ∧
      lb.canCoverClawback pool (some c) = .ok .tesSUCCESS ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable := by
  have h := clawbackSplitDiffers_witness
  unfold clawbackSplitDiffers at h
  split at h
  · rename_i e he
    split at h
    · rename_i m hm
      split at h
      · rename_i r1 hc1 h1
        split at h
        · rename_i r2 hc2 h2
          split at h
          · rename_i s hc3 h3
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨ha0, hc0⟩, hsum⟩, hfit⟩, hne⟩ := h
            have hpart : waSplitPart.ExactCanonical :=
              Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩
            exact ⟨_, _, _, _, _, r1, r2, s, e, m, h1, h2, h3, hpart, hpart,
              Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, rfl, rfl, rfl,
              ha0, ha0, hc0, rfl, rfl, rfl, hsum, he, hm, hfit, hc1, hc2, hc3, hne⟩
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Both orders of the two clawbacks pass every check with both requests under the cap, and they
end at different covers. -/
def clawbackOrderDiffers (lb : LoanBroker) (pool : Vault) (a b : STAmount) : Bool :=
  match AssetPool.exponent pool lb.numericType with
  | .ok e =>
    match minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e with
    | .ok m =>
      match lb.canCoverClawback pool (some a), lb.coverClawback pool (some a) with
      | .ok .tesSUCCESS, .ok (.ok r1) =>
        match r1.loanBroker'.canCoverClawback pool (some b),
            r1.loanBroker'.coverClawback pool (some b) with
        | .ok .tesSUCCESS, .ok (.ok r2) =>
          match lb.canCoverClawback pool (some b), lb.coverClawback pool (some b) with
          | .ok .tesSUCCESS, .ok (.ok s1) =>
            match s1.loanBroker'.canCoverClawback pool (some a),
                s1.loanBroker'.coverClawback pool (some a) with
            | .ok .tesSUCCESS, .ok (.ok s2) =>
              decide (0 ≤ a.toRat) && decide (0 ≤ b.toRat) &&
                decide (a.toRat + b.toRat ≤ lb.coverAvailable.toRat - m.toRat) &&
                decide (r2.loanBroker'.coverAvailable.toRat ≠ s2.loanBroker'.coverAvailable.toRat)
            | _, _ => false
          | _, _ => false
        | _, _ => false
      | _, _ => false
    | .error _ => false
  | .error _ => false

private lemma clawbackOrderDiffers_witness :
    clawbackOrderDiffers wbLargeCoverL wvPoolL waSplitPart waOrderPart = true := by
  native_decide

/-- Two clawbacks under the cap can pass every check in both orders and end at a different
`coverAvailable`. -/
lemma LoanBroker.coverClawback_comm_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a b : STAmount) (r1 r2 s1 s2 : LoanBrokerCoverResult)
      (e : Int) (minimumCover : Number),
      lb.coverClawback pool (some a) = .ok (.ok r1) ∧
      r1.loanBroker'.coverClawback pool (some b) = .ok (.ok r2) ∧
      lb.coverClawback pool (some b) = .ok (.ok s1) ∧
      s1.loanBroker'.coverClawback pool (some a) = .ok (.ok s2) ∧
      a.ExactCanonical ∧ b.ExactCanonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧
      0 ≤ a.toRat ∧ 0 ≤ b.toRat ∧ a.isZero = false ∧ b.isZero = false ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum e = .ok minimumCover ∧
      a.toRat + b.toRat ≤ lb.toExact.coverAvailable - minimumCover.toRat ∧
      lb.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS ∧
      lb.canCoverClawback pool (some b) = .ok .tesSUCCESS ∧
      s1.loanBroker'.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s2.loanBroker'.toExact.coverAvailable := by
  have h := clawbackOrderDiffers_witness
  unfold clawbackOrderDiffers at h
  split at h
  · rename_i e he
    split at h
    · rename_i m hm
      split at h
      · rename_i r1 hc1 h1
        split at h
        · rename_i r2 hc2 h2
          split at h
          · rename_i s1 hc3 h3
            split at h
            · rename_i s2 hc4 h4
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨⟨⟨ha0, hb0⟩, hfit⟩, hne⟩ := h
              exact ⟨_, _, _, _, r1, r2, s1, s2, e, m, h1, h2, h3, h4,
                Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩,
                Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, rfl, rfl, ha0, hb0, rfl,
                rfl, he, hm, hfit, hc1, hc2, hc3, hc4, hne⟩
            · exact absurd h (by decide)
          · exact absurd h (by decide)
        · exact absurd h (by decide)
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

end XRPL.Model.Lending
