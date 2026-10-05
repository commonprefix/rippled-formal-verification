import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber

/-! # Witnesses for the `LoanBroker.coverClawback` theorems

Concrete brokers, each run through the model against `wvPool` and checked by
`native_decide`.

* Clawback below the minimum: a `debtTotal` of `5` at a 10% minimum gives a
  minimum cover of `0.5`. `coverAvailable` `10^16` minus `0.5` rounds to nearest
  at 16 digits to `10^16`. The clawback takes all of it and leaves
  `coverAvailable` at zero.
* Clawback above `coverAvailable`: a 17-digit `coverAvailable`
  `19999999999999998` rounds up to `2 * 10^16` when converted to the asset. Clawing
  all of it leaves a negative `coverAvailable`.
* Inexact debit: clawing `1234.567890123456` from `10^18` lowers the cover by
  `1235`.
* Off the asset grid: clawing `7.5` from `10^16` leaves a 17-digit cover.
* Two clawbacks: from `coverAvailable` `10^6`, clawing `5.1 * 10^-10` and then
  `4.9 * 10^-10` passes both checks, while `4.9 * 10^-10` first is rejected.
* A clawback and a deposit: clawing `7.6 * 10^-10` from `10^6` and depositing it
  back credits only `7 * 10^-10`. -/

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

/-- A full clawback passes its checks, succeeds, and leaves less than the
minimum cover. -/
def clawsBelowMinimum (lb : LoanBroker) (pool : Vault) : Bool :=
  match lb.canCoverClawback pool none, lb.coverClawback pool none,
      AssetPool.exponent pool lb.numericType with
  | .ok .tesSUCCESS, .ok (.ok res), .ok e =>
    match res.loanBroker'.hasMinimumCover e with
    | .ok false => true
    | _ => false
  | _, _, _ => false

private lemma clawsBelowMinimum_witness : clawsBelowMinimum wbBelowMinimumL wvPoolL = true := by
  native_decide

/-- A clawback that passes its checks can leave `coverAvailable` below the
minimum cover. -/
lemma LoanBroker.coverClawback_keeps_minimum_within_half_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (res : LoanBrokerCoverResult) (e : Int),
      lb.canCoverClawback pool none = .ok .tesSUCCESS ∧
      lb.coverClawback pool none = .ok (.ok res) ∧
      AssetPool.exponent pool lb.numericType = .ok e ∧
      ¬ res.loanBroker'.HasMinimumCover e := by
  have h := clawsBelowMinimum_witness
  unfold clawsBelowMinimum at h
  split at h
  · rename_i res e hcan hok hexp
    split at h
    · rename_i hmin
      refine ⟨_, _, res, e, hcan, hok, hexp, ?_⟩
      unfold LoanBroker.HasMinimumCover
      rw [hmin]
      exact fun h' => absurd h' (by simp)
    · exact absurd h (by decide)
  · exact absurd h (by decide)

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

/-- The clawback passes its checks and takes the requested nonnegative amount, and
`coverAvailable` drops by a different amount. -/
def clawsInexact (lb : LoanBroker) (pool : Vault) (amount : STAmount) : Bool :=
  match lb.canCoverClawback pool (some amount), lb.coverClawback pool (some amount) with
  | .ok .tesSUCCESS, .ok (.ok res) =>
    res.amount' == amount && decide (0 ≤ amount.toRat) &&
      decide (lb.coverAvailable.toRat - res.loanBroker'.coverAvailable.toRat ≠ amount.toRat)
  | _, _ => false

private lemma clawsInexact_witness : clawsInexact wbLargeCoverL wvPoolL waSmallAmount = true := by
  native_decide

/-- A clawback from a large cover can pass its checks and lower `coverAvailable`
by a different amount than it claws. -/
lemma LoanBroker.coverClawback_debit_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult),
      lb.canCoverClawback pool amount = .ok .tesSUCCESS ∧
      lb.coverClawback pool amount = .ok (.ok res) ∧
      (∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat) ∧
      lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≠ res.amount'.toRat := by
  have h := clawsInexact_witness
  unfold clawsInexact at h
  split at h
  · rename_i res hcan hres
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hamt, h0⟩, hne⟩ := h
    refine ⟨_, _, _, res, hcan, hres, fun a ha _ => ?_, ?_⟩
    · rw [Option.mem_def, Option.some_inj] at ha
      subst ha
      exact ⟨Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩, h0⟩
    · rw [hamt]; exact hne
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

/-- `a` then `b` passes both clawback checks, and `b` alone is rejected. -/
def clawbackOrderDependent (lb : LoanBroker) (pool : Vault) (a b : STAmount) : Bool :=
  match lb.canCoverClawback pool (some a), lb.coverClawback pool (some a),
      lb.canCoverClawback pool (some b) with
  | .ok .tesSUCCESS, .ok (.ok r1), .ok .tecPRECISION_LOSS =>
    match r1.loanBroker'.canCoverClawback pool (some b) with
    | .ok .tesSUCCESS => true
    | _ => false
  | _, _, _ => false

private lemma clawbackOrderDependent_witness :
    clawbackOrderDependent wbMillionL wvPoolL waAboveHalfUnit waBelowHalfUnit = true := by
  native_decide

/-- Two clawbacks can pass their checks in one order while the second is rejected
when it goes first. -/
lemma LoanBroker.coverClawback_order_witness :
    ∃ (lb : LoanBroker) (pool : Vault) (a b : STAmount) (r1 : LoanBrokerCoverResult),
      lb.canCoverClawback pool (some a) = .ok .tesSUCCESS ∧
      lb.coverClawback pool (some a) = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverClawback pool (some b) = .ok .tesSUCCESS ∧
      lb.canCoverClawback pool (some b) = .ok .tecPRECISION_LOSS := by
  have h := clawbackOrderDependent_witness
  unfold clawbackOrderDependent at h
  split at h
  · rename_i r1 h1 h2 h3
    split at h
    · rename_i h4
      exact ⟨_, _, _, _, r1, h1, h2, h4, h3⟩
    · exact absurd h (by decide)
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

end XRPL.Model.Lending
