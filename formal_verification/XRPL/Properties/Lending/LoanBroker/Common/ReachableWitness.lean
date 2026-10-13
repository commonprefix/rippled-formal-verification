import XRPL.Properties.Lending.LoanBroker.Common.ReachableProofs
import XRPL.Properties.Lending.LoanBroker.Common.DepositWitness

/-! # Witnesses for the `LoanBroker.ReachableFromIn` theorems

A run of any length whose deposit rounding adds up, proven step by step. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The cover `10^15 + k` as a normalized `Number`: the mantissa `(10^15 + k) * 1000` at
exponent `-3`. -/
def unitCover (k : ℕ) : Number := ⟨false, ((10 ^ 15 + k) * 1000 : ℕ).toUInt64, -3⟩

private lemma unitCover_mantissa (k : ℕ) (hk : k < 9 * 10 ^ 15) :
    (unitCover k).mantissa_.toNat = (10 ^ 15 + k) * 1000 := by
  show (((10 ^ 15 + k) * 1000 : ℕ).toUInt64).toNat = _
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]

private lemma unitCover_isNormalized (k : ℕ) (hk : k < 9 * 10 ^ 15) :
    (unitCover k).isNormalized := by
  have hm := unitCover_mantissa k hk
  refine Or.inr ⟨?_, ?_, Or.inr (by rw [hm]; omega), by simp [unitCover, minExponent],
    by simp [unitCover, maxExponent]⟩
  · rw [UInt64.le_iff_toNat_le, hm]; simp [largeRange]; omega
  · rw [UInt64.le_iff_toNat_le, hm]; simp [largeRange]; omega

private lemma unitCover_toRat (k : ℕ) (hk : k < 9 * 10 ^ 15) :
    (unitCover k).toRat = 10 ^ 15 + k := by
  rw [Number.toRat_of_nonneg _ rfl, unitCover_mantissa k hk]
  show (((10 ^ 15 + k) * 1000 : ℕ) : ℚ) * (10 : ℚ) ^ (-3 : ℤ) = _
  push_cast; ring

/-- One unit of the scale of a `10^15 + k` cover is `1`. -/
private lemma unitCover_exponent (k : ℕ) (hk : k < 9 * 10 ^ 15) :
    numberExponent (unitCover k) .fractional = .ok 0 := by
  have hm := unitCover_mantissa k hk
  unfold numberExponent
  rw [STAmount.ofNumber_fractional_of_trailing_zeros _ _ (unitCover_isNormalized k hk)
    (by intro h; rw [h] at hm; simp at hm) rfl (by rw [hm]; omega) (by simp [unitCover])
    (by simp [unitCover])]
  rfl

/-- Rounded down at exponent `0`, the amount is a nonzero `1`. -/
def roundsToOne (a : STAmount) : Bool :=
  match a.roundToExponent 0 .downward with
  | .ok r => r.signum != 0 && decide (r.toRat = 1)
  | .error _ => false

private lemma roundsToOne_witness : roundsToOne waUnitScale = true := by native_decide

/-- A deposit of `1.999999999999999` on a cover of `10^15 + k` succeeds, is credited `1`, and
leaves a cover of `10^15 + k + 1`. -/
private lemma unitCover_deposit (lb : LoanBroker) (k : ℕ) (hk : k + 1 < 9 * 10 ^ 15)
    (hnt : lb.numericType = .fractional) (hc : lb.coverAvailable = unitCover k) :
    ∃ res, lb.coverDeposit waUnitScale = .ok (.ok res) ∧ res.amount'.toRat = 1 ∧
      res.loanBroker'.coverAvailable = unitCover (k + 1) ∧
      res.loanBroker'.numericType = .fractional ∧
      numberExponent lb.coverAvailable lb.numericType = .ok 0 := by
  have hexp : numberExponent lb.coverAvailable lb.numericType = .ok 0 := by
    rw [hc, hnt]; exact unitCover_exponent k (by omega)
  have hwc : waUnitScale.ExactCanonical := Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩
  have h1 := roundsToOne_witness
  unfold roundsToOne at h1
  split at h1
  · rename_i r hr
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h1
    -- the cover scale is `1`, so the deposit is rounded down to `1`
    have hrounded : lb.roundedCoverAmount waUnitScale = .ok (.rounded r) := by
      unfold LoanBroker.roundedCoverAmount
      rw [roundToCoverScale_eq _ _ _ _ 0 hexp, hr]
      simp [h1.1]
    have hcov : lb.toExact.coverAvailable = 10 ^ 15 + k := by
      show lb.coverAvailable.toRat = _; rw [hc, unitCover_toRat k (by omega)]
    have hkq : (k : ℚ) < 9 * 10 ^ 15 := by exact_mod_cast (show k < 9 * 10 ^ 15 by omega)
    obtain ⟨res, hok, hamt⟩ := LoanBroker.coverDeposit_total_proof lb waUnitScale r hrounded hwc
      (by decide) (by rw [hcov, h1.2]; linarith)
    have hamt1 : res.amount'.toRat = 1 := by rw [hamt, h1.2]
    -- the sum `10^15 + k + 1` fits a `Number`, so the credit is exact
    have hnext := unitCover_toRat (k + 1) hk
    have hup := LoanBroker.coverDeposit_credit_proof lb waUnitScale res hok hwc
      ⟨unitCover (k + 1), unitCover_isNormalized (k + 1) hk, by
        rw [hnext, hcov, hamt1]; push_cast; ring⟩
    have hcov' : res.loanBroker'.coverAvailable = unitCover (k + 1) := by
      apply res.loanBroker'.wf.coverAvailable_norm.toRat_inj (unitCover_isNormalized (k + 1) hk)
      show res.loanBroker'.toExact.coverAvailable = _
      rw [hnext]; push_cast; linarith
    exact ⟨res, hok, hamt1, hcov',
      by rw [(LoanBroker.coverDeposit_fixed_fields lb _ res hok).numericType, hnt], hexp⟩
  · exact absurd h1 (by decide)

/-- `k` deposits of `1.999999999999999` from a cover of `10^15` are a run that moved `k` and was
asked to move `k` times the deposit. -/
private lemma unitCover_run (k : ℕ) (hk : k < 9 * 10 ^ 15) :
    ∃ (lb : LoanBroker) (applied requested : ℚ),
      LoanBroker.ReachableFromIn wbUnitScaleL 1 lb k applied requested ∧ applied = k ∧
      requested = k * waUnitScale.toRat ∧ lb.numericType = .fractional ∧
      lb.coverAvailable = unitCover k := by
  induction k with
  | zero => exact ⟨wbUnitScaleL, 0, 0, .refl, by simp, by simp, rfl, by decide⟩
  | succ k ih =>
    obtain ⟨lb, a, q, hr, ha, hq, hnt, hc⟩ := ih (by omega)
    obtain ⟨res, hok, hamt, hc', hnt', hexp⟩ := unitCover_deposit lb k hk hnt hc
    have hwc : waUnitScale.ExactCanonical :=
      Or.inl ⟨rfl, by decide, by decide, by decide, by decide⟩
    have hcov : lb.toExact.coverAvailable = 10 ^ 15 + k := by
      show lb.coverAvailable.toRat = _; rw [hc, unitCover_toRat k (by omega)]
    refine ⟨res.loanBroker', a + res.amount'.toRat, q + waUnitScale.toRat,
      .coverDeposit lb k a q waUnitScale res hr hok hwc
        ⟨unitCover (k + 1), unitCover_isNormalized (k + 1) hk, by
          rw [unitCover_toRat (k + 1) hk, hcov, hamt]; push_cast; ring⟩
        (fun e he => by rw [hexp, Except.ok.injEq] at he; subst he; norm_num),
      by rw [ha, hamt]; push_cast; ring, by rw [hq]; push_cast; ring, hnt', hc'⟩

/-- Deposit rounding adds up over a run of any length below `9 * 10^15`: deposits of
`1.999999999999999` on a cover starting at `10^15` are each rounded down to `1`. -/
lemma LoanBroker.ReachableFromIn.cover_within_bounds_witness (n : ℕ) (hn : n < 9 * 10 ^ 15) :
    ∃ (start lb : LoanBroker) (unit applied requested : ℚ),
      0 ≤ unit ∧ LoanBroker.ReachableFromIn start unit lb n applied requested ∧
      (1 - 1 / 10 ^ 15) * (n * unit) ≤
        start.toExact.coverAvailable + requested - lb.toExact.coverAvailable := by
  obtain ⟨lb, a, q, hr, _, hq, _, hc⟩ := unitCover_run n hn
  refine ⟨wbUnitScaleL, lb, 1, a, q, by norm_num, hr, ?_⟩
  have hstart : wbUnitScaleL.toExact.coverAvailable = 10 ^ 15 := by
    show wbUnitScaleL.coverAvailable.toRat = _
    rw [show wbUnitScaleL.coverAvailable = unitCover 0 by decide, unitCover_toRat 0 (by norm_num)]
    norm_num
  have hend : lb.toExact.coverAvailable = 10 ^ 15 + n := by
    show lb.coverAvailable.toRat = _; rw [hc, unitCover_toRat n hn]
  have hwa : waUnitScale.toRat = 2 - 1 / 10 ^ 15 := by native_decide
  rw [hstart, hend, hq, hwa]
  exact le_of_eq (by ring)

end XRPL.Model.Lending
