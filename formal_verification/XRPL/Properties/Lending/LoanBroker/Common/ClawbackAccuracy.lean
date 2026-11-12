import XRPL.Properties.Lending.LoanBroker.Common.ClawbackExits
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackFloor
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-! # Proof bodies for the `LoanBroker.coverClawback` theorems

Proofs for the theorems in `LoanBrokerCoverClawback.lean`: what a clawback debits on any lawful
broker, on a broker in the Open zone or with a cover that fits, and on a reachable one. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

/-- CoverAvailable minus the minimum cover is a whole number of base units on a cover that fits. -/
private lemma cover_sub_minimum_units (lb : LoanBroker) (v : Vault) (m : Number)
    (hf : lb.CoverFits v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m) :
    ∃ k : ℤ, lb.toExact.coverAvailable - m.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  obtain ⟨-, jm, hjm⟩ := minimumBrokerCover_onGrid _ _ _ _ m ⟨by omega, by omega⟩
    (fun h => (hbint (hnt ▸ h)).le) hm
  obtain ⟨-, jc, hjc⟩ := hf.cover
  exact ⟨jc - jm, by show lb.coverAvailable.toRat - m.toRat = _; rw [hjc, hjm]; push_cast; ring⟩

/-- Proof body of the clawed-amount part of `LoanBroker.roundedCoverClawback_all`. -/
lemma LoanBroker.roundedCoverClawback_all_proof (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (m : Number) (hf : lb.CoverFits v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.amount'.toRat = lb.toExact.coverAvailable - m.toRat := by
  have hfl := LoanBroker.coverClawback_floor lb v amount res m hf hnt hmax hreq hm hok
  have htarget : lb.clawTarget m.toRat amount = lb.toExact.coverAvailable - m.toRat := by
    rcases hall with h | ⟨a, h, hz0⟩ <;> subst h <;> simp [LoanBroker.clawTarget, *]
  obtain ⟨k, hk⟩ := cover_sub_minimum_units lb v m hf hnt hm
  rw [hfl, htarget, floor_units_self _ _ k hk]

/-- Proof body of `LoanBroker.roundedCoverClawback_capped`. -/
lemma LoanBroker.roundedCoverClawback_capped_proof (lb : LoanBroker) (v : Vault) (a : STAmount)
    (res : LoanBrokerCoverResult) (m : Number) (hf : lb.CoverFits v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) (hnz : a.isZero = false)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    res.amount'.toRat =
      (⌊min a.toRat (lb.toExact.coverAvailable - m.toRat) / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent := by
  have hfl := LoanBroker.coverClawback_floor lb v (some a) res m hf hnt hmax
    (fun a' ha' => by cases ha'; exact hreq) hm hok
  simpa only [LoanBroker.clawTarget, hnz, Bool.false_eq_true, if_false] using hfl

/-- Proof body of the clawback line of `cover_keeps_minimum`. -/
lemma LoanBroker.coverClawback_keeps_minimum_proof (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (m : Number) (hf : lb.CoverFits v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    m.toRat ≤ res.loanBroker'.toExact.coverAvailable := by
  have hfl := LoanBroker.coverClawback_floor lb v amount res m hf hnt hmax hreq hm hok
  obtain ⟨-, -, -, -, hcov⟩ := LoanBroker.coverClawback_exact lb v amount res hf hmax hok
  have htle := LoanBroker.clawTarget_le lb m.toRat amount
  have := (floor_units_bounds (lb.clawTarget m.toRat amount) v.baseExponent).1
  rw [hcov, hfl]
  linarith

/-- Proof body of the minCover part of `LoanBroker.roundedCoverClawback_all`. -/
lemma LoanBroker.coverClawback_all_leaves_minimum_proof (lb : LoanBroker) (v : Vault)
    (amount : Option STAmount) (res : LoanBrokerCoverResult) (m : Number) (hf : lb.CoverFits v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.loanBroker'.toExact.coverAvailable = m.toRat := by
  have hall' := LoanBroker.roundedCoverClawback_all_proof lb v amount res m hf hnt hmax hreq hall hm hok
  obtain ⟨-, -, -, -, hcov⟩ := LoanBroker.coverClawback_exact lb v amount res hf hmax hok
  rw [hcov, hall']; ring

/-- Proof body of the clawback line of `cover_direction`. -/
lemma LoanBroker.coverClawback_decreases_cover_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback pool amount).run = .ok (.ok res))
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable := by
  obtain ⟨c, hc, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  obtain ⟨_, _, claw, claw', _, _, _, _, hof, hcl, _⟩ := LoanBroker.roundedCoverClawback_ok lb pool amount c hc
  have hcz : claw'.CanonicalOrZero := (STAmount.ofNumber_canonicalOrZero _ _ _ claw' hmax hof).1
  obtain ⟨hcc, -, hc0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ c _ hcz.operator_neg hb.1 hb.2 hcl
  exact LoanBroker.applyCoverTransaction_debit_le lb c res hcc hc0 happ

/-- Proof body of the debit part of `LoanBroker.coverClawback_debit`. -/
lemma LoanBroker.coverClawback_debit_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat := by
  obtain ⟨hz, -⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  obtain ⟨-, -, -, -, hcov⟩ := LoanBroker.coverClawback_exact lb v amount res hz.coverFits hmax hok
  rw [hcov]; ring

/-- Proof body of the at-most-the-amount part of `LoanBroker.coverClawback_debit`. -/
lemma LoanBroker.coverClawback_debit_le_amount_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a : STAmount)
    (hreq : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) (hnz : a.isZero = false)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≤ a.toRat := by
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  have hub := (LoanBroker.roundedCoverClawback_capped_proof lb v a res _ hz.coverFits hnt hmax hreq hnz hm hok).trans_le
    (floor_units_bounds _ _).1
  rw [LoanBroker.coverClawback_debit_proof lb base hr hmax v hvb (some a) res hok]
  exact le_trans hub (min_le_left _ _)

/-- Proof body of the monotone line of `LoanBroker.roundedCoverClawback_capped`. -/
lemma LoanBroker.coverClawback_monotone_proof (lb : LoanBroker) (v : Vault) (m : Number)
    (hf : lb.CoverFits v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (a b : STAmount)
    (ha : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hb : b.CanonicalOrZero ∧ b.mNumericType = lb.numericType ∧ 0 ≤ b.toRat)
    (hza : a.isZero = false) (hzb : b.isZero = false) (hab : a.toRat ≤ b.toRat)
    (ra rb : LoanBrokerCoverResult)
    (hoka : (lb.coverClawback v (some a)).run = .ok (.ok ra))
    (hokb : (lb.coverClawback v (some b)).run = .ok (.ok rb)) :
    ra.amount'.toRat ≤ rb.amount'.toRat := by
  have hfa := LoanBroker.coverClawback_floor lb v (some a) ra _ hf hnt hmax
    (fun a' ha' => by cases ha'; exact ha) hm hoka
  have hfb := LoanBroker.coverClawback_floor lb v (some b) rb _ hf hnt hmax
    (fun a' ha' => by cases ha'; exact hb) hm hokb
  simp only [LoanBroker.clawTarget, hza, hzb, Bool.false_eq_true, if_false] at hfa hfb
  rw [hfa, hfb]
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hle : min a.toRat (lb.toExact.coverAvailable - m.toRat) ≤
      min b.toRat (lb.toExact.coverAvailable - m.toRat) := min_le_min_right _ hab
  have := Int.floor_le_floor (div_le_div_of_nonneg_right hle hp.le)
  have : (⌊min a.toRat (lb.toExact.coverAvailable - m.toRat) / 10 ^ v.baseExponent⌋ : ℚ) ≤
      ⌊min b.toRat (lb.toExact.coverAvailable - m.toRat) / 10 ^ v.baseExponent⌋ := by
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right this hp.le

end XRPL.Model.Lending
