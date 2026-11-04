import XRPL.Properties.Lending.LoanBroker.Common.ClawbackExits
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackFloor
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-! # Proof bodies for the `LoanBroker.coverClawback` theorems

Proofs for the theorems in `LoanBrokerCoverClawback.lean`: what a clawback debits on any lawful
broker, on a broker in the Open zone, and on a reachable one. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

/-- CoverAvailable minus the minimum cover is a whole number of base units in the Open zone. -/
private lemma cover_sub_minimum_units (lb : LoanBroker) (v : Vault) (m : Number)
    (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m) :
    ∃ k : ℤ, lb.toExact.coverAvailable - m.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  obtain ⟨-, jm, hjm⟩ := minimumBrokerCover_onGrid _ _ _ _ m ⟨by omega, by omega⟩
    (fun h => (hbint (hnt ▸ h)).le) hm
  obtain ⟨-, jc, hjc⟩ := hz.cover
  exact ⟨jc - jm, by show lb.coverAvailable.toRat - m.toRat = _; rw [hjc, hjm]; push_cast; ring⟩

/-- Proof body of the clawed-amount part of `LoanBroker.roundedCoverClawback_all`. -/
lemma LoanBroker.roundedCoverClawback_all_proof (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (m : Number) (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.amount'.toRat = lb.toExact.coverAvailable - m.toRat := by
  have hfl := LoanBroker.coverClawback_floor lb v amount res m hz hnt hmax hreq hm hok
  have htarget : lb.clawTarget m.toRat amount = lb.toExact.coverAvailable - m.toRat := by
    rcases hall with h | ⟨a, h, hz0⟩ <;> subst h <;> simp [LoanBroker.clawTarget, *]
  obtain ⟨k, hk⟩ := cover_sub_minimum_units lb v m hz hnt hm
  rw [hfl, htarget, floor_units_self _ _ k hk]

/-- Proof body of the upper-bound part of `LoanBroker.roundedCoverClawback_capped`. -/
lemma LoanBroker.roundedCoverClawback_capped_upper_bound_proof (lb : LoanBroker) (v : Vault) (a : STAmount)
    (res : LoanBrokerCoverResult) (m : Number) (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) (hnz : a.isZero = false)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    res.amount'.toRat ≤ min a.toRat (lb.toExact.coverAvailable - m.toRat) := by
  have hfl := LoanBroker.coverClawback_floor lb v (some a) res m hz hnt hmax
    (fun a' ha' => by cases ha'; exact hreq) hm hok
  simp only [LoanBroker.clawTarget, hnz, Bool.false_eq_true, if_false] at hfl
  rw [hfl]
  exact (floor_units_bounds _ _).1

/-- Proof body of the lower-bound part of `LoanBroker.roundedCoverClawback_capped`. -/
lemma LoanBroker.roundedCoverClawback_capped_lower_bound_proof (lb : LoanBroker) (v : Vault) (a : STAmount)
    (res : LoanBrokerCoverResult) (m : Number) (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) (hnz : a.isZero = false)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    min a.toRat (lb.toExact.coverAvailable - m.toRat) - res.amount'.toRat < 10 ^ v.baseExponent := by
  have hfl := LoanBroker.coverClawback_floor lb v (some a) res m hz hnt hmax
    (fun a' ha' => by cases ha'; exact hreq) hm hok
  simp only [LoanBroker.clawTarget, hnz, Bool.false_eq_true, if_false] at hfl
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  rcases le_total a.toRat (lb.toExact.coverAvailable - m.toRat) with hle | hle
  · -- the request is the target, and a nonzero claw means it is at least one base unit
    rw [min_eq_left hle] at hfl ⊢
    obtain ⟨c, hc, happ⟩ := LoanBroker.coverClawback_ok_inv lb v (some a) res hok
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hcz⟩ := LoanBroker.roundedCoverClawback_ok lb v (some a) c hc
    obtain ⟨-, -, -, -, hamt, -⟩ := LoanBroker.applyCoverTransaction_debit_inv lb c res happ
    have hne : res.amount'.toRat ≠ 0 := by
      rw [hamt]
      exact fun h => (STAmount.isZero_eq_false_iff c).mp hcz ((STAmount.toRat_eq_zero_iff c).mp h)
    have hpos : 0 < (⌊a.toRat / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent :=
      lt_of_le_of_ne (floor_units_nonneg _ _ hreq.2.2) (by rw [← hfl]; exact hne.symm)
    rw [hfl]
    have hlt : (1 - 1 / 10 ^ 15 : ℚ) * 10 ^ v.baseExponent < 1 * 10 ^ v.baseExponent :=
      mul_lt_mul_of_pos_right (by norm_num) hp
    linarith [floor_units_error_le_of_canonical a (hreq.1.resolve_right (by rw [hnz]; exact Bool.false_ne_true)) _
      v.baseExponent_bounds.2.1 hpos]
  · -- the cover above the minimum is the target, already whole base units
    rw [min_eq_right hle] at hfl ⊢
    obtain ⟨k, hk⟩ := cover_sub_minimum_units lb v m hz hnt hm
    rw [hfl, floor_units_self _ _ k hk, sub_self]
    exact hp

/-- Proof body of `coverClawback_keeps_minimum`. -/
lemma LoanBroker.coverClawback_keeps_minimum_proof (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (m : Number) (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    m.toRat ≤ res.loanBroker'.toExact.coverAvailable := by
  have hfl := LoanBroker.coverClawback_floor lb v amount res m hz hnt hmax hreq hm hok
  obtain ⟨-, -, -, -, hcov⟩ := LoanBroker.coverClawback_exact lb v amount res hz hmax hok
  have htle := LoanBroker.clawTarget_le lb m.toRat amount
  have := (floor_units_bounds (lb.clawTarget m.toRat amount) v.baseExponent).1
  rw [hcov, hfl]
  linarith

/-- Proof body of the minCover part of `LoanBroker.roundedCoverClawback_all`. -/
lemma LoanBroker.coverClawback_all_leaves_minimum_proof (lb : LoanBroker) (v : Vault)
    (amount : Option STAmount) (res : LoanBrokerCoverResult) (m : Number) (hz : lb.OpenZone v.baseExponent)
    (hnt : v.numericType = lb.numericType)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hall : amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true)
    (hm : minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok m)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.loanBroker'.toExact.coverAvailable = m.toRat := by
  have hall' := LoanBroker.roundedCoverClawback_all_proof lb v amount res m hz hnt hmax hreq hall hm hok
  obtain ⟨-, -, -, -, hcov⟩ := LoanBroker.coverClawback_exact lb v amount res hz hmax hok
  rw [hcov, hall']; ring

/-- Proof body of `coverClawback_decreases_cover`. -/
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
  obtain ⟨-, -, -, -, hcov⟩ := LoanBroker.coverClawback_exact lb v amount res hz hmax hok
  rw [hcov]; ring

/-- Proof body of the at-most-the-amount part of `LoanBroker.coverClawback_debit`. -/
lemma LoanBroker.coverClawback_debit_le_amount_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a : STAmount)
    (hreq : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) (hnz : a.isZero = false)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≤ a.toRat := by
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  have hub := LoanBroker.roundedCoverClawback_capped_upper_bound_proof lb v a res _ hz hnt hmax hreq hnz hm hok
  rw [LoanBroker.coverClawback_debit_proof lb base hr hmax v hvb (some a) res hok]
  exact le_trans hub (min_le_left _ _)

/-- Proof body of `roundedCoverClawback_integral`. -/
lemma LoanBroker.roundedCoverClawback_integral_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hint : lb.numericType.isIntegral = true) (a : STAmount)
    (hreq : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) (hnz : a.isZero = false)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback v (some a)).run = .ok (.ok res)) :
    res.amount'.toRat = min a.toRat lb.toExact.coverAvailable := by
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  have hfl := LoanBroker.coverClawback_floor lb v (some a) res _ hz hnt hmax
    (fun a' ha' => by cases ha'; exact hreq) hm hok
  simp only [LoanBroker.clawTarget, hnz, Bool.false_eq_true, if_false, Number.toRat_zero, sub_zero] at hfl
  have hb0 : v.baseExponent = 0 := v.baseExponent_bounds.2.2 (hnt ▸ hint)
  -- an integral request and an integral cover are whole units
  have hai : ∃ k : ℤ, a.toRat = k := by
    have hc := hreq.1.resolve_right (by rw [hnz]; decide)
    have hic := (hc.1 (by unfold STAmount.integral; rw [hreq.2.1]; exact hint)).1
    exact ⟨_, STAmount.IntegralCanonical.toRat_eq_signedDrops a hic⟩
  obtain ⟨-, jc, hjc⟩ := hz.cover
  obtain ⟨ka, hka⟩ := hai
  rw [hb0] at hjc hfl
  have hmin : min a.toRat lb.toExact.coverAvailable = ((min ka jc : ℤ) : ℚ) * 10 ^ (0 : ℤ) := by
    show min a.toRat lb.coverAvailable.toRat = _
    rw [hka, hjc]; simp [Int.cast_min]
  rw [hfl, hmin, floor_units_self _ _ _ rfl]

/-- Proof body of `coverClawback_monotone`. -/
lemma LoanBroker.coverClawback_monotone_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (a b : STAmount)
    (ha : a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hb : b.CanonicalOrZero ∧ b.mNumericType = lb.numericType ∧ 0 ≤ b.toRat)
    (hza : a.isZero = false) (hzb : b.isZero = false) (hab : a.toRat ≤ b.toRat)
    (ra rb : LoanBrokerCoverResult)
    (hoka : (lb.coverClawback v (some a)).run = .ok (.ok ra))
    (hokb : (lb.coverClawback v (some b)).run = .ok (.ok rb)) :
    ra.amount'.toRat ≤ rb.amount'.toRat := by
  obtain ⟨hz, hm⟩ := LoanBroker.Reachable.zone_setup lb base hr hmax v hvb
  have hfa := LoanBroker.coverClawback_floor lb v (some a) ra _ hz hnt hmax
    (fun a' ha' => by cases ha'; exact ha) hm hoka
  have hfb := LoanBroker.coverClawback_floor lb v (some b) rb _ hz hnt hmax
    (fun a' ha' => by cases ha'; exact hb) hm hokb
  simp only [LoanBroker.clawTarget, hza, hzb, Bool.false_eq_true, if_false] at hfa hfb
  rw [hfa, hfb]
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hle : min a.toRat (lb.toExact.coverAvailable - Number.zero.toRat) ≤
      min b.toRat (lb.toExact.coverAvailable - Number.zero.toRat) := min_le_min_right _ hab
  have := Int.floor_le_floor (div_le_div_of_nonneg_right hle hp.le)
  have : (⌊min a.toRat (lb.toExact.coverAvailable - Number.zero.toRat) / 10 ^ v.baseExponent⌋ : ℚ) ≤
      ⌊min b.toRat (lb.toExact.coverAvailable - Number.zero.toRat) / 10 ^ v.baseExponent⌋ := by
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right this hp.le

/-- Proof body of the MPT part of `LoanBroker.coverClawback_debit`. -/
lemma LoanBroker.coverClawback_debit_integral_proof (lb : LoanBroker) (pool : α) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverClawback pool amount).run = .ok (.ok res))
    (hint : lb.numericType.isIntegral = true)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hcint : lb.toExact.coverAvailable.den = 1) (hbound : lb.toExact.coverAvailable < 2 ^ 63) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat := by
  obtain ⟨c, hrc, happ⟩ := LoanBroker.coverClawback_ok_inv lb pool amount res hok
  obtain ⟨_, _, claw, claw', _, _, _, _, hof, hcl, _⟩ := LoanBroker.roundedCoverClawback_ok lb pool amount c hrc
  obtain ⟨hicw, hntw⟩ := STAmount.ofNumber_integral_canonical _ _ _ _ hint hof
  obtain ⟨hic, hval, hrat⟩ := clampToSumExponent_neg_integral _ _ _ _ hicw hcl
  have h63 : maxRep.toNat ≤ 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num
  have hsz : c.mValue.toNat ≤ 2 ^ 63 - 1 := by
    rw [hval]
    exact le_trans hicw.in_range (le_trans (by rw [hntw]; exact hmax hint) h63)
  obtain ⟨hv, hamt⟩ := LoanBroker.applyCoverTransaction_debit_integral lb c res happ hic hsz
    (by rw [hrat]; exact abs_nonneg _) hcint hbound
  rw [hv, hamt]
  ring

end XRPL.Model.Lending
