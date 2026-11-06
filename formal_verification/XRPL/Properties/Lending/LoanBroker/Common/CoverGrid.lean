import XRPL.Properties.Lending.LoanBroker.Common.CoverReduction
import XRPL.Properties.Lending.Common.GridRounding
import XRPL.Model.Lending1_1.AssetPool
import XRPL.Properties.Vault.Proofs.Support.WithdrawPayout

/-! # Cover operations on the base grid

A deposit floors the sum onto a grid at or above the base, and a withdrawal or a clawback clamps the amount onto one,
so whole base units stay whole. A deposit past the Open-limit check stays within the larger of cover and limit. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A cover movement by whole base units keeps CoverAvailable whole base units. -/
private lemma LoanBroker.applyCoverTransaction_onGrid (lb : LoanBroker) (d : CoverDirection) (a : STAmount)
    (s : Int) (r : LoanBrokerCoverResult) (hc : Number.OnGrid s lb.coverAvailable)
    (ha : ∀ m, a.toNumber .to_nearest = .ok m → Number.OnGrid s m)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (h : lb.applyCoverTransaction d a = .ok r) : Number.OnGrid s r.loanBroker'.coverAvailable := by
  cases d with
  | credit =>
    obtain ⟨m, c', hm, hc', -, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb a r h
    rw [show r.loanBroker'.coverAvailable = c' from congrArg RawLoanBroker.coverAvailable hraw]
    exact Number.OnGrid.add hc (ha m hm) hs hc'
  | debit =>
    obtain ⟨m, c', hm, hc', -, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb a r h
    rw [show r.loanBroker'.coverAvailable = c' from congrArg RawLoanBroker.coverAvailable hraw]
    exact Number.OnGrid.sub hc (ha m hm) hs hc'

/-- A clamped amount of an IOU vault's asset converts to whole base units. -/
lemma Vault.clamp_onGrid (v : Vault) (A : Number) (delta result : STAmount) (hd : delta.CanonicalOrZero)
    (h : clampToSumExponent A delta v.baseExponent = .ok result) :
    ∀ m, result.toNumber .to_nearest = .ok m → Number.OnGrid v.baseExponent m := by
  intro m hm
  obtain ⟨hrc, -, -⟩ := clampToSumExponent_canonicalOrZero A delta result v.baseExponent hd
    v.baseExponent_range.1 v.baseExponent_range.2 h
  obtain ⟨k, hk⟩ := clampToSumExponent_units A delta result v.baseExponent hd v.baseExponent_range.1
    v.baseExponent_range.2 (fun _ => v.baseExponent_bounds.2.1) h
  obtain ⟨hv, hn⟩ := hrc.toNumber_exact m hm
  exact ⟨hn, k, by rw [hv, hk]; push_cast; rfl⟩

/-- A cover withdrawal keeps CoverAvailable whole base units: the withdrawal is clamped onto the base grid. -/
lemma LoanBroker.coverWithdraw_onGrid (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (r : LoanBrokerCoverResult) (hd : amount.CanonicalOrZero) (hc : Number.OnGrid v.baseExponent lb.coverAvailable)
    (h : (lb.coverWithdraw v amount).run = .ok (.ok r)) :
    Number.OnGrid v.baseExponent r.loanBroker'.coverAvailable := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  simp only [LoanBroker.coverWithdraw] at h
  unfold_ter at h
  walk_ok
  exact LoanBroker.applyCoverTransaction_onGrid lb .debit _ _ r hc
    (Vault.clamp_onGrid v _ _ _ hd.operator_neg ‹clampToSumExponent _ _ _ = _›) hsr ‹_›

/-- A cover clawback keeps CoverAvailable whole base units: the clawback is clamped onto the base grid. -/
lemma LoanBroker.coverClawback_onGrid (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (r : LoanBrokerCoverResult) (hfr : lb.numericType = .fractional)
    (hc : Number.OnGrid v.baseExponent lb.coverAvailable)
    (h : (lb.coverClawback v amount).run = .ok (.ok r)) :
    Number.OnGrid v.baseExponent r.loanBroker'.coverAvailable := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  simp only [LoanBroker.coverClawback, LoanBroker.roundedCoverClawback] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hof := ‹STAmount.ofNumber _ _ _ = _›
    rw [hfr] at hof
    have hcz := (STAmount.ofNumber_fractional_fczr _ _ _ hof).canonicalOrZero
    exact LoanBroker.applyCoverTransaction_onGrid lb .debit _ _ r hc
      (Vault.clamp_onGrid v _ _ _ hcz.operator_neg ‹clampToSumExponent _ _ _ = _›) hsr ‹_›

/-- A cover deposit keeps CoverAvailable whole base units: the deposit is floored onto the posterior grid. -/
lemma LoanBroker.coverDeposit_onGrid (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (r : LoanBrokerCoverResult) (hint : lb.numericType.isIntegral = true → v.baseExponent = 0)
    (hc : Number.OnGrid v.baseExponent lb.coverAvailable) (h : (lb.coverDeposit v amount).run = .ok (.ok r)) :
    Number.OnGrid v.baseExponent r.loanBroker'.coverAvailable := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  simp only [LoanBroker.coverDeposit, LoanBroker.roundedCoverAmount] at h
  unfold_ter at h
  walk_ok
  have hsrs := ‹sumRoundAndSubtract _ _ _ _ _ = _›
  have hap := ‹LoanBroker.applyCoverTransaction _ _ _ = _›
  exact LoanBroker.applyCoverTransaction_onGrid lb .credit _ _ r hc
    (fun m hm => sumRoundAndSubtract_onGrid _ _ _ _ _ _ m hc ⟨hb, v.baseExponent_bounds.2.1⟩ hint hsrs hm) hsr hap

/-- A cover clawback of an XRP or MPT broker keeps CoverAvailable whole units: the clawback is clamped onto the
base grid. -/
lemma LoanBroker.coverClawback_onGrid_integral (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (r : LoanBrokerCoverResult) (_hint : lb.numericType.isIntegral = true)
    (hmax : lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hc : Number.OnGrid v.baseExponent lb.coverAvailable)
    (h : (lb.coverClawback v amount).run = .ok (.ok r)) :
    Number.OnGrid v.baseExponent r.loanBroker'.coverAvailable := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  simp only [LoanBroker.coverClawback, LoanBroker.roundedCoverClawback] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hof := ‹STAmount.ofNumber _ _ _ = _›
    have hcz := (STAmount.ofNumber_canonicalOrZero _ _ _ _ (fun _ => hmax) hof).1
    exact LoanBroker.applyCoverTransaction_onGrid lb .debit _ _ r hc
      (Vault.clamp_onGrid v _ _ _ hcz.operator_neg ‹clampToSumExponent _ _ _ = _›) hsr ‹_›

/-- The Open limit is `9·10^15` base units. -/
lemma Vault.openLimit_value (v : Vault) :
    ∃ L : Number, v.openLimit = .ok L ∧ L.isNormalized ∧ L.toRat = 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨hblo, hbhi, -⟩ := v.baseExponent_bounds
  obtain ⟨w, hw, hwv, hwn⟩ := Number.from_rep_exact (9 : Int64) (15 + v.baseExponent) .to_nearest (by decide)
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  refine ⟨w, hw, hwn, ?_⟩
  rw [hwv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; push_cast; ring

/-- A debit of an amount at least zero leaves CoverAvailable at most what it was. -/
lemma LoanBroker.applyCoverTransaction_debit_le (lb : LoanBroker) (a : STAmount) (r : LoanBrokerCoverResult)
    (ha : a.CanonicalOrZero) (ha0 : 0 ≤ a.toRat) (h : lb.applyCoverTransaction .debit a = .ok r) :
    r.loanBroker'.coverAvailable.toRat ≤ lb.coverAvailable.toRat := by
  obtain ⟨m, c', hm, hc', -, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb a r h
  rw [show r.loanBroker'.coverAvailable = c' from congrArg RawLoanBroker.coverAvailable hraw]
  obtain ⟨hmv, hmn⟩ := ha.toNumber_exact m hm
  exact Number.roundsToRepresentable_le _ _ (operator_sub_rounded_to_nearest _ _ _ lb.wf.coverAvailable_norm hmn hc')
    _ lb.wf.coverAvailable_norm (by rw [hmv]; linarith)

/-- A sum of two amounts on a grid that the towards-zero check keeps at most the Open limit lands, rounded to
nearest, at most the larger of the first amount and the limit. -/
private lemma cover_credit_le (c n t L c' : Number) (s : Int) (hc : Number.OnGrid s c) (hn : Number.OnGrid s n)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hLn : L.isNormalized)
    (hLv : L.toRat = 9 * 10 ^ 15 * (10 : ℚ) ^ s)
    (htz : c.operator_add n .towards_zero = .ok t) (hgt : ¬ t.operator_gt L = true)
    (hadd : c.operator_add n .to_nearest = .ok c') : c'.toRat ≤ max c.toRat L.toRat := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hR := operator_add_rounded_to_nearest _ _ _ hc.1 hn.1 hadd
  by_cases hn0 : n.toRat ≤ 0
  · -- a deposit that rounded to nothing or less keeps the cover at most where it was
    exact (Number.roundsToRepresentable_le _ _ hR c hc.1 (by linarith)).trans (le_max_left _ _)
  push Not at hn0
  by_cases hle : c.toRat + n.toRat ≤ L.toRat
  · exact (Number.roundsToRepresentable_le _ _ hR L hLn hle).trans (le_max_right _ _)
  -- past the limit the sum reaches the next grid point, and the towards-zero sum with it
  exfalso
  push Not at hle
  obtain ⟨kc, hkc⟩ := hc.2
  obtain ⟨kn, hkn⟩ := hn.2
  have hk : 9 * 10 ^ 15 + 1 ≤ kc + kn := by
    have h1 : ((9 * 10 ^ 15 : ℤ) : ℚ) * 10 ^ s < ((kc + kn : ℤ) : ℚ) * 10 ^ s := by
      push_cast; rw [add_mul, ← hkc, ← hkn]; linarith
    have := lt_of_mul_lt_mul_right h1 hp.le
    exact_mod_cast this
  obtain ⟨m, hm, hmv⟩ := Number.exists_normalized_int_mul_pow (9 * 10 ^ 15 + 1) s (by constructor <;> norm_num) hs
  obtain ⟨l, hlo, htv⟩ := operator_add_rounded_towards_zero _ _ _ hc.1 hn.1 htz
  rw [if_pos (by linarith)] at hlo
  have hmt : m.toRat ≤ c.toRat + n.toRat := by
    rw [hmv, hkc, hkn]
    have : ((9 * 10 ^ 15 + 1 : ℤ) : ℚ) ≤ ((kc + kn : ℤ) : ℚ) := by exact_mod_cast hk
    push_cast at this ⊢
    nlinarith
  have hmle := Number.lower_tight _ l hlo m hm hmt
  have hlt : L.toRat < t.toRat := by
    rw [htv, hLv]
    refine lt_of_lt_of_le ?_ hmle
    rw [hmv]; push_cast; nlinarith
  have ht0 : t.mantissa_ ≠ 0 := by
    intro h0
    rw [Number.toRat_eq_zero_of_mantissa_zero t h0, hLv] at hlt
    have : (0 : ℚ) < 9 * 10 ^ 15 * 10 ^ s := by positivity
    linarith
  exact hgt ((operator_gt_iff _ _ (operator_add_isNormalized _ _ _ .towards_zero hc.1 hn.1 htz ht0) hLn).mpr hlt)

/-- A deposit that passes the Open-limit check leaves the cover at most the larger of the old cover and the
Open limit. -/
lemma LoanBroker.coverDeposit_le (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (r : LoanBrokerCoverResult) (hc : Number.OnGrid v.baseExponent lb.coverAvailable)
    (hint : lb.numericType.isIntegral = true → v.baseExponent = 0)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS) (h : (lb.coverDeposit v amount).run = .ok (.ok r)) :
    r.loanBroker'.coverAvailable.toRat ≤ max lb.coverAvailable.toRat (9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent) := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨a, ha, hap⟩ := LoanBroker.coverDeposit_ok_inv lb v amount r h
  obtain ⟨a', ha', hcheck⟩ := LoanBroker.canCoverDeposit_ok lb v amount hcan
  rw [ha, Except.ok.injEq, Except.ok.injEq] at ha'
  subst ha'
  obtain ⟨_, -, hsa, -⟩ := LoanBroker.roundedCoverAmount_ok lb v amount a ha
  obtain ⟨n, t, L, hnum, -, htz, hL, hgt⟩ := LoanBroker.checkCoverOpenLimit_ok lb v a hcheck
  obtain ⟨n', c', hn', hc', -, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb a r hap
  rw [hnum, Except.ok.injEq] at hn'
  subst hn'
  have hng : Number.OnGrid v.baseExponent n :=
    sumRoundAndSubtract_onGrid _ _ _ _ _ a n hc ⟨hb, v.baseExponent_bounds.2.1⟩ hint hsa hnum
  obtain ⟨L', hL', hL'n, hL'v⟩ := Vault.openLimit_value v
  rw [show AssetPool.openLimit v = v.openLimit from rfl, hL', Except.ok.injEq] at hL
  subst hL
  rw [show r.loanBroker'.coverAvailable = c' from congrArg RawLoanBroker.coverAvailable hraw, ← hL'v]
  exact cover_credit_le _ n t L' c' v.baseExponent hc hng hsr hL'n hL'v htz (by simp [hgt]) hc'

end XRPL.Model.Lending
