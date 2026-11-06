import XRPL.Model.Lending.Amortization
import XRPL.Properties.Protocol.Common.Reduction
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Normalize.NormalizedResult
import XRPL.Properties.Protocol.Number.Sub.ZeroShape

/-! # Facts about the amortization helpers

Every rate, factor and payment the helpers compute from normalized inputs is a normalized `Number`,
and a payment is either the principal over the count or the principal times the payment factor. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A tenth-bips share of a normalized value is normalized. -/
lemma tenthBipsOfValue_normalized {value r : Number} {bips : TenthBips32} {mode : rounding_mode}
    (hv : value.isNormalized) (h : tenthBipsOfValue value bips mode = .ok r) : r.isNormalized := by
  have heq : tenthBipsOfValue value bips mode =
      (value.operator_mul bips.toNumber mode) >>= (fun p => p.operator_div kTenthBipsPerUnity.toNumber mode) := rfl
  rw [heq] at h
  obtain ⟨p, hp, h⟩ := bind_ok_peel _ _ _ h
  exact Number.operator_div_isNormalized p _ r mode
    (Number.operator_mul_isNormalized _ _ p mode hv (Number.ofInt64_isNormalized _) hp)
    (Number.ofInt64_isNormalized _) h

/-- The periodic rate is normalized. -/
lemma loanPeriodicRate_isNormalized (rate : TenthBips32) (interval : UInt32) (r : Number)
    (h : loanPeriodicRate rate interval = .ok r) : r.isNormalized := by
  have heq : loanPeriodicRate rate interval =
      (tenthBipsOfValue (Number.ofInt64 interval.toInt64) rate .to_nearest) >>=
        (fun t => t.operator_div secondsInYear .to_nearest) := rfl
  rw [heq] at h
  cases ht : tenthBipsOfValue (Number.ofInt64 interval.toInt64) rate .to_nearest with
  | error e => rw [ht] at h; exact absurd h nofun
  | ok t =>
    rw [ht, ok_bind] at h
    exact Number.operator_div_isNormalized t _ r _
      (tenthBipsOfValue_normalized (Number.ofInt64_isNormalized _) ht) (Number.ofInt64_isNormalized _) h

/-- A power of a normalized base is normalized. -/
lemma Number.power_isNormalized (base : Number) (hb : base.isNormalized) :
    ∀ (k : Nat) (r : Number), base.power k = .ok r → r.isNormalized := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro r h
    match k, ih with
    | 0, _ =>
      rw [Number.power] at h
      cases h; exact Number.ofInt64_isNormalized 1
    | 1, _ =>
      rw [Number.power] at h
      cases h; exact hb
    | j + 2, ih =>
      rw [Number.power] at h
      cases hh : base.power ((j + 2) / 2) with
      | error e => rw [hh] at h; exact absurd h (by simp [bind, Except.bind])
      | ok half =>
        rw [hh] at h
        have hhalf := ih ((j + 2) / 2) (by omega) half hh
        simp only [bind, Except.bind] at h
        cases hs : half.operator_mul half .to_nearest with
        | error e => rw [hs] at h; exact absurd h (by simp)
        | ok sq =>
          rw [hs] at h
          have hsq := Number.operator_mul_isNormalized _ _ sq _ hhalf hhalf hs
          simp only at h
          split at h
          · exact Number.operator_mul_isNormalized _ _ r _ hsq hb h
          · cases h; exact hsq
/-- The binomial series of `(1 + rate)^n − 1` stays normalized. -/
private lemma powerMinusOneLoop_isNormalized (rate : Number) (hrate : rate.isNormalized) (pr : Nat) :
    ∀ (d index : Nat) (currentTerm runningSum r : Number), pr - index = d → currentTerm.isNormalized →
      runningSum.isNormalized → powerMinusOneLoop rate pr index currentTerm runningSum = .ok r →
      r.isNormalized := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro index currentTerm runningSum r hd hc hs h
    rw [powerMinusOneLoop] at h
    split at h
    · obtain ⟨c1, h1, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨c2, h2, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨c3, h3, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨ns, h4, h⟩ := bind_ok_peel _ _ _ h
      have hc1 := Number.operator_mul_isNormalized _ _ c1 _ hc hrate h1
      have hc2 := Number.operator_mul_isNormalized _ _ c2 _ hc1 (Number.ofInt64_isNormalized _) h2
      have hc3 := Number.operator_div_isNormalized _ _ c3 _ hc2 (Number.ofInt64_isNormalized _) h3
      have hns := operator_add_isNormalized_to_nearest_sz _ _ ns hs hc3 h4
      split at h
      · cases h; exact hs
      · exact ih (pr - (index + 1)) (by omega) (index + 1) c3 ns r rfl hc3 hns h
    · cases h; exact hs

/-- `(1 + rate)^n − 1` by the series is normalized. -/
private lemma computePowerMinusOne_isNormalized (rate n : Number) (pr : UInt32) (r : Number)
    (hrate : rate.isNormalized) (hn : n.isNormalized) (h : computePowerMinusOne rate n pr = .ok r) :
    r.isNormalized := by
  unfold computePowerMinusOne at h
  dsimp only at h
  split at h
  · cases h; exact Number.zero_isNormalized
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨c, hc, h⟩ := bind_ok_peel _ _ _ h
    have hc' := Number.operator_mul_isNormalized _ _ c _ hn hrate hc
    exact powerMinusOneLoop_isNormalized rate hrate pr.toNat _ 1 c c r rfl hc' hc' h

/-- `(1 + rate)^n − 1` by either method is normalized. -/
lemma computePowerMinusOneHybrid_isNormalized (rate n : Number) (pr : UInt32) (r : Number)
    (hrate : rate.isNormalized) (hn : n.isNormalized) (h : computePowerMinusOneHybrid rate n pr = .ok r) :
    r.isNormalized := by
  unfold computePowerMinusOneHybrid at h
  dsimp only at h
  split at h
  · cases h; exact Number.zero_isNormalized
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨nr, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨th, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · obtain ⟨b, hb, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨raised, hraised, h⟩ := bind_ok_peel _ _ _ h
      exact operator_sub_isNormalized_to_nearest_sz _ _ r
        (Number.power_isNormalized b (operator_add_isNormalized_to_nearest_sz _ _ b
          (Number.ofInt64_isNormalized 1) hrate hb) _ raised hraised) (Number.ofInt64_isNormalized 1) h
    · exact computePowerMinusOne_isNormalized rate n pr r hrate hn h

/-- The payment factor is normalized. -/
lemma computePaymentFactor_isNormalized (rate n : Number) (pr : UInt32) (r : Number)
    (hrate : rate.isNormalized) (hn : n.isNormalized) (h : computePaymentFactor rate n pr = .ok r) :
    r.isNormalized := by
  unfold computePaymentFactor at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Number.zero_isNormalized
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · exact Number.operator_div_isNormalized _ _ r _ (Number.ofInt64_isNormalized 1) hn h
    · obtain ⟨pmo, hpmo, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨rr, hrr, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨num, hnum, h⟩ := bind_ok_peel _ _ _ h
      have hp := computePowerMinusOneHybrid_isNormalized rate n pr pmo hrate hn hpmo
      have hr' := operator_add_isNormalized_to_nearest_sz _ _ rr (Number.ofInt64_isNormalized 1) hp hrr
      exact Number.operator_div_isNormalized _ _ r _ (Number.operator_mul_isNormalized _ _ num _ hrate hr' hnum) hp h

/-- The periodic payment is normalized. -/
lemma loanPeriodicPayment_isNormalized (principal rate : Number) (pr : UInt32) (r : Number)
    (hp : principal.isNormalized) (hrate : rate.isNormalized) (h : loanPeriodicPayment principal rate pr = .ok r) :
    r.isNormalized := by
  unfold loanPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Number.zero_isNormalized
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · exact Number.operator_div_isNormalized _ _ r _ hp (Number.ofInt64_isNormalized _) h
    · obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
      exact Number.operator_mul_isNormalized _ _ r _ hp
        (computePaymentFactor_isNormalized rate _ pr f hrate (Number.ofInt64_isNormalized _) hf) h

/-- A `to_nearest` rounding of a value at or below zero is at or below zero. -/
lemma Number.roundsToRepresentable_nonpos (r : Number) (t : ℚ) (hR : r.RoundsToRepresentable t .to_nearest)
    (ht : t ≤ 0) : r.toRat ≤ 0 := by
  rcases hR with ⟨n, hn, hr⟩ | ⟨n, hn, hr⟩
  · rw [hr]; exact le_trans (Number.lower_le t n hn) ht
  · rw [hr]
    have := Number.upper_tight t n hn Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; exact ht)
    rwa [Number.toRat_zero] at this

/-- A positive `to_nearest` rounding comes from a positive value. -/
lemma Number.pos_of_roundsToRepresentable (r : Number) (t : ℚ) (hR : r.RoundsToRepresentable t .to_nearest)
    (hr : 0 < r.toRat) : 0 < t := by
  by_contra h
  exact absurd (Number.roundsToRepresentable_nonpos r t hR (not_lt.mp h)) (not_le.mpr hr)

/-- A nonzero payment is the principal over the count when the rate is zero, and the principal times
the payment factor otherwise. -/
lemma loanPeriodicPayment_cases (principal rate : Number) (pr : UInt32) (pp : Number)
    (h : loanPeriodicPayment principal rate pr = .ok pp) (hpp : pp ≠ Number.zero) :
    (rate.operator_eq Number.zero = true ∧
      principal.operator_div (Number.ofInt64 pr.toInt64) .to_nearest = .ok pp) ∨
    (rate.operator_eq Number.zero = false ∧ ∃ f,
      computePaymentFactor rate (Number.ofInt64 pr.toInt64) pr = .ok f ∧
      principal.operator_mul f .to_nearest = .ok pp) := by
  unfold loanPeriodicPayment at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; exact absurd h.symm hpp
  · obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    split at h
    · exact Or.inl ⟨by assumption, h⟩
    · obtain ⟨f, hf, h⟩ := bind_ok_peel _ _ _ h
      exact Or.inr ⟨by simpa using ‹¬ _ = true›, f, hf, h⟩

/-- No payments left: the theoretical principal is zero. -/
lemma loanPrincipalFromPeriodicPayment_zero (pp rate : Number) :
    loanPrincipalFromPeriodicPayment pp rate 0 = .ok Number.zero := rfl

end XRPL.Model.Lending
