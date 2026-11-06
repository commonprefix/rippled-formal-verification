import XRPL.Properties.Lending.Loan.Common.ManageProofs
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Lending.Common.SumRounding
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Common.TenthBips
import XRPL.Properties.Vault.Proofs.Support.ClampFacts

/-! # Proof bodies for the cover a default pays

The cover never exceeds the liquidation amount capped by PrincipalOutstanding and CoverAvailable,
because every step after the liquidation amount rounds down. -/

namespace XRPL.Model.Protocol

/-- Towards zero and downward round the same way once the sign is clear. -/
private lemma Guard.round_towards_zero_of_sbit (g : Guard) (h : g.sbit_ = false) :
    g.round .towards_zero = g.round .downward := by
  unfold Guard.round; simp [h]

/-- On a value that is not negative, `to_rep` towards zero is `to_rep` downward. -/
lemma Number.to_rep_towards_zero (n : Number) (hneg : n.negative_ = false) :
    n.to_rep .towards_zero = n.to_rep .downward := by
  rw [Number.to_rep_eq_spec, Number.to_rep_eq_spec]
  unfold Number.to_repSpec
  simp only [hneg, Bool.false_eq_true, ↓reduceIte]
  by_cases hz : (n.mantissa == 0) = true
  · simp only [hz, ↓reduceIte]
  simp only [hz, Bool.false_eq_true, ↓reduceIte]
  by_cases hoff : n.exponent < 0
  · have hsb : (shiftSpec n.mantissa n.exponent Guard.new).2.sbit_ = false := by
      rw [Number.to_rep_shift_sbit]; rfl
    simp only [hoff, ↓reduceIte]
    simp only [Guard.round_towards_zero_of_sbit _ hsb]
  · have h0 : Guard.new.sbit_ = false := rfl
    simp only [hoff, ↓reduceIte]
    simp only [Guard.round_towards_zero_of_sbit _ h0]

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- `Number.min` is the smaller value, and it is normalized. -/
lemma Number.min_toRat (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized) :
    (Number.min x y).toRat = min x.toRat y.toRat ∧ (Number.min x y).isNormalized := by
  unfold Number.min
  by_cases h : y.operator_lt x = true
  · rw [if_pos h]
    exact ⟨(min_eq_right ((operator_lt_iff _ _ hy hx).mp h).le).symm, hy⟩
  · rw [if_neg h]
    refine ⟨(min_eq_left ?_).symm, hx⟩
    exact (operator_lt_eq_false_iff _ _ hy hx).mp (by simpa using h)

/-- A towards-zero `ofNumber` of a value that is not negative stays between zero and the value. -/
private lemma STAmount.ofNumber_towards_zero_le (nt : NumericType) (n : Number) (r : STAmount) (hn : n.isNormalized)
    (h0 : 0 ≤ n.toRat) (hok : STAmount.ofNumber nt n .towards_zero = .ok r) : 0 ≤ r.toRat ∧ r.toRat ≤ n.toRat := by
  have hneg := Number.negative_false_of_nonneg n hn h0
  refine ⟨STAmount.ofNumber_nonneg nt n _ r hn hneg hok, ?_⟩
  by_cases hz : r.mValue = 0
  · rw [STAmount.toRat_eq_zero_of_mValue_zero r hz]; exact h0
  by_cases hnt : nt.isIntegral = true
  · obtain ⟨iv, hiv, hr⟩ := STAmount.ofNumber_integral_toRat nt n _ r hnt hneg hok
    rw [Number.to_rep_towards_zero n hneg] at hiv
    rw [hr]
    exact (Number.to_rep_downward_floor n iv hn hneg hiv).1
  · have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hnt)
    subst hfr
    have hnz : n.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional n _ r hok hz
    obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hnz
    have hemin := Number.exponent_ge_min n hn hnz
    have hexp := (STAmount.ofNumber_iou_ok_facts n _ r hlo hhi hemin hok hz).2
    have habs := STAmount.ofNumber_iou_abs_le_towards_zero .fractional n r rfl hlo hhi hemin hexp hok hz
    have hr0 := STAmount.ofNumber_nonneg _ n _ r hn hneg hok
    rwa [abs_of_nonneg hr0, abs_of_nonneg h0] at habs

/-- Rounding towards zero to the asset stays between zero and the value. -/
lemma STAmount.roundToNumericType_towards_zero_le (nt : NumericType) (x c : Number) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (h : STAmount.roundToNumericType nt x .towards_zero = .ok c) :
    0 ≤ c.toRat ∧ c.toRat ≤ x.toRat ∧ c.isNormalized := by
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber nt x .towards_zero with
  | error e => rw [hof] at h; exact absurd h (by simp)
  | ok ret =>
    rw [hof] at h
    obtain ⟨hv, hn⟩ := STAmount.ofNumber_toNumber_exact nt x _ _ ret c hx (fun _ => h0) hof h
    obtain ⟨h1, h2⟩ := STAmount.ofNumber_towards_zero_le nt x ret hx h0 hof
    exact ⟨hv ▸ h1, hv ▸ h2, hn⟩

/-- The cover never exceeds the capped liquidation amount: it is at most the liquidation amount,
PrincipalOutstanding and CoverAvailable. -/
lemma Loan.defaultCover_le (loan : Loan) (v : Vault) (dc minimumCover liquidationAmount : Number)
    (h : loan.defaultCover v = .ok dc)
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount) :
    dc.toRat ≤ min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat := by
  obtain ⟨mc, liq, c, st, hmc, hl, hc, hst, hdc⟩ := Loan.defaultCover_parts loan v dc h
  rw [hmin, Except.ok.injEq] at hmc
  subst hmc
  rw [hliq, Except.ok.injEq] at hl
  subst hl
  have hb := loan.broker.exact
  have hpo0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg

  obtain ⟨hmcn, hmc0⟩ := tenthBipsOfValue_upward_facts _ _ _ loan.broker.wf.debtTotal_norm hb.debtTotal_nonneg hmin
  obtain ⟨hliqn, hliq0⟩ := tenthBipsOfValue_upward_facts _ _ _ hmcn hmc0 hliq
  obtain ⟨hm1, hm1n⟩ := Number.min_toRat _ _ hliqn loan.wf.principalOutstanding_norm
  obtain ⟨hm2, hm2n⟩ := Number.min_toRat _ _ hm1n loan.broker.wf.coverAvailable_norm
  have hcap0 : 0 ≤ (Number.min (Number.min liquidationAmount loan.principalOutstanding)
      loan.broker.coverAvailable).toRat := by
    rw [hm2, hm1]; exact le_min (le_min hliq0 hpo0) hb.coverAvailable_nonneg

  -- rounding towards zero, then the floor onto the posterior grid, never add anything
  obtain ⟨hc0, hcle, hcn⟩ := STAmount.roundToNumericType_towards_zero_le _ _ _ hm2n hcap0 hc
  obtain ⟨hstle, hex⟩ := sumRoundAndSubtract_downward_le _ _ _ _ _ v.wf.assetsAvailable_norm
    v.exact.assetsAvailable_nonneg hcn hc0 (Vault.baseExponent_range v) hst
  rw [(hex dc hdc).1, ← hm1, ← hm2]
  exact hstle.trans hcle

variable (loan : Loan) (v : Vault)

/-- Proof body of `manageDefault_cover_upper_bound`. -/
lemma Loan.manageDefault_cover_upper_bound_proof (minimumCover liquidationAmount : Number)
    (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount) :
    r.amountToPool.toRat -
      min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat ≤ 0 := by
  obtain ⟨_, _, _, _, _, -, hdc, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  linarith [Loan.defaultCover_le loan v _ _ _ hdc hmin hliq]

end XRPL.Model.Lending
