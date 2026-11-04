import XRPL.Properties.Lending.LoanBroker.Common.DepositExits
import XRPL.Properties.Lending.LoanBroker.Common.DepositFloor
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # Proof bodies for the `LoanBroker.coverDeposit` theorems

Proofs for the theorems in `LoanBrokerCoverDeposit.lean`: what a deposit credits on any lawful broker,
and exactly on a reachable one. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

/-- Proof body of the integral line of `LoanBroker.roundedCoverAmount_bounds`. -/
lemma LoanBroker.roundedCoverAmount_integral_proof (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (hint : lb.numericType.isIntegral = true) (hc : amount.Canonical)
    (hat : amount.mNumericType = lb.numericType)
    (hok : (lb.roundedCoverAmount pool amount).run = .ok (.ok r)) : r.toRat = amount.toRat := by
  obtain ⟨aN, hnum, hs, -⟩ := LoanBroker.roundedCoverAmount_ok lb pool amount r hok
  obtain ⟨hv, hn⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hc) aN hnum
  unfold sumRoundAndSubtract at hs
  rw [if_pos hint] at hs
  simp only [bind_pure] at hs
  have hic := (hc.1 (by unfold STAmount.integral; rw [hat]; exact hint)).1
  have hden : aN.toRat.den = 1 := by rw [hv]; exact STAmount.IntegralCanonical.den_eq_one amount hic
  rw [STAmount.ofNumber_integral_exact _ _ _ r hint hn hden hs, hv]

/-- Proof body of the CoverAvailable line of `LoanBroker.coverDeposit_increases_cover`. -/
lemma LoanBroker.coverDeposit_increases_cover_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit pool amount).run = .ok (.ok res))
    (hc : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80) :
    lb.toExact.coverAvailable ≤ res.loanBroker'.toExact.coverAvailable := by
  obtain ⟨r, hr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb pool amount res hok
  obtain ⟨m, c', hm, hadd, -, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  obtain ⟨-, -, -, hpos⟩ := LoanBroker.roundedCoverAmount_ok lb pool amount r hr
  obtain ⟨hmv, hmn⟩ := (LoanBroker.roundedCoverAmount_le lb pool amount r hc hnn hb hr).2 m hm
  have hm0 : 0 ≤ m.toRat := by rw [hmv]; exact ((STAmount.signum_pos_iff_toRat_pos r).mp hpos).le
  show lb.coverAvailable.toRat ≤ res.loanBroker'.toRawLoanBroker.coverAvailable.toRat
  rw [hraw]
  exact operator_add_ge_of_ge_normalized _ _ _ _ lb.wf.coverAvailable_norm hmn hadd lb.wf.coverAvailable_norm
    (by linarith)

/-- Proof body of `coverDeposit_total`. -/
lemma LoanBroker.coverDeposit_total_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (hc : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80)
    (hcan : lb.canCoverDeposit pool amount = .ok .tesSUCCESS) :
    ∃ r res, (lb.roundedCoverAmount pool amount).run = .ok (.ok r) ∧
      (lb.coverDeposit pool amount).run = .ok (.ok res) ∧ res.amount' = r := by
  obtain ⟨r, hr, hcheck⟩ := LoanBroker.canCoverDeposit_ok lb pool amount hcan
  obtain ⟨rN, -, -, hrN, hps, -, -, -⟩ := LoanBroker.checkCoverOpenLimit_ok lb pool r hcheck
  -- the check already added the credit to the cover, to nearest
  obtain ⟨c', hadd, -⟩ := postSumExponent_reduces _ _ _ _ _ hps
  obtain ⟨lb', hres, -⟩ := LoanBroker.coverDeposit_success_proof lb pool amount r rN c' hr hc hnn hb hrN hadd
  exact ⟨r, ⟨r, lb'⟩, hr, hres, rfl⟩

/-- Proof body of the minCover line of `LoanBroker.coverDeposit_increases_cover`. -/
lemma LoanBroker.coverDeposit_keeps_minimum_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (e : Int) (hok : (lb.coverDeposit pool amount).run = .ok (.ok res))
    (hc : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80)
    (hmin : lb.HasMinimumCover e) : res.loanBroker'.HasMinimumCover e := by
  have hf := LoanBroker.coverDeposit_fixed_fields lb pool amount res hok
  exact LoanBroker.hasMinimumCover_of_cover_le lb res.loanBroker' e hf.numericType hf.debtTotal
    hf.coverRateMinimum (LoanBroker.coverDeposit_increases_cover_proof lb pool amount res hok hc hnn hb) hmin

/-- Proof body of the credit line of `LoanBroker.coverDeposit_credit`. -/
lemma LoanBroker.coverDeposit_credit_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = res.amount'.toRat := by
  have hz : lb.OpenZone v.baseExponent := hvb ▸ LoanBroker.Reachable.openZone lb base hr
  obtain ⟨-, -, -, -, hcov⟩ := LoanBroker.coverDeposit_exact lb v amount res hz hnt hc hpos hcan hok
  rw [hcov]; ring

/-- Proof body of the amount line of `LoanBroker.coverDeposit_credit`. -/
lemma LoanBroker.coverDeposit_credit_le_amount_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable ≤ amount.toRat := by
  have hz : lb.OpenZone v.baseExponent := hvb ▸ LoanBroker.Reachable.openZone lb base hr
  obtain ⟨-, -, -, hle, hcov⟩ := LoanBroker.coverDeposit_exact lb v amount res hz hnt hc hpos hcan hok
  rw [hcov]; linarith

/-- Proof body of the bounds line of `LoanBroker.roundedCoverAmount_bounds`. -/
lemma LoanBroker.roundedCoverAmount_bounds_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (r : STAmount) (hok : (lb.roundedCoverAmount v amount).run = .ok (.ok r)) :
    r.toRat ≤ amount.toRat ∧ amount.toRat - r.toRat < 10 ^ base := by
  have hz : lb.OpenZone v.baseExponent := hvb ▸ LoanBroker.Reachable.openZone_proof lb base hr hmax
  obtain ⟨-, -, -, hsig⟩ := LoanBroker.roundedCoverAmount_ok lb v amount r hok
  have hrpos := (STAmount.signum_pos_iff_toRat_pos r).mp hsig
  obtain ⟨r', res, hr', hres, hamt⟩ :=
    LoanBroker.coverDeposit_total_proof lb v amount hc hpos.le v.baseExponent_range hcan
  rw [hok, Except.ok.injEq, Except.ok.injEq] at hr'
  subst hr'
  have hfl := LoanBroker.coverDeposit_floor lb v amount res hz hnt hc hat hpos hcan hres
  rw [hamt] at hfl
  rw [hfl] at hrpos
  rw [hfl, ← hvb]
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hlt : (1 - 1 / 10 ^ 15 : ℚ) * 10 ^ v.baseExponent < 1 * 10 ^ v.baseExponent :=
    mul_lt_mul_of_pos_right (by norm_num) hp
  exact ⟨(floor_units_bounds amount.toRat v.baseExponent).1, by
    linarith [floor_units_error_le_of_canonical amount hc v.baseExponent v.baseExponent_bounds.2.1 hrpos]⟩

/-- Proof body of the integral line of `LoanBroker.coverDeposit_credit`. -/
lemma LoanBroker.coverDeposit_credit_integral_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit pool amount).run = .ok (.ok res))
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hat : amount.mNumericType = lb.numericType) (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable + amount.toRat < 2 ^ 63) :
    res.loanBroker'.toExact.coverAvailable - lb.toExact.coverAvailable = amount.toRat := by
  have hnt : lb.numericType.isIntegral = true := by rw [← hat]; exact hint.is_integral
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb pool amount res hok
  obtain ⟨aN, hnum, hs, -⟩ := LoanBroker.roundedCoverAmount_ok lb pool amount r hrr
  obtain ⟨hv, hn⟩ := STAmount.toNumber_exact_of amount aN (Or.inr ⟨hint, hsz⟩) hnum
  unfold sumRoundAndSubtract at hs
  rw [if_pos hnt] at hs
  simp only [bind_pure] at hs
  have hden : aN.toRat.den = 1 := by rw [hv]; exact STAmount.IntegralCanonical.den_eq_one amount hint
  have hrv : r.toRat = amount.toRat := by rw [STAmount.ofNumber_integral_exact _ _ _ r hnt hn hden hs, hv]
  -- the credit counts the same units as the amount
  have hicr := (STAmount.ofNumber_integral_canonical _ _ _ r hnt hs).1
  have hszr : r.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have hr := STAmount.abs_toRat r
    have ha := STAmount.abs_toRat amount
    rw [hicr.offset_zero, zpow_zero, mul_one] at hr
    rw [hint.offset_zero, zpow_zero, mul_one] at ha
    have he : (r.mValue.toNat : ℚ) = amount.mValue.toNat := by rw [← hr, ← ha, hrv]
    have := Nat.cast_injective he
    omega
  have hden' := Rat.den_one_add _ _ hcint (STAmount.IntegralCanonical.den_eq_one _ hint)
  have hcov : 0 ≤ lb.toExact.coverAvailable := lb.exact.coverAvailable_nonneg
  have habs := STAmount.IntegralCanonical.abs_toRat_le_of_mValue_le amount hint hsz
  obtain ⟨hcv, -⟩ := LoanBroker.applyCoverTransaction_credit_value lb r res happ (Or.inr ⟨hicr, hszr⟩)
    (by rw [hrv]; exact Number.exists_of_int _ hden' (by linarith [neg_abs_le amount.toRat]) hbound)
  rw [hcv, hrv]
  ring

end XRPL.Model.Lending
