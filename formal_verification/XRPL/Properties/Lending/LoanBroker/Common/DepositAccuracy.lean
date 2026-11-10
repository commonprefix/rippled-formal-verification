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

/-- Proof body of the XRP or MPT line of `LoanBroker.coverDeposit_credit`. -/
lemma LoanBroker.coverDeposit_integral_amount_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hint : lb.numericType.isIntegral = true) (hc : amount.Canonical)
    (hat : amount.mNumericType = lb.numericType) (hok : (lb.coverDeposit pool amount).run = .ok (.ok res)) :
    res.amount'.toRat = amount.toRat := by
  obtain ⟨r, hrr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb pool amount res hok
  obtain ⟨-, -, -, -, hres, -⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  rw [hres]
  obtain ⟨aN, hnum, hs, -⟩ := LoanBroker.roundedCoverAmount_ok lb pool amount r hrr
  obtain ⟨hv, hn⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hc) aN hnum
  unfold sumRoundAndSubtract at hs
  rw [if_pos hint] at hs
  simp only [bind_pure] at hs
  have hic := (hc.1 (by unfold STAmount.integral; rw [hat]; exact hint)).1
  have hden : aN.toRat.den = 1 := by rw [hv]; exact STAmount.IntegralCanonical.den_eq_one amount hic
  rw [STAmount.ofNumber_integral_exact _ _ _ r hint hn hden hs, hv]

/-- Proof body of the deposit line of `LoanBroker.cover_direction`. -/
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

/-- Proof body of the deposit line of `cover_total`. -/
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

/-- Proof body of the deposit line of `LoanBroker.cover_keeps_minimum`. -/
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

/-- Proof body of the floor line of `LoanBroker.coverDeposit_credit`. -/
lemma LoanBroker.coverDeposit_amount_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.amount'.toRat = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base := by
  have hz : lb.OpenZone v.baseExponent := hvb ▸ LoanBroker.Reachable.openZone_proof lb base hr hmax
  rw [LoanBroker.coverDeposit_floor lb v amount res hz hnt hc hat hpos hcan hok, hvb]

end XRPL.Model.Lending
