import XRPL.Properties.Lending.LoanBroker.Common.WithdrawExits
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawFloor
import XRPL.Properties.Lending.LoanBroker.Common.MaxValueFits

/-! # Proof bodies for the `LoanBroker.coverWithdraw` theorems

Proofs for the theorems in `LoanBrokerCoverWithdraw.lean`: what a withdrawal debits on any lawful
broker, and exactly on a reachable one. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

variable {α : Type} [AssetPool α]

/-- Proof body of `coverWithdraw_decreases_cover`. -/
lemma LoanBroker.coverWithdraw_decreases_cover_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw pool amount).run = .ok (.ok res))
    (hc : amount.Canonical)
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80) :
    res.loanBroker'.toExact.coverAvailable ≤ lb.toExact.coverAvailable := by
  obtain ⟨a, hcl, happ⟩ := LoanBroker.coverWithdraw_ok_inv lb pool amount res hok
  obtain ⟨hac, -, ha0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ a _
    (STAmount.CanonicalOrZero.operator_neg (Or.inl hc)) hb.1 hb.2 hcl
  exact LoanBroker.applyCoverTransaction_debit_le lb a res hac ha0 happ

/-- Proof body of `coverWithdraw_total`. -/
lemma LoanBroker.coverWithdraw_total_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS) :
    ∃ a res, clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent pool) = .ok a ∧
      (lb.coverWithdraw pool amount).run = .ok (.ok res) ∧ res.amount' = a := by
  obtain ⟨a, aN, c', hcl, -, hnum, hge, hsub, -⟩ := LoanBroker.canCoverWithdraw_ok lb pool amount hcan
  obtain ⟨lb', hres, -⟩ := LoanBroker.coverWithdraw_success_proof lb pool amount a aN c' hcl hnum hge hsub
  exact ⟨a, ⟨a, lb'⟩, hcl, hres, rfl⟩

/-- Proof body of `coverWithdraw_keeps_minimum`. -/
lemma LoanBroker.coverWithdraw_keeps_minimum_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hcan : lb.canCoverWithdraw pool amount = .ok .tesSUCCESS)
    (hok : (lb.coverWithdraw pool amount).run = .ok (.ok res)) :
    res.loanBroker'.HasMinimumCover (AssetPool.baseExponent pool) := by
  obtain ⟨a, aN, c', hcl, -, hnum, -, hsub, hmin⟩ := LoanBroker.canCoverWithdraw_ok lb pool amount hcan
  obtain ⟨a2, hcl2, happ⟩ := LoanBroker.coverWithdraw_ok_inv lb pool amount res hok
  rw [hcl, Except.ok.injEq] at hcl2
  subst hcl2
  obtain ⟨m, c2, hm, hsub2, -, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb a res happ
  rw [hnum, Except.ok.injEq] at hm
  subst hm
  rw [hsub, Except.ok.injEq] at hsub2
  subst hsub2
  unfold LoanBroker.HasMinimumCover
  rw [hraw]
  exact hmin

/-- Proof body of the floored payout part of `LoanBroker.coverWithdraw_debit`. -/
lemma LoanBroker.coverWithdraw_amount_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (v : Vault) (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (amount : STAmount) (hc : amount.Canonical) (hat : amount.mNumericType = lb.numericType)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    res.amount'.toRat = (⌊amount.toRat / 10 ^ base⌋ : ℚ) * 10 ^ base := by
  have hz : lb.OpenZone v.baseExponent := hvb ▸ LoanBroker.Reachable.openZone_proof lb base hr hmax
  rw [← hvb]
  exact LoanBroker.coverWithdraw_floor lb v amount res hz hnt hc hat hpos hcan hok

/-- Proof body of the debit part of `LoanBroker.coverWithdraw_debit`. -/
lemma LoanBroker.coverWithdraw_debit_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (amount : STAmount) (hc : amount.Canonical)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = res.amount'.toRat := by
  have hz : lb.OpenZone v.baseExponent := hvb ▸ LoanBroker.Reachable.openZone lb base hr
  obtain ⟨-, -, -, -, -, hcov⟩ := LoanBroker.coverWithdraw_exact lb v amount res hz hc hpos hcan hok
  rw [hcov]; ring

/-- Proof body of the at-most-the-amount part of `LoanBroker.coverWithdraw_debit`. -/
lemma LoanBroker.coverWithdraw_debit_le_amount_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (hvb : v.baseExponent = base) (amount : STAmount) (hc : amount.Canonical)
    (hpos : 0 < amount.toRat) (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable ≤ amount.toRat := by
  have hz : lb.OpenZone v.baseExponent := hvb ▸ LoanBroker.Reachable.openZone lb base hr
  obtain ⟨-, -, -, hle, -, hcov⟩ := LoanBroker.coverWithdraw_exact lb v amount res hz hc hpos hcan hok
  rw [hcov]; linarith

/-- Proof body of the XRP or MPT part of `LoanBroker.coverWithdraw_debit`. -/
lemma LoanBroker.coverWithdraw_debit_integral_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hok : (lb.coverWithdraw pool amount).run = .ok (.ok res))
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ amount.toRat) (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63) :
    lb.toExact.coverAvailable - res.loanBroker'.toExact.coverAvailable = amount.toRat := by
  obtain ⟨a, hcl, happ⟩ := LoanBroker.coverWithdraw_ok_inv lb pool amount res hok
  obtain ⟨hic, hval, hrat⟩ := clampToSumExponent_neg_integral _ _ _ _ hint hcl
  rw [abs_of_nonneg hnn] at hrat
  obtain ⟨hv, -⟩ := LoanBroker.applyCoverTransaction_debit_integral lb a res happ hic (by rw [hval]; exact hsz)
    (by rw [hrat]; exact hnn) hcint hbound
  rw [hv, hrat]
  ring

end XRPL.Model.Lending
