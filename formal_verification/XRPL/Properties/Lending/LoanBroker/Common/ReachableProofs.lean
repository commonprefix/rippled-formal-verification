import XRPL.Properties.Lending.LoanBroker.Common.ReachableDefs
import XRPL.Properties.Lending.LoanBroker.Common.Create
import XRPL.Properties.Lending.LoanBroker.Common.CoverReduction

/-! # Reachability induction proofs

Proofs for the reachability theorems, by induction over the operations. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- `update` only changes `debtMaximum`: it keeps the fixed fields and
`coverAvailable`. -/
private lemma LoanBroker.update_fixed_fields (lb lb' : LoanBroker) (dm : Option Number)
    (hok : lb.update dm = .ok lb') :
    LoanBroker.SameFixedFields lb lb' ∧ lb'.coverAvailable = lb.coverAvailable := by
  rw [LoanBroker.update_eq] at hok
  have h := (RawLoanBroker.to_lawful_ok hok).1
  have e1 := congrArg RawLoanBroker.numericType h
  have e2 := congrArg RawLoanBroker.debtTotal h
  have e3 := congrArg RawLoanBroker.loanCount h
  have e4 := congrArg RawLoanBroker.managementFeeRate h
  have e5 := congrArg RawLoanBroker.coverRateMinimum h
  have e6 := congrArg RawLoanBroker.coverRateLiquidation h
  have e7 := congrArg RawLoanBroker.coverAvailable h
  exact ⟨⟨e1, e2, e3, e4, e5, e6⟩, e7⟩

/-- No operation changes the numeric type, `debtTotal`, `loanCount` or the rates:
a broker reachable from `start` keeps all of them. -/
lemma LoanBroker.ReachableFrom.fixed_fields (base : Int) (start lb : LoanBroker)
    (hr : LoanBroker.ReachableFrom base start lb) : LoanBroker.SameFixedFields start lb := by
  induction hr with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | update lb lb' _ dm _ _ _ _ hok ih =>
    exact ih.trans (LoanBroker.update_fixed_fields lb lb' dm hok).1
  | coverDeposit lb v amount res _ _ _ _ _ _ _ _ hok ih =>
    exact ih.trans (LoanBroker.coverDeposit_fixed_fields lb v amount res hok)
  | coverWithdraw lb v amount res _ _ _ _ _ _ _ hok ih =>
    exact ih.trans (LoanBroker.coverWithdraw_fixed_fields lb v amount res hok)
  | coverClawback lb v amount res _ _ _ _ _ hok ih =>
    exact ih.trans (LoanBroker.coverClawback_fixed_fields lb v amount res hok)

/-- Proof body of the DebtTotal line of `LoanBroker.Reachable.broker_fields`. -/
lemma LoanBroker.Reachable.debtTotal_zero_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base) :
    lb.debtTotal = Number.zero := by
  obtain ⟨v, tx, start, _, _, hc, hrf⟩ := hr
  rw [(LoanBroker.ReachableFrom.fixed_fields base start lb hrf).debtTotal]
  exact (LoanBroker.create_no_exposure_proof tx _ start hc).1

/-- Proof body of the LoanCount line of `LoanBroker.Reachable.broker_fields`. -/
lemma LoanBroker.Reachable.loanCount_zero_proof (lb : LoanBroker) (base : Int) (hr : lb.Reachable base) :
    lb.loanCount = 0 := by
  obtain ⟨v, tx, start, _, _, hc, hrf⟩ := hr
  rw [(LoanBroker.ReachableFrom.fixed_fields base start lb hrf).loanCount]
  exact (LoanBroker.create_no_exposure_proof tx _ start hc).2.2

/-- Proof body of the rates line of `LoanBroker.Reachable.broker_fields`. -/
lemma LoanBroker.ReachableFrom.creation_rates_proof (tx : LoanBrokerSetCreate) (nt : NumericType)
    (base : Int) (start lb : LoanBroker) (hc : LoanBroker.create tx nt = .ok start)
    (hr : LoanBroker.ReachableFrom base start lb) :
    lb.managementFeeRate = tx.managementFeeRate.getD 0 ∧
      lb.coverRateMinimum = tx.coverRateMinimum.getD 0 ∧
      lb.coverRateLiquidation = tx.coverRateLiquidation.getD 0 := by
  have hf := LoanBroker.ReachableFrom.fixed_fields base start lb hr
  unfold LoanBroker.create at hc
  have h := (RawLoanBroker.to_lawful_ok hc).1
  refine ⟨?_, ?_, ?_⟩
  · rw [hf.managementFeeRate]; show start.toRawLoanBroker.managementFeeRate = _; rw [h]; rfl
  · rw [hf.coverRateMinimum]; show start.toRawLoanBroker.coverRateMinimum = _; rw [h]; rfl
  · rw [hf.coverRateLiquidation]; show start.toRawLoanBroker.coverRateLiquidation = _; rw [h]; rfl

/-- A deposit that passes its checks keeps a broker reachable. -/
lemma LoanBroker.Reachable.coverDeposit_step (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (hc : amount.Canonical)
    (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    (hcap : lb.numericType.isIntegral = true →
      lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    res.loanBroker'.Reachable base := by
  obtain ⟨v0, tx, start, hv0, hcreate, hc0, hrf⟩ := hr
  exact ⟨v0, tx, start, hv0, hcreate, hc0,
    .coverDeposit lb v amount res hrf hvb hnt hc hat hpos hcap hcan hok⟩

/-- A withdrawal that passes its checks keeps a broker reachable. -/
lemma LoanBroker.Reachable.coverWithdraw_step (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (amount : STAmount) (res : LoanBrokerCoverResult)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType) (hc : amount.Canonical)
    (hat : amount.mNumericType = lb.numericType) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    res.loanBroker'.Reachable base := by
  obtain ⟨v0, tx, start, hv0, hcreate, hc0, hrf⟩ := hr
  exact ⟨v0, tx, start, hv0, hcreate, hc0,
    .coverWithdraw lb v amount res hrf hvb hnt hc hat hpos hcan hok⟩

/-- A clawback that passes its checks keeps a broker reachable. -/
lemma LoanBroker.Reachable.coverClawback_step (lb : LoanBroker) (base : Int) (hr : lb.Reachable base)
    (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hvb : v.baseExponent = base) (hnt : v.numericType = lb.numericType)
    (hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat)
    (hcan : lb.canCoverClawback v amount = .ok .tesSUCCESS)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    res.loanBroker'.Reachable base := by
  obtain ⟨v0, tx, start, hv0, hcreate, hc0, hrf⟩ := hr
  exact ⟨v0, tx, start, hv0, hcreate, hc0,
    .coverClawback lb v amount res hrf hvb hnt hreq hcan hok⟩

end XRPL.Model.Lending
