import XRPL.Properties.Lending.LoanBroker.Common.CoverCredit

/-! # Proof bodies for the `LoanBroker.coverDeposit` exits

Proofs for the exits of the deposit's rounding, its Open-limit check and the deposit itself. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

variable {α : Type} [AssetPool α]

/-- Proof body of the precision-loss exit of `LoanBroker.roundedCoverAmount_exits`. -/
lemma LoanBroker.roundedCoverAmount_precision_loss_proof (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (aN : Number) (hnum : amount.toNumber .to_nearest = .ok aN)
    (hr : sumRoundAndSubtract lb.coverAvailable aN (AssetPool.baseExponent pool) lb.numericType .downward = .ok r)
    (hz : r.signum ≤ 0) :
    (lb.roundedCoverAmount pool amount).run = .ok (.error .tecPRECISION_LOSS) := by
  rw [LoanBroker.roundedCoverAmount_run lb pool amount aN r hnum hr, if_pos hz]

/-- Proof body of the rounded exit of `LoanBroker.roundedCoverAmount_exits`. -/
lemma LoanBroker.roundedCoverAmount_rounded_proof (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (aN : Number) (hnum : amount.toNumber .to_nearest = .ok aN)
    (hr : sumRoundAndSubtract lb.coverAvailable aN (AssetPool.baseExponent pool) lb.numericType .downward = .ok r)
    (hpos : 0 < r.signum) :
    (lb.roundedCoverAmount pool amount).run = .ok (.ok r) := by
  rw [LoanBroker.roundedCoverAmount_run lb pool amount aN r hnum hr, if_neg (not_le.mpr hpos)]

/-- Once the rounding succeeds, the deposit check is the Open-limit check of the rounded amount. -/
private lemma LoanBroker.canCoverDeposit_rounded (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (hrounded : (lb.roundedCoverAmount pool amount).run = .ok (.ok r)) :
    lb.canCoverDeposit pool amount = lb.checkCoverOpenLimit pool r := by
  unfold LoanBroker.canCoverDeposit
  rw [hrounded]
  rfl

/-- Proof body of the precision-loss exit of `LoanBroker.canCoverDeposit_exits`. -/
lemma LoanBroker.canCoverDeposit_precision_loss_proof (lb : LoanBroker) (pool : α) (amount : STAmount)
    (hrej : (lb.roundedCoverAmount pool amount).run = .ok (.error .tecPRECISION_LOSS)) :
    lb.canCoverDeposit pool amount = .ok .tecPRECISION_LOSS := by
  unfold LoanBroker.canCoverDeposit
  rw [hrej]
  rfl

/-- Proof body of the scale exit of `LoanBroker.canCoverDeposit_exits`. -/
lemma LoanBroker.canCoverDeposit_scale_exceeded_proof (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (rN : Number) (e : Int) (hrounded : (lb.roundedCoverAmount pool amount).run = .ok (.ok r))
    (hnum : r.toNumber .to_nearest = .ok rN)
    (hps : postSumExponent lb.coverAvailable rN (AssetPool.baseExponent pool) lb.numericType = .ok e)
    (hne : e ≠ AssetPool.baseExponent pool) :
    lb.canCoverDeposit pool amount = .ok .tecLIMIT_EXCEEDED := by
  rw [LoanBroker.canCoverDeposit_rounded lb pool amount r hrounded]
  unfold LoanBroker.checkCoverOpenLimit
  simp [hnum, hps, hne]

/-- Proof body of the Open limit exit of `LoanBroker.canCoverDeposit_exits`. -/
lemma LoanBroker.canCoverDeposit_open_limit_exceeded_proof (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (rN c' limit : Number) (hrounded : (lb.roundedCoverAmount pool amount).run = .ok (.ok r))
    (hnum : r.toNumber .to_nearest = .ok rN)
    (hps : postSumExponent lb.coverAvailable rN (AssetPool.baseExponent pool) lb.numericType =
      .ok (AssetPool.baseExponent pool))
    (hadd : lb.coverAvailable.operator_add rN .towards_zero = .ok c')
    (hlimit : AssetPool.openLimit pool = .ok limit) (hgt : c'.operator_gt limit = true) :
    lb.canCoverDeposit pool amount = .ok .tecLIMIT_EXCEEDED := by
  rw [LoanBroker.canCoverDeposit_rounded lb pool amount r hrounded]
  unfold LoanBroker.checkCoverOpenLimit
  simp [hnum, hps, hadd, hlimit, hgt]

/-- Proof body of the success exit of `LoanBroker.canCoverDeposit_exits`. -/
lemma LoanBroker.canCoverDeposit_success_proof (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (rN c' limit : Number) (hrounded : (lb.roundedCoverAmount pool amount).run = .ok (.ok r))
    (hnum : r.toNumber .to_nearest = .ok rN)
    (hps : postSumExponent lb.coverAvailable rN (AssetPool.baseExponent pool) lb.numericType =
      .ok (AssetPool.baseExponent pool))
    (hadd : lb.coverAvailable.operator_add rN .towards_zero = .ok c')
    (hlimit : AssetPool.openLimit pool = .ok limit) (hgt : c'.operator_gt limit = false) :
    lb.canCoverDeposit pool amount = .ok .tesSUCCESS := by
  rw [LoanBroker.canCoverDeposit_rounded lb pool amount r hrounded]
  unfold LoanBroker.checkCoverOpenLimit
  simp [hnum, hps, hadd, hlimit, hgt]

/-- Proof body of `canCoverDeposit_error_codes`. -/
lemma LoanBroker.canCoverDeposit_error_codes_proof (lb : LoanBroker) (pool : α) (amount : STAmount) (ter : TER)
    (hok : lb.canCoverDeposit pool amount = .ok ter) :
    ter = .tesSUCCESS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED := by
  cases h : (lb.roundedCoverAmount pool amount).run with
  | error e => unfold LoanBroker.canCoverDeposit at hok; rw [h] at hok; cases hok
  | ok x =>
    cases x with
    | error t =>
      rw [LoanBroker.roundedCoverAmount_error_code lb pool amount t h] at h
      rw [LoanBroker.canCoverDeposit_precision_loss_proof lb pool amount h] at hok
      cases hok
      exact Or.inr (Or.inl rfl)
    | ok r =>
      rw [LoanBroker.canCoverDeposit_rounded lb pool amount r h] at hok
      unfold LoanBroker.checkCoverOpenLimit at hok
      unfold_ter at hok
      walk_ok
      all_goals first | exact Or.inl rfl | exact Or.inr (Or.inr rfl)

/-- Proof body of the rejected exit of `LoanBroker.coverDeposit_exits`. -/
lemma LoanBroker.coverDeposit_rejected_proof (lb : LoanBroker) (pool : α) (amount : STAmount) (ter : TER)
    (hrej : (lb.roundedCoverAmount pool amount).run = .ok (.error ter)) :
    (lb.coverDeposit pool amount).run = .ok (.error .tecINTERNAL) := by
  unfold LoanBroker.coverDeposit
  unfold_ter
  rw [show lb.roundedCoverAmount pool amount = .ok (.error ter) from hrej]

/-- Proof body of the success exit of `LoanBroker.coverDeposit_exits`. -/
lemma LoanBroker.coverDeposit_success_proof (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (rN c' : Number) (hrounded : (lb.roundedCoverAmount pool amount).run = .ok (.ok r))
    (hc : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80)
    (hnum : r.toNumber .to_nearest = .ok rN)
    (hadd : lb.coverAvailable.operator_add rN .to_nearest = .ok c') :
    ∃ lb' : LoanBroker, (lb.coverDeposit pool amount).run = .ok (.ok ⟨r, lb'⟩) ∧
      lb'.toRawLoanBroker = { lb.toRawLoanBroker with coverAvailable := c' } := by
  obtain ⟨_, -, -, hpos⟩ := LoanBroker.roundedCoverAmount_ok lb pool amount r hrounded
  obtain ⟨hrv, hrn⟩ := (LoanBroker.roundedCoverAmount_le lb pool amount r hc hnn hb hrounded).2 rN hnum
  have hr0 : 0 ≤ rN.toRat := by rw [hrv]; exact ((STAmount.signum_pos_iff_toRat_pos r).mp hpos).le
  obtain ⟨lb', htl, hraw⟩ := LoanBroker.credit_lawful lb rN c' hrn hr0 hadd
  refine ⟨lb', ?_, hraw⟩
  unfold LoanBroker.coverDeposit
  unfold_ter
  rw [show lb.roundedCoverAmount pool amount = .ok (.ok r) from hrounded]
  simp only
  unfold LoanBroker.applyCoverTransaction
  simp [hnum, hadd, htl]

/-- Proof body of `coverDeposit_error_codes`. -/
lemma LoanBroker.coverDeposit_error_codes_proof (lb : LoanBroker) (pool : α) (amount : STAmount) (ter : TER)
    (hok : (lb.coverDeposit pool amount).run = .ok (.error ter)) : ter = .tecINTERNAL := by
  unfold LoanBroker.coverDeposit at hok
  unfold_ter at hok
  walk_ok
  rfl

end XRPL.Model.Lending
