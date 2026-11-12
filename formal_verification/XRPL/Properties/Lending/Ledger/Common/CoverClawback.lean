import XRPL.Properties.Lending.Ledger.Common.BrokerProofs
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy

/-! # A cover clawback on the lending ledger

Every broker's CoverAvailable is whole base units, so below `10^16` of them the clawback of `ClawbackAccuracy.lean`
is exact: a full clawback leaves the minimum cover, and no clawback leaves less. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A cover clawback that passed its preflight names no amount, or an amount of the vault's asset that is canonical
or zero and not negative. -/
private lemma LendingTx.preflight_coverClawback_request (l : LendingLedger) (hasset : Vault.HoldsAsset l.vault)
    (j : Nat) (amount : Option STAmount)
    (hpre : (LendingTx.loanBrokerCoverClawback j amount).preflight l = .tesSUCCESS) :
    ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = l.vault.numericType ∧ 0 ≤ a.toRat := by
  intro a ha
  rw [Option.mem_def] at ha
  subst ha
  have hc : (isCanonicalAmount a l.vault.numericType && !a.mIsNegative) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hc
  have hty : a.mNumericType = l.vault.numericType := by
    have h := hc.1
    unfold isCanonicalAmount at h
    rw [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  refine ⟨?_, hty, STAmount.toRat_nonneg_of a hc.2⟩
  by_cases hz : a.isZero = true
  · exact Or.inr hz
  · have hnz : a.mValue ≠ 0 := by simpa [STAmount.isZero] using hz
    exact Or.inl (isCanonicalAmount_canonical a _ hasset.maxValue_le hc.1 hnz).1

/-- Proof body of `Lending.coverClawback_minimum`. -/
lemma LendingLedger.coverClawback_minimum_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger)
    (j : Nat) (amount : Option STAmount) (h : (l.apply (.loanBrokerCoverClawback j amount)).run = .ok (.ok l'))
    (b b' : LoanBroker) (hb : l.broker? j = some b) (hb' : l'.broker? j = some b') (r : LoanBrokerCoverResult)
    (hok : (b.coverClawback l.vault amount).run = .ok (.ok r)) (m : Number)
    (hmin : minimumBrokerCover b.numericType b.debtTotal b.coverRateMinimum l.vault.baseExponent = .ok m)
    (hlt : b.coverAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ((amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) →
      r.amount'.toRat = b.coverAvailable.toRat - m.toRat ∧ b'.coverAvailable.toRat = m.toRat) ∧
    m.toRat ≤ b'.coverAvailable.toRat := by
  have hpre := (LendingLedger.apply_checked h).1
  have hpre' : (LendingTx.loanBrokerCoverClawback j amount).preflight l = .tesSUCCESS :=
    (TER.isTesSuccess_iff _).mp hpre
  have hbnt := hr.scaleInv.brokers j b hb
  have hnt : l.vault.numericType = b.numericType := hbnt.symm
  have hmax : b.numericType.isIntegral = true → b.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hbnt]; exact hr.holdsAsset.maxValue_le
  have hreq : ∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = b.numericType ∧ 0 ≤ a.toRat := by
    intro a ha
    rw [hbnt]
    exact LendingTx.preflight_coverClawback_request l hr.holdsAsset j amount hpre' a ha
  have hf : b.CoverFits l.vault.baseExponent := ⟨hr.cover_onGrid hb, hlt⟩

  -- the ledger stores the broker the clawback returns
  have hbr : b' = r.loanBroker' := by
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker rfl h
    simp only [LendingLedger.applyBroker] at hu
    unfold_ter at hu
    walk_ok
    rename_i _ b₀ hb₀ _ _ _ _ _ _ _ _ r₀ hcl
    obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
    have hcl : (b₀.coverClawback l.vault amount).run = .ok (.ok r₀) := hcl
    obtain rfl : r₀ = r := Except.ok.inj (Except.ok.inj (hcl.symm.trans hok))
    rw [LendingLedger.broker?_commitBroker, if_pos (by simp [LendingLedger.broker?_lt hb₀])] at hb'
    exact (Option.some.inj hb').symm
  subst hbr
  refine ⟨fun hall => ⟨?_, ?_⟩, ?_⟩
  · exact LoanBroker.roundedCoverClawback_all_proof b l.vault amount r m hf hnt hmax hreq hall hmin hok
  · exact LoanBroker.coverClawback_all_leaves_minimum_proof b l.vault amount r m hf hnt hmax hreq hall hmin hok
  · exact LoanBroker.coverClawback_keeps_minimum_proof b l.vault amount r m hf hnt hmax hreq hmin hok

end XRPL.Model.Lending
