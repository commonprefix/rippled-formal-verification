import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Concrete reachable histories for the witnesses

A witness runs an operation on a concrete reachable vault. The vault comes from a history the model
computes: a create, then deposits and donations at one close time. Each step checks the input facts
C++ guarantees, so any history the function returns is reachable. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Protocol

/-- `STAmount.Canonical` as a check: a whole amount of its type, or a 16-digit IOU amount. -/
def STAmount.canonicalB (a : STAmount) : Bool :=
  if a.integral then
    a.mOffset == 0 && decide (a.mValue.toNat ≤ a.mNumericType.maxValue.toNat) &&
      decide (a.mNumericType.maxValue.toNat ≤ maxRep.toNat)
  else
    a.mNumericType == .fractional && decide (10 ^ 15 ≤ a.mValue.toNat) && decide (a.mValue.toNat < 10 ^ 16) &&
      decide ((-96 : ℤ) ≤ a.mOffset) && decide (a.mOffset ≤ 80)

lemma STAmount.canonical_of_canonicalB (a : STAmount) (h : a.canonicalB = true) : a.Canonical := by
  unfold STAmount.canonicalB at h
  refine ⟨fun hi => ?_, fun hf => ?_⟩
  · rw [if_pos hi] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨⟨hi, h.1.1, h.1.2⟩, h.2⟩
  · rw [if_neg (by rw [hf]; decide)] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Deposits and donations at close time `t`, each a canonical amount of the vault's asset that keeps
the share issuance within the MPT maximum. -/
def depositHistory (v : Vault) (t : UInt32) : List (STAmount × Bool) → Option Vault
  | [] => some v
  | (a, isDonation) :: rest =>
    if a.canonicalB = true ∧ a.mNumericType = v.numericType then
      if hpos : 0 < a.toRat then
        match (v.deposit a isDonation t hpos).run with
        | .ok (.ok r) =>
          if (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 then depositHistory r.vault' t rest
          else none
        | _ => none
      else none
    else none

lemma depositHistory_reachable (v : Vault) (t : UInt32) (steps : List (STAmount × Bool)) (v' : Vault)
    (hr : Vault.Reachable v t) (h : depositHistory v t steps = some v') : Vault.Reachable v' t := by
  induction steps generalizing v with
  | nil => simp only [depositHistory, Option.some.injEq] at h; rw [← h]; exact hr
  | cons step rest ih =>
    obtain ⟨a, isDonation⟩ := step
    simp only [depositHistory] at h
    split_ifs at h with hc hpos
    split at h
    · rename_i r hrun
      split_ifs at h with hmint
      exact ih r.vault' (Vault.Reachable.deposit v t t a isDonation r hr (UInt32.le_refl t)
        (STAmount.canonical_of_canonicalB a hc.1) hc.2 hpos hrun hmint) h
    · exact absurd h (by simp)

/-- A create at close time `t`, then deposits and donations at the same time. -/
def createHistory (nt : NumericType) (scale : UInt8) (schedule : Option VaultSchedule)
    (earlyExitFeeRate : Option TenthBips32) (t : UInt32) (steps : List (STAmount × Bool)) : Option Vault :=
  if Vault.canCreate (some scale) none schedule t nt = .ok .tesSUCCESS then
    match Vault.create (some scale) none schedule earlyExitFeeRate false nt with
    | .ok v => depositHistory v t steps
    | .error _ => none
  else none

lemma createHistory_reachable (nt : NumericType) (scale : UInt8) (schedule : Option VaultSchedule)
    (earlyExitFeeRate : Option TenthBips32) (t : UInt32) (steps : List (STAmount × Bool)) (v : Vault)
    (h : createHistory nt scale schedule earlyExitFeeRate t steps = some v) : Vault.Reachable v t := by
  unfold createHistory at h
  split_ifs at h with hcan
  split at h
  · rename_i v0 hcr
    exact depositHistory_reachable v0 t steps v
      (Vault.Reachable.create (some scale) none schedule earlyExitFeeRate false nt t v0 hcan hcr) h
  · exact absurd h (by simp)

/-- An empty `int64` vault, the stand-in for a history that fails. -/
def Vault.placeholder : Vault :=
  ⟨{ assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero
     assetsMaximum := none, numericType := .int64, scale := 0, sharesTotal := Number.zero
     lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := none
     earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false },
    by native_decide, by native_decide⟩

/-- The vault a history computes, with any vault standing in when it fails. -/
def createHistory.vault (fallback : Vault) (nt : NumericType) (scale : UInt8)
    (schedule : Option VaultSchedule) (earlyExitFeeRate : Option TenthBips32) (t : UInt32)
    (steps : List (STAmount × Bool)) : Vault :=
  (createHistory nt scale schedule earlyExitFeeRate t steps).getD fallback

lemma createHistory.vault_reachable (fallback : Vault) (nt : NumericType) (scale : UInt8)
    (schedule : Option VaultSchedule) (earlyExitFeeRate : Option TenthBips32) (t : UInt32)
    (steps : List (STAmount × Bool))
    (h : (createHistory nt scale schedule earlyExitFeeRate t steps).isSome = true) :
    Vault.Reachable (createHistory.vault fallback nt scale schedule earlyExitFeeRate t steps) t := by
  unfold createHistory.vault
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  rw [hv, Option.getD_some]
  exact createHistory_reachable nt scale schedule earlyExitFeeRate t steps v hv

end XRPL.Model.SingleAssetVault
