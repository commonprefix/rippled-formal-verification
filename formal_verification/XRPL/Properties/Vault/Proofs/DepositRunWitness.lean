import XRPL.Properties.Vault.Common.DepositRunDefs
import XRPL.Properties.Vault.Proofs.DilutionWitness

/-! # Witnesses for a run of deposits on an IOU vault

100 deposits of 0.03 into a Scale 2 vault are each charged 0.02, so redeeming their 200 shares pays more than the
deposits were charged, and the per-share value falls. -/

set_option linter.style.native false

namespace XRPL.Model.SingleAssetVault.DilWit

open XRPL.Model.Protocol

/-- The vault: a deposit of 70 and a donation of 30 at Scale 2. -/
def vE : Vault :=
  createHistory.vault Vault.placeholder .fractional 2 none none 0
    [(iouAmount 7000000000000000 (-14), false), (iouAmount 3000000000000000 (-14), true)]

lemma vE_reach : Vault.Reachable vE 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

/-- A deposit of 0.03. -/
def xE : STAmount := iouAmount 3000000000000000 (-17)

/-- The 200 shares the deposits issue. -/
def sharesE : STAmount := int64Amount 200

/-- `k` more deposits of `amount` at close time `t` from `u`, with `charged`, `shares` and `n` so far. -/
def depositsRun (amount : STAmount) (t : UInt32) (u : Vault) (charged shares : ℚ) (n : ℕ) :
    ℕ → Option (Vault × ℚ × ℚ × ℕ)
  | 0 => some (u, charged, shares, n)
  | k + 1 =>
    if hpos : 0 < amount.toRat then
      match (u.deposit amount false t hpos).run with
      | .ok (.ok r) =>
        if amount.canonicalB && decide (amount.mNumericType = u.numericType) then
          depositsRun amount t r.vault' (charged + r.assets.toRat) (shares + r.shares.toRat) (n + 1) k
        else none
      | _ => none
    else none

lemma depositsRun_sound (v : Vault) (amount : STAmount) (t : UInt32) :
    ∀ (k : ℕ) (u w : Vault) (charged shares charged' shares' : ℚ) (n n' : ℕ),
      Vault.DepositRun v t u charged shares n →
      depositsRun amount t u charged shares n k = some (w, charged', shares', n') →
      Vault.DepositRun v t w charged' shares' n' := by
  intro k
  induction k with
  | zero =>
    intro u w charged shares charged' shares' n n' hu h
    simp only [depositsRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact hu
  | succ k ih =>
    intro u w charged shares charged' shares' n n' hu h
    unfold depositsRun at h
    split at h
    case isFalse => cases h
    rename_i hpos
    split at h
    case h_2 => cases h
    rename_i r hr
    split at h
    case isFalse => cases h
    rename_i hck
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
    exact ih _ _ _ _ _ _ _ _
      (Vault.DepositRun.deposit u charged shares n amount r hu (STAmount.canonical_of_canonicalB _ hck.1) hck.2
        hpos hr) h

/-- 100 deposits of 0.03, then a redemption of the 200 shares they issue that pays more than they were charged,
and per-share value lower after the deposits. -/
def runCheck : Bool :=
  match depositsRun xE 0 vE 0 0 0 100 with
  | some (w, charged, shares, n) =>
    if hpos : 0 < (WithdrawAmount.vaultShares sharesE).amount.toRat then
      match (w.withdraw (.vaultShares sharesE) false 0 hpos).run with
      | .ok (.ok r) =>
        decide (shares = sharesE.toRat) && decide (1 < n) && decide (charged < r.assets.toRat) &&
          decide (w.withdrawNav / (w.toExact.sharesTotal : ℚ) < vE.withdrawNav / (vE.toExact.sharesTotal : ℚ))
      | _ => false
    else false
  | none => false

lemma runCheck_true : runCheck = true := by native_decide

end XRPL.Model.SingleAssetVault.DilWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DilWit

/-- The run of 100 deposits of 0.03 and the redemption of their 200 shares. -/
lemma Vault.deposits_run_witness :
    ∃ (w : Vault) (charged : ℚ) (n : ℕ) (hpos : 0 < (WithdrawAmount.vaultShares sharesE).amount.toRat)
      (r : VaultWithAmounts),
      Vault.DepositRun vE 0 w charged sharesE.toRat n ∧ 1 < n ∧
      (w.withdraw (.vaultShares sharesE) false 0 hpos).run = .ok (.ok r) ∧ charged < r.assets.toRat ∧
      w.withdrawNav / (w.toExact.sharesTotal : ℚ) < vE.withdrawNav / (vE.toExact.sharesTotal : ℚ) := by
  have h := runCheck_true
  unfold runCheck at h
  split at h
  case h_2 => cases h
  rename_i w charged shares n hrun
  split at h
  case isFalse => cases h
  rename_i hpos
  split at h
  case h_2 => cases h
  rename_i r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs, hn⟩, hgain⟩, hnav⟩ := h
  have hd := depositsRun_sound vE xE 0 100 vE w 0 0 charged shares 0 n Vault.DepositRun.nil hrun
  rw [hs] at hd
  exact ⟨w, charged, n, hpos, r, hd, hn, hr, hgain, hnav⟩

/-- Proof body of `deposits_withdraw_roundtrip_attained`. -/
lemma Vault.deposits_withdraw_roundtrip_witness :
    ∃ (v w : Vault) (t0 t : UInt32) (n : ℕ) (charged : ℚ) (shares : STAmount)
      (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (r : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ Vault.DepositRun v t w charged shares.toRat n ∧ 1 < n ∧
      (w.withdraw (.vaultShares shares) false t hpos).run = .ok (.ok r) ∧ charged < r.assets.toRat := by
  obtain ⟨w, charged, n, hpos, r, hd, hn, hr, hgain, -⟩ := Vault.deposits_run_witness
  exact ⟨vE, w, 0, 0, n, charged, sharesE, hpos, r, vE_reach, UInt32.le_refl 0, hd, hn, hr, hgain⟩

/-- Proof body of `ReachableFromIn.dilution_deposit_attained`. -/
lemma Vault.ReachableFromIn.dilution_deposit_witness :
    ∃ (v : Vault) (t0 t : UInt32) (n : ℕ) (w : Vault) (charged shares : ℚ),
      Vault.Reachable v t0 ∧ Vault.DepositRun v t w charged shares n ∧ Vault.ReachableFromIn false v t w n ∧
      1 < n ∧ w.withdrawNav / (w.toExact.sharesTotal : ℚ) < v.withdrawNav / (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨w, charged, n, -, -, hd, hn, -, -, hnav⟩ := Vault.deposits_run_witness
  exact ⟨vE, 0, 0, n, w, charged, _, vE_reach, hd, hd.reachableFromIn, hn, hnav⟩

end XRPL.Model.SingleAssetVault
