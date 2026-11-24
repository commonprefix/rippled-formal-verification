import XRPL.Properties.Vault.Common.ReachableDefs

/-! # A run of deposits by one depositor

A sequence of deposits at one close time, with the total charged and the total shares issued. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- `n` deposits from `v` at close time `t` lead to `w`, charged `charged` and issuing `shares` in total. Each
amount is canonical and of the vault's asset, as C++ guarantees. -/
inductive Vault.DepositRun (v : Vault) (t : UInt32) : Vault → ℚ → ℚ → ℕ → Prop where
  | nil : Vault.DepositRun v t v 0 0 0
  | deposit (u : Vault) (charged shares : ℚ) (n : ℕ) (amount : STAmount) (r : VaultWithAmounts) :
      Vault.DepositRun v t u charged shares n →
      amount.Canonical → amount.mNumericType = u.numericType →
      (hpos : 0 < amount.toRat) → (u.deposit amount false t hpos).run = .ok (.ok r) →
      Vault.DepositRun v t r.vault' (charged + r.assets.toRat) (shares + r.shares.toRat) (n + 1)

/-- A run of deposits is a sequence of vault transactions. -/
lemma Vault.DepositRun.reachableFromIn {v w : Vault} {t : UInt32} {charged shares : ℚ} {n : ℕ}
    (h : Vault.DepositRun v t w charged shares n) : Vault.ReachableFromIn false v t w n := by
  induction h with
  | nil => exact Vault.ReachableFromIn.refl v t
  | deposit u charged shares n amount r _ hc hty hpos hok ih =>
    exact Vault.ReachableFromIn.deposit v u t t n amount false r ih (UInt32.le_refl t) hc hty hpos hok
      (fun h => absurd h (by decide))

end XRPL.Model.SingleAssetVault
