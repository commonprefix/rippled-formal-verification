import XRPL.Properties.Vault.Proofs.Support.ReachableHistory

/-! # Witness for a withdrawal above the XRP range

The run's result is computed by the model and checked by `native_decide`. The vault comes from a reachable
history: a create, then one deposit.

An XRP vault of 100 drops and 100 shares. A withdrawal of `10^17 + 1` shares is worth `10^17 + 1` drops, one drop
above the largest XRP amount, so pricing it ends in an error before the holder's shares are checked. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.WithdrawRangeWit

open XRPL.Model.Protocol

/-- An XRP vault of 100 drops and 100 shares. -/
def vXrp : Vault :=
  createHistory.vault Vault.placeholder NumericType.native 0 none none 0
    [(⟨NumericType.native, 100, 0, false⟩, false)]

lemma vXrp_reach : Vault.Reachable vXrp 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

/-- `10^17 + 1` shares, worth one drop more than the largest XRP amount. -/
def sharesBig : STAmount := ⟨.int64, 100000000000000001, 0, false⟩

lemma sharesBig_pos : 0 < (WithdrawAmount.vaultShares sharesBig).amount.toRat := by native_decide

end XRPL.Model.SingleAssetVault.WithdrawRangeWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WithdrawRangeWit

/-- Withdrawal by shares on a reachable XRP vault, worth more than the largest XRP amount -> an error, not a result
code. -/
lemma Vault.withdraw_out_of_range_witness :
    ∃ (v : Vault) (t0 t : UInt32) (amount : WithdrawAmount) (waive : Bool) (hpos : 0 < amount.amount.toRat),
      Vault.Reachable v t0 ∧ amount.amount.Canonical ∧
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (v.withdraw amount waive t hpos).run = .error .outOfRange :=
  ⟨vXrp, 0, 0, .vaultShares sharesBig, false, sharesBig_pos, vXrp_reach,
    STAmount.canonical_of_canonicalB _ (by native_decide), fun _ => by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
