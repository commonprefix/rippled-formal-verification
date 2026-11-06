import XRPL.Properties.Protocol.Common.Errors
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback

/-! # Errors of the vault helpers

The pricing, dust and cash-update steps of the vault transactions only pass on Protocol errors.
`notLawful` comes from the final `to_lawful` re-check alone. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma RawVault.assetsTotal_ne_notLawful (rv : RawVault) : rv.assetsTotal ≠ .error .notLawful :=
  Number.operator_add_ne_notLawful _ _ _

lemma Vault.assetsTotalForWithdrawal_ne_notLawful (v : Vault) (waive : Bool) :
    v.assetsTotalForWithdrawal waive ≠ .error .notLawful := by
  unfold Vault.assetsTotalForWithdrawal
  simp only [bind, Except.bind]
  split_ne_notLawful [RawVault.assetsTotal_ne_notLawful, Number.operator_sub_ne_notLawful]

lemma Vault.sharesToAssetsWithdraw_ne_notLawful (v : Vault) (shares : STAmount) (waive : Bool) :
    v.sharesToAssetsWithdraw shares waive ≠ .error .notLawful := by
  unfold Vault.sharesToAssetsWithdraw
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Vault.assetsTotalForWithdrawal_ne_notLawful, STAmount.toNumber_ne_notLawful,
    Number.operator_mul_ne_notLawful, Number.operator_div_ne_notLawful, STAmount.ofNumber_ne_notLawful]

lemma assetsToSharesWithdraw_ne_notLawful (v : Vault) (assets : STAmount) (truncateShares waive : Bool) :
    assetsToSharesWithdraw v assets truncateShares waive ≠ .error .notLawful := by
  unfold assetsToSharesWithdraw
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [Vault.assetsTotalForWithdrawal_ne_notLawful, STAmount.toNumber_ne_notLawful,
    Number.operator_mul_ne_notLawful, Number.operator_div_ne_notLawful, Number.truncate_ne_notLawful,
    STAmount.ofNumber_ne_notLawful]

lemma computeWithdraw_ne_notLawful (v : Vault) (amount : WithdrawAmount) (waive : Bool) :
    (computeWithdraw v amount waive).run ≠ .error .notLawful := by
  intro h
  simp only [computeWithdraw] at h
  unfold_ter at h
  walk_ok
  all_goals simp_all [assetsToSharesWithdraw_ne_notLawful, Vault.sharesToAssetsWithdraw_ne_notLawful]

lemma Vault.checkDebitNotDust_ne_notLawful (v : Vault) (amount : Number) :
    v.checkDebitNotDust amount ≠ .error .notLawful := by
  intro h
  simp only [Vault.checkDebitNotDust] at h
  unfold_ter at h
  walk_ok
  all_goals simp_all [Number.operator_sub_ne_notLawful, STAmount.ofNumber_ne_notLawful]

lemma Vault.adjustBalances_ne_notLawful (v : Vault) (change : Lending.PoolBalanceChange) :
    (v.adjustBalances change).run ≠ .error .notLawful := by
  intro h
  simp only [Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  all_goals simp_all [Number.operator_add_ne_notLawful, STAmount.roundToNumericType_ne_notLawful]

lemma Vault.adjustAssetsAndShares_ne_notLawful (v : Vault) (assets shares : STAmount) :
    (v.adjustAssetsAndShares assets shares).run ≠ .error .notLawful := by
  intro h
  simp only [Vault.adjustAssetsAndShares] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | simp_all [STAmount.toNumber_ne_notLawful, Number.operator_add_ne_notLawful]
    | exact Vault.adjustBalances_ne_notLawful _ _ ‹_›

/-- A lawful record passes the `to_lawful` re-check. -/
lemma RawVault.to_lawful_ne_notLawful {rv : RawVault} (h : rv.WF ∧ rv.Valid) :
    rv.to_lawful ≠ .error .notLawful := by
  obtain ⟨v, hv, -⟩ := RawVault.to_lawful_ok_of h.1 h.2
  rw [hv]; exact nofun

lemma assetsToSharesClawback_ne_notLawful (v : Vault) (assets holderShares : STAmount) (waive : Bool) :
    assetsToSharesClawback v assets holderShares waive ≠ .error .notLawful := by
  unfold assetsToSharesClawback
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_notLawful [STAmount.ofNumber_ne_notLawful, assetsToSharesWithdraw_ne_notLawful]

lemma computeClawback_ne_notLawful (v : Vault) (assets holderShares : STAmount) (waive : Bool) :
    (computeClawback v assets holderShares waive).run ≠ .error .notLawful := by
  intro h
  simp only [computeClawback] at h
  unfold_ter at h
  walk_ok
  all_goals simp_all [assetsToSharesClawback_ne_notLawful, assetsToSharesWithdraw_ne_notLawful,
    Vault.sharesToAssetsWithdraw_ne_notLawful, STAmount.toNumber_ne_notLawful, STAmount.ofNumber_ne_notLawful,
    clampToSumExponent_ne_notLawful, STAmount.isFractionalNonPositive_ne_notLawful]

end XRPL.Model.SingleAssetVault
