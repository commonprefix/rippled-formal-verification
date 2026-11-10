import XRPL.Properties.Lending.Common.Walk
import XRPL.Properties.Lending.Ledger.Defs
import XRPL.Properties.Protocol.Common.Wrap
import XRPL.Properties.Vault.Proofs.Support.Wrap

/-! # The vault transactions never wrap around

A vault transaction runs Number and STAmount operations and the vault's re-check, and none of them wraps. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.openLimit_ne_wrap (v : Vault) : v.openLimit ≠ .error .wrap :=
  Number.from_rep_ne_wrap _ _ _ _ largeRange_min_toNat_le

lemma Vault.exceedsOpenLimit_ne_wrap (v : Vault) (x : Number) (hx : x.isNormalized) :
    v.exceedsOpenLimit x ≠ .error .wrap := by
  unfold Vault.exceedsOpenLimit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [RawVault.assetsTotal_ne_wrap, Number.operator_add_ne_wrap, Vault.openLimit_ne_wrap]

lemma Vault.checkOpenLimit_ne_wrap (v : Vault) (amount : STAmount) (ha : amount.mValue.toNat < 2 ^ 63) :
    v.checkOpenLimit amount ≠ .error .wrap := by
  unfold Vault.checkOpenLimit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [RawVault.assetsTotal_ne_wrap, STAmount.toNumber_ne_wrap, postSumExponent_ne_wrap,
    Vault.exceedsOpenLimit_ne_wrap]

lemma Vault.roundedDepositAmount_ne_wrap (v : Vault) (amount : STAmount) (ha : amount.mValue.toNat < 2 ^ 63) :
    (v.roundedDepositAmount amount).run ≠ .error .wrap := by
  intro h
  simp only [Vault.roundedDepositAmount] at h
  unfold_ter at h
  walk_ok
  all_goals close_wrap [RawVault.assetsTotal_ne_wrap, clampToSumExponent_ne_wrap]

lemma Vault.roundedDepositAmount_mValue_lt {v : Vault} {amount r : STAmount} (ha : amount.mValue.toNat < 2 ^ 63)
    (h : (v.roundedDepositAmount amount).run = .ok (.ok r)) : r.mValue.toNat < 2 ^ 63 := by
  simp only [Vault.roundedDepositAmount] at h
  unfold_ter at h
  walk_ok
  all_goals wrap_side

lemma assetsToSharesDeposit_ne_wrap (v : Vault) (amount : STAmount) (ha : amount.mValue.toNat < 2 ^ 63) :
    assetsToSharesDeposit v amount ≠ .error .wrap := by
  unfold assetsToSharesDeposit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [RawVault.assetsTotal_ne_wrap, Number.normalized_ne_wrap _ _ _ _ _ largeRange_min_toNat_le,
    Number.truncate_ne_wrap, STAmount.ofNumber_ne_wrap, STAmount.toNumber_ne_wrap, Number.operator_mul_ne_wrap,
    Number.operator_div_ne_wrap]

lemma assetsToSharesDeposit_mValue_lt {v : Vault} {amount r : STAmount} (h : assetsToSharesDeposit v amount = .ok r) :
    r.mValue.toNat < 2 ^ 63 := by
  unfold assetsToSharesDeposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals wrap_side

lemma sharesToAssetsDeposit_ne_wrap (v : Vault) (shares : STAmount) (hs : shares.mValue.toNat < 2 ^ 63) :
    sharesToAssetsDeposit v shares ≠ .error .wrap := by
  unfold sharesToAssetsDeposit
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [RawVault.assetsTotal_ne_wrap, STAmount.checked_ne_wrap, STAmount.ofNumber_ne_wrap,
    STAmount.toNumber_ne_wrap, Number.operator_mul_ne_wrap, Number.operator_div_ne_wrap]

lemma sharesToAssetsDeposit_mValue_lt {v : Vault} {shares r : STAmount} (hnt : v.numericType.maxValue.toNat < 2 ^ 63)
    (h : sharesToAssetsDeposit v shares = .ok r) : r.mValue.toNat < 2 ^ 63 := by
  unfold sharesToAssetsDeposit at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals wrap_side

lemma STAmount.operator_gt_ne_wrap (lhs rhs : STAmount) : lhs.operator_gt rhs ≠ .error .wrap := by
  unfold STAmount.operator_gt
  exact STAmount.operator_lt_ne_wrap _ _

lemma computeDeposit_ne_wrap (v : Vault) (amount : STAmount) (isDonation : Bool)
    (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (ha : amount.mValue.toNat < 2 ^ 63) :
    (computeDeposit v amount isDonation).run ≠ .error .wrap := by
  intro h
  simp only [computeDeposit] at h
  unfold_ter at h
  walk_ok
  all_goals close_wrap [assetsToSharesDeposit_ne_wrap, sharesToAssetsDeposit_ne_wrap, STAmount.operator_gt_ne_wrap,
    RawVault.assetsTotal_ne_wrap, clampToSumExponent_ne_wrap, STAmount.isFractionalNonPositive_ne_wrap]

lemma computeDeposit_mValue_lt {v : Vault} {amount : STAmount} {isDonation : Bool} {r : VaultAmounts}
    (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (ha : amount.mValue.toNat < 2 ^ 63)
    (h : (computeDeposit v amount isDonation).run = .ok (.ok r)) :
    r.assets.mValue.toNat < 2 ^ 63 ∧ r.shares.mValue.toNat < 2 ^ 63 := by
  simp only [computeDeposit] at h
  unfold_ter at h
  walk_ok
  all_goals exact ⟨by wrap_side, by wrap_side⟩

/-- A cash update that passed its checks wrote normalized balances. -/
lemma Vault.adjustAssetsAndShares_norm {v : Vault} {assets shares : STAmount} {raw : RawVault}
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.ok raw)) :
    raw.assetsAvailable.isNormalized ∧ raw.assetsDeployed.isNormalized := by
  simp only [Vault.adjustAssetsAndShares, Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  all_goals exact ⟨by wrap_side, by wrap_side⟩

macro_rules
  | `(tactic| wrap_rule) => `(tactic| first
    | (refine (XRPL.Model.SingleAssetVault.computeDeposit_mValue_lt ?_ ?_ (by wrap_hyp)).1 <;> wrap_side)
    | (refine (XRPL.Model.SingleAssetVault.computeDeposit_mValue_lt ?_ ?_ (by wrap_hyp)).2 <;> wrap_side)
    | exact (XRPL.Model.SingleAssetVault.Vault.adjustAssetsAndShares_norm (by wrap_hyp)).1
    | exact (XRPL.Model.SingleAssetVault.Vault.adjustAssetsAndShares_norm (by wrap_hyp)).2)

lemma Vault.deposit_ne_wrap (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (ha : amount.mValue.toNat < 2 ^ 63) :
    (v.deposit amount isDonation t hpos).run ≠ .error .wrap := by
  intro h
  simp only [Vault.deposit] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | (refine Vault.roundedDepositAmount_ne_wrap _ _ ?_ ‹_›; wrap_side)
    | (refine computeDeposit_ne_wrap _ _ _ ?_ ?_ ‹_› <;> wrap_side)
    | (refine Vault.adjustAssetsAndShares_ne_wrap _ _ _ ?_ ?_ ‹_› <;> wrap_side)
    | (refine Vault.checkOpenLimit_ne_wrap _ _ ?_ ‹_›; wrap_side)
    | (refine RawVault.assetsTotal_ne_wrap _ ?_ ?_ ‹_› <;> wrap_side)
    | exact RawVault.to_lawful_ne_wrap _ ‹_›

lemma Vault.deposit_mValue_lt {v : Vault} {amount : STAmount} {isDonation : Bool} {t : UInt32}
    {hpos : 0 < amount.toRat} {r : VaultWithAmounts} (hnt : v.numericType.maxValue.toNat < 2 ^ 63)
    (ha : amount.mValue.toNat < 2 ^ 63) (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    r.shares.mValue.toNat < 2 ^ 63 := by
  simp only [Vault.deposit] at h
  unfold_ter at h
  walk_ok
  all_goals ((try dsimp only); wrap_side)

set_option maxHeartbeats 400000 in
-- the withdrawal has about seventy paths, each closed with its own lemma
lemma Vault.withdraw_ne_wrap (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (held : Option Number) (hnt : v.numericType.maxValue.toNat < 2 ^ 63)
    (ha : amount.amount.mValue.toNat < 2 ^ 63) : (v.withdraw amount waive t hpos held).run ≠ .error .wrap := by
  intro h
  simp only [Vault.withdraw] at h
  unfold_ter at h
  walk_ok
  all_goals wrap_leaf

lemma Vault.withdraw_mValue_lt {v : Vault} {amount : WithdrawAmount} {waive : Bool} {t : UInt32}
    {hpos : 0 < amount.amount.toRat} {held : Option Number} {r : VaultWithAmounts}
    (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (ha : amount.amount.mValue.toNat < 2 ^ 63)
    (h : (v.withdraw amount waive t hpos held).run = .ok (.ok r)) : r.shares.mValue.toNat < 2 ^ 63 := by
  simp only [Vault.withdraw] at h
  unfold_ter at h
  walk_ok
  all_goals ((try dsimp only); wrap_side)

lemma Vault.clawback_ne_wrap (v : Vault) (assets held : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat)
    (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (ha : assets.mValue.toNat < 2 ^ 63)
    (hh : held.mValue.toNat < 2 ^ 63) : (v.clawback assets held waive hnn).run ≠ .error .wrap := by
  intro h
  simp only [Vault.clawback] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | (refine computeClawback_ne_wrap _ _ _ _ ?_ ?_ ?_ ‹_› <;> wrap_side)
    | (refine Vault.adjustAssetsAndShares_ne_wrap _ _ _ ?_ ?_ ‹_› <;> wrap_side)
    | exact RawVault.to_lawful_ne_wrap _ ‹_›
    | close_wrap [STAmount.toNumber_ne_wrap, Vault.checkDebitNotDust_ne_wrap]

lemma Vault.clawback_mValue_lt {v : Vault} {assets held : STAmount} {waive : Bool} {hnn : 0 ≤ assets.toRat}
    {r : VaultWithAmounts} (hnt : v.numericType.maxValue.toNat < 2 ^ 63) (hh : held.mValue.toNat < 2 ^ 63)
    (h : (v.clawback assets held waive hnn).run = .ok (.ok r)) : r.shares.mValue.toNat < 2 ^ 63 := by
  simp only [Vault.clawback] at h
  unfold_ter at h
  walk_ok
  all_goals ((try dsimp only); wrap_side)

lemma Vault.canVaultDelete_ne_wrap (v : Vault) : v.canVaultDelete ≠ .error .wrap := by
  unfold Vault.canVaultDelete
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [RawVault.assetsTotal_ne_wrap]

lemma Vault.canBurnShares_ne_wrap (v : Vault) (amount held : STAmount) :
    (v.canBurnShares amount held).run ≠ .error .wrap := by
  intro h
  simp only [Vault.canBurnShares] at h
  unfold_ter at h
  walk_ok
  exact STAmount.ofNumber_ne_wrap _ _ _ ‹_›

lemma Vault.burnShares_ne_wrap (v : Vault) (held : STAmount) (hh : held.mValue.toNat < 2 ^ 63) :
    (v.burnShares held).run ≠ .error .wrap := by
  intro h
  simp only [Vault.burnShares] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact RawVault.to_lawful_ne_wrap _ ‹_›
    | close_wrap [STAmount.toNumber_ne_wrap, Number.operator_sub_ne_wrap]

lemma Vault.canVaultUpdate_ne_wrap (v : Vault) (am : Option Number) (bd : Option Bool) :
    v.canVaultUpdate am bd ≠ .error .wrap := by
  unfold Vault.canVaultUpdate
  simp only [bind, Except.bind, pure, Except.pure]
  split_ne_wrap [RawVault.assetsTotal_ne_wrap, Number.isOnExponentGrid_ne_wrap]

lemma Vault.update_ne_wrap (v : Vault) (am : Option Number) (bd : Option Bool) :
    v.update am bd ≠ .error .wrap := by
  unfold Vault.update
  exact RawVault.to_lawful_ne_wrap _

end XRPL.Model.SingleAssetVault
