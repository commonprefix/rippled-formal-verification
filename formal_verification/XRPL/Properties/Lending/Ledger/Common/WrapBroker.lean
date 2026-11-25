import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Ledger.Common.WrapHelpers
import XRPL.Properties.Lending.Ledger.Common.WrapVault

/-! # The broker transactions never wrap around

A broker transaction runs Number and STAmount operations, the vault's balance update and re-checks, and none
of them wraps. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

lemma AssetPool.assetsTotal_ne_wrap (v : Vault) : AssetPool.assetsTotal v ≠ .error .wrap := by
  intro h; rw [Vault.pool_assetsTotal] at h; wrap_leaf

lemma AssetPool.assetsTotal_isNormalized {v : Vault} {n : Number} (h : AssetPool.assetsTotal v = .ok n) :
    n.isNormalized := by
  rw [Vault.pool_assetsTotal] at h; wrap_side

/-- The vault balances the lending protocol reads are normalized. -/
lemma AssetPool.amounts_isNormalized (v : Vault) : (AssetPool.amounts v).assetsAvailable.isNormalized ∧
    (AssetPool.amounts v).assetsDeployed.isNormalized ∧ (AssetPool.amounts v).assetsReserved.isNormalized ∧
    (AssetPool.amounts v).lossUnrealized.isNormalized ∧ (AssetPool.amounts v).yieldUnrealized.isNormalized := by
  rw [Vault.pool_amounts]
  dsimp only
  exact ⟨by wrap_side, by wrap_side, by wrap_side, by wrap_side, by wrap_side⟩

macro_rules
  | `(tactic| wrap_rule) => `(tactic| first
    | exact (XRPL.Model.Lending.AssetPool.amounts_isNormalized _).1
    | exact (XRPL.Model.Lending.AssetPool.amounts_isNormalized _).2.1
    | exact (XRPL.Model.Lending.AssetPool.amounts_isNormalized _).2.2.1
    | exact (XRPL.Model.Lending.AssetPool.amounts_isNormalized _).2.2.2.1
    | exact (XRPL.Model.Lending.AssetPool.amounts_isNormalized _).2.2.2.2)

lemma AssetPool.exponent_ne_wrap (v : Vault) (nt : NumericType) : AssetPool.exponent v nt ≠ .error .wrap := by
  intro h; wrap_leaf

lemma AssetPool.adjustBalances_ne_wrap (v : Vault) (c : PoolBalanceChange) (hcash : c.cash.isNormalized)
    (hdep : c.deployed.isNormalized) (hloss : c.loss.isNormalized) (hres : c.reserved.isNormalized)
    (hyield : c.yield.isNormalized) : (AssetPool.adjustBalances v c).run ≠ .error .wrap := by
  intro h
  rw [Vault.pool_adjustBalances] at h
  unfold_ter at h
  walk_ok
  all_goals wrap_leaf

lemma AssetPool.openLimit_ne_wrap (v : Vault) : AssetPool.openLimit v ≠ .error .wrap :=
  Vault.openLimit_ne_wrap v

lemma AssetPool.exceedsOpenLimit_ne_wrap (v : Vault) (x : Number) (hx : x.isNormalized) :
    AssetPool.exceedsOpenLimit v x ≠ .error .wrap :=
  Vault.exceedsOpenLimit_ne_wrap v x hx

lemma LoanBroker.checkCoverOpenLimit_ne_wrap (lb : LoanBroker) (v : Vault) (amount : STAmount) (ha : amount.Fits) :
    lb.checkCoverOpenLimit v amount ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.roundedCoverAmount_ne_wrap (lb : LoanBroker) (v : Vault) (amount : STAmount) (ha : amount.Fits) :
    (lb.roundedCoverAmount v amount).run ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.applyCoverTransaction_ne_wrap (lb : LoanBroker) (d : CoverDirection) (amount : STAmount)
    (ha : amount.Fits) : lb.applyCoverTransaction d amount ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.canCreate_ne_wrap (v : Vault) (dm : Option Number) (nt : NumericType) :
    LoanBroker.canCreate v dm nt ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.canUpdate_ne_wrap (lb : LoanBroker) (v : Vault) (dm : Option Number) :
    lb.canUpdate v dm ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.create_ne_wrap (tx : LoanBrokerSetCreate) (nt : NumericType) :
    LoanBroker.create tx nt ≠ .error .wrap :=
  RawLoanBroker.to_lawful_ne_wrap _

lemma LoanBroker.update_ne_wrap (lb : LoanBroker) (dm : Option Number) : lb.update dm ≠ .error .wrap :=
  RawLoanBroker.to_lawful_ne_wrap _

lemma LoanBroker.canCoverDeposit_ne_wrap (lb : LoanBroker) (v : Vault) (amount : STAmount) (ha : amount.Fits) :
    lb.canCoverDeposit v amount ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.coverDeposit_ne_wrap (lb : LoanBroker) (v : Vault) (amount : STAmount) (ha : amount.Fits) :
    (lb.coverDeposit v amount).run ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.canCoverWithdraw_ne_wrap (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (ha : amount.mValue.toNat < 2 ^ 63) : lb.canCoverWithdraw v amount ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.coverWithdraw_ne_wrap (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (ha : amount.mValue.toNat < 2 ^ 63) : (lb.coverWithdraw v amount).run ≠ .error .wrap := by
  intro h; wrap_leaf

lemma LoanBroker.roundedCoverClawback_ne_wrap (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (hnt : lb.numericType.maxValue.toNat < 2 ^ 63) (ha : ∀ a ∈ amount, a.Fits) :
    (lb.roundedCoverClawback v amount).run ≠ .error .wrap := by
  intro h
  cases amount with
  | none => wrap_leaf
  | some a => have := ha a rfl; wrap_leaf

lemma LoanBroker.canCoverClawback_ne_wrap (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (hnt : lb.numericType.maxValue.toNat < 2 ^ 63) (ha : ∀ a ∈ amount, a.Fits) :
    lb.canCoverClawback v amount ≠ .error .wrap := by
  intro h
  unfold LoanBroker.canCoverClawback at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  walk_ok
  exact LoanBroker.roundedCoverClawback_ne_wrap _ _ _ hnt ha ‹_›

lemma LoanBroker.coverClawback_ne_wrap (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (hnt : lb.numericType.maxValue.toNat < 2 ^ 63) (ha : ∀ a ∈ amount, a.Fits) :
    (lb.coverClawback v amount).run ≠ .error .wrap := by
  intro h
  simp only [LoanBroker.coverClawback] at h
  unfold_ter at h
  walk_ok
  all_goals first
    | exact LoanBroker.roundedCoverClawback_ne_wrap _ _ _ hnt ha ‹_›
    | wrap_leaf

lemma LoanBroker.canDelete_ne_wrap (lb : LoanBroker) (v : Vault) : lb.canDelete v ≠ .error .wrap := by
  intro h; wrap_leaf

end XRPL.Model.Lending
