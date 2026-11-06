import XRPL.Properties.Lending.Common.Walk
import XRPL.Properties.Lending.Ledger.Common.ReachableProofs
import XRPL.Properties.Vault.Proofs.ClawbackExits
import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # Ledger exits

Rejections of whole ledger transactions, after the preflight and the earlier checks passed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault VaultAmounts WithdrawAmount computeDeposit computeWithdraw)

/-- A transaction that passes its preflight runs its checks and operation. -/
lemma LendingLedger.apply_of_preflight {l : LendingLedger} {tx : LendingTx} (h : tx.preflight l = .tesSUCCESS) :
    l.apply tx = l.applyChecked tx := by
  unfold LendingLedger.apply
  dsimp only
  rw [h, if_neg (by rw [show TER.tesSUCCESS.isTesSuccess = true from rfl]; decide)]

/-- A stored broker makes the broker list hold a broker. -/
private lemma LendingLedger.brokers_any_of_broker? {l : LendingLedger} {j : Nat} {b : LoanBroker}
    (hb : l.broker? j = some b) :
    l.brokers.any Option.isSome = true := by
  unfold LendingLedger.broker? at hb
  cases hj : l.brokers[j]? with
  | none => rw [hj] at hb; cases hb
  | some x =>
    rw [hj] at hb
    cases x with
    | none => cases hb
    | some x => exact List.any_eq_true.mpr ⟨some x, List.mem_of_getElem? hj, rfl⟩

/-- Proof body of the VaultDelete exit of `Lending.vault_exits`. -/
lemma LendingLedger.vaultDelete_has_broker_proof (l : LendingLedger) (hnd : l.vaultDeleted = false)
    (hcan : l.vault.canVaultDelete = .ok .tesSUCCESS) (j : Nat) (b : LoanBroker) (hb : l.broker? j = some b) :
    (l.apply .vaultDelete).run = .ok (.error .tecHAS_OBLIGATIONS) := by
  rw [LendingLedger.apply_of_preflight rfl]
  simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete]
  have hany := LendingLedger.brokers_any_of_broker? hb
  unfold_ter
  rw [hnd, hcan]
  simp only [Bool.false_eq_true, ↓reduceIte, show TER.tesSUCCESS.isTesSuccess = true from rfl, Bool.not_true, hany]
  split <;> rfl

/-- A charge past the Open limit fails the inflow check, whatever its exponent. -/
private lemma Vault.checkOpenLimit_exceeded (v : Vault) (amount : STAmount) (assetsTotal amountNum : Number) (e : Int)
    (hat : v.assetsTotal = .ok assetsTotal) (hnum : amount.toNumber .to_nearest = .ok amountNum)
    (hexp : postSumExponent assetsTotal amountNum v.baseExponent v.numericType = .ok e)
    (hexceeds : v.exceedsOpenLimit amountNum = .ok true) :
    v.checkOpenLimit amount = .ok .tecLIMIT_EXCEEDED := by
  unfold XRPL.Model.SingleAssetVault.Vault.checkOpenLimit
  rw [hat]
  simp only [bind, Except.bind, hnum, hexp]
  split
  · rfl
  · rw [hexceeds]; rfl

/-- Proof body of the VaultDeposit exit of `Lending.vault_exits`. -/
lemma LendingLedger.vaultDeposit_open_zone_proof (l : LendingLedger) (h : Nat) (amount : STAmount) (isDonation : Bool)
    (hpre : (LendingTx.vaultDeposit h amount isDonation).preflight l = .tesSUCCESS) (hnd : l.vaultDeleted = false)
    (hpos : 0 < amount.toRat) (roundedAmount : STAmount) (amounts : VaultAmounts) (assetsTotal amountNum : Number)
    (e : Int) (hopen : l.vault.DepositOpen isDonation l.now)
    (hrounded : (l.vault.roundedDepositAmount amount).run = .ok (.ok roundedAmount))
    (hcomp : (computeDeposit l.vault roundedAmount isDonation).run = .ok (.ok amounts))
    (hat : l.vault.assetsTotal = .ok assetsTotal) (hnum : amounts.assets.toNumber .to_nearest = .ok amountNum)
    (hexp : postSumExponent assetsTotal amountNum l.vault.baseExponent l.vault.numericType = .ok e)
    (hexceeds : l.vault.exceedsOpenLimit amountNum = .ok true) :
    (l.apply (.vaultDeposit h amount isDonation)).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  have hdep := Vault.deposit_inflow_rejected_proof l.vault amount isDonation l.now hpos roundedAmount amounts _
    hopen hrounded hcomp (Vault.checkOpenLimit_exceeded _ _ _ _ _ hat hnum hexp hexceeds) (by decide)
  rw [LendingLedger.apply_of_preflight hpre]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, Bool.false_eq_true, ↓reduceIte,
    LendingLedger.applyVault, hpos, ↓reduceDIte]
  unfold_ter
  simp only [ExceptT.run] at hdep
  rw [hdep]
  rfl

/-- A final VaultWithdraw while AssetsDeployed ≠ 0 is rejected with tecHAS_OBLIGATIONS. -/
lemma LendingLedger.vaultWithdraw_has_obligations (l : LendingLedger) (h : Nat) (amount : WithdrawAmount)
    (hpre : (LendingTx.vaultWithdraw h amount).preflight l = .tesSUCCESS) (hnd : l.vaultDeleted = false)
    (hpos : 0 < amount.amount.toRat) (amounts : VaultAmounts) (sharesTotalAmount : STAmount)
    (hsoon : (l.vault.earlyExitFeeRate.isNone && l.vault.phase l.now == .investment) = false)
    (hcomp : (computeWithdraw l.vault amount (l.isSoleShareholder h)).run = .ok (.ok amounts))
    (hst : STAmount.ofNumber .int64 l.vault.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfinal : amounts.shares.operator_eq sharesTotalAmount = true)
    (hdeployed : l.vault.assetsDeployed.operator_ne Number.zero = true) :
    (l.apply (.vaultWithdraw h amount)).run = .ok (.error .tecHAS_OBLIGATIONS) := by
  have hw := Vault.withdraw_has_obligations_holder l.vault amount (l.isSoleShareholder h) l.now hpos
    (some (l.sharesOf h)) amounts sharesTotalAmount hsoon hcomp hst hfinal hdeployed
  rw [LendingLedger.apply_of_preflight hpre]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, Bool.false_eq_true, ↓reduceIte,
    LendingLedger.applyVault, hpos, ↓reduceDIte]
  unfold_ter
  simp only [ExceptT.run] at hw
  rw [hw]
  rfl

/-- A VaultClawback that passes its preflight is on a vault whose asset is not XRP. -/
lemma LendingTx.preflight_vaultClawback_not_native (l : LendingLedger) (h : Nat) (assets : STAmount)
    (hpre : (LendingTx.vaultClawback h assets).preflight l = .tesSUCCESS) : l.vault.numericType ≠ .native := by
  intro hnat
  have hc : (isCanonicalAmount assets l.vault.numericType && !assets.mIsNegative) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  have hnt : assets.mNumericType = l.vault.numericType := by
    simp only [isCanonicalAmount, Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.1
  simp only [LendingTx.preflight] at hpre
  rw [hc] at hpre
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnt, hnat] at hpre
  cases hpre

/-- A VaultClawback of every share while AssetsDeployed ≠ 0 is rejected with tecHAS_OBLIGATIONS. -/
lemma LendingLedger.vaultClawback_has_obligations (l : LendingLedger) (h : Nat) (assets : STAmount)
    (hpre : (LendingTx.vaultClawback h assets).preflight l = .tesSUCCESS) (hnd : l.vaultDeleted = false)
    (hnn : 0 ≤ assets.toRat) (holderShares shares recovered sharesTotalAmount : STAmount)
    (hheld : STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok holderShares)
    (hpr : l.vault.ClawbackPriced assets holderShares (l.isSoleShareholder h) shares recovered)
    (hst : STAmount.ofNumber .int64 l.vault.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfinal : shares.operator_eq sharesTotalAmount = true)
    (hdeployed : l.vault.assetsDeployed.operator_ne Number.zero = true) :
    (l.apply (.vaultClawback h assets)).run = .ok (.error .tecHAS_OBLIGATIONS) := by
  have hc := Vault.clawback_has_obligations_proof l.vault assets holderShares (l.isSoleShareholder h) hnn
    (LendingTx.preflight_vaultClawback_not_native l h assets hpre) shares recovered sharesTotalAmount hpr hst hfinal
    hdeployed
  rw [LendingLedger.apply_of_preflight hpre]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, Bool.false_eq_true, ↓reduceIte,
    LendingLedger.applyVault, hnn, ↓reduceDIte]
  unfold_ter
  simp only [ExceptT.run] at hc
  rw [hheld]
  simp only [hc]
  rfl


/-- A VaultDeposit that passes its preflight deposits a positive amount. -/
lemma LendingTx.preflight_vaultDeposit_pos (l : LendingLedger) (h : Nat) (amount : STAmount) (isDonation : Bool)
    (hpre : (LendingTx.vaultDeposit h amount isDonation).preflight l = .tesSUCCESS) : 0 < amount.toRat := by
  simp only [LendingTx.preflight] at hpre
  split at hpre
  · rename_i hc
    simp only [Bool.and_eq_true, isPositiveAmount, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc
    exact STAmount.toRat_pos_of _ hc.2.1 hc.2.2
  · cases hpre

/-- A VaultWithdraw that passes its preflight asks for a positive amount of assets or shares. -/
lemma LendingTx.preflight_vaultWithdraw_pos (l : LendingLedger) (h : Nat) (amount : WithdrawAmount)
    (hpre : (LendingTx.vaultWithdraw h amount).preflight l = .tesSUCCESS) : 0 < amount.amount.toRat := by
  cases amount with
  | vaultAssets a | vaultShares a =>
    simp only [LendingTx.preflight, WithdrawAmount.amount] at hpre ⊢
    split at hpre
    · rename_i hc
      simp only [Bool.and_eq_true, isPositiveAmount, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc
      exact STAmount.toRat_pos_of _ hc.2.1 hc.2.2
    · cases hpre

/-- A VaultClawback that passes its preflight asks for an amount that is not negative. -/
lemma LendingTx.preflight_vaultClawback_nonneg (l : LendingLedger) (h : Nat) (assets : STAmount)
    (hpre : (LendingTx.vaultClawback h assets).preflight l = .tesSUCCESS) : 0 ≤ assets.toRat := by
  have hc : (isCanonicalAmount assets l.vault.numericType && !assets.mIsNegative) = true := by
    by_contra hne
    simp only [Bool.not_eq_true] at hne
    simp [LendingTx.preflight, hne] at hpre
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  exact STAmount.toRat_nonneg_of _ hc.2

end XRPL.Model.Lending
