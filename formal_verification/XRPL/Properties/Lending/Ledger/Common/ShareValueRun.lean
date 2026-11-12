import XRPL.Properties.Lending.Ledger.Common.ShareValueRunDefs
import XRPL.Properties.Lending.Ledger.Common.ShareValueVaultSteps
import XRPL.Properties.Lending.Ledger.Common.VaultAccounting
import XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
import XRPL.Properties.Lending.Ledger.Common.SubscriptionInv
import XRPL.Properties.Lending.Loan.Common.ManageLedger
import XRPL.Properties.Lending.Loan.Common.ShareValue

/-! # shareValue never falls over a sequence of transactions

One transaction that is not an impair, a default of a loan that is not impaired or an exit of the only holder keeps
shareValue = (AssetsTotal − LossUnrealized) / SharesTotal, on a vault that is not coarsened and when the shares a
vault transaction moves are worth whole base units. The sequence row follows by induction over the run. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts VaultSchedule)

open private LendingLedger.lending_step from XRPL.Properties.Lending.Ledger.Common.VaultAccounting
open private LendingLedger.sharesTotal_step LendingLedger.holderShares_balance
  from XRPL.Properties.Lending.Ledger.Common.BrokerAccounting
open private LendingLedger.default_total_eq from XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps

/-- A vault whose SharesTotal is not zero has a positive exact SharesTotal. -/
private lemma Vault.exact_sharesTotal_pos (v : Vault) (h : v.sharesTotal ≠ Number.zero) :
    0 < (v.toExact.sharesTotal : ℚ) := by
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  exact lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm fun h0 => h ((Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp h0))

/-- The cross-multiplied bound is the bound on shareValue, on positive share totals. -/
private lemma Vault.shareValue_le_of_cross (v v' : Vault) (hS : 0 < (v.toExact.sharesTotal : ℚ))
    (hS' : 0 < (v'.toExact.sharesTotal : ℚ))
    (h : v'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (v'.toExact.sharesTotal : ℚ)) :
    v.toRawVault.shareValue ≤ v'.toRawVault.shareValue := by
  unfold RawVault.shareValue
  rw [div_le_div_iff₀ hS hS']
  linarith

/-- With SharesTotal unchanged, shareValue moves with AssetsTotal − LossUnrealized. -/
private lemma Vault.shareValue_le_of_nav (v v' : Vault) (hST : v'.sharesTotal.toRat = v.sharesTotal.toRat)
    (hNav : v.withdrawNav ≤ v'.withdrawNav) : v.toRawVault.shareValue ≤ v'.toRawVault.shareValue := by
  unfold RawVault.shareValue
  have hS : v'.toExact.sharesTotal = v.toExact.sharesTotal := by
    show v'.sharesTotal.toRat.num.toNat = v.sharesTotal.toRat.num.toNat
    rw [hST]
  rw [hS]
  exact div_le_div_of_nonneg_right hNav (Nat.cast_nonneg _)

/-- A deposit that issues shares runs in the subscription phase of a closed-ended vault. -/
private lemma Vault.deposit_subscription (v : Vault) (s : VaultSchedule) (hs : v.schedule = some s)
    (amount : STAmount) (t : UInt32) (hpos : 0 < amount.toRat) (r : VaultWithAmounts)
    (h : (v.deposit amount false t hpos).run = .ok (.ok r)) : v.phase t = .subscription := by
  cases hph : v.phase t with
  | subscription => rfl
  | investment =>
    exfalso
    simp only [XRPL.Model.SingleAssetVault.Vault.deposit, hph] at h
    unfold_ter at h
    simp at h
  | redemption =>
    exfalso
    simp only [XRPL.Model.SingleAssetVault.Vault.deposit, hph] at h
    unfold_ter at h
    simp at h
  | noPhase =>
    exfalso
    unfold XRPL.Model.SingleAssetVault.Vault.phase at hph
    rw [hs] at hph
    dsimp only at hph
    split at hph
    · cases hph
    · split at hph <;> cases hph

/-- The vault a vault transaction stores is the vault of its effect. -/
private lemma LendingLedger.vault_of_commitVault (l : LendingLedger) (u : VaultEffect) :
    (l.commitVault u).vault = u.vault := by
  unfold LendingLedger.commitVault
  split <;> simp [LendingLedger.setShares]

/-- A successful VaultDeposit ran the vault's deposit and stored its vault. -/
private lemma LendingLedger.vaultDeposit_inv {l l' : LendingLedger} {h : Nat} {amount : STAmount}
    {isDonation : Bool} (hok : (l.apply (.vaultDeposit h amount isDonation)).run = .ok (.ok l')) :
    ∃ (hpos : 0 < amount.toRat) (r : VaultWithAmounts),
      (l.vault.deposit amount isDonation l.now hpos).run = .ok (.ok r) ∧ l'.vault = r.vault' := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault (tx := .vaultDeposit h amount isDonation) rfl hok
  rw [LendingLedger.vault_of_commitVault]
  simp only [LendingLedger.applyVault] at hu
  split at hu
  · rename_i hpos
    unfold_ter at hu
    walk_ok
    exact ⟨hpos, _, ‹_›, rfl⟩
  · cases hu

/-- A successful VaultWithdraw ran the vault's withdrawal and stored its vault. -/
private lemma LendingLedger.vaultWithdraw_inv {l l' : LendingLedger} {h : Nat}
    {amount : XRPL.Model.SingleAssetVault.WithdrawAmount}
    (hok : (l.apply (.vaultWithdraw h amount)).run = .ok (.ok l')) :
    ∃ (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts),
      (l.vault.withdraw amount (l.isSoleShareholder h) l.now hpos (some (l.sharesOf h))).run = .ok (.ok r) ∧
        l'.vault = r.vault' := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault (tx := .vaultWithdraw h amount) rfl hok
  rw [LendingLedger.vault_of_commitVault]
  simp only [LendingLedger.applyVault] at hu
  split at hu
  · rename_i hpos
    unfold_ter at hu
    walk_ok
    exact ⟨hpos, _, ‹_›, rfl⟩
  · cases hu

/-- A successful VaultClawback ran the vault's clawback on the holder's shares and stored its vault. -/
private lemma LendingLedger.vaultClawback_inv {l l' : LendingLedger} {h : Nat} {assets : STAmount}
    (hok : (l.apply (.vaultClawback h assets)).run = .ok (.ok l')) :
    ∃ (hnn : 0 ≤ assets.toRat) (holderShares : STAmount) (r : VaultWithAmounts),
      STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok holderShares ∧
      (l.vault.clawback assets holderShares (l.isSoleShareholder h) hnn).run = .ok (.ok r) ∧
        l'.vault = r.vault' := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault (tx := .vaultClawback h assets) rfl hok
  rw [LendingLedger.vault_of_commitVault]
  simp only [LendingLedger.applyVault] at hu
  split at hu
  · rename_i hnn
    unfold_ter at hu
    walk_ok
    exact ⟨hnn, _, _, ‹_›, ‹_›, rfl⟩
  · cases hu

/-- A successful VaultBurnShares passed the burn checks, which need an insolvent vault. -/
private lemma LendingLedger.vaultBurnShares_inv {l l' : LendingLedger} {h : Nat} {amount : STAmount}
    (hok : (l.apply (.vaultBurnShares h amount)).run = .ok (.ok l')) : l.vault.isInsolvent = true := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault (tx := .vaultBurnShares h amount) rfl hok
  simp only [LendingLedger.applyVault] at hu
  unfold_ter at hu
  walk_ok
  exact (Vault.canBurnShares_ok_reduces _ _ _ _ ‹_›).1

/-- A transaction takes at least zero off LossUnrealized by ending an impairment. -/
private lemma LendingLedger.unimpairedOf_nonneg (l : LendingLedger) (tx : LendingTx) : 0 ≤ l.unimpairedOf tx := by
  unfold LendingLedger.unimpairedOf
  split
  · split
    · exact (Loan.exact _).principalOutstanding_nonneg
    · exact le_rfl
  · split
    · split
      · exact (Loan.exact _).principalOutstanding_nonneg
      · exact le_rfl
    · exact le_rfl
  · split
    · split
      · exact (Loan.exact _).principalOutstanding_nonneg
      · exact le_rfl
    · exact le_rfl
  · exact le_rfl

/-- One transaction that is not one of the listed kinds keeps shareValue. The vault is not coarsened before or
after it, shares are left, and the shares a vault transaction moves are worth whole base units. -/
private lemma LendingLedger.shareValue_step (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (hkeep : l.lowersShareValue tx = false) (hnc : l.NotCoarsened)
    (hnc' : l'.NotCoarsened) (hS : l.vault.sharesTotal ≠ Number.zero) (hS' : l'.vault.sharesTotal ≠ Number.zero)
    (hfit : l.vault.sharesTotal.toRat + l.sharesCreatedOf tx ≤ 2 ^ 63 - 1) (hwhole : l.movesWholeWorth tx) :
    l.vault.toRawVault.shareValue ≤ l'.vault.toRawVault.shareValue := by
  have hLUstep := (LendingLedger.lending_step hr h).2.2.1
  have hSTstep := LendingLedger.sharesTotal_step hr h hfit
  have hSpos := Vault.exact_sharesTotal_pos l.vault hS
  have hS'pos := Vault.exact_sharesTotal_pos l'.vault hS'
  have hcast := RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf
  have hasset := hr.holdsAsset
  obtain ⟨hAAg, hADg, -, -, -, -⟩ := LendingLedger.base_grid_proof l hr hasset.maxValue_le
  have hgrid : Vault.OnBaseGrid l.vault := ⟨hAAg, hADg⟩
  have hSlt : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ (16 + l.vault.baseExponent) := by
    rw [open_line_eq]; exact hnc
  -- a transaction that moves no shares, is not an impair and takes nothing out of AssetsTotal
  have hgen : tx.isOutflow = false → l.sharesCreatedOf tx = 0 → l.sharesRemovedOf tx = 0 → l.impairedOf tx = 0 →
      l.vault.toRawVault.shareValue ≤ l'.vault.toRawVault.shareValue := by
    intro hout hcr hrm himp
    refine Vault.shareValue_le_of_nav _ _ (by rw [hSTstep, hcr, hrm]; ring) ?_
    have hAT := LendingLedger.noLoss_step l l' tx hr h hnc hnc' hout
    have hun := l.unimpairedOf_nonneg tx
    show l.vault.toExact.assetsTotal - l.vault.lossUnrealized.toRat ≤
      l'.vault.toExact.assetsTotal - l'.vault.lossUnrealized.toRat
    rw [hLUstep, himp]
    linarith
  cases tx with
  | vaultDeposit hd amount isDonation =>
    obtain ⟨hpos, r, hdep, hv'⟩ := LendingLedger.vaultDeposit_inv h
    obtain ⟨hc, hty⟩ :=
      LendingTx.preflight_vaultDeposit_canonical l hasset hd amount isDonation (LendingLedger.apply_preflight h)
    have hcreated : l.sharesCreatedOf (.vaultDeposit hd amount isDonation) = r.shares.toRat := by
      simp only [LendingLedger.sharesCreatedOf, dif_pos hpos, hdep]
    cases isDonation with
    | true =>
      -- a donation issues no shares
      obtain ⟨ra, -, -, hra, -⟩ := Vault.deposit_ok_reduces l.vault amount true l.now hpos r hdep
      have hsh := (Vault.deposit_donation_proof l.vault amount ra l.now hpos hc hra r hdep).2
      exact hgen rfl (by rw [hcreated, hsh]; exact STAmount.zero_toRat _) rfl rfl
    | false =>
      -- shares are issued only in the subscription phase, where nothing is lent out
      obtain ⟨s, hinv⟩ := hr.loansInv
      have hsub := Vault.deposit_subscription l.vault s hinv.schedule amount l.now hpos r hdep
      obtain ⟨-, -, hat, hAD, hLU, -, hYU⟩ := LendingLedger.subscription_no_loans_proof l hr hsub
      rw [hcreated] at hfit
      have hworth : ∃ k : ℤ, l.vault.idealChargeDeposit r.shares.toRat = k * 10 ^ l.vault.baseExponent := by
        rw [← hcreated]; exact hwhole
      have hcross := Vault.deposit_keeps_shareValue l.vault hasset hat hAD hLU hYU hr.availableStored
        (hr.assetsAvailable_units hasset) amount l.now hpos hc hty r hdep (by rw [hcast]; exact hfit) hworth
      rw [hv'] at hS'pos ⊢
      exact Vault.shareValue_le_of_cross _ _ hSpos hS'pos hcross
  | vaultWithdraw hd amount =>
    have hsole : l.isSoleShareholder hd = false := hkeep
    obtain ⟨hpos, r, hwh, hv'⟩ := LendingLedger.vaultWithdraw_inv h
    obtain ⟨hc, hty⟩ :=
      LendingTx.preflight_vaultWithdraw_canonical l hasset hd amount (LendingLedger.apply_preflight h)
    have hremoved : l.sharesRemovedOf (.vaultWithdraw hd amount) = r.shares.toRat := by
      simp only [LendingLedger.sharesRemovedOf, dif_pos hpos, hwh]
    have hw : (l.vault.withdraw amount false l.now hpos).run = .ok (.ok r) := by
      rw [← hsole]; exact (Vault.withdraw_holder_ok _ _ _ _ _ _ _ hwh).1
    have hworth : ∃ k : ℤ, l.vault.idealAssetsWithdraw false r.shares.toRat = k * 10 ^ l.vault.baseExponent := by
      rw [← hremoved, ← hsole]; exact hwhole
    have hST' := Vault.withdraw_exact_sharesTotal l.vault amount false l.now hpos hc hty r hw
    rw [hv'] at hS'pos ⊢
    exact Vault.shareValue_le_of_cross _ _ hSpos hS'pos
      (Vault.withdraw_keeps_shareValue l.vault hasset hgrid hSlt hr.loss_units hr.availableStored
        (hr.assetsAvailable_units hasset) amount l.now hpos hc hty r hw (by linarith) hworth)
  | vaultClawback hd assets =>
    have hsole : l.isSoleShareholder hd = false := hkeep
    obtain ⟨hnn, holderShares, r, hof, hcl, hv'⟩ := LendingLedger.vaultClawback_inv h
    have hc := LendingTx.preflight_vaultClawback_canonical l hasset hd assets (LendingLedger.apply_preflight h)
    obtain ⟨hhs, -, hhs0⟩ := LendingLedger.holderShares_balance l hr hd holderShares hof
    have hremoved : l.sharesRemovedOf (.vaultClawback hd assets) = r.shares.toRat := by
      simp only [LendingLedger.sharesRemovedOf, dif_pos hnn, hof, hcl]
    have hcl' : (l.vault.clawback assets holderShares false hnn).run = .ok (.ok r) := by
      rw [← hsole]; exact hcl
    have hworth : ∃ k : ℤ, l.vault.idealAssetsWithdraw false r.shares.toRat = k * 10 ^ l.vault.baseExponent := by
      rw [← hremoved, ← hsole]; exact hwhole
    rw [hv'] at hS'pos ⊢
    exact Vault.shareValue_le_of_cross _ _ hSpos hS'pos
      (Vault.clawback_keeps_shareValue l.vault hasset hgrid hSlt hr.loss_units assets holderShares hnn hc hhs hhs0
        r hcl' hworth)
  | vaultBurnShares hd amount =>
    -- a burn runs only on a vault with no assets, whose shares are worth nothing
    have hins := LendingLedger.vaultBurnShares_inv h
    unfold XRPL.Model.SingleAssetVault.Vault.isInsolvent at hins
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hins
    have hLU0 : 0 ≤ l.vault.lossUnrealized.toRat := l.vault.exact.lossUnrealized_nonneg
    have hnav : l.vault.withdrawNav ≤ 0 := by
      show l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat - l.vault.lossUnrealized.toRat ≤ 0
      rw [Number.toRat_eq_zero_of_mantissa_zero _ hins.1.1, Number.toRat_eq_zero_of_mantissa_zero _ hins.1.2]
      linarith
    exact le_trans (div_nonpos_of_nonpos_of_nonneg hnav (Nat.cast_nonneg _))
      (Vault.perShareValue_nonneg l'.vault)
  | vaultSet m b ub => exact hgen rfl rfl rfl rfl
  | vaultDelete => exact hgen rfl rfl rfl rfl
  | loanBrokerCreate t => exact hgen rfl rfl rfl rfl
  | loanBrokerUpdate j dm => exact hgen rfl rfl rfl rfl
  | loanBrokerCoverDeposit j a => exact hgen rfl rfl rfl rfl
  | loanBrokerCoverWithdraw j a => exact hgen rfl rfl rfl rfl
  | loanBrokerCoverClawback j a => exact hgen rfl rfl rfl rfl
  | loanBrokerDelete j => exact hgen rfl rfl rfl rfl
  | loanSet j principal rates fees pi pt gp sd twoStep ao => exact hgen rfl rfl rfl rfl
  | loanAccept i => exact hgen rfl rfl rfl rfl
  | loanDelete i => exact hgen rfl rfl rfl rfl
  | loanPay i paymentType amount => exact hgen rfl rfl rfl rfl
  | close t => exact hgen rfl rfl rfl rfl
  | loanManage i action =>
    cases action with
    | impair => exact absurd hkeep (by simp [LendingLedger.lowersShareValue])
    | unimpair => exact hgen rfl rfl rfl rfl
    | default =>
      -- the default of an impaired loan takes its principal off LossUnrealized and adds the cover it pays
      obtain ⟨e, loan, r, he, hat, -, hdef, -, hv', -⟩ := LendingLedger.loanDefault_ok h
      have himp : loan.isImpaired = true := by
        have hk : (l.loan? i).any (!·.loan.isImpaired) = false := hkeep
        obtain ⟨e₀, he₀, -, hraw⟩ := hat.stored
        rw [he₀] at hk
        have hi : loan.isImpaired = e₀.loan.isImpaired := (congrArg RawLoan.isImpaired hraw :)
        rw [hi]
        simpa using hk
      have hLU := LendingLedger.manageDefault_loss_proof hr h hat himp
      have hAT := LendingLedger.default_total_eq l hr i loan hat r hdef hnc
      have hdc := LendingLedger.manageDefault_cover_nonneg_proof hr h hat hdef hnc
      refine Vault.shareValue_le_of_nav _ _ (by rw [hSTstep]; show _ + (0 : ℚ) - 0 = _; ring) ?_
      show l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat - l.vault.lossUnrealized.toRat ≤
        l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat - l'.vault.lossUnrealized.toRat
      rw [hLU, hv', hAT]
      linarith

/-- Proof body of `Lending.Reachable.no_dilution`. -/
lemma LendingLedger.no_dilution_proof (start l : LendingLedger) (txs : List LendingTx) (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) (hkeep : start.KeepsShareValueAlong txs)
    (hshares : start.SharesLeftAlong txs) (hnc : start.NotCoarsenedAlong txs) (hfit : start.SharesFitAlong txs)
    (hwhole : start.WholeWorthAlong txs) :
    start.vault.toRawVault.shareValue ≤ l.vault.toRawVault.shareValue := by
  induction hrun with
  | refl => exact le_rfl
  | @step txs₀ l₀ l₁ tx hprev hok ih =>
    have ih' := ih (fun pre l₂ t hp hr' => hkeep pre l₂ t (hp.trans (List.prefix_append _ _)) hr')
      (fun pre l₂ hp hr' => hshares pre l₂ (hp.trans (List.prefix_append _ _)) hr')
      (fun pre l₂ hp hr' => hnc pre l₂ (hp.trans (List.prefix_append _ _)) hr')
      (fun pre l₂ t hp hr' => hfit pre l₂ t (hp.trans (List.prefix_append _ _)) hr')
      (fun pre l₂ t hp hr' => hwhole pre l₂ t (hp.trans (List.prefix_append _ _)) hr')
    have hstep := LendingLedger.shareValue_step l₀ l₁ tx (hprev.reachable hr) hok
      (hkeep txs₀ l₀ tx (List.prefix_refl _) hprev) (hnc txs₀ l₀ (List.prefix_append _ _) hprev)
      (hnc (txs₀ ++ [tx]) l₁ (List.prefix_refl _) (.step tx hprev hok))
      (hshares txs₀ l₀ (List.prefix_append _ _) hprev)
      (hshares (txs₀ ++ [tx]) l₁ (List.prefix_refl _) (.step tx hprev hok))
      (hfit txs₀ l₀ tx (List.prefix_refl _) hprev) (hwhole txs₀ l₀ tx (List.prefix_refl _) hprev)
    exact ih'.trans hstep

end XRPL.Model.Lending
