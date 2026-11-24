import XRPL.Properties.Lending.Ledger.Common.NoExceptionVaultWithdrawOps
import XRPL.Properties.Lending.Ledger.Common.RecheckVault
import XRPL.Properties.Lending.Ledger.Common.WrapLedger
import XRPL.Properties.Lending.Ledger.Common.ShareSum
import XRPL.Properties.Lending.Ledger.Common.TotalStoredInv
import XRPL.Properties.Vault.Proofs.OpenZone

/-! # VaultWithdraw, VaultClawback and the burn of shares never end in an exception

They fail only in the final re-check or on a wrap, which other rows exclude, and on a VaultWithdraw by shares on XRP
worth more than `10^17` drops (FV_M2_25). -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault WithdrawAmount VaultAmounts VaultWithAmounts computeClawback)
open XRPL.Model.SingleAssetVault.VaultWithdrawErrors

/-- A vault transaction that ends in an error passed its preflight, and its vault operation ended in that error. -/
private lemma LendingLedger.applyVault_error {l : LendingLedger} {tx : LendingTx} {e : Error}
    (hv : tx.isVault = true) (h : (l.apply tx).run = .error e) :
    tx.preflight l = .tesSUCCESS ∧ (l.applyVault tx).run = .error e := by
  obtain ⟨hpre, ha⟩ := LendingLedger.apply_error h
  refine ⟨hpre, ?_⟩
  cases tx <;> simp only [LendingTx.isVault, Bool.false_eq_true] at hv <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, ↓reduceIte] at ha
    split at ha
    · cases ha
    · exact TerExcept.map_error ha

/-- The holder's shares less a share amount the vault burned never fail to subtract: both are at most `2^63 - 1`. -/
private lemma LendingLedger.holder_sub_ne_error (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (hbal : (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) (shares : STAmount) (hic : shares.IntegralCanonical)
    (h64 : shares.mNumericType = .int64) (hs0 : 0 ≤ shares.toRat) (e : Error) :
    shares.toNumber .to_nearest ≠ .error e ∧ ∀ s : Number, shares.toNumber .to_nearest = .ok s →
      (l.sharesOf h).operator_sub s .to_nearest ≠ .error e := by
  obtain ⟨sn, hsn, hsv, hsnn, -⟩ := STAmount.toNumber_integral_exact shares .to_nearest hic (by rw [h64]; decide)
  obtain ⟨hheldn, hheld0⟩ := hr.sharesNonneg.sharesOf h
  have hcap : shares.toRat ≤ 2 ^ 63 - 1 := le_trans (le_abs_self _) (hic.abs_le_int64 h64)
  refine ⟨by rw [hsn]; exact nofun, fun s hs => ?_⟩
  obtain rfl := Except.ok.inj (hsn.symm.trans hs)
  obtain ⟨d, hd⟩ := Number.operator_sub_ok_of_normalized_cap (l.sharesOf h) sn .to_nearest hheldn hsnn
    (Number.negative_false_of_nonneg _ hheldn hheld0)
    (Number.negative_false_of_nonneg _ hsnn (by rw [hsv]; exact hs0))
    (le_trans hbal (SingleAssetVault.Vault.sharesTotal_le_maxRep l.vault)) (by rw [hsv]; exact hcap)
  rw [hd]
  exact nofun

/-- Proof body of the "never throws" row of VaultWithdraw. -/
lemma LendingLedger.vaultWithdraw_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (amount : WithdrawAmount)
    -- the holder's shares are within SharesTotal, which C++ keeps for the share MPT
    (hbal : (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat)
    -- on an XRP vault the shares redeemed are worth at most `10^17` drops (FV_M2_25)
    (hxrp : l.vault.numericType = NumericType.native → ∀ shares : STAmount, amount = .vaultShares shares →
      l.vault.idealAssetsWithdraw (l.isSoleShareholder h) shares.toRat ≤ 10 ^ 17) :
    ∃ r, (l.apply (.vaultWithdraw h amount)).run = .ok r := by
  cases hrun : (l.apply (.vaultWithdraw h amount)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, hv⟩ := LendingLedger.applyVault_error rfl hrun
    obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultWithdraw_canonical l hr.holdsAsset h amount hpre
    have hkind : e = .notLawful ∨ e = .wrap := by
      simp only [LendingLedger.applyVault] at hv
      split at hv
      · rename_i hpos
        -- the bound of the XRP case, at the net asset value the code computes
        have hxrp' : l.vault.numericType = NumericType.native → ∀ sh : STAmount, amount = .vaultShares sh →
            ∀ nav : Number, l.vault.assetsTotalForWithdrawal (l.isSoleShareholder h) = .ok nav →
            nav.toRat * sh.toRat ≤ (10 ^ 17 + 3 / 10) * l.vault.sharesTotal.toRat := by
          intro hnt sh hsh nav hnav
          have hideal := hxrp hnt sh hsh
          have hsh0 : 0 ≤ sh.toRat := by
            rw [hsh] at hpos
            exact le_of_lt hpos
          have hnle := nav_le hnav
          have hQ0 := SingleAssetVault.WdPrice.navQ_nonneg l.vault (l.isSoleShareholder h)
          have hS0 : 0 ≤ l.vault.sharesTotal.toRat := l.vault.wf.sharesTotal_nonneg
          unfold SingleAssetVault.RawVault.idealAssetsWithdraw at hideal
          rw [SingleAssetVault.RawVault.WF.toExact_sharesTotal l.vault.toRawVault l.vault.wf] at hideal
          generalize (if l.isSoleShareholder h = true then l.vault.depositNav else l.vault.withdrawNav) = Q
            at hideal hnle hQ0
          have h1 : nav.toRat * sh.toRat ≤ Q * sh.toRat * (1 + 1 / 10 ^ 18) := by
            have := mul_le_mul_of_nonneg_right hnle hsh0
            linarith
          rcases eq_or_lt_of_le hS0 with hSz | hSpos
          · -- no shares: the vault holds nothing
            have hSn : l.vault.sharesTotal = Number.zero :=
              (Number.toRat_eq_zero_iff_eq_zero l.vault.wf.sharesTotal_norm).mp hSz.symm
            obtain ⟨hA, hD⟩ := l.vault.valid.empty_shares hSn
            obtain ⟨-, hN0⟩ := SingleAssetVault.Vault.assetsTotalForWithdrawal_nonneg l.vault _ nav hnav
            have hnav0 : nav.toRat ≤ 0 := by
              obtain ⟨total, hat, hdown, hnear, -⟩ :=
                SingleAssetVault.Vault.assetsTotalForWithdrawal_steps_proof l.vault _ nav hnav
              obtain ⟨n, hlo, hval⟩ := hdown
              have htle := Number.lower_le _ n hlo
              rw [← hval, hA, hD, Number.toRat_zero, add_zero] at htle
              refine Number.RoundsToRepresentable.nonpos_of_nonpos nav _ hnear ?_
              have hL0 : 0 ≤ l.vault.lossUnrealized.toRat := l.vault.exact.lossUnrealized_nonneg
              split <;> linarith
            rw [← hSz, mul_zero]
            nlinarith
          · have h2 : Q * sh.toRat ≤ 10 ^ 17 * l.vault.sharesTotal.toRat := by
              rwa [div_le_iff₀ hSpos] at hideal
            nlinarith
        have hheld := hr.sharesNonneg.sharesOf h
        have hbal' : (l.sharesOf h).toRat ≤ l.vault.toExact.sharesTotal := by
          rw [SingleAssetVault.RawVault.WF.toExact_sharesTotal _ l.vault.wf]; exact hbal
        -- the shares a successful withdrawal burned
        have hburn : ∀ r : VaultWithAmounts,
            (l.vault.withdraw amount (l.isSoleShareholder h) l.now hpos (some (l.sharesOf h))).run = .ok (.ok r) →
            r.shares.toNumber .to_nearest ≠ .error e ∧ ∀ s : Number, r.shares.toNumber .to_nearest = .ok s →
              (l.sharesOf h).operator_sub s .to_nearest ≠ .error e := by
          intro r hok
          obtain ⟨hok', -⟩ := SingleAssetVault.Vault.withdraw_holder_ok l.vault amount _ l.now hpos _ r hok
          obtain ⟨hic, h64, hspos⟩ :=
            SingleAssetVault.Vault.withdraw_shares_form l.vault amount _ l.now hpos hc hty r hok'
          exact l.holder_sub_ne_error hr h hbal r.shares hic h64 hspos.le e
        unfold_ter at hv
        walk_ok'
        · exact withdraw_error hr.holdsAsset hr.totalStored hc hty hheld.1 hbal' hxrp' ‹_›
        · exact absurd ‹_› (hburn _ ‹_›).1
        · exact absurd ‹_› ((hburn _ ‹_›).2 _ ‹_›)
      · cases hv
    rcases hkind with rfl | rfl
    · exact l.vaultWithdraw_ne_notLawful hr h amount hbal hrun
    · exact l.applyVault_ne_wrap hr _ hpre hv

/-- The holder's shares convert into a share amount when they are a whole number within SharesTotal. -/
private lemma LendingLedger.holderShares_amount (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (hbal : (l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧
      (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) (e : Error) :
    STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest ≠ .error e ∧
      ∀ hs : STAmount, STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs → hs.ShareBalance := by
  obtain ⟨hden, h0, hle⟩ := hbal
  have hn := hr.sharesNormalized.sharesOf h
  have hcap := le_trans hle (SingleAssetVault.Vault.sharesTotal_le_maxRep l.vault)
  refine ⟨?_, fun hs hof => ?_⟩
  · obtain ⟨hs, hhs⟩ := STAmount.ofNumber_int64_ok (l.sharesOf h) .to_nearest hn
      (Number.negative_false_of_nonneg _ hn h0) hcap
    rw [hhs]
    exact nofun
  · obtain ⟨hty, -, hneg, -, -⟩ := STAmount.ofNumber_int64_shape _ _ _ hn h0 hden hcap hof
    have hic := (STAmount.ofNumber_integral_canonical _ _ _ _ (by decide) hof).1
    exact ⟨hty, hic.canonical (by rw [hty]; decide), hneg⟩

/-- Proof body of the "never throws" row of VaultClawback. -/
lemma LendingLedger.vaultClawback_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (assets : STAmount)
    -- the holder's shares are a whole number within SharesTotal, which C++ keeps for the share MPT
    (hbal : (l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧
      (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat)
    -- the holder owns the shares the clawback destroys, which C++ accountSend checks
    (hheld : ∀ (hs : STAmount) (amounts : VaultAmounts),
      STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
      (computeClawback l.vault assets hs (l.isSoleShareholder h)).run = .ok (.ok amounts) →
      amounts.shares.toRat ≤ (l.sharesOf h).toRat)
    -- an MPT vault holds less than `10^16` units, so the price of all the shares rounds back to the cash
    (htotal : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∃ r, (l.apply (.vaultClawback h assets)).run = .ok r := by
  cases hrun : (l.apply (.vaultClawback h assets)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨hpre, hv⟩ := LendingLedger.applyVault_error rfl hrun
    have hc := LendingTx.preflight_vaultClawback_canonical l hr.holdsAsset h assets hpre
    have hkind : e = .notLawful ∨ e = .wrap := by
      obtain ⟨hof, hbalance⟩ := l.holderShares_amount hr h hbal e
      simp only [LendingLedger.applyVault] at hv
      split at hv
      · rename_i hnn
        have hclaw : ∀ hs : STAmount, STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
            (l.vault.clawback assets hs (l.isSoleShareholder h) hnn).run = .error e →
            e = .notLawful ∨ e = .wrap := by
          intro hs hof' hcl
          refine clawback_error hr.holdsAsset hr.totalStored hc (hbalance hs hof') (fun amounts hcomp => ?_) hcl
          rw [SingleAssetVault.RawVault.WF.toExact_sharesTotal _ l.vault.wf]
          exact le_trans (hheld hs amounts hof' hcomp) hbal.2.2
        -- the shares a successful clawback destroyed
        have hburn : ∀ (hs : STAmount) (r : VaultWithAmounts),
            STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest = .ok hs →
            (l.vault.clawback assets hs (l.isSoleShareholder h) hnn).run = .ok (.ok r) →
            r.shares.toNumber .to_nearest ≠ .error e ∧ ∀ s : Number, r.shares.toNumber .to_nearest = .ok s →
              (l.sharesOf h).operator_sub s .to_nearest ≠ .error e := by
          intro hs r hof' hok
          obtain ⟨amounts, raw, hcomp, -, -, -, hsh⟩ :=
            SingleAssetVault.Vault.clawback_ok_reduces l.vault assets hs _ hnn r hok
          obtain ⟨hic, h64, hs0, -⟩ := SingleAssetVault.computeClawback_amounts_form l.vault assets hs _ amounts hc
            hnn (hbalance hs hof') hr.holdsAsset.maxValue_le hcomp
          rw [hsh]
          exact l.holder_sub_ne_error hr h hbal.2.2 amounts.shares hic h64 hs0 e
        unfold_ter at hv
        walk_ok'
        all_goals first
          | exact absurd ‹_› hof
          | exact hclaw _ ‹_› ‹_›
          | exact absurd ‹_› (hburn _ _ ‹_› ‹_›).1
          | exact absurd ‹_› ((hburn _ _ ‹_› ‹_›).2 _ ‹_›)
      · cases hv
    rcases hkind with rfl | rfl
    · exact l.vaultClawback_ne_notLawful hr h assets hbal hheld htotal hrun
    · exact l.applyVault_ne_wrap hr _ hpre hv

/-- Proof body of the "never throws" row of the burn of a holder's shares. -/
lemma LendingLedger.vaultBurnShares_no_exception_proof (l : LendingLedger) (hr : l.Reachable) (h : Nat)
    (amount : STAmount)
    -- the holder's shares are a whole number within SharesTotal, which C++ keeps for the share MPT
    (hbal : (l.sharesOf h).toRat.den = 1 ∧ 0 ≤ (l.sharesOf h).toRat ∧
      (l.sharesOf h).toRat ≤ l.vault.sharesTotal.toRat) :
    ∃ r, (l.apply (.vaultBurnShares h amount)).run = .ok r := by
  cases hrun : (l.apply (.vaultBurnShares h amount)).run with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    obtain ⟨-, hv⟩ := LendingLedger.applyVault_error rfl hrun
    have hkind : e = .notLawful := by
      obtain ⟨hof, hbalance⟩ := l.holderShares_amount hr h hbal e
      simp only [LendingLedger.applyVault] at hv
      unfold_ter at hv
      walk_ok'
      all_goals first
        | exact absurd ‹_› hof
        | exact absurd ‹_› (canBurnShares_ne_error _ _ _ _)
        | exact burnShares_error (hbalance _ ‹_›) ‹_›
    subst hkind
    exact l.vaultBurnShares_ne_notLawful hr h amount hbal hrun

end XRPL.Model.Lending
