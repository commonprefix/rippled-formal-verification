import XRPL.Properties.Vault.Common.ClawbackDefs
import XRPL.Properties.Vault.Common.ClawbackReduction
import XRPL.Properties.Vault.Common.WithdrawAccuracy

/-! # `Vault.clawback` accuracy proofs

Proof bodies behind the accuracy headlines in `VaultClawback.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **Proof body of `clawback_vault_updates_integral`.** -/
theorem Vault.clawback_vault_updates_integral_proof (v : Vault) (assets : STAmount)
    (r : ClawbackResult)
    (hv : v.Lawful) (hint : v.numericType.isIntegral = true)
    (hok : v.clawback assets = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.assetsRecovered.toRat)
    (hsz : v.toExact.assetsTotal ≤ 2 ^ 63 - 1) :
    r.vault'.assetsTotal.toRat = v.toExact.assetsTotal - r.assetsRecovered.toRat ∧
    r.vault'.assetsAvailable.toRat = v.toExact.assetsAvailable - r.assetsRecovered.toRat := by
  obtain ⟨cr, hcomp, herr2, -, hra, -, sbn, arn, at', st', av', atr, atr',
      -, harn, hat, -, -, -, -, hav, hr⟩ :=
    Vault.clawback_success_reduces v assets r hok herr
  -- the recovered amount came from `sharesToAssetsWithdraw` and passed the
  -- `assetsAvailable` cap
  obtain ⟨-, sd, ar, arn2, -, has, hnum2, hcase⟩ :=
    computeClawback_none_reduces v assets cr hcomp herr2
  have hrec : ∃ sd' : STAmount, v.sharesToAssetsWithdraw sd' false = .ok cr.assetsRecovered := by
    rcases hcase with ⟨-, hval, -⟩ | ⟨-, clamped, sd', ar', arn', -, -, hshareA, -, -, hval, -⟩
    · exact ⟨sd, by rw [hval]; exact has⟩
    · exact ⟨sd', by rw [hval]; exact hshareA⟩
  obtain ⟨sd0, hsd0⟩ := hrec
  obtain ⟨hshape_nt, hshape_off, hshape_val⟩ :=
    Vault.sharesToAssetsWithdraw_integral_shape v sd0 cr.assetsRecovered false hint hsd0
  obtain ⟨sn, hsn_ok, hsn_val, hsn_norm, hsn_den⟩ :=
    STAmount.toNumber_integral_exact' cr.assetsRecovered .to_nearest
      (by rw [hshape_nt]; exact hint) hshape_off hshape_val
  have harn_eq : arn = sn := by
    rw [hsn_ok] at harn
    exact (Except.ok.inj harn).symm
  rw [harn_eq] at hat hav
  set k : ℚ := cr.assetsRecovered.toRat with hk_def
  have hknn : 0 ≤ k := by rw [hk_def, ← hra]; exact hnn
  -- the cap: the recovered value never exceeds `assetsAvailable`
  have hk_le_AA : k ≤ v.assetsAvailable.toRat := by
    have hgt : sn.operator_gt v.assetsAvailable = false := by
      rcases hcase with ⟨hgt', hvalA, -⟩ |
          ⟨-, clamped, sd', ar', arn', -, -, -, hnum', hgt', hvalA, -⟩
      · rw [← hvalA, hsn_ok] at hnum2
        rw [show arn2 = sn from (Except.ok.inj hnum2).symm] at hgt'
        exact hgt'
      · rw [← hvalA, hsn_ok] at hnum'
        rw [show arn' = sn from (Except.ok.inj hnum').symm] at hgt'
        exact hgt'
    have hbridge := operator_gt_iff sn v.assetsAvailable hsn_norm hv.wf.assetsAvailable_norm
    by_contra hc
    push_neg at hc
    have : sn.operator_gt v.assetsAvailable = true := by
      rw [hbridge, hsn_val]
      exact hc
    rw [this] at hgt
    exact absurd hgt (by simp)
  have hAA_le_A : v.assetsAvailable.toRat ≤ v.assetsTotal.toRat :=
    hv.valid.assetsAvailable_le
  have hsz' : v.assetsTotal.toRat ≤ 2 ^ 63 - 1 := hsz
  have hat_exact : at'.toRat = v.assetsTotal.toRat - k :=
    operator_sub_exact_int_le v.assetsTotal sn at' k hv.wf.assetsTotal_norm hsz'
      hsn_norm (by rw [hsn_val]) hsn_den hknn (le_trans hk_le_AA hAA_le_A) hat
  have hav_exact : av'.toRat = v.assetsAvailable.toRat - k :=
    operator_sub_exact_int_le v.assetsAvailable sn av' k hv.wf.assetsAvailable_norm
      (le_trans hAA_le_A hsz') hsn_norm (by rw [hsn_val]) hsn_den hknn hk_le_AA hav
  constructor
  · rw [hr]
    show at'.toRat = v.toExact.assetsTotal - cr.assetsRecovered.toRat
    exact hat_exact
  · rw [hr]
    show av'.toRat = v.toExact.assetsAvailable - cr.assetsRecovered.toRat
    exact hav_exact

end XRPL.Model.SingleAssetVault
