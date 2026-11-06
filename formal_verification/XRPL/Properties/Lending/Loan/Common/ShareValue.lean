import XRPL.Properties.Lending.Loan.Common.ManageCoverBase
import XRPL.Properties.Vault.Common.WithdrawDefs

/-! # Proof bodies for the share value around impair, unimpair and default

shareValue = (AssetsTotal − LossUnrealized) / SharesTotal, read exactly. An impair moves only
LossUnrealized, and a default the cover pays in full leaves AssetsTotal unchanged. -/

namespace XRPL.Model.SingleAssetVault

/-- The value of one share, exactly: (AssetsTotal − LossUnrealized) / SharesTotal. -/
def RawVault.shareValue (rv : RawVault) : ℚ :=
  rv.withdrawNav / rv.toExact.sharesTotal

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The share value of a vault that differs from another only in LossUnrealized. -/
private lemma shareValue_of_loss (v : Vault) (rv : RawVault)
    (h : rv = { v.toRawVault with lossUnrealized := rv.lossUnrealized }) :
    rv.shareValue = (v.toExact.assetsTotal - rv.lossUnrealized.toRat) / v.toExact.sharesTotal := by
  rw [h]
  rfl

variable (loan : Loan) (v : Vault) (now : UInt32)

/-- Proof body of the share value part of `Lending.impair_updates`. -/
lemma Loan.impair_share_value_proof (r : LoanWithPool Vault) (hok : (loan.manageImpair v now).run = .ok (.ok r))
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    v.shareValue - r.pool'.shareValue =
      (r.pool'.lossUnrealized.toRat - v.lossUnrealized.toRat) / v.toExact.sharesTotal := by
  obtain ⟨hrec, -⟩ := Loan.manageImpair_record loan v now r hok haa
  rw [shareValue_of_loss v _ hrec]
  show (v.toExact.assetsTotal - v.lossUnrealized.toRat) / v.toExact.sharesTotal - _ = _
  ring

/-- A fully covered default on the base grid. With PrincipalOutstanding in whole base units and the cover
caps above it, the cover pays it all and AssetsTotal is unchanged. -/
lemma Loan.default_fully_covered_at_base (minimumCover liquidationAmount : Number) (a p : ℕ)
    (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hcov : loan.principalOutstanding.toRat ≤ min liquidationAmount.toRat loan.broker.coverAvailable.toRat)
    (hnt : loan.broker.numericType = v.numericType)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hpo : loan.principalOutstanding.toRat = (p : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + loan.principalOutstanding.toRat ≤
      (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent)
    (hdeployed : ∃ w : Number, w.isNormalized ∧
      w.toRat = v.assetsDeployed.toRat - loan.principalOutstanding.toRat) :
    r.amountToPool.toRat = loan.principalOutstanding.toRat ∧ r.pool'.toExact.assetsTotal = v.toExact.assetsTotal := by
  have hcap : min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat =
      loan.principalOutstanding.toRat := by
    have h1 := (le_min_iff.mp hcov).1
    have h2 := (le_min_iff.mp hcov).2
    rw [min_eq_right h1, min_eq_left h2]
  have hroom' : v.assetsAvailable.toRat + min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat ≤ (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent := by
    rw [hcap]; exact hroom
  obtain ⟨hdc, -⟩ := Loan.manageDefault_at_base loan v _ _ a r hok hmin hliq hnt haa hroom'
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hdcv : r.amountToPool.toRat = loan.principalOutstanding.toRat := by
    rw [hdc, hcap, hpo, mul_div_assoc, div_self hp.ne', mul_one]
    norm_cast
  refine ⟨hdcv, ?_⟩
  obtain ⟨hat, -⟩ := Loan.manageDefault_vault_at_base loan v _ _ a r hok hmin hliq hnt haa hroom' hdeployed
  rw [hat, hdcv]
  ring

end XRPL.Model.Lending
