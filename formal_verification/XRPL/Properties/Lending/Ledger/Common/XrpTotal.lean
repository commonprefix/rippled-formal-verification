import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.TotalStoredInv
import XRPL.Properties.Lending.Loan.Common.SetScale

/-! # On XRP the vault total is within the largest XRP amount

Every vault update stores AssetsAvailable + AssetsDeployed as an amount of the asset (C++ `syncAssetsTotal`). XRP
balances are whole drops far below `2^63`, so their sum is exact and the stored total is the sum itself. An MPT sum
of `2^63` or `2^63 + 1` is stored rounded down, so the same does not follow there. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- On a reachable XRP ledger AssetsAvailable + AssetsDeployed is at most the largest XRP amount. The vault stored
the sum as an XRP amount, and a sum of drops is exact. -/
lemma LendingLedger.Reachable.total_le_native {l : LendingLedger} (hr : l.Reachable)
    (hnt : l.vault.numericType = NumericType.native) :
    l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ l.vault.numericType.maxValue.toNat := by
  have hint : l.vault.numericType.isIntegral = true := by rw [hnt]; rfl
  have hAAN := l.vault.wf.assetsAvailable_norm
  have hADN := l.vault.wf.assetsDeployed_norm
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  obtain ⟨hAAd, hAA63⟩ := STAmount.whole_of_stored _ hint _ hAAN hAA0 hr.availableStored
  obtain ⟨hADd, -⟩ := STAmount.whole_of_stored _ hint _ hADN hAD0 l.vault.valid.assetsDeployed_representable
  obtain ⟨d, hd16, hdv⟩ := hr.deployed_units
  have hAD16 : l.vault.assetsDeployed.toRat ≤ 10 ^ 16 := by
    rw [hdv, Vault.baseExponent_integral l.vault hint, zpow_zero, mul_one]
    exact_mod_cast hd16
  -- XRP amounts are at most `10^17` drops, so the sum is below `2^63`
  have hAA17 : l.vault.assetsAvailable.toRat ≤ 10 ^ 17 := by
    have hrep := (STAmount.isRounded_eq_false_iff _ _ hAAN hAA0).mp hr.availableStored
    rw [hnt] at hrep
    rcases hrep with h0 | ⟨-, k, hk, -, hkv⟩
    · rw [h0]; norm_num
    · rw [hkv]
      exact_mod_cast (show k ≤ 100000000000000000 from hk)
  exact XRPL.Model.SingleAssetVault.TotalStores.whole_le hr.totalStored hr.holdsAsset hint hAAN hADN hAA0 hAD0 hAAd
    hADd (by linarith [show (10 : ℚ) ^ 17 + 10 ^ 16 < 2 ^ 63 by norm_num])

end XRPL.Model.Lending
