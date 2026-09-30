import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.Defs

/-! # Witnesses for the deposit rounding and vault-update rows

Each is closed by `native_decide` over the model.

* Truncation: depositing `0.4444444444444445` into a 3-asset / 7·10¹⁵-share IOU vault
  floors on the `10^(-15)` grid to `0.444444444444444`.
* Vault updates: donating `9000000000000000006` into an int64 vault holding
  `9000000000000000007` makes the exact total `18000000000000000013`, stored rounded to
  19 digits as `18000000000000000010`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.DepWit

open XRPL.Model.Protocol

def wvF : RawVault :=
  { assetsTotal := ⟨false, 3000000000000000000, -18⟩
  , assetsAvailable := ⟨false, 3000000000000000000, -18⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .fractional, scale := 0
  , sharesTotal := ⟨false, 7000000000000000000, -3⟩
  , lossUnrealized := Number.zero }

def wvFL : Vault := ⟨wvF, by native_decide, by native_decide⟩

def wtF : STAmount := STAmount.unchecked .fractional 4444444444444445 (-16) false

def wtrF : STAmount := STAmount.unchecked .fractional 4444444444444440 (-16) false

def wvDVU : RawVault :=
  { assetsTotal := ⟨false, 9000000000000000007, 0⟩
  , assetsAvailable := ⟨false, 9000000000000000007, 0⟩
  , assetsReserved := Number.zero
  , assetsMaximum := none, numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 1000000000000000000, 0⟩
  , lossUnrealized := Number.zero }

def wvDVUL : Vault := ⟨wvDVU, by native_decide, by native_decide⟩

def waDVU : STAmount := STAmount.unchecked .int64 9000000000000000006 0 false

lemma waDVU_pos : 0 < waDVU.toRat := by native_decide

/-- The donation's result, computed by the model. -/
def wrDVU : DepositResult :=
  (wvDVUL.deposit waDVU true waDVU_pos).toOption.getD (DepositResult.rejected wvDVUL .tecINTERNAL)

end XRPL.Model.SingleAssetVault.DepWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DepWit

set_option maxRecDepth 10000

lemma Vault.roundedDepositAmount_truncation_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount),
      v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat :=
  ⟨wvFL, wtF, wtrF, by native_decide⟩

lemma Vault.deposit_vault_updates_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (hpos : 0 < amountDeposit.toRat)
      (r : DepositResult),
      v.deposit amountDeposit isDonation hpos = .ok r ∧ r.error = none ∧
      r.vault'.assetsTotal.toRat ≠ v.toExact.assetsTotal + r.amountDeposit'.toRat :=
  ⟨wvDVUL, waDVU, true, waDVU_pos, wrDVU, by native_decide⟩

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.SingleAssetVault.DepWit

open XRPL.Model.Protocol

/-- Scale-15 IOU vault holding `1.234567890123456` (16 digits, on the IOU grid). -/
def wvG : RawVault :=
  { assetsTotal := ⟨false, 1234567890123456000, -18⟩
  , assetsAvailable := ⟨false, 1234567890123456000, -18⟩
  , assetsReserved := Number.zero, assetsMaximum := none
  , numericType := .fractional, scale := 15
  , sharesTotal := ⟨false, 1234567890123456000, -3⟩
  , lossUnrealized := Number.zero }

def wvGL : Vault := ⟨wvG, by native_decide, by native_decide⟩

/-- The deposit, `100`. -/
def waG : STAmount := STAmount.unchecked .fractional 1000000000000000 (-13) false

lemma waG_pos : 0 < waG.toRat := by native_decide

/-- The deposit's result, computed by the model. -/
def wrG : DepositResult :=
  (wvGL.deposit waG false waG_pos).toOption.getD (DepositResult.rejected wvGL .tecINTERNAL)

end XRPL.Model.SingleAssetVault.DepWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DepWit

set_option maxRecDepth 10000

/-- A canonical deposit into an on-grid vault leaves a total that is off the asset grid: the
charge `99.99999999999994` is clamped to the post-deposit grid, but the sum keeps the old
total's `10⁻¹⁵` digit, giving `101.234567890123396` (18 digits). -/
lemma Vault.deposit_offgrid_witness :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat) (r : DepositResult),
      amountDeposit.Canonical ∧ ¬ v.assetsRounded ∧
      v.deposit amountDeposit false hpos = .ok r ∧ r.error = none ∧
      r.vault'.assetsRounded :=
  ⟨wvGL, waG, waG_pos, wrG,
    ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, by decide, by decide, by decide, by decide⟩⟩,
    by unfold Vault.assetsRounded; native_decide, by native_decide, by native_decide,
    by unfold Vault.assetsRounded; native_decide⟩

end XRPL.Model.SingleAssetVault
