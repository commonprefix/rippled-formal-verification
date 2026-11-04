import XRPL.Properties.Vault.Proofs.Support.ReachableHistory
import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs

/-! # Witnesses for the deposit rounding of the request

Each run's result is computed by the model and checked by `native_decide`.

* Truncation: a reachable scale-0 vault holding 10 rounds a deposit of `1.5` to `1`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.DepWit

open XRPL.Model.Protocol

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

def vT : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 none none 0 [(iouAmount 1000000000000000 (-14), false)]

lemma vT_reach : Vault.Reachable vT 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

def aT : STAmount := iouAmount 1500000000000000 (-15)

end XRPL.Model.SingleAssetVault.DepWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol DepWit

/-- Truncation: `1.5` is rounded to `1`. -/
lemma Vault.roundedDepositAmount_truncation_witness :
    ∃ (v : Vault) (amountDeposit roundedAmount : STAmount),
      (amountDeposit.integral = false → amountDeposit.IOUCanonical) ∧ 0 < amountDeposit.toRat ∧
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) ∧
      roundedAmount.toRat < amountDeposit.toRat :=
  ⟨vT, aT, iouAmount 1000000000000000 (-15),
    (STAmount.canonical_of_canonicalB aT (by native_decide)).2, by native_decide, by native_decide,
    by native_decide⟩

end XRPL.Model.SingleAssetVault
