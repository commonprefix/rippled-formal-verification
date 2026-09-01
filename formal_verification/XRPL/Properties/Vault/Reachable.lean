import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Common.ReachableProofs

/-! # Vault reachability (statement sketch)

`LawfulVault.Reachable v` holds when `v` is the result of `LawfulVault.create_lawful` with parameters
satisfying the creation hypotheses, or the result of a `deposit`, `withdraw`,
`clawback`, or `burnShares` that ran without a throw on a vault that is itself
reachable, with the operation's user-supplied inputs satisfying the
canonical-storage and sign side conditions of the matching preservation theorem
(the facts about the amounts the run computes are derived inside that theorem).
The constructors do not require the operation to succeed. A rejected operation returns the starting
vault unchanged (the theorems in `Unchanged.lean`), so admitting rejected
results does not enlarge the set of states. `create` is the only constructor
that does not require a prior reachability proof, so every proof of
`LawfulVault.Reachable` starts with a creation. Induction on `LawfulVault.Reachable`
therefore has exactly one base case, `create`, and one step case per operation,
which is how induction over `LawfulVault.Reachable` covers every possible history: `create_lawful`
discharges the creation case and the preservation theorems discharge the
operation cases. The zero-loss corollary and the asset-parity corollary supply
the state hypotheses those preservation theorems take.
-/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- No operation changes `lossUnrealized`. -/
theorem LawfulVault.Reachable.lossUnrealized_zero (lv : LawfulVault) (hr : LawfulVault.Reachable lv) :
    lv.toExact.lossUnrealized = 0 :=
  LawfulVault.Reachable.lossUnrealized_zero_proof lv hr

/-- Every operation writes both asset fields with the identical update, so
record-level asset parity holds on all reachable states. -/
theorem LawfulVault.Reachable.asset_parity (lv : LawfulVault) (hr : LawfulVault.Reachable lv) :
    lv.assetsAvailable = lv.assetsTotal :=
  LawfulVault.Reachable.asset_parity_proof lv hr

end XRPL.Model.SingleAssetVault
