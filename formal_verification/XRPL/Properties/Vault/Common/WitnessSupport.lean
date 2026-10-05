import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.ProofTactics
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRange
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts
import XRPL.Properties.Protocol.Number.ToRep.Common.Proofs
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.RoundToScaleHelpers
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU

/-! # Witness plumbing for the `*_attained` sharpness theorems

Shared, value-agnostic helpers for lifting the vault-operation `*_attained`
witnesses (whose concrete records live, fully visible, in the headline files)
into kernel proofs. The decimal pipeline (`checked`/`canonicalize`/`normalize`
and the `Number` arithmetic ops) is a well-founded recursion the kernel cannot
reduce by `decide`/defeq, so a concrete run is stepped by hand: the structural
`Except` binds collapse with `ok_bind` (from `Protocol/Common/Reduction`), and each
`Number` operation is traced through its equation lemmas the way the
`Number/*/Common/*/WitnessTrace.lean` files trace `operator_mul`/`operator_div`.

An in-range integral amount converts to the `Number` with the same mantissa at
exponent `0` (the `normalize` inside `from_rep` is the identity, discharged by
`doNormalize_id`); the value-specific version lives with each witness because the
`intAmount` step carries a concrete `Int64` mantissa literal. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Empty (`STAmount.zero`) integral amount converts to `Number.zero`. -/
theorem zero_int64_toNumber :
    (STAmount.zero .int64).toNumber .to_nearest = .ok Number.zero := by
  unfold STAmount.toNumber
  rw [if_pos (show (STAmount.zero .int64).integral = true from rfl),
    show (STAmount.zero .int64).intAmount = .ok { value := 0 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show (STAmount.zero .int64).integral = true from rfl)]; rfl]
  show IntAmount.toNumber { value := 0 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 0 0 largeRange.min largeRange.max .to_nearest = _
  unfold doNormalize
  rw [show ((0 : UInt64) == 0) = true from rfl]; simp only [if_true]

end XRPL.Model.SingleAssetVault
