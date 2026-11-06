import XRPL.Model.Protocol.TER
import XRPL.Properties.Protocol.Common.Reduction

/-! # Stepping through the lending `Except` pipelines

The lending exit proofs step through `do` blocks with `simp`, so the shared
`Except` identities are `simp` lemmas here. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

attribute [scoped simp] ok_bind err_bind pure_eq except_pure_eq

/-- A check passes exactly when it returns success. -/
theorem TER.isTesSuccess_iff (ter : TER) : ter.isTesSuccess = true ↔ ter = .tesSUCCESS := by
  unfold TER.isTesSuccess
  split <;> simp_all

/-- Every code other than success fails the check. -/
theorem TER.isTesSuccess_eq_false (ter : TER) (h : ter ≠ .tesSUCCESS) : ter.isTesSuccess = false := by
  cases hs : ter.isTesSuccess
  · rfl
  · exact absurd ((TER.isTesSuccess_iff ter).mp hs) h

end XRPL.Model.Lending
