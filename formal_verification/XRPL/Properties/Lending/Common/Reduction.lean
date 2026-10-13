import XRPL.Properties.Protocol.Common.Reduction

/-! # Stepping through the lending `Except` pipelines

The lending exit proofs step through `do` blocks with `simp`, so the shared
`Except` identities are `simp` lemmas here. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

attribute [scoped simp] ok_bind err_bind pure_eq except_pure_eq

end XRPL.Model.Lending
