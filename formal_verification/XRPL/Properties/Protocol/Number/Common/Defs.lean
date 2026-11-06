import Mathlib.Tactic

import XRPL.Properties.Approx
import XRPL.Properties.Protocol.Number.Common.ClosestRepresentable
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize


namespace XRPL.Model.Protocol

/-- `result` has the value of a representable neighbour of `truth`: `upper` for `upward`, `lower` for `downward`,
the one toward zero for `towards_zero`, and either one for `to_nearest`. -/
def Number.RoundsToRepresentable (result : Number) (truth : ℚ) (mode : rounding_mode) : Prop :=
  match mode with
  | .to_nearest   =>
      (∃ n, Number.lower truth = some n ∧ result.toRat = n.toRat) ∨
      (∃ n, Number.upper truth = some n ∧ result.toRat = n.toRat)
  | .upward       =>
      ∃ n, Number.upper truth = some n ∧ result.toRat = n.toRat
  | .downward     =>
      ∃ n, Number.lower truth = some n ∧ result.toRat = n.toRat
  | .towards_zero =>
      ∃ n, (if truth ≥ 0 then Number.lower truth else Number.upper truth) = some n ∧
            result.toRat = n.toRat

end XRPL.Model.Protocol
