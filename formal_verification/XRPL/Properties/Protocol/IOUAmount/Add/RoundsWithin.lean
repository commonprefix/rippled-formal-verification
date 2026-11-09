import XRPL.Properties.Protocol.IOUAmount.Add.Common.Proofs
import XRPL.Properties.Protocol.IOUAmount.Common.Defs

/-! # Correctness of the `IOUAmount` addition -/

namespace XRPL.Model.Protocol

/-- IOU addition rounding downward never lands above the true sum, and its relative error is at most `εDirected`,
about `10⁻¹⁵`. -/
theorem IOUAmount.operator_add_rounds_downward (x y result : IOUAmount)
    (hx : x.InRange16) (hy : y.InRange16)
    (hok : IOUAmount.operator_add x y .downward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat + y.toRat) .downward IOUAmount.εDirected :=
  IOUAmount.operator_add_rounds_proof x y result .downward hx hy
    (IOUAmount.operator_add_truth_ne_of_result x y result _ hx hy hok hresult) hok hresult

/-- IOU addition, `upward` directed rounding within `εDirected`. -/
theorem IOUAmount.operator_add_rounds_upward (x y result : IOUAmount)
    (hx : x.InRange16) (hy : y.InRange16)
    (hok : IOUAmount.operator_add x y .upward = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat + y.toRat) .upward IOUAmount.εDirected :=
  IOUAmount.operator_add_rounds_proof x y result .upward hx hy
    (IOUAmount.operator_add_truth_ne_of_result x y result _ hx hy hok hresult) hok hresult

/-- IOU addition, `towards_zero` directed rounding within `εDirected`. -/
theorem IOUAmount.operator_add_rounds_towards_zero (x y result : IOUAmount)
    (hx : x.InRange16) (hy : y.InRange16)
    (hok : IOUAmount.operator_add x y .towards_zero = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat + y.toRat) .towards_zero IOUAmount.εDirected :=
  IOUAmount.operator_add_rounds_proof x y result .towards_zero hx hy
    (IOUAmount.operator_add_truth_ne_of_result x y result _ hx hy hok hresult) hok hresult

/-- IOU addition under `to_nearest` has relative error at most `εToNearest`, about `½·10⁻¹⁵`. -/
theorem IOUAmount.operator_add_rounds_to_nearest_tight (x y result : IOUAmount)
    (hx : x.InRange16) (hy : y.InRange16)
    (hok : IOUAmount.operator_add x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    |result.toRat - (x.toRat + y.toRat)| ≤ |x.toRat + y.toRat| * IOUAmount.εToNearest :=
  IOUAmount.operator_add_rounds_to_nearest_proof x y result hx hy
    (IOUAmount.operator_add_truth_ne_of_result x y result _ hx hy hok hresult) hok hresult

/-- IOU addition rounds within `εDirected` in every mode. -/
theorem IOUAmount.operator_add_rounds (x y result : IOUAmount) (mode : rounding_mode)
    (hx : x.InRange16) (hy : y.InRange16)
    (hok : IOUAmount.operator_add x y mode = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    RoundsWithin result (x.toRat + y.toRat) mode IOUAmount.εDirected :=
  IOUAmount.operator_add_rounds_proof x y result mode hx hy
    (IOUAmount.operator_add_truth_ne_of_result x y result _ hx hy hok hresult) hok hresult

end XRPL.Model.Protocol
