import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.Guard
import XRPL.Properties.Protocol.Number.Add.Common.Align

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace XRPL.Model.Protocol

lemma abs_add_eq_of_same_sign {x y : Number} (h : x.negative_ = y.negative_) :
    |x.toRat + y.toRat| = |x.toRat| + |y.toRat| := by
  cases hxn : x.negative_
  · have hyn : y.negative_ = false := h ▸ hxn
    have hx_nn : 0 ≤ x.toRat := Number.toRat_nonneg_of_nonnegative x hxn
    have hy_nn : 0 ≤ y.toRat := Number.toRat_nonneg_of_nonnegative y hyn
    rw [abs_of_nonneg (add_nonneg hx_nn hy_nn), abs_of_nonneg hx_nn, abs_of_nonneg hy_nn]
  · have hyn : y.negative_ = true := h ▸ hxn
    have hx_np : x.toRat ≤ 0 := Number.toRat_nonpos_of_negative x hxn
    have hy_np : y.toRat ≤ 0 := Number.toRat_nonpos_of_negative y hyn
    rw [abs_of_nonpos (add_nonpos hx_np hy_np), abs_of_nonpos hx_np, abs_of_nonpos hy_np]
    ring

end XRPL.Model.Protocol
