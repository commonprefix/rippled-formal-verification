import XRPL.Properties.Protocol.Number.Signum.Common.Proofs


namespace XRPL.Model.Protocol

/-- `Number.signum` returns the sign of the value: `1` if positive, `-1` if negative, `0` if zero. The
`isNormalized` hypothesis rules out a "negative zero" (`negative_ = true`, `mantissa_ = 0`). -/
theorem Number.signum_eq (n : Number) (hn : n.isNormalized) :
    n.signum = if 0 < n.toRat then 1 else if n.toRat < 0 then -1 else 0 :=
  Number.signum_eq_proof n hn

theorem Number.signum_eq_one_iff (n : Number) (hn : n.isNormalized) :
    n.signum = 1 ↔ 0 < n.toRat :=
  Number.signum_eq_one_iff_proof n hn

theorem Number.signum_eq_neg_one_iff (n : Number) (hn : n.isNormalized) :
    n.signum = -1 ↔ n.toRat < 0 :=
  Number.signum_eq_neg_one_iff_proof n hn

theorem Number.signum_eq_zero_iff (n : Number) (hn : n.isNormalized) :
    n.signum = 0 ↔ n.toRat = 0 :=
  Number.signum_eq_zero_iff_proof n hn

/-- A `Number` has a positive sign exactly when it is not negative and its
mantissa is nonzero. -/
lemma Number.signum_pos_iff (n : Number) : 0 < n.signum ↔ n.negative_ = false ∧ n.mantissa_ ≠ 0 :=
  Number.signum_pos_iff_proof n

end XRPL.Model.Protocol
