import XRPL.Properties.Protocol.IntAmount.Accessors.Common.Proofs

namespace XRPL.Model.Protocol

/-- `value` accessor returns exactly `toRat`. -/
theorem IntAmount.value_toRat (x : IntAmount) :
    ((IntAmount.value x).toInt : ℚ) = x.toRat :=
  IntAmount.value_toRat_proof x

end XRPL.Model.Protocol
