import XRPL.Properties.Protocol.IOUAmount.Common.Defs
import XRPL.Properties.Protocol.IOUAmount.Accessors.Accessors
import XRPL.Properties.Protocol.IOUAmount.Signum.Signum
import XRPL.Properties.Protocol.IOUAmount.Constructors.Constructors
import XRPL.Properties.Protocol.IOUAmount.ToNumber.ToNumber
import XRPL.Properties.Protocol.IOUAmount.Compare.Compare
import XRPL.Properties.Protocol.IOUAmount.Neg.Neg
import XRPL.Properties.Protocol.IOUAmount.Add.RoundsWithin
import XRPL.Properties.Protocol.IOUAmount.Sub.RoundsWithin

/-! # `IOUAmount` operator-correctness aggregator

Imports every `IOUAmount` headline file. `mulRatio` has no theorem. -/
