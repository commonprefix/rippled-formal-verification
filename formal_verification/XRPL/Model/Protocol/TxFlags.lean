import Mathlib.Tactic


namespace XRPL.Model.Protocol

abbrev tfMPTUnauthorize : UInt32 := 0x00000001

abbrev tfFullyCanonicalSig : UInt32 := 0x80000000
abbrev tfInnerBatchTxn : UInt32 := 0x40000000
abbrev tfUniversal : UInt32 := tfFullyCanonicalSig ||| tfInnerBatchTxn

abbrev tfVaultPrivate : UInt32 := 0x00010000
abbrev tfVaultShareNonTransferable : UInt32 := 0x00020000

end XRPL.Model.Protocol
