import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.AssetPool

namespace XRPL.Model.Lending1_1

open XRPL.Model.Lending (AssetPool PoolAmounts)
open XRPL.Model.SingleAssetVault (Vault RawVault)

-- A vault is the asset pool of the lending protocol. Writing the amounts back re-checks the vault.
instance : AssetPool Vault where
  amounts v :=
    { assetsTotal := v.assetsTotal, assetsAvailable := v.assetsAvailable,
      assetsReserved := v.assetsReserved, lossUnrealized := v.lossUnrealized }
  updateAmounts v a :=
    let rawVault' : RawVault := { v.toRawVault with
      assetsTotal := a.assetsTotal, assetsAvailable := a.assetsAvailable
      assetsReserved := a.assetsReserved, lossUnrealized := a.lossUnrealized }
    rawVault'.to_lawful

end XRPL.Model.Lending1_1
