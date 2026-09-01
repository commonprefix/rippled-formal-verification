import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Vault.Vault

open XRPL.Model.Protocol (Number NumericType Error)
open XRPL.Model.SingleAssetVault

-- Build a lawful vault from the raw C++ fields, validating at the boundary.
-- `.error .notLawful` is the untrusted-boundary rejection (the state is not lawful).
@[export lean_lawful_vault_build]
def lean_lawful_vault_build (assetsTotal : Number) (assetsAvailable : Number)
    (assetsMaximum : Option Number)
    (numericType : NumericType) (scale : UInt8) (sharesTotal : Number) (lossUnrealized : Number)
    : Except Error LawfulVault :=
  RawVault.to_lawful
    { assetsTotal, assetsAvailable,
      assetsReserved := Number.zero,
      assetsMaximum,
      numericType, scale, sharesTotal, lossUnrealized }

@[export lean_lawful_vault_assets_total]
def lean_lawful_vault_assets_total (lv : LawfulVault) : Number := lv.assetsTotal
@[export lean_lawful_vault_assets_available]
def lean_lawful_vault_assets_available (lv : LawfulVault) : Number := lv.assetsAvailable
@[export lean_lawful_vault_assets_maximum]
def lean_lawful_vault_assets_maximum (lv : LawfulVault) : Option Number := lv.assetsMaximum
@[export lean_lawful_vault_numeric_type]
def lean_lawful_vault_numeric_type (lv : LawfulVault) : NumericType := lv.numericType
-- 3-way tag: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
@[export lean_lawful_vault_numeric_tag]
def lean_lawful_vault_numeric_tag (lv : LawfulVault) : UInt8 :=
  match lv.numericType with
  | .fractional => 2
  | .integral maxValue _ _ _ => if maxValue == 100000000000000000 then 0 else 1
@[export lean_lawful_vault_scale]
def lean_lawful_vault_scale (lv : LawfulVault) : UInt8 := lv.scale
@[export lean_lawful_vault_shares_total]
def lean_lawful_vault_shares_total (lv : LawfulVault) : Number := lv.sharesTotal
@[export lean_lawful_vault_loss_unrealized]
def lean_lawful_vault_loss_unrealized (lv : LawfulVault) : Number := lv.lossUnrealized
