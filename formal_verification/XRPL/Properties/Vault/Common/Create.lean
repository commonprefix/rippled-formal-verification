import XRPL.Model.Vault.VaultCreate
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Proofs.Walk

/-! # Vault creation

`Vault.create` builds the empty vault from the creation inputs and re-validates it with
`to_lawful`. Reading the created record back is the base case of every `Vault.Reachable`
induction. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A created vault is the empty record built from the creation inputs. -/
lemma Vault.create_ok_toRawVault {scale : Option UInt8} {assetsMaximum : Option Number}
    {schedule : Option VaultSchedule} {earlyExitFeeRate : Option TenthBips32}
    {ownerCanBlockDeposit : Bool} {nt : NumericType} {v : Vault}
    (h : Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok v) :
    v.toRawVault = {
      assetsAvailable := Number.zero
      assetsDeployed := Number.zero
      assetsReserved := Number.zero
      assetsMaximum := assetsMaximum.filter (·.operator_ne Number.zero)
      numericType := nt
      scale := if nt.isIntegral then 0 else scale.getD vaultDefaultIOUScale
      sharesTotal := Number.zero
      lossUnrealized := Number.zero
      yieldUnrealized := Number.zero
      schedule
      earlyExitFeeRate := if schedule.isSome then earlyExitFeeRate else none
      ownerCanBlockDeposit
      depositBlocked := false } := by
  unfold Vault.create at h
  exact (RawVault.to_lawful_ok h).1

/-- A creation the checks accept has a maximum on the vault's base grid. -/
lemma Vault.canCreate_assetsMaximum (scale : Option UInt8) (assetsMaximum : Option Number)
    (schedule : Option VaultSchedule) (t : UInt32) (nt : NumericType)
    (h : Vault.canCreate scale assetsMaximum schedule t nt = .ok .tesSUCCESS) :
    ∀ m ∈ assetsMaximum, m.isOnExponentGrid (nt.baseExponent (scale.getD vaultDefaultIOUScale)) nt = .ok true := by
  intro m hm
  simp only [Option.mem_def] at hm
  subst hm
  simp only [Vault.canCreate, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp_all

end XRPL.Model.SingleAssetVault
