import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.Lawful

/-! # `Vault.withdraw` exits (final withdrawal and error codes)

Proof bodies behind `VaultWithdrawReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.withdraw_final_proof (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (cw : ComputeWithdrawResult) (assetsNumber' : Number)
    (sharesTotalAmount allAvailable : STAmount)
    (hcomp : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets waiveUnrealizedLoss
        | .vaultShares shares => computeWithdrawByShares v shares waiveUnrealizedLoss)
      = .ok cw)
    (herr : cw.error = none)
    (haN : cw.assets'.toNumber .to_nearest = .ok assetsNumber')
    (hins : v.assetsAvailable.operator_lt assetsNumber' = false)
    (hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount)
    (hfin : cw.sharesRedeemed.operator_eq sharesTotalAmount = true)
    (hloss : v.lossUnrealized.operator_ne Number.zero = false)
    (hallAvail : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok allAvailable)
    (hpos : 0 < amount.amount.toRat) :
    ∃ v' : Vault,
      v.withdraw amount waiveUnrealizedLoss hpos = .ok ⟨none, v', allAvailable, cw.sharesRedeemed⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  have hL : v.toExact.lossUnrealized = 0 :=
    (Number.operator_ne_zero_eq_false_iff v.lossUnrealized v.wf.lossUnrealized_norm).mp hloss
  obtain ⟨v', htl, hlv'eq⟩ := Vault.zero_lawful v hL
  refine ⟨v', ?_, hlv'eq⟩
  cases amount <;>
    simp_all [Vault.withdraw, bind, Except.bind, pure, Except.pure]

/-- Every outcome of a `computeWithdrawBy*` that runs without a throw. -/
private lemma computeWithdraw_error_codes (v : Vault) (amount : WithdrawAmount) (w : Bool)
    (cw : ComputeWithdrawResult)
    (hok : (match amount with
        | .vaultAssets assets => computeWithdrawByAssets v assets w
        | .vaultShares shares => computeWithdrawByShares v shares w) = .ok cw) :
    cw.error = none ∨ cw.error = some .tecPRECISION_LOSS ∨ cw.error = some .tecPATH_DRY := by
  cases amount <;>
    simp only [computeWithdrawByAssets, computeWithdrawByShares, bind, Except.bind, pure,
      Except.pure, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok <;>
    walk_ok <;> simp

lemma Vault.withdraw_error_codes_proof (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (r : WithdrawResult)
    (hpos : 0 < amount.amount.toRat) (hok : v.withdraw amount waiveUnrealizedLoss hpos = .ok r) :
    r.error = none ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecINSUFFICIENT_FUNDS ∨
    r.error = some .tefINTERNAL := by
  have hcw := computeWithdraw_error_codes v amount waiveUnrealizedLoss
  cases amount <;> simp only [Vault.withdraw, bind, Except.bind, pure, Except.pure] at hok <;>
    walk_ok
  all_goals first
    | (rcases hcw _ ‹_› with h | h | h <;> simp [h])
    | simp [WithdrawResult.rejected]

end XRPL.Model.SingleAssetVault
