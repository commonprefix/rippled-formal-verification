import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Protocol.Common.Reduction

/-! # Monadic reduction toolkit for `Vault.deposit`

Building blocks for stepping the `Except Error` do-blocks of the deposit
pipeline: a clean `if`-form characterization of `roundedDepositAmount` once
`roundToVaultExponent` is known, and the two bridges that read that
characterization back. The generic `Except` bind identities live in
`Protocol/Common/Reduction.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- Clean `if`-form of `roundedDepositAmount` when `roundToVaultExponent` succeeds. -/
theorem roundedDepositAmount_ok (v : Vault) (amountDeposit ra' : STAmount)
    (hr : roundToVaultExponent amountDeposit v.assetsTotal = .ok ra') :
    v.roundedDepositAmount amountDeposit =
      (if ra'.isZero then .ok (.rejected .tecPRECISION_LOSS) else .ok (.rounded ra')) := by
  simp only [Vault.roundedDepositAmount, hr, ok_bind]; rfl

/-- `roundedDepositAmount` propagates a `roundToVaultExponent` error. -/
theorem roundedDepositAmount_err (v : Vault) (amountDeposit : STAmount) (e : Error)
    (hr : roundToVaultExponent amountDeposit v.assetsTotal = .error e) :
    v.roundedDepositAmount amountDeposit = .error e := by
  simp only [Vault.roundedDepositAmount, hr, err_bind]

/-- A `rounded` outcome means `roundToVaultExponent` produced exactly that nonzero
amount. -/
theorem roundedDepositAmount_rounded (v : Vault) (amountDeposit ra : STAmount)
    (h : v.roundedDepositAmount amountDeposit = .ok (.rounded ra)) :
    roundToVaultExponent amountDeposit v.assetsTotal = .ok ra ∧ ra.isZero = false := by
  cases hr : roundToVaultExponent amountDeposit v.assetsTotal with
  | error e => rw [roundedDepositAmount_err v amountDeposit e hr] at h; exact absurd h (by simp)
  | ok ra' =>
    rw [roundedDepositAmount_ok v amountDeposit ra' hr] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hz
      rw [Except.ok.injEq, RoundingResult.rounded.injEq] at h
      subst h
      exact ⟨rfl, by simpa using hz⟩

end XRPL.Model.SingleAssetVault
