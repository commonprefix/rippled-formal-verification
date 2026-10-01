import XRPL.Properties.Vault.Proofs.DepositWitness
import XRPL.Properties.Vault.Proofs.AssociateAssetWitness

/-! # `associateAsset` is not a no-op

Every vault transactor calls `associateAsset` on the vault SLE after updating it, which
rounds each `kSmdNeedsAsset` field (`assetsTotal`, `assetsAvailable`, `assetsReserved`,
`lossUnrealized`, `assetsMaximum`) to the asset's precision. The model has no such step,
and each of deposit, withdraw and clawback can leave a field that it would round
(`Vault.assetsRounded`). The claim that it never does on a reachable vault is refuted in
`Unprovable.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **`associateAsset` is not a no-op after a deposit.** A canonical deposit of `100` into
an on-grid scale-15 IOU vault holding `1.234567890123456` leaves `assetsTotal` at
`101.234567890123396` (18 significant digits), off the STAmount grid. -/
theorem Vault.deposit_associateAsset_rounds :
    ∃ (v : Vault) (amountDeposit : STAmount) (hpos : 0 < amountDeposit.toRat) (r : DepositResult),
      v.deposit amountDeposit false hpos = .ok r ∧ r.vault'.assetsRounded :=
  let ⟨v, a, hpos, r, _, _, hok, _, hr⟩ := Vault.deposit_offgrid_witness
  ⟨v, a, hpos, r, hok, hr⟩

/-- **`associateAsset` is not a no-op after a withdrawal.** Redeeming all but one of the
`2·10¹⁵` shares of an on-grid IOU vault holding `2·10⁻⁸¹` leaves `assetsTotal` at `10⁻⁹⁶`,
below the smallest IOU magnitude, so the post-withdraw vault satisfies `assetsRounded`. -/
theorem Vault.withdraw_associateAsset_rounds :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (r : WithdrawResult),
      v.withdraw amount waiveUnrealizedLoss hpos = .ok r ∧ r.vault'.assetsRounded :=
  let ⟨v, a, w, hpos, r, _, hok, _, hr⟩ := Vault.withdraw_underflow_witness
  ⟨v, a, w, hpos, r, hok, hr⟩

/-- **`associateAsset` is not a no-op after a clawback.** Clawing back
`1999999999999999·10⁻⁹⁶` from the same vault leaves `assetsTotal` at `10⁻⁹⁶`, so the
post-clawback vault satisfies `assetsRounded`. -/
theorem Vault.clawback_associateAsset_rounds :
    ∃ (v : Vault) (assets holderShares : STAmount) (hnn : 0 ≤ assets.toRat) (r : ClawbackResult),
      v.clawback assets holderShares hnn = .ok r ∧ r.vault'.assetsRounded :=
  let ⟨v, a, h, hnn, r, _, hok, _, hr⟩ := Vault.clawback_underflow_witness
  ⟨v, a, h, hnn, r, hok, hr⟩

end XRPL.Model.SingleAssetVault
