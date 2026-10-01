import XRPL.Properties.Vault.Proofs.LawfulDeposit
import XRPL.Properties.Vault.Proofs.Create

/-! # Lawfulness of the created vault and of the operations' post-states

`create_toExact` reads the freshly created vault. Each `*_poststate_lawful` takes the
record an exit writes and shows its in-op `to_lawful` re-check succeeds. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **A newly created vault is empty.** Zero assets, zero shares, no unrealized loss,
with the requested maximum, asset type and scale. -/
theorem Vault.create_toExact (nt : NumericType) (scale : UInt8) (am : Option Number)
    (hmax_norm : ∀ m ∈ am, m.isNormalized) (hmax_pos : ∀ m ∈ am, 0 < m.toRat)
    (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) :
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.assetsTotal = 0 ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.assetsAvailable = 0 ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.sharesTotal = 0 ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.lossUnrealized = 0 ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).toExact.assetsMaximum
      = am.map Number.toRat ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).numericType = nt ∧
    (Vault.create_lawful nt scale am hmax_norm hmax_pos hscale_int hscale_le).scale = scale :=
  Vault.create_toExact_proof nt scale am hmax_norm hmax_pos hscale_int hscale_le

/-- **Post-state lawfulness for `deposit`.** A successful deposit's computed record
re-validates: its in-op `to_lawful` re-check returns `.ok v'`. The record carries the
clamped charge, so the pricing and the recorded charge are named separately. -/
theorem Vault.deposit_poststate_lawful (v : Vault) (amount : STAmount) (isDonation : Bool)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanon : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (am aD sC : STAmount) (cN sN at' av' st' : Number)
    (hround : roundToVaultExponent amount v.assetsTotal = .ok am)
    (hamz : am.isZero = false)
    (hsh_don : isDonation = true → v.sharesTotal.mantissa_ ≠ 0)
    (hdon_eq : isDonation = true → aD = am ∧ sC = STAmount.zero .int64)
    (hcomp : isDonation = false → ∃ priced : STAmount,
      computeDeposit v am = .ok (.success priced sC) ∧
      clampToSumExponent v.assetsTotal priced = .ok aD ∧
      aD.isFractionalNonPositive = .ok false)
    (hcN : aD.toNumber .to_nearest = .ok cN) (hsN : sC.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + sC.toRat ≤ 2 ^ 63 - 1) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } :=
  Vault.deposit_lawful v amount isDonation hL hAV hcanon hnn am aD sC cN sN at' av' st'
    hround hamz hsh_don hdon_eq hcomp hcN hsN hat hav hst hmax hSsz

/-- **Post-state lawfulness for a subtracting exit (withdraw non-final / clawback).**
Subtracting one payout from both asset totals and one burn from `sharesTotal`
re-validates. `hempty`: dropping to zero shares must also zero the assets. -/
theorem Vault.withdraw_poststate_lawful (v : Vault)
    (payout burned at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hp_norm : payout.isNormalized) (hp_nn : 0 ≤ payout.toRat)
    (hp_le : payout.toRat ≤ v.assetsTotal.toRat)
    (hb_norm : burned.isNormalized) (hb_nn : 0 ≤ burned.toRat)
    (hb_den : burned.toRat.den = 1) (hb_le : burned.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hat : v.assetsTotal.operator_sub payout .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_sub payout .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_sub burned .to_nearest = .ok st')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } :=
  Vault.subtract_lawful v payout burned at' av' st' hL hAV hp_norm hp_nn hp_le hb_norm hb_nn
    hb_den hb_le hfit hat hav hst hempty

/-- **Post-state lawfulness for the final withdrawal.** The all-zero record (both
asset totals and `sharesTotal` zeroed) re-validates like a freshly created vault. -/
theorem Vault.withdraw_final_poststate_lawful (v : Vault)
    (hL : v.toExact.lossUnrealized = 0) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } :=
  Vault.zero_lawful v hL

/-- **Post-state lawfulness for `clawback`.** Delegates to the subtracting-exit
assembly. `hempty`: a recovery that empties the shares must also empty the assets. -/
theorem Vault.clawback_poststate_lawful (v : Vault)
    (assetsRecoveredNumber sharesDestroyedNumber at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hr_norm : assetsRecoveredNumber.isNormalized) (hr_nn : 0 ≤ assetsRecoveredNumber.toRat)
    (hr_le : assetsRecoveredNumber.toRat ≤ v.assetsTotal.toRat)
    (hd_norm : sharesDestroyedNumber.isNormalized) (hd_nn : 0 ≤ sharesDestroyedNumber.toRat)
    (hd_den : sharesDestroyedNumber.toRat.den = 1)
    (hd_le : sharesDestroyedNumber.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ v' : Vault,
      ({ v.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } :=
  v.withdraw_poststate_lawful assetsRecoveredNumber sharesDestroyedNumber at' av' st'
    hL hAV hr_norm hr_nn hr_le hd_norm hd_nn hd_den hd_le hfit hat hav hst hempty

/-- **Post-state lawfulness for `burnShares`.** The record with only `sharesTotal`
reduced re-validates: its in-op `to_lawful` re-check returns `.ok v'`. -/
theorem Vault.burnShares_poststate_lawful (v : Vault)
    (sharesDestroyed sharesTotalAmount : STAmount) (sdn st' : Number)
    (hcan : v.canBurnShares = .ok (.assets sharesTotalAmount))
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sdn)
    (hst : v.sharesTotal.operator_sub sdn .to_nearest = .ok st') :
    ∃ v' : Vault, ({ v.toRawVault with sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st' } :=
  Vault.burnShares_lawful v sharesDestroyed sharesTotalAmount sdn st' hcan hcanon hnn hle hfit
    hnum hst

end XRPL.Model.SingleAssetVault
