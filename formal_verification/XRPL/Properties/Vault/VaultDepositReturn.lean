import XRPL.Properties.Vault.Proofs.DepositExits

/-! # `Vault.deposit` exits

One line per exit of `Vault.deposit_exits`, in the order the deposit runs its checks. A rejection
carries only its code: the vault is not touched. The later exits assume the earlier checks passed,
read off the code (`Vault.DepositOpen` for the four entry checks). -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- The exits of `deposit`, in the order it runs its checks. Each line assumes the checks before it passed. -/
theorem Vault.deposit_exits (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) :
    ((v.phase t == .investment || v.phase t == .redemption) = true →
      (v.deposit amountDeposit false t hpos).run = .ok (.error .tecEXPIRED)) ∧
    (v.sharesTotal.mantissa_ = 0 → (v.deposit amountDeposit true t hpos).run = .ok (.error .tecNO_PERMISSION)) ∧
    ((v.phase t == .investment || v.phase t == .redemption) = false → v.isInsolvent = true →
      (v.deposit amountDeposit false t hpos).run = .ok (.error .tecLOCKED)) ∧
    ((!isDonation && (v.phase t == .investment || v.phase t == .redemption)) = false →
      (isDonation && v.sharesTotal.mantissa_ == 0) = false → (v.isInsolvent && !isDonation) = false →
      v.depositBlocked = true → (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecLOCKED)) ∧
    (∀ (assetsTotal : Number) (roundedAmount : STAmount), v.DepositOpen isDonation t →
      v.assetsTotal = .ok assetsTotal →
      clampToSumExponent assetsTotal amountDeposit v.baseExponent = .ok roundedAmount →
      roundedAmount.isZero = true →
      (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ roundedAmount shares : STAmount, v.DepositOpen false t →
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      assetsToSharesDeposit v roundedAmount = .ok shares → shares.isZero = true →
      (v.deposit amountDeposit false t hpos).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ roundedAmount shares assets : STAmount, v.DepositOpen false t →
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      assetsToSharesDeposit v roundedAmount = .ok shares → shares.isZero = false →
      sharesToAssetsDeposit v shares = .ok assets → assets.operator_gt roundedAmount = .ok true →
      (v.deposit amountDeposit false t hpos).run = .ok (.error .tecINTERNAL)) ∧
    (∀ (roundedAmount shares assets charge : STAmount) (assetsTotal : Number), v.DepositOpen false t →
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      assetsToSharesDeposit v roundedAmount = .ok shares → shares.isZero = false →
      sharesToAssetsDeposit v shares = .ok assets → assets.operator_gt roundedAmount = .ok false →
      v.assetsTotal = .ok assetsTotal → clampToSumExponent assetsTotal assets v.baseExponent = .ok charge →
      charge.isFractionalNonPositive = .ok true →
      (v.deposit amountDeposit false t hpos).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ (roundedAmount charge : STAmount) (assetsTotal : Number), v.DepositOpen true t →
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      v.assetsTotal = .ok assetsTotal → clampToSumExponent assetsTotal roundedAmount v.baseExponent = .ok charge →
      charge.isFractionalNonPositive = .ok true →
      (v.deposit amountDeposit true t hpos).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ roundedAmount : STAmount, v.DepositOpen isDonation t →
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      (computeDeposit v roundedAmount isDonation).run = .ok (.error .tecPATH_DRY) →
      (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecPATH_DRY)) ∧
    (∀ (roundedAmount : STAmount) (amounts : VaultAmounts) (ter : TER), v.DepositOpen isDonation t →
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts) →
      v.checkOpenLimit amounts.assets = .ok ter → (ter != .tesSUCCESS) = true →
      (v.deposit amountDeposit isDonation t hpos).run = .ok (.error ter)) ∧
    (∀ (roundedAmount : STAmount) (amounts : VaultAmounts) (raw : RawVault) (assetsTotal' : Number),
      v.DepositOpen isDonation t →
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts) →
      v.checkOpenLimit amounts.assets = .ok .tesSUCCESS →
      (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.ok raw) →
      raw.assetsTotal = .ok assetsTotal' →
      ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
        assetsTotal'.operator_gt (v.assetsMaximum.getD Number.zero)) = true →
      (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecLIMIT_EXCEEDED)) ∧
    -- a transaction amount is a canonical amount of the vault's asset, and the new share total stays within the
    -- MPT maximum
    ∀ (roundedAmount : STAmount) (amounts : VaultAmounts) (raw : RawVault) (assetsTotal' : Number),
      amountDeposit.Canonical → amountDeposit.mNumericType = v.numericType → v.DepositOpen isDonation t →
      (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount) →
      (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts) →
      v.checkOpenLimit amounts.assets = .ok .tesSUCCESS →
      (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.ok raw) →
      raw.assetsTotal = .ok assetsTotal' →
      ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
        assetsTotal'.operator_gt (v.assetsMaximum.getD Number.zero)) = false →
      (v.toExact.sharesTotal : ℚ) + amounts.shares.toRat ≤ 2 ^ 63 - 1 →
      ∃ v' : Vault, (v.deposit amountDeposit isDonation t hpos).run = .ok (.ok { amounts with vault' := v' }) ∧
        v'.toRawVault = raw :=
  ⟨Vault.deposit_expired_proof v amountDeposit t hpos, Vault.deposit_donation_no_shares_proof v amountDeposit t hpos,
    Vault.deposit_insolvent_proof v amountDeposit t hpos,
    Vault.deposit_blocked_proof v amountDeposit isDonation t hpos,
    Vault.deposit_rounded_zero_proof v amountDeposit isDonation t hpos,
    Vault.deposit_zero_shares_proof v amountDeposit t hpos, Vault.deposit_overpriced_proof v amountDeposit t hpos,
    Vault.deposit_zero_charge_proof v amountDeposit t hpos, Vault.deposit_zero_donation_proof v amountDeposit t hpos,
    fun roundedAmount hopen hrounded => Vault.deposit_compute_rejected_proof v amountDeposit isDonation t hpos
      roundedAmount _ hopen hrounded,
    Vault.deposit_inflow_rejected_proof v amountDeposit isDonation t hpos,
    Vault.deposit_maximum_exceeded_proof v amountDeposit isDonation t hpos,
    fun roundedAmount amounts raw assetsTotal' hc hty =>
      Vault.deposit_success_proof v amountDeposit isDonation t hpos hc hty roundedAmount amounts raw assetsTotal'⟩

/-- Every rejection of a deposit. -/
theorem Vault.deposit_error_codes (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat)
    (hc : amountDeposit.Canonical) -- a transaction amount is a canonical amount
    (hty : amountDeposit.mNumericType = v.numericType) -- of the vault's asset
    (ter : TER) (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.error ter)) :
    ter = .tecEXPIRED ∨ ter = .tecNO_PERMISSION ∨ ter = .tecLOCKED ∨ ter = .tecPRECISION_LOSS ∨
      ter = .tecINTERNAL ∨ ter = .tecPATH_DRY ∨ ter = .tecLIMIT_EXCEEDED :=
  Vault.deposit_error_codes_proof v amountDeposit isDonation t hpos hc hty ter hok

end XRPL.Model.SingleAssetVault
