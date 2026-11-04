import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.MaxValueFits

/-! # `Vault.withdraw` exits

One line per exit of `Vault.withdraw_exits`, in the order the withdrawal runs its checks. A rejection
carries only its code: the vault is not touched. The later exits assume the earlier checks passed, read off
the code (`Vault.WithdrawPriced` for the entry checks, `Vault.WithdrawNonFinal` before the fee). -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-- A net asset value with a zero mantissa prices any shares at zero. -/
theorem Vault.sharesToAssetsWithdraw_zero_nav (shares : STAmount) (waiveUnrealizedLoss : Bool)
    (netAssetValue : Number) (hnav : v.assetsTotalForWithdrawal waiveUnrealizedLoss = .ok netAssetValue)
    (hz : netAssetValue.mantissa_ = 0) :
    v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok (STAmount.zero v.numericType) :=
  Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waiveUnrealizedLoss netAssetValue hnav hz

/-- The exits of `withdraw`, in the order it runs its checks, then its success lines. Each line assumes the checks
before it passed. -/
theorem Vault.withdraw_exits (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat) :
    ((v.earlyExitFeeRate.isNone && v.phase t == .investment) = true →
      (v.withdraw amount waive t hpos).run = .ok (.error .tecTOO_SOON)) ∧
    (∀ ter : TER, (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false →
      (computeWithdraw v amount waive).run = .ok (.error ter) →
      (v.withdraw amount waive t hpos).run = .ok (.error ter)) ∧
    (∀ (amounts : VaultAmounts) (sharesTotalAmount : STAmount),
      (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false →
      (computeWithdraw v amount waive).run = .ok (.ok amounts) →
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount →
      amounts.shares.operator_eq sharesTotalAmount = true → v.assetsDeployed.operator_ne Number.zero = true →
      (v.withdraw amount waive t hpos).run = .ok (.error .tecHAS_OBLIGATIONS)) ∧
    (∀ (shares : STAmount) (hpos' : 0 < (WithdrawAmount.vaultShares shares).amount.toRat) (amounts : VaultAmounts)
        (sharesTotalAmount : STAmount) (assetsNumber netAssetValue : Number),
      v.WithdrawPriced (.vaultShares shares) waive t amounts sharesTotalAmount →
      amounts.shares.operator_eq sharesTotalAmount = false →
      amounts.assets.toNumber .to_nearest = .ok assetsNumber → v.assetsTotalForWithdrawal waive = .ok netAssetValue →
      amounts.assets.isZero = true → netAssetValue.operator_ne Number.zero = true →
      (v.withdraw (.vaultShares shares) waive t hpos').run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ (amounts : VaultAmounts) (sharesTotalAmount : STAmount) (assetsNumber netAssetValue : Number) (ter : TER),
      v.WithdrawPriced amount waive t amounts sharesTotalAmount →
      amounts.shares.operator_eq sharesTotalAmount = false →
      amounts.assets.toNumber .to_nearest = .ok assetsNumber → v.assetsTotalForWithdrawal waive = .ok netAssetValue →
      (amount.isByShares && amounts.assets.isZero && netAssetValue.operator_ne Number.zero) = false →
      v.checkDebitNotDust assetsNumber = .ok ter → (ter != .tesSUCCESS) = true →
      (v.withdraw amount waive t hpos).run = .ok (.error ter)) ∧
    (∀ (amounts : VaultAmounts) (sharesTotalAmount : STAmount) (assetsNumber : Number),
      v.WithdrawNonFinal amount waive t amounts sharesTotalAmount assetsNumber → v.earlyExitFeeRateAt t = 0 →
      v.assetsAvailable.operator_lt assetsNumber = true →
      (v.withdraw amount waive t hpos).run = .ok (.error .tecINSUFFICIENT_FUNDS)) ∧
    (∀ (amounts : VaultAmounts) (sharesTotalAmount : STAmount) (assetsNumber fee payoutNumber : Number)
        (payout : STAmount),
      v.WithdrawNonFinal amount waive t amounts sharesTotalAmount assetsNumber →
      (v.earlyExitFeeRateAt t == 0 && v.assetsAvailable.operator_lt assetsNumber) = false →
      (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false →
      tenthBipsOfValue assetsNumber (v.earlyExitFeeRateAt t) .upward = .ok fee →
      assetsNumber.operator_sub fee .downward = .ok payoutNumber →
      STAmount.ofNumber v.numericType payoutNumber .downward = .ok payout →
      (payout.isZero = true ∨ ∃ clamped : STAmount,
        clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent = .ok clamped ∧
          clamped.isFractionalNonPositive = .ok true) →
      (v.withdraw amount waive t hpos).run = .ok (.error .tecPRECISION_LOSS)) ∧
    (∀ (amounts : VaultAmounts) (sharesTotalAmount : STAmount) (assetsNumber fee payoutNumber clampedNumber : Number)
        (payout clamped : STAmount),
      v.WithdrawNonFinal amount waive t amounts sharesTotalAmount assetsNumber →
      (v.earlyExitFeeRateAt t == 0 && v.assetsAvailable.operator_lt assetsNumber) = false →
      (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false →
      tenthBipsOfValue assetsNumber (v.earlyExitFeeRateAt t) .upward = .ok fee →
      assetsNumber.operator_sub fee .downward = .ok payoutNumber →
      STAmount.ofNumber v.numericType payoutNumber .downward = .ok payout → payout.isZero = false →
      clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent = .ok clamped →
      clamped.isFractionalNonPositive = .ok false → clamped.toNumber .to_nearest = .ok clampedNumber →
      v.assetsAvailable.operator_lt clampedNumber = true →
      (v.withdraw amount waive t hpos).run = .ok (.error .tecINSUFFICIENT_FUNDS)) ∧
    (∀ (amounts : VaultAmounts) (sharesTotalAmount : STAmount) (assetsNumber : Number),
      v.WithdrawPriced amount waive t amounts sharesTotalAmount →
      amounts.shares.operator_eq sharesTotalAmount = true →
      amounts.assets.toNumber .to_nearest = .ok assetsNumber → v.assetsAvailable.operator_lt assetsNumber = true →
      (v.withdraw amount waive t hpos).run = .ok (.error .tecINSUFFICIENT_FUNDS)) ∧
    -- a transaction amount is a canonical amount of the vault's asset or of its shares, and the asset's maximum
    -- fits an int64 amount, as C++ caps every MPT maximum. The holder redeems fewer than all the shares
    (amount.amount.Canonical → amount.InAsset v.numericType →
      (v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) →
      (∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
        amounts.shares.toRat < v.toExact.sharesTotal) →
      (v.withdraw amount waive t hpos).run ≠ .error .notLawful) ∧
    -- a transaction amount is a canonical amount of the vault's asset or of its shares
    (∀ (t0 : UInt32) (r : VaultWithAmounts), Vault.Reachable v t0 → amount.amount.Canonical →
      amount.InAsset v.numericType → (v.withdraw amount waive t hpos).run = .ok (.ok r) →
      r.shares.toRat = v.toExact.sharesTotal →
      r.assets.toRat = v.assetsAvailable.toRat ∧ r.vault'.assetsAvailable = Number.zero ∧
        r.vault'.sharesTotal = Number.zero) ∧
    -- a transaction amount is a canonical amount of the vault's asset or of its shares. The holder redeems every
    -- outstanding share
    ∀ t0 : UInt32, Vault.Reachable v t0 → amount.amount.Canonical → amount.InAsset v.numericType →
      (∀ amounts : VaultAmounts, (computeWithdraw v amount waive).run = .ok (.ok amounts) →
        amounts.shares.toRat = v.toExact.sharesTotal) →
      (v.withdraw amount waive t hpos).run ≠ .error .notLawful :=
  ⟨Vault.withdraw_too_soon_proof v amount waive t hpos, Vault.withdraw_compute_rejected_proof v amount waive t hpos,
    Vault.withdraw_has_obligations_proof v amount waive t hpos,
    fun shares hpos' => Vault.withdraw_zero_payout_proof v shares waive t hpos',
    Vault.withdraw_payout_too_small_proof v amount waive t hpos,
    Vault.withdraw_insufficient_funds_proof v amount waive t hpos,
    Vault.withdraw_clamp_precision_loss_proof v amount waive t hpos,
    Vault.withdraw_payout_insufficient_funds_proof v amount waive t hpos,
    Vault.withdraw_final_insufficient_funds_proof v amount waive t hpos,
    Vault.withdraw_success_proof v amount waive t hpos,
    fun t0 r hr hc hty hok hfinal => Vault.withdraw_final_proof v amount waive t t0 hpos hr hc hty
      (Vault.Reachable.maxValue_fits v t0 hr (Vault.withdraw_sharesTotal_pos v amount waive t hpos hc hty r hok))
      r hok hfinal,
    fun t0 => Vault.withdraw_final_success_proof v amount waive t t0 hpos⟩

/-- A withdrawal never fails with `tefINTERNAL`: a final withdrawal finds nothing deployed, so
no unrealized loss. -/
theorem Vault.withdraw_never_internal (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) :
    (v.withdraw amount waive t hpos).run ≠ .ok (.error .tefINTERNAL) :=
  Vault.withdraw_never_internal_proof v amount waive t hpos

/-- Every rejection of a withdrawal. A `tefBAD_LEDGER` needs a cash amount not stored exactly. -/
theorem Vault.withdraw_error_codes (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat)
    -- the asset's maximum fits an int64 amount, as C++ caps every MPT maximum
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (ter : TER) (hok : (v.withdraw amount waive t hpos).run = .ok (.error ter)) :
    ter = .tecTOO_SOON ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecPATH_DRY ∨ ter = .tecHAS_OBLIGATIONS ∨
      ter = .tecINSUFFICIENT_FUNDS ∨
      (ter = .tefBAD_LEDGER ∧ STAmount.isRounded v.numericType v.assetsAvailable = true) :=
  Vault.withdraw_error_codes_proof v amount waive t hpos hmax ter hok

end XRPL.Model.SingleAssetVault
