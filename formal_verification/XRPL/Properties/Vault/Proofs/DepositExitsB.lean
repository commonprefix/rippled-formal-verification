import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.Proofs.Walk
import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit

/-! # `Vault.deposit` exits (rejections and error codes)

Proof bodies behind `VaultDepositReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.deposit_rejected_request_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (ter : TER)
    (hrej : v.roundedDepositAmount amountDeposit = .ok (.rejected ter))
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit isDonation hpos = .ok (.rejected v .tecINTERNAL) := by
  simp only [Vault.roundedDepositAmount, bind, Except.bind, pure, Except.pure] at hrej
  walk_ok
  simp_all [Vault.deposit, bind, Except.bind, pure, Except.pure]

lemma Vault.deposit_rounded_zero_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (isDonation : Bool)
    (hround : roundToVaultExponent amountDeposit v.assetsTotal = .ok roundedAmount)
    (hz : roundedAmount.isZero = true)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit isDonation hpos = .ok (.rejected v .tecINTERNAL) := by
  simp_all [Vault.deposit, bind, Except.bind, pure, Except.pure]

lemma Vault.deposit_donation_no_shares_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ = 0)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit true hpos = .ok (.rejected v .tecNO_PERMISSION) := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  simp_all [Vault.deposit, bind, Except.bind, pure, Except.pure]

lemma Vault.deposit_insolvent_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = true)
    (hpos : 0 < amountDeposit.toRat) :
    v.deposit amountDeposit false hpos = .ok (.rejected v .tecLOCKED) := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  simp_all [Vault.deposit, bind, Except.bind, pure, Except.pure]

lemma Vault.deposit_error_codes_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (r : DepositResult)
    (hpos : 0 < amountDeposit.toRat) (hok : v.deposit amountDeposit isDonation hpos = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecNO_PERMISSION ∨
    r.error = some .tecLOCKED ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecLIMIT_EXCEEDED := by
  simp only [Vault.deposit, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | (simp only [DepositResult.rejected]; simp; done)
    | (rcases computeDeposit_codes v _ _ ‹_› with h | h | h | ⟨_, _, h⟩ <;>
        cases h <;> simp [DepositResult.rejected])

end XRPL.Model.SingleAssetVault
