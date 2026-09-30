import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.Proofs.Walk

/-! # `Vault.deposit` exits

Proof bodies behind `VaultDepositReturn.lean`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

lemma Vault.roundedDepositAmount_rejected_code_proof (v : Vault) (amountDeposit : STAmount)
    (ter : TER) (hok : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS := by
  simp only [Vault.roundedDepositAmount, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals rfl

lemma Vault.deposit_donation_maximum_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hpos : 0 < amountDeposit.toRat)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) :
    v.deposit amountDeposit true hpos = .ok (.rejected v .tecLIMIT_EXCEEDED) := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  simp_all [Vault.deposit, bind, Except.bind, pure, Except.pure]

end XRPL.Model.SingleAssetVault
