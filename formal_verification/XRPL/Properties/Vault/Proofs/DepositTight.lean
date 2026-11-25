import XRPL.Properties.Vault.Proofs.DepositTight.Charge
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.Proofs.DepositTight.Upper
import XRPL.Properties.Vault.Proofs.DepositTight.LowerMint

/-! # Tight accuracy bounds of `Vault.deposit` -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

/-- Share count bound on any lawful vault, against the shares priced at the computed total. -/
lemma Vault.deposit_sharesCreated_total_proof (v : Vault) (amountDeposit roundedAmount : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hposA : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hposA).run = .ok (.ok r))
    (hmint : v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat) :
    r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
    v.idealSharesDepositAt navN.toRat roundedAmount.toRat * (1 - sharesShortε) - 1 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesDepositAt navN.toRat roundedAmount.toRat * (1 + sharesOverε) := by
  obtain ⟨hden, hnn, -, hup⟩ := Vault.deposit_sharesCreated_upper_sharp_proof v amountDeposit
    roundedAmount t hcanon hposA navN hat hrounded r hok
  have hlo := Vault.deposit_sharesCreated_lower_mint_proof v amountDeposit roundedAmount t
    hcanon hposA navN hat hrounded r hok hmint
  exact ⟨hden, hnn, by unfold sharesShortε; exact hlo, hup⟩

end XRPL.Model.SingleAssetVault
