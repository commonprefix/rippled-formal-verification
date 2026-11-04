import XRPL.Properties.Vault.Proofs.DepositTight.Charge
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Vault.Proofs.DepositTight.Upper
import XRPL.Properties.Vault.Proofs.DepositTight.LowerMint

/-! # Tight accuracy bounds of `Vault.deposit` -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

/-- Sharp share count bound on a vault whose computed total is exact. The issued shares are a whole number
at most `sharesOverε` relatively above the ideal and, under the mint cap, less than one plus `sharesShortε` below. -/
lemma Vault.deposit_sharesIssued_proof (v : Vault) (amountDeposit roundedAmount : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hposA : 0 < amountDeposit.toRat)
    (hexactNav : v.DepositNavExact)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hposA).run = .ok (.ok r))
    (hmint : v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat) :
    r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
    v.idealSharesDeposit roundedAmount.toRat * (1 - sharesShortε) - 1 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesDeposit roundedAmount.toRat * (1 + sharesOverε) := by
  obtain ⟨navN, hat, hexact⟩ := hexactNav
  obtain ⟨hden, hnn, -, hup⟩ := Vault.deposit_sharesIssued_upper_sharp_proof v amountDeposit
    roundedAmount t hcanon hposA navN hat hrounded r hok
  have hlo := Vault.deposit_sharesIssued_lower_mint_proof v amountDeposit roundedAmount t
    hcanon hposA navN hat hrounded r hok hmint
  rw [hexact, RawVault.idealSharesDepositAt_depositNav] at hup hlo
  exact ⟨hden, hnn, hlo, hup⟩

/-- Share count bound on any valid vault. The shortfall side keeps the exact ideal, since a lower price
only issues more shares. The overshoot side is measured against the shares priced at the computed total. -/
lemma Vault.deposit_sharesIssued_total_proof (v : Vault) (amountDeposit roundedAmount : STAmount) (t : UInt32)
    (hcanon : amountDeposit.Canonical) (hposA : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hposA).run = .ok (.ok r))
    (hmint : v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat) :
    r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
    v.idealSharesDeposit roundedAmount.toRat * (1 - sharesShortε) - 1 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesDepositAt navN.toRat roundedAmount.toRat * (1 + sharesOverε) := by
  obtain ⟨hden, hnn, -, hup⟩ := Vault.deposit_sharesIssued_upper_sharp_proof v amountDeposit
    roundedAmount t hcanon hposA navN hat hrounded r hok
  have hlo := Vault.deposit_sharesIssued_lower_mint_proof v amountDeposit roundedAmount t
    hcanon hposA navN hat hrounded r hok hmint
  have hrp := (DepRnd.Vault.roundedDepositAmount_canonical_pos v amountDeposit roundedAmount hcanon hrounded).2
  have hle := Vault.idealSharesDeposit_le_at v navN hat roundedAmount.toRat hrp.le
  refine ⟨hden, hnn, ?_, hup⟩
  have : v.idealSharesDeposit roundedAmount.toRat * (1 - sharesShortε) ≤
      v.idealSharesDepositAt navN.toRat roundedAmount.toRat * (1 - 4879 / 10 ^ 22) := by
    unfold sharesShortε; exact mul_le_mul_of_nonneg_right hle (by norm_num)
  linarith

end XRPL.Model.SingleAssetVault
