import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.ExitOrder
import XRPL.Properties.Vault.Proofs.ExitOrderFloor
import XRPL.Properties.Vault.Proofs.ExitOrderWitness

/-! # The order of two exits in the redemption phase

Two holders A and B redeem all their shares from a reachable vault in its redemption phase, so with
no early-exit fee. A payout that leaves shares is the priced amount floored onto the base grid, and the
last one pays all the cash left. Each is within one base unit of the shares' worth. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- In the redemption phase, when A and B withdraw all their shares -> A's payout going first never exceeds A's payout
going second, and A's payout when B goes first exceeds A's payout when A goes first by at most two base units. -/
theorem Vault.redemption_exit_order (v : Vault) (t t0 : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) -- the withdrawals come after the history
    (hphase : v.phase t = .redemption) -- in the redemption phase
    (sA sB : STAmount) (hA : sA.ShareBalance) (hB : sB.ShareBalance) -- the holders' share balances
    (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat)
    (hsum : sA.toRat + sB.toRat ≤ v.toExact.sharesTotal) -- both balances are part of the share total
    (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts)
    -- A goes first
    (hA1 : (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1))
    -- B goes first, then A
    (hB2 : (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2))
    (hA2 : (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2)) :
    -- a price rounds to nearest, so it needs a worth of whole base units
    ((∃ k : ℤ, v.idealAssetsWithdraw waiveA sA.toRat = k * 10 ^ v.baseExponent) →
      (∃ k : ℤ, v.idealAssetsWithdraw waiveB sB.toRat = k * 10 ^ v.baseExponent) →
      rA1.assets.toRat - rA2.assets.toRat ≤ 0) ∧
    rA2.assets.toRat - rA1.assets.toRat ≤ 2 * (10 : ℚ) ^ v.baseExponent :=
  ⟨Vault.redemption_exit_order_upper_bound_intended_proof v t t0 hr ht hphase sA sB hA hB hposA hposB hsum waiveA
      waiveB waiveA' rA1 rB2 rA2 hA1 hB2 hA2,
    Vault.redemption_exit_order_lower_bound_proof v t t0 hr ht hphase sA sB hA hB hposA hposB hsum waiveA waiveB
      waiveA' rA1 rB2 rA2 hA1 hB2 hA2⟩

/-- In the redemption phase, when A and B are the only holders and redeem all their shares, A's
payout when B goes first exceeds A's payout when A goes first by at most one base unit. -/
theorem Vault.redemption_exit_order_lower_bound_final (v : Vault) (t t0 : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) -- the withdrawals come after the history
    (hphase : v.phase t = .redemption) -- in the redemption phase
    (sA sB : STAmount) (hA : sA.ShareBalance) (hB : sB.ShareBalance) -- the holders' share balances
    (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat)
    (hsum : sA.toRat + sB.toRat = v.toExact.sharesTotal) -- the two balances make up the share total
    (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts)
    -- A goes first
    (hA1 : (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1))
    -- B goes first, then A
    (hB2 : (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2))
    (hA2 : (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2)) :
    rA2.assets.toRat - rA1.assets.toRat ≤ (10 : ℚ) ^ v.baseExponent :=
  Vault.redemption_exit_order_lower_bound_final_proof v t t0 hr ht hphase sA sB hA hB hposA hposB hsum waiveA
    waiveB waiveA' rA1 rB2 rA2 hA1 hB2 hA2

/-- Witness for the first line of `redemption_exit_order`: a run where A gets one base unit more by going first (`2`
alone, `1` after B, from a vault of `3` assets and `2` shares). -/
theorem Vault.redemption_exit_order_upper_bound_attained :
    ∃ (v : Vault) (t t0 : UInt32) (sA sB : STAmount) (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat)
      (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ v.phase t = .redemption ∧ sA.ShareBalance ∧ sB.ShareBalance ∧
      sA.toRat + sB.toRat ≤ v.toExact.sharesTotal ∧
      (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1) ∧
      (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2) ∧
      (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2) ∧
      rA1.assets.toRat - rA2.assets.toRat = (10 : ℚ) ^ v.baseExponent :=
  Vault.redemption_exit_order_upper_bound_witness

/-- Witness for the second line of `redemption_exit_order`: A gets two base units more after B (`999999999999999`
alone, `1000000000000001` after B), holding `9·10^14` of `1800000000000001` shares on `2000000000000001`. -/
theorem Vault.redemption_exit_order_lower_bound_attained :
    ∃ (v : Vault) (t t0 : UInt32) (sA sB : STAmount) (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat)
      (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ v.phase t = .redemption ∧ sA.ShareBalance ∧ sB.ShareBalance ∧
      sA.toRat + sB.toRat ≤ v.toExact.sharesTotal ∧
      (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1) ∧
      (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2) ∧
      (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2) ∧
      rA2.assets.toRat - rA1.assets.toRat = 2 * (10 : ℚ) ^ v.baseExponent :=
  Vault.redemption_exit_order_lower_bound_witness

/-- Witness for `redemption_exit_order_lower_bound_final`: A, one of the two holders, gets one base unit more
after B (`2` alone, `3` after B, from a vault of `5` assets and `2` shares). -/
theorem Vault.redemption_exit_order_lower_bound_final_attained :
    ∃ (v : Vault) (t t0 : UInt32) (sA sB : STAmount) (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat)
      (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ v.phase t = .redemption ∧ sA.ShareBalance ∧ sB.ShareBalance ∧
      sA.toRat + sB.toRat = v.toExact.sharesTotal ∧
      (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1) ∧
      (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2) ∧
      (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2) ∧
      rA2.assets.toRat - rA1.assets.toRat = (10 : ℚ) ^ v.baseExponent :=
  Vault.redemption_exit_order_lower_bound_final_witness

end XRPL.Model.SingleAssetVault
