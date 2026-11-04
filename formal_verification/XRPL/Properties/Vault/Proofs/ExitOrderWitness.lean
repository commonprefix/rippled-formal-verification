import XRPL.Properties.Vault.Proofs.Support.ReachableHistory

/-! # Witnesses for the exit-order bounds

Each run is computed by the model and checked by `native_decide`. Every vault comes from a reachable
history: a create with a closed-ended schedule, a deposit, then a donation, all at close time 0. The
withdrawals run at close time 1500, in the redemption phase.

* Going first gains a unit: 3 assets and 2 shares, A and B hold one each. Alone, A's share prices at
  `1.5`, paid `2`. After B, who also gets `2`, A gets the remaining `1`.
* Going second gains a unit when A and B are the only holders: 5 assets and 2 shares. Alone, A's
  share prices at `2.5`, paid `2`. After B, who gets `2`, A gets the remaining `3`.
* Going second gains two units: a fractional vault of `2000000000000001` assets and
  `1800000000000001` shares, A and B hold `900000000000000` each. Alone, A's shares price at
  `999999999999999.9`, floored to `999999999999999`. After B, who gets the same, A's shares are
  worth `1000000000000000.89`, priced on the base grid at `1000000000000001`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.ExitWit

open XRPL.Model.Protocol

def int64Amount (n : UInt64) : STAmount := ⟨.int64, n, 0, false⟩

def iouAmount (m : UInt64) (e : Int) : STAmount := ⟨.fractional, m, e, false⟩

/-- The closed-ended schedule of the witnesses: withdrawals at time 1500 are in the redemption
phase. -/
def schedule : VaultSchedule := ⟨100, 1000⟩

def vU : Vault :=
  createHistory.vault Vault.placeholder .int64 0 (some schedule) none 0
    [(int64Amount 2, false), (int64Amount 1, true)]
def vF : Vault :=
  createHistory.vault Vault.placeholder .int64 0 (some schedule) none 0
    [(int64Amount 2, false), (int64Amount 3, true)]
def vL : Vault :=
  createHistory.vault Vault.placeholder .fractional 0 (some schedule) none 0
    [(iouAmount 1800000000000001 0, false), (iouAmount 2000000000000000 (-1), true)]

lemma vU_reach : Vault.Reachable vU 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vF_reach : Vault.Reachable vF 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)
lemma vL_reach : Vault.Reachable vL 0 := createHistory.vault_reachable _ _ _ _ _ _ _ (by native_decide)

def oneShare : STAmount := int64Amount 1
def bigShare : STAmount := int64Amount 900000000000000
lemma oneShare_pos : 0 < oneShare.toRat := by native_decide
lemma bigShare_pos : 0 < bigShare.toRat := by native_decide

lemma oneShare_balance : oneShare.ShareBalance := ⟨rfl, STAmount.canonical_of_canonicalB _ (by native_decide), rfl⟩
lemma bigShare_balance : bigShare.ShareBalance := ⟨rfl, STAmount.canonical_of_canonicalB _ (by native_decide), rfl⟩

/-- Redeeming `shares` at close time 1500, with the input vault standing in when the run fails. -/
def redeem (v : Vault) (shares : STAmount) (hpos : 0 < shares.toRat) : VaultWithAmounts :=
  ((v.withdraw (.vaultShares shares) false 1500 hpos).run.toOption.bind Except.toOption).getD
    ⟨⟨shares, shares⟩, v⟩

def rU1 : VaultWithAmounts := redeem vU oneShare oneShare_pos
def rU2 : VaultWithAmounts := redeem rU1.vault' oneShare oneShare_pos
def rF1 : VaultWithAmounts := redeem vF oneShare oneShare_pos
def rF2 : VaultWithAmounts := redeem rF1.vault' oneShare oneShare_pos
def rL1 : VaultWithAmounts := redeem vL bigShare bigShare_pos
def rL2 : VaultWithAmounts := redeem rL1.vault' bigShare bigShare_pos

end XRPL.Model.SingleAssetVault.ExitWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol ExitWit

/-- Going first gains A one base unit: B's price rounds up across a grid point, so A gets one unit
less after B. -/
lemma Vault.redemption_exit_order_upper_bound_witness :
    ∃ (v : Vault) (t t0 : UInt32) (sA sB : STAmount) (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat)
      (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ v.phase t = .redemption ∧ sA.ShareBalance ∧ sB.ShareBalance ∧
      sA.toRat + sB.toRat ≤ v.toExact.sharesTotal ∧
      (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1) ∧
      (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2) ∧
      (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2) ∧
      rA1.assets.toRat - rA2.assets.toRat = (10 : ℚ) ^ v.baseExponent :=
  ⟨vU, 1500, 0, oneShare, oneShare, oneShare_pos, oneShare_pos, false, false, false, rU1, rU1, rU2, vU_reach,
    by decide, by native_decide, oneShare_balance, oneShare_balance, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Going second gains A two base units: both first prices floor away nearly a unit, B's stays in
the vault, and A's second price rounds up onto the base grid. -/
lemma Vault.redemption_exit_order_lower_bound_witness :
    ∃ (v : Vault) (t t0 : UInt32) (sA sB : STAmount) (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat)
      (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ v.phase t = .redemption ∧ sA.ShareBalance ∧ sB.ShareBalance ∧
      sA.toRat + sB.toRat ≤ v.toExact.sharesTotal ∧
      (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1) ∧
      (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2) ∧
      (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2) ∧
      rA2.assets.toRat - rA1.assets.toRat = 2 * (10 : ℚ) ^ v.baseExponent :=
  ⟨vL, 1500, 0, bigShare, bigShare, bigShare_pos, bigShare_pos, false, false, false, rL1, rL1, rL2, vL_reach,
    by decide, by native_decide, bigShare_balance, bigShare_balance, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Going second gains A one base unit when A and B are the only holders: A's price rounds down
across a grid point, and after B the rest of the cash is A's. -/
lemma Vault.redemption_exit_order_lower_bound_final_witness :
    ∃ (v : Vault) (t t0 : UInt32) (sA sB : STAmount) (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat)
      (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts),
      Vault.Reachable v t0 ∧ t0 ≤ t ∧ v.phase t = .redemption ∧ sA.ShareBalance ∧ sB.ShareBalance ∧
      sA.toRat + sB.toRat = v.toExact.sharesTotal ∧
      (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1) ∧
      (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2) ∧
      (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2) ∧
      rA2.assets.toRat - rA1.assets.toRat = (10 : ℚ) ^ v.baseExponent :=
  ⟨vF, 1500, 0, oneShare, oneShare, oneShare_pos, oneShare_pos, false, false, false, rF1, rF1, rF2, vF_reach,
    by decide, by native_decide, oneShare_balance, oneShare_balance, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
