import XRPL.Properties.Vault.Proofs.ExitOrder
import XRPL.Properties.Vault.Proofs.PricedWorth

/-! # Going first gains nothing when the worths are whole base units

When A's and B's shares are worth whole base units, both first payouts stay at or below the worth, so B leaves at
least as much cash per remaining share and A's later price lands at or above A's first worth. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A payout floored onto the base grid from a price at most a worth of whole base units is at most that worth. -/
private lemma floor_le_of_le (b : ℤ) (p P I : ℚ) (hP : P = (⌊p / 10 ^ b⌋ : ℚ) * 10 ^ b) (hp : p ≤ I) : P ≤ I := by
  have hb : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have := Int.floor_le (p / 10 ^ b)
  rw [le_div_iff₀ hb] at this
  rw [hP]; linarith

/-- A payout floored onto the base grid from a price at least `k` base units is at least `k` base units. -/
private lemma floor_ge_of_ge (b : ℤ) (k : ℤ) (p P : ℚ) (hP : P = (⌊p / 10 ^ b⌋ : ℚ) * 10 ^ b)
    (hp : (k : ℚ) * 10 ^ b ≤ p) : (k : ℚ) * 10 ^ b ≤ P := by
  have hb : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hk : (k : ℚ) ≤ p / 10 ^ b := by rw [le_div_iff₀ hb]; exact hp
  have hfl : k ≤ ⌊p / 10 ^ b⌋ := Int.le_floor.mpr hk
  rw [hP]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfl) hb.le

/-- Proof of the first line of `Vault.redemption_exit_order`. -/
lemma Vault.redemption_exit_order_upper_bound_intended_proof (v : Vault) (t t0 : UInt32)
    (hr : Vault.Reachable v t0) (ht : t0 ≤ t) (hphase : v.phase t = .redemption)
    (sA sB : STAmount) (hA : sA.ShareBalance) (hB : sB.ShareBalance)
    (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat) (hsum : sA.toRat + sB.toRat ≤ v.toExact.sharesTotal)
    (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts)
    (hA1 : (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1))
    (hB2 : (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2))
    (hA2 : (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2))
    (hworthA : ∃ k : ℤ, v.idealAssetsWithdraw waiveA sA.toRat = k * 10 ^ v.baseExponent)
    (hworthB : ∃ k : ℤ, v.idealAssetsWithdraw waiveB sB.toRat = k * 10 ^ v.baseExponent) :
    rA1.assets.toRat - rA2.assets.toRat ≤ 0 := by
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by linarith
  have hltA : sA.toRat < v.toExact.sharesTotal := by linarith
  have hltB : sB.toRat < v.toExact.sharesTotal := by linarith
  have hmax := Vault.Reachable.maxValue_fits v t0 hr hSpos
  have hfee : v.earlyExitFeeRateAt t = 0 := by
    unfold Vault.earlyExitFeeRateAt
    rw [hphase]
    cases v.earlyExitFeeRate <;> rfl
  have hLU := (Vault.Reachable.noLending_proof v t0 hr).2.1
  rw [Vault.withdraw_waive v hLU (.vaultShares sA) waiveA t hposA] at hA1
  rw [Vault.withdraw_waive v hLU (.vaultShares sB) waiveB t hposB] at hB2
  have hrB : Vault.Reachable rB2.vault' t :=
    Vault.Reachable.withdraw_shares_step v t t0 hr ht sB hB false hposB hltB rB2 hB2
  rw [Vault.withdraw_waive rB2.vault' (Vault.Reachable.noLending_proof _ t hrB).2.1 (.vaultShares sA) waiveA' t
    hposA] at hA2
  obtain ⟨_, _, hfr⟩ := Vault.withdraw_frame v (.vaultShares sB) false t hposB rB2 hB2
  have hnt : rB2.vault'.numericType = v.numericType := (congrArg RawVault.numericType hfr).trans rfl
  have hb' : rB2.vault'.baseExponent = v.baseExponent := by
    unfold Vault.baseExponent
    rw [hnt, (congrArg RawVault.scale hfr).trans rfl]
  have hfee' : rB2.vault'.earlyExitFeeRateAt t = 0 := by
    unfold Vault.earlyExitFeeRateAt Vault.phase at hfee ⊢
    rw [(congrArg RawVault.schedule hfr).trans rfl, (congrArg RawVault.earlyExitFeeRate hfr).trans rfl]
    exact hfee
  have hmax' : rB2.vault'.numericType.isIntegral = true → rB2.vault'.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hnt]; exact hmax
  obtain ⟨hC', hS'⟩ := Vault.withdraw_vault_updates_exact_proof v (.vaultShares sB) false t t0 hposB hr
    hB.canonical hB.int64 hmax rB2 hB2
  rw [Vault.withdraw_sharesRedeemed_exact_proof v sB false t hposB rB2 hB2] at hS'
  have hsharesA2 : rA2.shares = sA := Vault.withdraw_sharesRedeemed_exact_proof _ sA false t hposA rA2 hA2
  set C := v.assetsAvailable.toRat with hCdef
  set S : ℚ := (v.toExact.sharesTotal : ℚ) with hSdef
  have hIeq : ∀ (w : Bool) (x : ℚ), v.idealAssetsWithdraw w x = C * x / S :=
    fun w x => Vault.Reachable.idealAssetsWithdraw_eq v t0 hr w x
  obtain ⟨kA, hkA⟩ := hworthA
  obtain ⟨kB, hkB⟩ := hworthB
  rw [hIeq] at hkA hkB
  -- both first payouts are floored prices at most the worth
  obtain ⟨pA, eA, hprA, hPA, hpAC, -, -⟩ :=
    Vault.Reachable.redemptionPayout v t t0 hr hmax hfee sA hA hposA hltA rA1 hA1
  obtain ⟨pB, eB, hprB, hPB, hpBC, -, -⟩ :=
    Vault.Reachable.redemptionPayout v t t0 hr hmax hfee sB hB hposB hltB rB2 hB2
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hpA := hz.priced_le_worth hmax sA pA false hposA.le hA.canonical hprA hpAC ⟨kA, by rw [hIeq]; exact hkA⟩
  have hpB := hz.priced_le_worth hmax sB pB false hposB.le hB.canonical hprB hpBC ⟨kB, by rw [hIeq]; exact hkB⟩
  rw [hIeq] at hpA hpB
  have hA1le : rA1.assets.toRat ≤ C * sA.toRat / S := floor_le_of_le _ _ _ _ hPA.floor hpA
  have hB2le : rB2.assets.toRat ≤ C * sB.toRat / S := floor_le_of_le _ _ _ _ hPB.floor hpB
  -- B leaves at least A's worth for A's shares
  have hS'pos : (0 : ℚ) < S - sB.toRat := by linarith
  have hIA' : C * sA.toRat / S ≤ (C - rB2.assets.toRat) * sA.toRat / (S - sB.toRat) := by
    rw [div_le_div_iff₀ hSpos hS'pos]
    have h1 : rB2.assets.toRat * S ≤ C * sB.toRat := by rwa [le_div_iff₀ hSpos] at hB2le
    nlinarith
  suffices h : C * sA.toRat / S ≤ rA2.assets.toRat by linarith
  rcases lt_or_eq_of_le hsum with hnonfinal | hfinal
  · -- shares remain: A's second price is at least A's first worth, and so is its floor
    have hltA' : sA.toRat < rB2.vault'.toExact.sharesTotal := by rw [hS']; linarith
    obtain ⟨pA', eA', hprA', hPA', hpAC', -, -⟩ :=
      Vault.Reachable.redemptionPayout rB2.vault' t t hrB hmax' hfee' sA hA hposA hltA' rA2 hA2
    rw [hb', hC', hS'] at hPA'
    rw [hkA]
    refine floor_ge_of_ge _ kA _ _ hPA'.floor ?_
    by_cases hpz : pA'.toRat = 0
    · -- a zero price leaves nothing to compare: the cash left and A's worth are zero
      have hle := hPA'.lower
      have hrel := hPA'.relative
      have hg : (0 : ℚ) < 10 ^ eA' := zpow_pos (by norm_num) _
      rw [hpz] at hle ⊢
      have hI0 : (C - rB2.assets.toRat) * sA.toRat / (S - sB.toRat) < 10 ^ eA' := by linarith
      have hg' : (10 : ℚ) ^ eA' ≤ 10 ^ v.baseExponent := zpow_le_zpow_right₀ (by norm_num) hPA'.grid
      have : (kA : ℚ) * 10 ^ v.baseExponent < 10 ^ v.baseExponent := by rw [← hkA]; linarith
      have hb : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
      have hk1 : (kA : ℚ) < 1 := by nlinarith
      have hk1' : kA < 1 := by exact_mod_cast hk1
      have hk0 : kA ≤ 0 := by omega
      have : (kA : ℚ) ≤ 0 := by exact_mod_cast hk0
      nlinarith
    obtain ⟨hpv, heb, -, hpl, hrel⟩ := (Vault.Reachable.openZone_proof rB2.vault' t hrB hmax').priced_grid hmax' sA pA'
      false hposA.le hA.canonical hprA' hpAC' hpz
    rw [hb'] at heb
    rw [Vault.Reachable.idealAssetsWithdraw_eq rB2.vault' t hrB false, hC', hS'] at hpl hrel
    have hg : (0 : ℚ) < 10 ^ pA'.exponent := zpow_pos (by norm_num) _
    exact ge_of_grid_lt _ kA _ _ heb _ _ hpv rfl (by rw [← hkA]; linarith)
  · -- A and B are the only holders: A's second withdrawal takes all the cash B left
    have hfin : rA2.shares.toRat = rB2.vault'.toExact.sharesTotal := by rw [hsharesA2, hS']; linarith
    obtain ⟨hpay, -, -⟩ := Vault.withdraw_final_proof rB2.vault' (.vaultShares sA) false t t hposA hrB
      hA.canonical hA.int64 hmax' rA2 hA2 hfin
    rw [hpay, hC']
    have hsA : sA.toRat = S - sB.toRat := by linarith
    have hIA'' : (C - rB2.assets.toRat) * sA.toRat / (S - sB.toRat) = C - rB2.assets.toRat := by
      rw [hsA, mul_div_assoc, div_self hS'pos.ne', mul_one]
    linarith

end XRPL.Model.SingleAssetVault
