import XRPL.Properties.Vault.Proofs.ExitOrderPayout
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.MaxValueFits

/-! # The order of two exits from a vault in the redemption phase

A payout that leaves shares is the priced amount floored onto the base grid, and the last one pays all
the cash left. Each is within one base unit of the shares' worth, and B's rounding moves A's remaining
worth by at most B's own deviation. Going second gains A two units when B's floor leaves nearly a unit,
A's first price floors away nearly a unit and A's second rounds up. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A whole number of base units below two of them is at most one. -/
private lemma int_mul_le_one (m : ℤ) (u : ℚ) (hu : 0 < u) (h : (m : ℚ) * u < 2 * u) : (m : ℚ) * u ≤ u := by
  have h1 : (m : ℚ) < 2 := lt_of_mul_lt_mul_right h hu.le
  have h2 : m ≤ 1 := by
    have : m < 2 := by exact_mod_cast h1
    omega
  have h3 : (m : ℚ) ≤ 1 := by exact_mod_cast h2
  nlinarith

/-- A whole number of base units below three of them is at most two. -/
private lemma int_mul_le_two (m : ℤ) (u : ℚ) (hu : 0 < u) (h : (m : ℚ) * u < 3 * u) :
    (m : ℚ) * u ≤ 2 * u := by
  have h1 : (m : ℚ) < 3 := lt_of_mul_lt_mul_right h hu.le
  have h2 : m ≤ 2 := by
    have : m < 3 := by exact_mod_cast h1
    omega
  have h3 : (m : ℚ) ≤ 2 := by exact_mod_cast h2
  nlinarith

namespace Vault.RedemptionPayout

variable {b : ℤ} {I p P : ℚ} {e : ℤ}

private lemma base_pos (_h : Vault.RedemptionPayout b I p P e) : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _

private lemma grid_pos (_h : Vault.RedemptionPayout b I p P e) : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _

private lemma grid_le (h : Vault.RedemptionPayout b I p P e) : (10 : ℚ) ^ e ≤ 10 ^ b :=
  zpow_le_zpow_right₀ (by norm_num) h.grid

/-- The payout never exceeds the priced amount. -/
private lemma payout_le (h : Vault.RedemptionPayout b I p P e) : P ≤ p := by
  rw [h.floor]
  have := Int.floor_le (p / 10 ^ b)
  rwa [le_div_iff₀ h.base_pos] at this

private lemma payout_nonneg (h : Vault.RedemptionPayout b I p P e) : 0 ≤ P := by
  rw [h.floor]
  have h0 : (0 : ℚ) ≤ ⌊p / 10 ^ b⌋ := by exact_mod_cast Int.floor_nonneg.mpr (div_nonneg h.nonneg h.base_pos.le)
  exact mul_nonneg h0 h.base_pos.le

/-- The payout exceeds the worth by at most half the priced grid plus the relative error. -/
private lemma above (h : Vault.RedemptionPayout b I p P e) : P - I ≤ 1 / 2 * (10 : ℚ) ^ e + I * sharesε := by
  have hu := h.upper
  rw [mul_add, mul_one] at hu
  linarith [h.payout_le]

/-- The payout falls short of the worth by at most a base step less half the priced grid, plus the
relative error. -/
private lemma below (h : Vault.RedemptionPayout b I p P e) :
    I - P ≤ (10 : ℚ) ^ b - 1 / 2 * 10 ^ e + I * sharesε := by
  linarith [h.lower, h.remainder]

/-- The payout falls short of the worth by less than one base step. -/
private lemma below_lt (h : Vault.RedemptionPayout b I p P e) : I - P < (10 : ℚ) ^ b := by
  linarith [h.below, h.relative, h.grid_pos]

end Vault.RedemptionPayout

/-- The final case: A and B are the only holders, so A's payout after B is all the cash B left. The two
worths add up to the cash, and each payout is within a base step of its worth. -/
private lemma final_bounds (b : ℤ) (k : ℕ) (C IA IB pA pB PA PB : ℚ) (eA eB : ℤ)
    (hC : C = k * 10 ^ b) (hsum : IA + IB = C)
    (hA : Vault.RedemptionPayout b IA pA PA eA) (hB : Vault.RedemptionPayout b IB pB PB eB)
    (hεA : IA * sharesε ≤ 99 / 10 ^ 4 * (10 : ℚ) ^ b) (hεB : IB * sharesε ≤ 99 / 10 ^ 4 * (10 : ℚ) ^ b) :
    PA - (C - PB) ≤ 10 ^ b ∧ (C - PB) - PA ≤ 10 ^ b := by
  have hu := hA.base_pos
  have hgA := hA.grid_le
  have hgB := hB.grid_le
  constructor
  · have hm : PA - (C - PB) = ((⌊pA / 10 ^ b⌋ + ⌊pB / 10 ^ b⌋ - k : ℤ) : ℚ) * 10 ^ b := by
      rw [hA.floor, hB.floor, hC]; push_cast; ring
    rw [hm]
    refine int_mul_le_one _ _ hu ?_
    rw [← hm]
    linarith [hA.above, hB.above]
  · have hm : (C - PB) - PA = ((k - ⌊pA / 10 ^ b⌋ - ⌊pB / 10 ^ b⌋ : ℤ) : ℚ) * 10 ^ b := by
      rw [hA.floor, hB.floor, hC]; push_cast; ring
    rw [hm]
    refine int_mul_le_one _ _ hu ?_
    rw [← hm]
    linarith [hA.below_lt, hB.below_lt]

/-- The non-final case: A's payout after B is again a floored price. B's deviation moves A's remaining
worth by `ρ` times itself, `ρ` being A's part of the shares B left. -/
private lemma nonfinal_bounds (b : ℤ) (IA IB IA' pA pB pA' PA PB PA' ρ : ℚ) (eA eB eA' : ℤ)
    (hA : Vault.RedemptionPayout b IA pA PA eA) (hB : Vault.RedemptionPayout b IB pB PB eB)
    (hA' : Vault.RedemptionPayout b IA' pA' PA' eA')
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hshift : IA - IA' = ρ * (PB - IB))
    (hεA : IA * sharesε ≤ 99 / 10 ^ 4 * (10 : ℚ) ^ b) (hεB : IB * sharesε ≤ 99 / 10 ^ 4 * (10 : ℚ) ^ b)
    (hεA' : IA' * sharesε ≤ 99 / 10 ^ 4 * (10 : ℚ) ^ b)
    -- on a fractional vault a nonzero priced amount has a 16-digit mantissa
    (hAlo : eA' ≤ b - 2 → pA ≠ 0 → 10 ^ 15 * (10 : ℚ) ^ eA ≤ pA) :
    PA - PA' ≤ 10 ^ b ∧ PA' - PA ≤ 2 * 10 ^ b := by
  have hu := hA.base_pos
  have hgA := hA.grid_le
  have hgB := hB.grid_le
  have hgA' := hA'.grid_le
  have hgApos := hA.grid_pos
  have hgA'pos := hA'.grid_pos
  -- B's deviation, scaled by `ρ`, moves A's worth by at most about half a step either way
  have hQB : PB - IB ≤ 5099 / 10 ^ 4 * (10 : ℚ) ^ b := by linarith [hB.above]
  have hρQB : ρ * (PB - IB) ≤ 5099 / 10 ^ 4 * (10 : ℚ) ^ b :=
    calc ρ * (PB - IB) ≤ ρ * (5099 / 10 ^ 4 * (10 : ℚ) ^ b) := mul_le_mul_of_nonneg_left hQB hρ0
      _ ≤ 1 * (5099 / 10 ^ 4 * (10 : ℚ) ^ b) := mul_le_mul_of_nonneg_right hρ1 (by positivity)
      _ = 5099 / 10 ^ 4 * (10 : ℚ) ^ b := one_mul _
  have hρQB' : ρ * (IB - PB) ≤ (10 : ℚ) ^ b :=
    calc ρ * (IB - PB) ≤ ρ * (10 : ℚ) ^ b := mul_le_mul_of_nonneg_left hB.below_lt.le hρ0
      _ ≤ 1 * (10 : ℚ) ^ b := mul_le_mul_of_nonneg_right hρ1 hu.le
      _ = (10 : ℚ) ^ b := one_mul _
  constructor
  · have hm : PA - PA' = ((⌊pA / 10 ^ b⌋ - ⌊pA' / 10 ^ b⌋ : ℤ) : ℚ) * 10 ^ b := by
      rw [hA.floor, hA'.floor]; push_cast; ring
    rw [hm]
    refine int_mul_le_one _ _ hu ?_
    rw [← hm]
    have hbelowA' := hA'.below
    have hrelA' := hA'.relative
    rcases le_or_gt (b - 1) eA' with hcoarse | hfine
    · -- A's second price sits on a grid at most ten times finer than the base grid
      have h10 : (10 : ℚ) ^ (b - 1) ≤ 10 ^ eA' := zpow_le_zpow_right₀ (by norm_num) hcoarse
      have hb1 : (10 : ℚ) ^ (b - 1) = 10 ^ b / 10 := by
        rw [zpow_sub_one₀ (by norm_num)]; ring
      rw [hb1] at h10
      linarith [hA.above]
    · -- a much finer grid: A's second price is below `10^14` base units
      have h100 : (10 : ℚ) ^ eA' ≤ 10 ^ (b - 2) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hb2 : (10 : ℚ) ^ (b - 2) = 10 ^ b / 100 := by
        rw [show b - 2 = b - 1 - 1 by ring, zpow_sub_one₀ (by norm_num), zpow_sub_one₀ (by norm_num)]; ring
      rw [hb2] at h100
      rcases lt_or_eq_of_le hA.grid with heA | heA
      · -- A's first price is on a finer grid too, so it exceeds A's worth by far less than a step
        have h10 : (10 : ℚ) ^ eA ≤ 10 ^ (b - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        have hb1 : (10 : ℚ) ^ (b - 1) = 10 ^ b / 10 := by
          rw [zpow_sub_one₀ (by norm_num)]; ring
        rw [hb1] at h10
        linarith [hA.above, hA.relative]
      · -- A's first price is on the base grid, at least `10^15` base units: then so is the second
        by_cases hpA : pA = 0
        · have hPA : PA = 0 := by rw [hA.floor, hpA, zero_div, Int.floor_zero, Int.cast_zero, zero_mul]
          linarith [hA'.payout_nonneg]
        exfalso
        have hbig := hAlo (by omega) hpA
        rw [heA] at hbig
        have hupA := hA.upper
        rw [mul_add, mul_one] at hupA
        -- the two prices of A are within about a step of each other
        have hclose : pA - pA' ≤ 103 / 10 ^ 2 * (10 : ℚ) ^ b := by
          linarith [hA'.lower, hA'.relative]
        linarith [hA'.small]
  · have hm : PA' - PA = ((⌊pA' / 10 ^ b⌋ - ⌊pA / 10 ^ b⌋ : ℤ) : ℚ) * 10 ^ b := by
      rw [hA.floor, hA'.floor]; push_cast; ring
    rw [hm]
    refine int_mul_le_two _ _ hu ?_
    rw [← hm]
    linarith [hA'.above, hA.below_lt]

/-- The three exit-order bounds at once, on a reachable vault in the redemption phase. -/
lemma Vault.redemption_exit_order_core (v : Vault) (t t0 : UInt32) (hr : Vault.Reachable v t0) (ht : t0 ≤ t)
    (hphase : v.phase t = .redemption)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (sA sB : STAmount) (hA : sA.ShareBalance) (hB : sB.ShareBalance)
    (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat) (hsum : sA.toRat + sB.toRat ≤ v.toExact.sharesTotal)
    (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts)
    (hA1 : (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1))
    (hB2 : (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2))
    (hA2 : (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2)) :
    rA1.assets.toRat - rA2.assets.toRat ≤ (10 : ℚ) ^ v.baseExponent ∧
    rA2.assets.toRat - rA1.assets.toRat ≤ 2 * (10 : ℚ) ^ v.baseExponent ∧
    (sA.toRat + sB.toRat = v.toExact.sharesTotal →
      rA2.assets.toRat - rA1.assets.toRat ≤ (10 : ℚ) ^ v.baseExponent) := by
  have hupos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by linarith
  have hltA : sA.toRat < v.toExact.sharesTotal := by linarith
  have hltB : sB.toRat < v.toExact.sharesTotal := by linarith
  -- no early-exit fee in the redemption phase
  have hfee : v.earlyExitFeeRateAt t = 0 := by
    unfold Vault.earlyExitFeeRateAt
    rw [hphase]
    cases v.earlyExitFeeRate <;> rfl
  -- the waive flags change nothing on a vault with no loss
  have hLU := (Vault.Reachable.noLending_proof v t0 hr).2.1
  rw [Vault.withdraw_waive v hLU (.vaultShares sA) waiveA t hposA] at hA1
  rw [Vault.withdraw_waive v hLU (.vaultShares sB) waiveB t hposB] at hB2
  have hrB : Vault.Reachable rB2.vault' t :=
    Vault.Reachable.withdraw_shares_step v t t0 hr ht sB hB false hposB hltB rB2 hB2
  rw [Vault.withdraw_waive rB2.vault' (Vault.Reachable.noLending_proof _ t hrB).2.1 (.vaultShares sA) waiveA' t
    hposA] at hA2
  -- the vault B leaves: the same asset, the cash less B's payout, the shares less B's
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
  rw [Vault.withdraw_sharesBurned_exact_proof v sB false t hposB rB2 hB2] at hS'
  have hsharesA2 : rA2.shares = sA := Vault.withdraw_sharesBurned_exact_proof _ sA false t hposA rA2 hA2
  -- the two payouts from the original vault
  obtain ⟨pA, eA, -, hPA, -, -, hfracA⟩ :=
    Vault.Reachable.redemptionPayout v t t0 hr hmax hfee sA hA hposA hltA rA1 hA1
  obtain ⟨pB, eB, -, hPB, hpBC, -, -⟩ :=
    Vault.Reachable.redemptionPayout v t t0 hr hmax hfee sB hB hposB hltB rB2 hB2
  -- the cash is a whole number of base units within the Open-zone limit
  obtain ⟨k, hk, hkv⟩ := (Vault.Reachable.openZone_proof v t0 hr hmax).cash
  have hcash : v.assetsAvailable.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
    rw [hkv]
    have : (k : ℚ) ≤ 9 * 10 ^ 15 := by exact_mod_cast hk
    exact mul_le_mul_of_nonneg_right this hupos.le
  have hC0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  -- the relative pricing error of any worth at most the cash
  have hε : ∀ I : ℚ, I ≤ v.assetsAvailable.toRat →
      I * sharesε ≤ 99 / 10 ^ 4 * (10 : ℚ) ^ v.baseExponent := by
    intro I hI
    unfold sharesε
    linarith
  have hIA : v.assetsAvailable.toRat * sA.toRat / v.toExact.sharesTotal ≤ v.assetsAvailable.toRat := by
    rw [div_le_iff₀ hSpos]
    exact mul_le_mul_of_nonneg_left hltA.le hC0
  have hIB : v.assetsAvailable.toRat * sB.toRat / v.toExact.sharesTotal ≤ v.assetsAvailable.toRat := by
    rw [div_le_iff₀ hSpos]
    exact mul_le_mul_of_nonneg_left hltB.le hC0
  rcases lt_or_eq_of_le hsum with hnonfinal | hfinal
  · -- shares remain after both exits: A's second payout is a floored price as well
    have hltA' : sA.toRat < rB2.vault'.toExact.sharesTotal := by rw [hS']; linarith
    obtain ⟨pA', eA', -, hPA', -, hintA', -⟩ :=
      Vault.Reachable.redemptionPayout rB2.vault' t t hrB hmax' hfee' sA hA hposA hltA' rA2 hA2
    rw [hb', hC', hS'] at hPA'
    rw [hb'] at hintA'
    have hS'pos : (0 : ℚ) < v.toExact.sharesTotal - sB.toRat := by linarith
    have hPB0 := hPB.payout_nonneg
    have hIA' : (v.assetsAvailable.toRat - rB2.assets.toRat) * sA.toRat / (v.toExact.sharesTotal - sB.toRat) ≤
        v.assetsAvailable.toRat := by
      rw [div_le_iff₀ hS'pos]
      nlinarith
    have hshift : v.assetsAvailable.toRat * sA.toRat / v.toExact.sharesTotal -
        (v.assetsAvailable.toRat - rB2.assets.toRat) * sA.toRat / (v.toExact.sharesTotal - sB.toRat) =
        sA.toRat / (v.toExact.sharesTotal - sB.toRat) *
          (rB2.assets.toRat - v.assetsAvailable.toRat * sB.toRat / v.toExact.sharesTotal) := by
      field_simp
      ring
    have hAlo : eA' ≤ v.baseExponent - 2 → pA.toRat ≠ 0 → 10 ^ 15 * (10 : ℚ) ^ eA ≤ pA.toRat := by
      intro he hp
      refine hfracA ?_ hp
      -- an integral vault prices on the base grid, so the grid of A's second price is a fractional one
      by_contra hint
      rw [hnt] at hintA'
      have := hintA' (by simpa using hint)
      omega
    obtain ⟨h1, h2⟩ := nonfinal_bounds v.baseExponent _ _ _ _ _ _ _ _ _ _ eA eB eA' hPA hPB hPA'
      (div_nonneg hposA.le hS'pos.le) (by rw [div_le_one hS'pos]; linarith) hshift (hε _ hIA) (hε _ hIB)
      (hε _ hIA') hAlo
    exact ⟨h1, h2, fun h => absurd h (ne_of_lt hnonfinal)⟩
  · -- A and B are the only holders: A's second withdrawal takes all the cash B left
    have hfin : rA2.shares.toRat = rB2.vault'.toExact.sharesTotal := by rw [hsharesA2, hS']; linarith
    obtain ⟨hpay, -, -⟩ := Vault.withdraw_final_proof rB2.vault' (.vaultShares sA) false t t hposA hrB
      hA.canonical hA.int64 hmax' rA2 hA2 hfin
    rw [hpay, hC']
    have hsumI : v.assetsAvailable.toRat * sA.toRat / v.toExact.sharesTotal +
        v.assetsAvailable.toRat * sB.toRat / v.toExact.sharesTotal = v.assetsAvailable.toRat := by
      rw [← add_div, ← mul_add, hfinal, mul_div_assoc, div_self hSpos.ne', mul_one]
    obtain ⟨h1, h2⟩ := final_bounds v.baseExponent k _ _ _ _ _ _ _ eA eB hkv hsumI hPA hPB (hε _ hIA) (hε _ hIB)
    exact ⟨h1, by linarith, fun _ => h2⟩

/-- Proof of the second line of `Vault.redemption_exit_order`. -/
lemma Vault.redemption_exit_order_lower_bound_proof (v : Vault) (t t0 : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) (hphase : v.phase t = .redemption)
    (sA sB : STAmount) (hA : sA.ShareBalance) (hB : sB.ShareBalance)
    (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat) (hsum : sA.toRat + sB.toRat ≤ v.toExact.sharesTotal)
    (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts)
    (hA1 : (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1))
    (hB2 : (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2))
    (hA2 : (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2)) :
    rA2.assets.toRat - rA1.assets.toRat ≤ 2 * (10 : ℚ) ^ v.baseExponent :=
  (Vault.redemption_exit_order_core v t t0 hr ht hphase (Vault.Reachable.maxValue_fits v t0 hr (by linarith)) sA sB
    hA hB hposA hposB hsum waiveA waiveB waiveA' rA1 rB2 rA2 hA1 hB2 hA2).2.1

/-- Proof of `Vault.redemption_exit_order_lower_bound_final`. -/
lemma Vault.redemption_exit_order_lower_bound_final_proof (v : Vault) (t t0 : UInt32) (hr : Vault.Reachable v t0)
    (ht : t0 ≤ t) (hphase : v.phase t = .redemption)
    (sA sB : STAmount) (hA : sA.ShareBalance) (hB : sB.ShareBalance)
    (hposA : 0 < sA.toRat) (hposB : 0 < sB.toRat) (hsum : sA.toRat + sB.toRat = v.toExact.sharesTotal)
    (waiveA waiveB waiveA' : Bool) (rA1 rB2 rA2 : VaultWithAmounts)
    (hA1 : (v.withdraw (.vaultShares sA) waiveA t hposA).run = .ok (.ok rA1))
    (hB2 : (v.withdraw (.vaultShares sB) waiveB t hposB).run = .ok (.ok rB2))
    (hA2 : (rB2.vault'.withdraw (.vaultShares sA) waiveA' t hposA).run = .ok (.ok rA2)) :
    rA2.assets.toRat - rA1.assets.toRat ≤ (10 : ℚ) ^ v.baseExponent :=
  (Vault.redemption_exit_order_core v t t0 hr ht hphase (Vault.Reachable.maxValue_fits v t0 hr (by linarith)) sA sB
    hA hB hposA hposB hsum.le waiveA waiveB waiveA' rA1 rB2 rA2 hA1 hB2 hA2).2.2 hsum

end XRPL.Model.SingleAssetVault
