import XRPL.Properties.Vault.Proofs.WithdrawPayoutFloor
import XRPL.Properties.Vault.Proofs.WithdrawTight
import XRPL.Properties.Vault.Proofs.WithdrawPricing
import XRPL.Properties.Vault.Proofs.WithdrawFee

/-! # One payout of the exit-order comparison

For one withdrawal by shares from a reachable vault in the redemption phase, the payout is the priced
amount floored onto the base grid, and the priced amount sits within `sharesε` and half its own ULP of
the shares' worth. The waive flag changes nothing on a vault with no unrealized loss. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- With no unrealized loss both net asset values are the same: there is no loss to subtract. -/
lemma Vault.assetsTotalForWithdrawal_waive (v : Vault) (hLU : v.lossUnrealized = Number.zero) (w : Bool) :
    v.assetsTotalForWithdrawal w = v.assetsTotalForWithdrawal false := by
  cases w
  · rfl
  · simp only [Vault.assetsTotalForWithdrawal, hLU]

lemma Vault.sharesToAssetsWithdraw_waive (v : Vault) (hLU : v.lossUnrealized = Number.zero)
    (shares : STAmount) (w : Bool) :
    v.sharesToAssetsWithdraw shares w = v.sharesToAssetsWithdraw shares false := by
  unfold Vault.sharesToAssetsWithdraw
  rw [Vault.assetsTotalForWithdrawal_waive v hLU w]

lemma assetsToSharesWithdraw_waive (v : Vault) (hLU : v.lossUnrealized = Number.zero)
    (assets : STAmount) (truncateShares w : Bool) :
    assetsToSharesWithdraw v assets truncateShares w = assetsToSharesWithdraw v assets truncateShares false := by
  unfold assetsToSharesWithdraw
  rw [Vault.assetsTotalForWithdrawal_waive v hLU w]

lemma computeWithdraw_waive (v : Vault) (hLU : v.lossUnrealized = Number.zero) (amount : WithdrawAmount)
    (w : Bool) : computeWithdraw v amount w = computeWithdraw v amount false := by
  cases w
  · rfl
  · unfold computeWithdraw
    simp only [Vault.sharesToAssetsWithdraw_waive v hLU, assetsToSharesWithdraw_waive v hLU]

/-- On a vault with no unrealized loss, as every reachable vault is, the waive flag changes nothing. -/
lemma Vault.withdraw_waive (v : Vault) (hLU : v.lossUnrealized = Number.zero) (amount : WithdrawAmount)
    (w : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat) :
    (v.withdraw amount w t hpos).run = (v.withdraw amount false t hpos).run := by
  cases w
  · rfl
  · unfold Vault.withdraw
    simp only [computeWithdraw_waive v hLU, Vault.assetsTotalForWithdrawal_waive v hLU]

/-- A reachable vault prices at its cash: nothing is deployed and there is no loss. -/
lemma Vault.Reachable.assetsTotalForWithdrawal_eq (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (w : Bool) : v.assetsTotalForWithdrawal w = .ok v.assetsAvailable := by
  obtain ⟨-, hLU, -⟩ := Vault.Reachable.noLending_proof v t0 hr
  have hsub : v.assetsAvailable.operator_sub Number.zero .to_nearest = .ok v.assetsAvailable := by
    show v.assetsAvailable.operator_add Number.zero.operator_neg .to_nearest = _
    rw [show Number.zero.operator_neg = Number.zero by decide]
    exact Number.operator_add_zero_right _ _
  simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, Vault.Reachable.asset_parity_proof v t0 hr]
  cases w
  · rw [hLU]; exact hsub
  · exact hsub

/-- The shares' worth on a reachable vault: the cash, times the shares, over the share total. -/
lemma Vault.Reachable.idealAssetsWithdraw_eq (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) (w : Bool)
    (shares : ℚ) :
    v.idealAssetsWithdraw w shares = v.assetsAvailable.toRat * shares / v.toExact.sharesTotal := by
  obtain ⟨hAD, hLU, -⟩ := Vault.Reachable.noLending_proof v t0 hr
  have hAD0 : v.assetsDeployed.toRat = 0 := by rw [hAD, Number.toRat_zero]
  have hLU0 : v.lossUnrealized.toRat = 0 := by rw [hLU, Number.toRat_zero]
  unfold RawVault.idealAssetsWithdraw
  cases w
  · show (v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat) * shares / _ = _
    rw [hAD0, hLU0]; ring
  · show (v.assetsAvailable.toRat + v.assetsDeployed.toRat) * shares / _ = _
    rw [hAD0]; ring

/-- A withdrawal by fewer than all the shares of a reachable vault keeps it reachable, whatever the
waive flag: only the sole shareholder may waive, and the flag changes nothing anyway. -/
lemma Vault.Reachable.withdraw_shares_step (v : Vault) (t t0 : UInt32) (hr : Vault.Reachable v t0) (ht : t0 ≤ t)
    (shares : STAmount) (hs : shares.ShareBalance) (w : Bool) (hpos : 0 < shares.toRat)
    (hlt : shares.toRat < v.toExact.sharesTotal) (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultShares shares) w t hpos).run = .ok (.ok r)) :
    Vault.Reachable r.vault' t := by
  rw [Vault.withdraw_waive v (Vault.Reachable.noLending_proof v t0 hr).2.1 (.vaultShares shares) w t hpos] at hok
  exact Vault.Reachable.withdraw v t0 t (.vaultShares shares) shares false r hr ht hs.canonical hs.int64 hs
    (iff_of_false (by decide) (fun h => absurd h.2 (ne_of_lt hlt))) hpos hok
    (le_of_eq (congrArg STAmount.toRat (Vault.withdraw_sharesBurned_exact_proof v shares false t hpos r hok)))

/-- A withdrawal by shares priced at zero succeeds only at a zero net asset value: otherwise
the precision-loss check refuses it. -/
lemma Vault.withdraw_shares_zero_price (v : Vault) (shares : STAmount) (w : Bool) (t : UInt32)
    (hpos : 0 < shares.toRat) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (r : VaultWithAmounts) (hok : (v.withdraw (.vaultShares shares) w t hpos).run = .ok (.ok r))
    (hlt : shares.toRat < v.toExact.sharesTotal) (priced : STAmount)
    (hpr : v.sharesToAssetsWithdraw shares w = .ok priced) (hz : priced.isZero = true) :
    ∃ nav : Number, v.assetsTotalForWithdrawal w = .ok nav ∧ nav.operator_ne Number.zero = false := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v (.vaultShares shares) w t hpos hc hty r hok
  have hsz : shares.isZero = false := by
    unfold STAmount.isZero
    have hm : shares.mValue ≠ 0 := fun h => by
      rw [(STAmount.toRat_eq_zero_iff shares).mpr h] at hpos; exact lt_irrefl _ hpos
    simpa using hm
  have hcomp := computeWithdraw_shares_ok_of_price v shares priced w hsz hpr
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  -- the computation priced the named shares
  all_goals
    have hcomp' : (computeWithdraw v (.vaultShares shares) w).run = .ok (.ok _) := ‹_›
    obtain rfl := Except.ok.inj (Except.ok.inj (hcomp.symm.trans hcomp'))
  all_goals try dsimp only at *
  -- the run is not final
  all_goals
    have hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok _ := ‹_›
    have hnf : ¬ STAmount.operator_eq shares _ = true :=
      (Vault.isFinalWithdrawal_iff v shares _ hsic hs64 hspos hst).not.mpr (ne_of_lt hlt)
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  all_goals
    have hnav : v.assetsTotalForWithdrawal w = .ok _ := ‹_›
    refine ⟨_, hnav, Bool.eq_false_iff.mpr (fun h => ?_)⟩
    exact absurd (And.intro hz h) ‹_›

/-- What the exit-order bounds use about one payout: the shares' worth `I`, the priced amount `p`
on the grid `10^e`, and the payout `P` on the base grid `10^b`. -/
structure Vault.RedemptionPayout (b : ℤ) (I p P : ℚ) (e : ℤ) : Prop where
  grid : e ≤ b
  floor : P = (⌊p / 10 ^ b⌋ : ℚ) * 10 ^ b
  nonneg : 0 ≤ p
  upper : p ≤ I * (1 + sharesε) + 1 / 2 * (10 : ℚ) ^ e
  lower : I - p ≤ I * sharesε + 1 / 2 * (10 : ℚ) ^ e
  remainder : p - P ≤ (10 : ℚ) ^ b - 10 ^ e
  relative : I * sharesε < 111 / 10 ^ 4 * (10 : ℚ) ^ e
  small : p < 10 ^ 16 * (10 : ℚ) ^ e
  idealNonneg : 0 ≤ I

/-- A priced amount below `10^16` steps of its grid keeps the relative pricing error of the worth below `111/10^4`
of a step. -/
private lemma relative_of_small (I p g : ℚ) (hg : 0 < g) (hl : I - p ≤ I * sharesε + 1 / 2 * g)
    (hs : p < 10 ^ 16 * g) : I * sharesε < 111 / 10 ^ 4 * g := by
  unfold sharesε at *
  have h1 : I * (1 - 11 / 10 ^ 19) < (10 ^ 16 + 1 / 2) * g := by linarith
  have h2 : I < (10 ^ 16 + 1 / 2) * g / (1 - 11 / 10 ^ 19) := by
    rw [lt_div_iff₀ (by norm_num)]; linarith
  have hc : ((10 ^ 16 + 1 / 2) / (1 - 11 / 10 ^ 19) * (11 / 10 ^ 19) : ℚ) ≤ 111 / 10 ^ 4 := by norm_num
  calc I * (11 / 10 ^ 19) < (10 ^ 16 + 1 / 2) * g / (1 - 11 / 10 ^ 19) * (11 / 10 ^ 19) :=
        mul_lt_mul_of_pos_right h2 (by norm_num)
    _ = ((10 ^ 16 + 1 / 2) / (1 - 11 / 10 ^ 19) * (11 / 10 ^ 19)) * g := by ring
    _ ≤ 111 / 10 ^ 4 * g := mul_le_mul_of_nonneg_right hc hg.le

/-- The facts of one withdrawal by shares from a reachable vault with no fee. The priced amount sits on
the base grid on an integral vault, and has a 16-digit mantissa on a fractional one when nonzero. -/
lemma Vault.Reachable.redemptionPayout (v : Vault) (t t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hfee : v.earlyExitFeeRateAt t = 0)
    (shares : STAmount) (hs : shares.ShareBalance) (hpos : 0 < shares.toRat)
    (hlt : shares.toRat < v.toExact.sharesTotal) (r : VaultWithAmounts)
    (hok : (v.withdraw (.vaultShares shares) false t hpos).run = .ok (.ok r)) :
    ∃ (p : STAmount) (e : ℤ),
      v.sharesToAssetsWithdraw shares false = .ok p ∧
      Vault.RedemptionPayout v.baseExponent (v.assetsAvailable.toRat * shares.toRat / v.toExact.sharesTotal)
        p.toRat r.assets.toRat e ∧
      p.toRat ≤ v.assetsAvailable.toRat ∧
      (v.numericType.isIntegral = true → e = v.baseExponent) ∧
      (v.numericType.isIntegral = false → p.toRat ≠ 0 → 10 ^ 15 * (10 : ℚ) ^ e ≤ p.toRat) := by
  set I : ℚ := v.assetsAvailable.toRat * shares.toRat / v.toExact.sharesTotal with hI
  have hsc : shares.Canonical := hs.canonical
  have hshares : r.shares = shares := Vault.withdraw_sharesBurned_exact_proof v shares false t hpos r hok
  have hlt' : r.shares.toRat < v.toExact.sharesTotal := by rw [hshares]; exact hlt
  obtain ⟨p, hpr, hfl⟩ := Vault.Reachable.withdraw_payout_floor_proof v (.vaultShares shares) false t t0 hpos hr
    hsc hs.int64 hmax r hok hlt'
  rw [hshares] at hpr
  have h0 : ((v.earlyExitFeeRateAt t).toNat : ℚ) = 0 := by rw [hfee]; rfl
  rw [h0, zero_div, sub_zero, mul_one] at hfl
  obtain ⟨hp0, hpu, hpl⟩ := Vault.sharesToAssetsWithdraw_bounds_proof v shares p false hpos.le hsc
    (Vault.Reachable.withdrawNavExact_proof v t0 hr false) hpr
  rw [Vault.Reachable.idealAssetsWithdraw_eq v t0 hr false, ← hI] at hpu hpl
  have hpc : p.toRat ≤ v.assetsAvailable.toRat :=
    Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax shares p false hpos.le hsc hlt.le hpr
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v shares p false hmax hpr
  have hcash := (Vault.Reachable.openZone_proof v t0 hr hmax).assetsAvailable_le_openLimit
  have hC0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hS0 : (0 : ℚ) ≤ v.toExact.sharesTotal := Nat.cast_nonneg _
  have hI0 : 0 ≤ I := by rw [hI]; exact div_nonneg (mul_nonneg hC0 hpos.le) hS0
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  by_cases hpz : p.toRat = 0
  · -- a zero price: the vault holds nothing, so the worth and the payout are zero as well
    have hC : v.assetsAvailable.toRat = 0 := by
      obtain ⟨nav, hnav, hne⟩ := Vault.withdraw_shares_zero_price v shares false t hpos hsc hs.int64 r hok hlt p
        hpr (by simpa [STAmount.isZero] using (STAmount.toRat_eq_zero_iff p).mp hpz)
      rw [Vault.Reachable.assetsTotalForWithdrawal_eq v t0 hr false, Except.ok.injEq] at hnav
      rw [← hnav] at hne
      exact (Number.operator_ne_zero_eq_false_iff _ v.wf.assetsAvailable_norm).mp hne
    have hI0' : I = 0 := by rw [hI, hC, zero_mul, zero_div]
    have hP : r.assets.toRat = 0 := by rw [hfl, hpz, zero_div, Int.floor_zero, Int.cast_zero, zero_mul]
    refine ⟨p, v.baseExponent, hpr, ⟨le_refl _, hfl, hp0, ?_, ?_, ?_, ?_, ?_, hI0⟩, hpc, fun _ => rfl,
      fun _ h => absurd hpz h⟩
    · rw [hpz, hI0', zero_mul, zero_add]; positivity
    · rw [hpz, hI0', sub_zero, zero_mul, zero_add]; positivity
    · rw [hpz, hP, sub_zero, sub_self]
    · rw [hI0', zero_mul]; positivity
    · rw [hpz]; positivity
  have hppos : 0 < p.toRat := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hpm : p.mValue ≠ 0 := fun h => hpz ((STAmount.toRat_eq_zero_iff p).mpr h)
  have hpcan : p.Canonical := hpcz.resolve_right (by simpa [STAmount.isZero] using hpm)
  replace hpl := hpl (by simpa [STAmount.isZero] using hpm)
  have hpv : p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent :=
    STAmount.toRat_of_nonneg p (STAmount.mIsNegative_false_of_pos p hppos)
  by_cases hint : v.numericType.isIntegral = true
  · -- integral: the priced amount is a whole number of base units, so the floor keeps it
    have hb0 : v.baseExponent = 0 := v.baseExponent_bounds.2.2 hint
    have hic : p.IntegralCanonical := (hpcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1
    have he : p.exponent = 0 := hic.offset_zero
    rw [he] at hpu hpl hpv
    rw [zpow_zero, mul_one] at hpv
    have hpfl : r.assets.toRat = p.toRat := by
      rw [hfl, hb0, zpow_zero, div_one, mul_one, hpv, Int.floor_natCast, Int.cast_natCast]
    have hsmall : p.toRat < 10 ^ 16 * (10 : ℚ) ^ (0 : ℤ) := by
      rw [hb0] at hcash
      norm_num at hcash ⊢
      linarith
    refine ⟨p, 0, hpr, ⟨by rw [hb0], hfl, hp0, hpu, hpl, by rw [hpfl, hb0]; simp,
      relative_of_small I p.toRat _ (by norm_num) hpl hsmall, hsmall, hI0⟩, hpc, fun _ => hb0.symm,
      fun h => absurd hint (by rw [h]; decide)⟩
  -- fractional: a 16-digit priced amount on a grid no coarser than the base grid
  have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hio : p.IOUCanonical := hpcan.2 (by unfold STAmount.integral; rw [hpt, hvfr]; rfl)
  have hmlo : (10 ^ 15 : ℚ) ≤ p.mValue.toNat := by exact_mod_cast hio.mant_lo
  have hmhi : (p.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hio.mant_hi
  have hgpos : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  have hsmall : p.toRat < 10 ^ 16 * (10 : ℚ) ^ p.exponent := by
    rw [hpv]; exact mul_lt_mul_of_pos_right hmhi hgpos
  have hbig : 10 ^ 15 * (10 : ℚ) ^ p.exponent ≤ p.toRat := by
    rw [hpv]; exact mul_le_mul_of_nonneg_right hmlo hgpos.le
  -- the grid is no coarser than the base grid: 16 digits of it stay under `9·10^15` base units
  have heb : p.exponent ≤ v.baseExponent := by
    by_contra h
    push Not at h
    have h1 : (10 : ℚ) ^ (15 + v.baseExponent + 1) ≤ 10 ^ (15 + p.exponent) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (15 + p.exponent) = 10 ^ 15 * 10 ^ p.exponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    have h3 : (10 : ℚ) ^ (15 + v.baseExponent + 1) = 10 * 10 ^ (15 + v.baseExponent) := by
      rw [zpow_add_one₀ (by norm_num)]; ring
    have hb' : (0 : ℚ) < 10 ^ (15 + v.baseExponent) := zpow_pos (by norm_num) _
    linarith
  -- the floor onto the base grid drops less than one base step, in whole steps of the fine grid
  have hrem : p.toRat - r.assets.toRat ≤ (10 : ℚ) ^ v.baseExponent - 10 ^ p.exponent := by
    set d := (v.baseExponent - p.exponent).toNat with hd
    have hdb : (10 : ℚ) ^ v.baseExponent = ((10 ^ d : ℕ) : ℚ) * 10 ^ p.exponent := by
      rw [hd]
      push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ (by norm_num)]
      congr 1
      ring
    set q := ⌊p.toRat / 10 ^ v.baseExponent⌋ with hq
    have hq1 := Int.lt_floor_add_one (p.toRat / 10 ^ v.baseExponent)
    rw [div_lt_iff₀ hbpos, ← hq, hdb, hpv] at hq1
    have hlin : ((p.mValue.toNat : ℤ) - q * (10 ^ d : ℕ) : ℤ) < (10 ^ d : ℕ) := by
      have hlt1 : (((p.mValue.toNat : ℤ) - q * (10 ^ d : ℕ) : ℤ) : ℚ) * 10 ^ p.exponent <
          ((10 ^ d : ℕ) : ℚ) * 10 ^ p.exponent := by
        push_cast at hq1 ⊢
        linear_combination hq1
      exact_mod_cast lt_of_mul_lt_mul_right hlt1 hgpos.le
    have hle : (((p.mValue.toNat : ℤ) - q * (10 ^ d : ℕ) : ℤ) : ℚ) ≤ ((10 ^ d : ℕ) : ℚ) - 1 := by
      have : ((p.mValue.toNat : ℤ) - q * (10 ^ d : ℕ) : ℤ) ≤ (10 ^ d : ℕ) - 1 := by omega
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right hle hgpos.le
    rw [hfl, hdb, hpv]
    push_cast at this ⊢
    linear_combination this
  refine ⟨p, p.exponent, hpr, ⟨heb, hfl, hp0, hpu, hpl, hrem, relative_of_small I p.toRat _ hgpos hpl hsmall,
    hsmall, hI0⟩, hpc, fun h => absurd h (by simpa using hint), fun _ _ => hbig⟩

end XRPL.Model.SingleAssetVault
