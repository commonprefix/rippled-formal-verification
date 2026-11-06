import XRPL.Properties.Vault.Proofs.ExitOrderPayout
import XRPL.Properties.Vault.Proofs.DepositCharge
import XRPL.Properties.Vault.Proofs.ClawbackRecovery
import XRPL.Properties.Vault.Proofs.MaxValueFits

/-! # Every share of a reachable vault is worth at least one base unit

A first deposit issues one share per base unit. A later deposit takes a whole number of base units, short
of the issued shares' worth by less than one, so at least one per share. A withdrawal or a clawback pays a
whole number of base units less than one above the burned shares' worth, which leaves at least one base unit
for every share that stays. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A whole number of steps above `m - 1` steps is at least `m` steps. -/
private lemma steps_ge_of_gt (m : ℤ) (k : ℕ) (B : ℚ) (hB : 0 < B) (h : ((m : ℚ) - 1) * B < (k : ℚ) * B) :
    (m : ℚ) * B ≤ (k : ℚ) * B := by
  have h1 : (m : ℚ) - 1 < (k : ℚ) := lt_of_mul_lt_mul_right h hB.le
  have h2 : m - 1 < (k : ℤ) := by exact_mod_cast h1
  have h3 : (m : ℚ) ≤ (k : ℚ) := by exact_mod_cast (show m ≤ (k : ℤ) by omega)
  exact mul_le_mul_of_nonneg_right h3 hB.le

/-- When every share of a reachable vault is worth at least a base unit, the price of `s` shares stays
below the cash less a base unit for each other share, plus one base unit. -/
private lemma Vault.Reachable.priced_lt_room (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hinv : (v.toExact.sharesTotal : ℚ) * 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat)
    (shares p : STAmount) (w : Bool) (hsc : shares.Canonical) (hs0 : 0 ≤ shares.toRat)
    (hle : shares.toRat ≤ v.toExact.sharesTotal) (hpr : v.sharesToAssetsWithdraw shares w = .ok p) :
    p.toRat < v.assetsAvailable.toRat - ((v.toExact.sharesTotal : ℚ) - shares.toRat) * 10 ^ v.baseExponent +
      10 ^ v.baseExponent := by
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hpc : p.toRat ≤ v.assetsAvailable.toRat :=
    Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax shares p w hs0 hsc hle hpr
  have hp0 : 0 ≤ p.toRat := Vault.sharesToAssetsWithdraw_nonneg v _ _ w (Or.inl hsc) hs0 hpr
  -- the cash less a base unit for each other share still holds a base unit for each priced share
  have hroom : shares.toRat * 10 ^ v.baseExponent ≤
      v.assetsAvailable.toRat - ((v.toExact.sharesTotal : ℚ) - shares.toRat) * 10 ^ v.baseExponent := by
    linarith
  have hsB : 0 ≤ shares.toRat * 10 ^ v.baseExponent := mul_nonneg hs0 hbpos.le
  rcases eq_or_lt_of_le hp0 with hpz | hppos
  · rw [← hpz]
    linarith
  rcases eq_or_lt_of_le (Nat.cast_nonneg v.toExact.sharesTotal : (0 : ℚ) ≤ _) with hS0 | hSpos
  · rw [← hS0]
    nlinarith
  -- the price sits on a grid no coarser than the base grid
  have hpm : p.mValue ≠ 0 := fun h => by
    rw [(STAmount.toRat_eq_zero_iff p).mpr h] at hppos
    exact lt_irrefl _ hppos
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v shares p w hmax hpr
  have hpcan : p.Canonical := hpcz.resolve_right (by simpa [STAmount.isZero] using hpm)
  have hcash : v.assetsAvailable.toRat ≤ 9 * (10 : ℚ) ^ (15 + v.baseExponent) := hz.assetsAvailable_le_openLimit
  have h9 : (9 : ℚ) * 10 ^ (15 + v.baseExponent) = 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
    try ring
  have heb : p.exponent ≤ v.baseExponent := by
    by_cases hint : v.numericType.isIntegral = true
    · have hic : p.IntegralCanonical := (hpcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1
      have he : p.exponent = 0 := hic.offset_zero
      rw [he, v.baseExponent_bounds.2.2 hint]
    have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
    have hio : p.IOUCanonical := hpcan.2 (by unfold STAmount.integral; rw [hpt, hvfr]; rfl)
    have hmlo : (10 ^ 15 : ℚ) ≤ p.mValue.toNat := by exact_mod_cast hio.mant_lo
    have hpv : p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent :=
      STAmount.toRat_of_nonneg p (STAmount.mIsNegative_false_of_pos p hppos)
    have hgpos : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
    have hbig : 10 ^ 15 * (10 : ℚ) ^ p.exponent ≤ p.toRat := by
      rw [hpv]
      exact mul_le_mul_of_nonneg_right hmlo hgpos.le
    by_contra h
    push Not at h
    have h1 : (10 : ℚ) ^ (15 + v.baseExponent + 1) ≤ 10 ^ (15 + p.exponent) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (15 + p.exponent) = 10 ^ 15 * 10 ^ p.exponent := by
      rw [zpow_add₀ (by norm_num)]
      norm_num
    have h3 : (10 : ℚ) ^ (15 + v.baseExponent + 1) = 10 * 10 ^ (15 + v.baseExponent) := by
      rw [zpow_add_one₀ (by norm_num)]
      ring
    have hb' : (0 : ℚ) < 10 ^ (15 + v.baseExponent) := zpow_pos (by norm_num) _
    linarith
  have hE : (10 : ℚ) ^ p.exponent ≤ 10 ^ v.baseExponent := zpow_le_zpow_right₀ (by norm_num) heb
  -- the price is the worth `I` within `sharesε` and half a unit of its grid
  obtain ⟨-, hpu, -⟩ := Vault.sharesToAssetsWithdraw_bounds_proof v shares p w hs0 hsc
    (Vault.Reachable.withdrawNavExact_proof v t0 hr w) hpr
  rw [Vault.Reachable.idealAssetsWithdraw_eq v t0 hr w] at hpu
  set I := v.assetsAvailable.toRat * shares.toRat / (v.toExact.sharesTotal : ℚ) with hI
  have hI0 : 0 ≤ I := div_nonneg (mul_nonneg hA0 hs0) hSpos.le
  have hIroom : I ≤ v.assetsAvailable.toRat - ((v.toExact.sharesTotal : ℚ) - shares.toRat) * 10 ^ v.baseExponent := by
    rw [hI, div_le_iff₀ hSpos]
    nlinarith [mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr hle)]
  have hIA : I ≤ v.assetsAvailable.toRat := by
    rw [hI, div_le_iff₀ hSpos]
    nlinarith [mul_le_mul_of_nonneg_left hle hA0]
  have hIε : I * sharesε ≤ 1 / 100 * 10 ^ v.baseExponent := by
    have hε : sharesε = 11 / 10 ^ 19 := rfl
    rw [h9] at hcash
    rw [hε]
    have h1 : I * (11 / 10 ^ 19) ≤ v.assetsAvailable.toRat * (11 / 10 ^ 19) :=
      mul_le_mul_of_nonneg_right hIA (by norm_num)
    nlinarith
  nlinarith

/-- When every share of an Open-zone vault is worth at least a base unit, so is every share it issues:
the ideal charge for `x` shares is at least `x` base units. -/
private lemma Vault.OpenZone.idealChargeDeposit_ge {v : Vault} (hz : v.OpenZone)
    (hinv : (v.toExact.sharesTotal : ℚ) * 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat) (x : ℚ) (hx : 0 ≤ x) :
    x * 10 ^ v.baseExponent ≤ v.idealChargeDeposit x := by
  unfold RawVault.idealChargeDeposit
  split_ifs with hAT
  · -- an empty vault issues one share per base unit
    have hB : (10 : ℚ) ^ v.baseExponent = 1 / 10 ^ v.scale.toNat := by
      unfold Vault.baseExponent NumericType.baseExponent
      split_ifs with hint
      · rw [v.wf.scale_integral hint]; simp
      · rw [zpow_neg, zpow_natCast]; ring
    rw [hB, mul_one_div]
  · have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by
      rcases eq_or_lt_of_le (Nat.cast_nonneg v.toExact.sharesTotal : (0 : ℚ) ≤ _) with h0 | h0
      · exfalso
        obtain ⟨hA0, hD0⟩ := v.exact.empty_shares (by exact_mod_cast h0.symm)
        exact hAT (by unfold RawVault.Exact.assetsTotal; rw [hA0, hD0]; ring)
      · exact h0
    rw [hz.depositNav_eq, le_div_iff₀ hSpos]
    nlinarith [mul_le_mul_of_nonneg_left hinv hx]

/-- On a reachable vault whose asset fits an `int64` amount every share is worth at least one base unit. -/
private lemma Vault.Reachable.sharesTotal_le_cash_of_fits (v : Vault) (t : UInt32) (hr : Vault.Reachable v t)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) :
    (v.toExact.sharesTotal : ℚ) * 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat := by
  induction hr with
  | create _ _ _ _ _ _ _ w _ hcr =>
    have hv := Vault.create_ok_toRawVault hcr
    have hST : w.sharesTotal = Number.zero := (congrArg RawVault.sharesTotal hv).trans rfl
    have hAA : w.assetsAvailable = Number.zero := (congrArg RawVault.assetsAvailable hv).trans rfl
    rw [RawVault.WF.toExact_sharesTotal w.toRawVault w.wf, hST, hAA, Number.toRat_zero, zero_mul]
  | deposit u t₁ t₂ amount isDonation r hru _ hc hty hpos hok hSsz ih =>
    have hnt := Vault.deposit_numericType u amount isDonation t₂ hpos r hok
    have hmaxu : u.numericType.isIntegral = true → u.numericType.maxValue.toNat ≤ maxRep.toNat := hnt ▸ hmax
    have hinv := ih hmaxu
    have hz := Vault.Reachable.openZone_proof u t₁ hru hmaxu
    obtain ⟨hAA', hz'⟩ := Vault.deposit_openZone u amount isDonation t₂ hpos hc hty hz r hok
    have hST' := Vault.deposit_exact_sharesTotal u amount isDonation t₂ hpos hc hty r hok hSsz
    have hbe := Vault.deposit_baseExponent u amount isDonation t₂ hpos r hok
    have hbpos : (0 : ℚ) < 10 ^ u.baseExponent := zpow_pos (by norm_num) _
    obtain ⟨k', -, hk'⟩ := hz'.cash
    rw [hbe] at hk'
    rw [hbe, hST']
    cases isDonation with
    | true =>
      -- a donation issues no shares and takes a nonnegative amount
      obtain ⟨ra, -, -, hra, -, -, -, -, -, -⟩ := Vault.deposit_ok_reduces u amount true t₂ hpos r hok
      have hrsh := (Vault.deposit_donation_proof u amount ra t₂ hpos hc hra r hok).2
      have hs0 : r.shares.toRat = 0 := by rw [hrsh]; exact STAmount.zero_toRat _
      have hc0 := (Vault.deposit_charge_form u amount true t₂ hpos hc hty r hok).2.2
      rw [hs0, add_zero, hAA']
      linarith
    | false =>
      -- the charge is short of the issued shares' worth by less than a base unit, and that worth is at
      -- least a base unit per share
      obtain ⟨-, hlow, -, -⟩ := Vault.Reachable.deposit_charge_proof u amount t₂ t₁ hpos hru hc r hok
      obtain ⟨-, -, -, -, -, -, -, -, hshc, -, hshpos, -⟩ :=
        DepAcc.Vault.deposit_success_reduces u amount t₂ hpos hc r hok
      have hideal := hz.idealChargeDeposit_ge hinv _ hshpos.le
      set sh := r.shares.toRat with hsh
      have hshint : sh = (sh.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hshc.den_eq_one).symm
      have hcast : ((u.toExact.sharesTotal : ℚ) + sh) = (((u.toExact.sharesTotal : ℤ) + sh.num : ℤ) : ℚ) := by
        push_cast
        rw [← hshint]
      rw [hcast, hk']
      refine steps_ge_of_gt _ k' _ hbpos ?_
      rw [← hk', hAA', ← hcast]
      nlinarith
  | withdraw u t₁ t₂ amount holderShares waive r hru _ hc hty _ _ hpos hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.withdraw_frame u _ _ _ _ r hok
    have hnt : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hsc' : r.vault'.scale = u.scale := (congrArg RawVault.scale hv).trans rfl
    have hbe : r.vault'.baseExponent = u.baseExponent := by unfold Vault.baseExponent; rw [hnt, hsc']
    have hmaxu : u.numericType.isIntegral = true → u.numericType.maxValue.toNat ≤ maxRep.toNat := hnt ▸ hmax
    have hinv := ih hmaxu
    have hz := Vault.Reachable.openZone_proof u t₁ hru hmaxu
    obtain ⟨hAA', hz'⟩ := Vault.withdraw_openZone u amount waive t₂ hpos hz hmaxu r hok
    have hST' := Vault.withdraw_exact_sharesTotal u amount waive t₂ hpos hc hty r hok
    have hbpos : (0 : ℚ) < 10 ^ u.baseExponent := zpow_pos (by norm_num) _
    have hS'0 : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
    rw [hST'] at hS'0
    obtain ⟨k', -, hk'⟩ := hz'.cash
    rw [hbe] at hk'
    rw [hbe, hST']
    rcases eq_or_lt_of_le (show r.shares.toRat ≤ (u.toExact.sharesTotal : ℚ) by linarith) with hfin | hlt
    · -- the final withdrawal leaves no shares
      rw [hfin, sub_self, zero_mul]
      exact r.vault'.exact.assetsAvailable_nonneg
    -- shares remain: the payout is at most the price of the burned shares
    obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form u amount waive t₂ hpos hc hty r hok
    have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
    obtain ⟨priced, hpr, hP, -⟩ := Vault.withdraw_payout_proof u amount waive t₂ t₁ hpos hru hc hty hmaxu r hok hlt
    have hp0 : 0 ≤ priced.toRat := Vault.sharesToAssetsWithdraw_nonneg u _ _ waive (Or.inl hsc) hspos.le hpr
    have hρ : (0 : ℚ) ≤ ((u.earlyExitFeeRateAt t₂).toNat : ℚ) / 100000 := by positivity
    have hPp : r.assets.toRat ≤ priced.toRat := by nlinarith [mul_nonneg hp0 hρ]
    have hroom := Vault.Reachable.priced_lt_room u t₁ hru hmaxu hinv r.shares priced waive hsc hspos.le hlt.le hpr
    set s := r.shares.toRat with hs
    have hsint : s = (s.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hsic.den_eq_one).symm
    have hcast : (u.toExact.sharesTotal : ℚ) - s = (((u.toExact.sharesTotal : ℤ) - s.num : ℤ) : ℚ) := by
      push_cast
      rw [← hsint]
    rw [hcast, hk']
    refine steps_ge_of_gt _ k' _ hbpos ?_
    rw [← hk', hAA', ← hcast]
    linarith
  | clawback u t₁ t₂ assets holderShares waive r hru _ hc hty hhs _ hnn hok _ ih =>
    obtain ⟨_, _, hv⟩ := Vault.clawback_frame u _ _ _ _ r hok
    have hnt : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hsc' : r.vault'.scale = u.scale := (congrArg RawVault.scale hv).trans rfl
    have hbe : r.vault'.baseExponent = u.baseExponent := by unfold Vault.baseExponent; rw [hnt, hsc']
    have hmaxu : u.numericType.isIntegral = true → u.numericType.maxValue.toNat ≤ maxRep.toNat := hnt ▸ hmax
    have hinv := ih hmaxu
    have hz := Vault.Reachable.openZone_proof u t₁ hru hmaxu
    obtain ⟨hAA', hz'⟩ := Vault.clawback_openZone u assets holderShares waive hnn hc hhs hmaxu hz r hok
    have hST' := Vault.clawback_exact_sharesTotal u assets holderShares waive hnn hc hhs hmaxu r hok
    have hbpos : (0 : ℚ) < 10 ^ u.baseExponent := zpow_pos (by norm_num) _
    have hS'0 : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
    rw [hST'] at hS'0
    obtain ⟨k', -, hk'⟩ := hz'.cash
    rw [hbe] at hk'
    rw [hbe, hST']
    -- the recovery is at most the price of the destroyed shares
    obtain ⟨rec, hcp, -, -⟩ := Vault.clawback_recovery_cases u assets holderShares waive hnn r hok
    obtain ⟨hsic, hs64, hs0, -⟩ := hcp.form hc hnn hhs hmaxu
    have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
    obtain ⟨priced, hpr, -, -, -, -, hPp, -⟩ :=
      Vault.clawback_recovery_le u assets holderShares waive hnn hmaxu r hok (Or.inl hsc) hs0
    have hroom := Vault.Reachable.priced_lt_room u t₁ hru hmaxu hinv r.shares priced waive hsc hs0 (by linarith) hpr
    set s := r.shares.toRat with hs
    have hsint : s = (s.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hsic.den_eq_one).symm
    have hcast : (u.toExact.sharesTotal : ℚ) - s = (((u.toExact.sharesTotal : ℤ) - s.num : ℤ) : ℚ) := by
      push_cast
      rw [← hsint]
    rw [hcast, hk']
    refine steps_ge_of_gt _ k' _ hbpos ?_
    rw [← hk', hAA', ← hcast]
    linarith
  | burnShares u t₁ t₂ amount holderShares sharesTotalAmount u' hru _ _ hcan hok ih =>
    -- a burn needs an insolvent vault, which has shares but no cash: impossible here
    obtain ⟨_, hv⟩ := Vault.burnShares_frame u _ u' hok
    have hnt : u'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hinv := ih (hnt ▸ hmax)
    have hSpos := Vault.canBurnShares_sharesTotal_pos u amount holderShares sharesTotalAmount hcan
    obtain ⟨hins, -, -⟩ := Vault.canBurnShares_ok_reduces u amount holderShares sharesTotalAmount hcan
    have hAm : u.assetsAvailable.mantissa_ = 0 := by
      unfold Vault.isInsolvent at hins
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hins
      exact hins.1.1
    rw [Number.toRat_eq_zero_of_mantissa_zero _ hAm] at hinv
    have hbpos : (0 : ℚ) < 10 ^ u.baseExponent := zpow_pos (by norm_num) _
    exfalso
    nlinarith [mul_pos hSpos hbpos]
  | update u t₁ t₂ _ _ _ u' _ _ _ hok ih =>
    obtain ⟨_, _, hv⟩ := Vault.update_frame u _ _ _ u' hok
    have hnt : u'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hsc' : u'.scale = u.scale := (congrArg RawVault.scale hv).trans rfl
    have hAA : u'.assetsAvailable = u.assetsAvailable := (congrArg RawVault.assetsAvailable hv).trans rfl
    have hST : u'.sharesTotal = u.sharesTotal := (congrArg RawVault.sharesTotal hv).trans rfl
    have hbe : u'.baseExponent = u.baseExponent := by unfold Vault.baseExponent; rw [hnt, hsc']
    have hinv := ih (hnt ▸ hmax)
    rw [RawVault.WF.toExact_sharesTotal u'.toRawVault u'.wf, hST, hAA, hbe]
    rwa [RawVault.WF.toExact_sharesTotal u.toRawVault u.wf] at hinv

/-- Proof of the share line of `Vault.Reachable.vault_fields`. A vault with shares has an asset that fits. -/
lemma Vault.Reachable.sharesTotal_le_cash_proof (v : Vault) (t : UInt32) (hr : Vault.Reachable v t) :
    (v.toExact.sharesTotal : ℚ) * 10 ^ v.baseExponent ≤ v.assetsAvailable.toRat := by
  rcases Vault.Reachable.maxValue_fits_or_no_shares v t hr with hmax | hS
  · exact Vault.Reachable.sharesTotal_le_cash_of_fits v t hr hmax
  · rw [hS, zero_mul]
    exact v.exact.assetsAvailable_nonneg

/-- A deposit into a reachable vault keeps the share total within the MPT maximum: the share total is at most the
cash in base units, so within the Open-zone limit, and each issued share costs at least a base unit. -/
lemma Vault.Reachable.deposit_mint_fits_proof (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (amount : STAmount) (isDonation : Bool) (t : UInt32) (hpos : 0 < amount.toRat) (hc : amount.Canonical)
    (hty : amount.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1 := by
  have hmax := Vault.maxValue_fits_of_canonical v amount hc hty
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hinv := Vault.Reachable.sharesTotal_le_cash_of_fits v t0 hr hmax
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have h9 : (9 : ℚ) * 10 ^ (15 + v.baseExponent) = 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
    try ring
  have hcash := hz.assetsAvailable_le_openLimit
  rw [h9] at hcash
  -- the share total is at most `9·10^15`
  have hS : (v.toExact.sharesTotal : ℚ) ≤ 9 * 10 ^ 15 := by
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_right h hbpos]
  cases isDonation with
  | true =>
    obtain ⟨ra, -, -, hra, -, -, -, -, -, -⟩ := Vault.deposit_ok_reduces v amount true t hpos r hok
    have hrsh := (Vault.deposit_donation_proof v amount ra t hpos hc hra r hok).2
    rw [hrsh, STAmount.zero_toRat]
    linarith
  | false =>
    -- the issued shares cost at least a base unit each, and the charge stays within the Open-zone limit
    obtain ⟨-, hlow, -, -⟩ := Vault.Reachable.deposit_charge_proof v amount t t0 hpos hr hc r hok
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hshpos, -⟩ :=
      DepAcc.Vault.deposit_success_reduces v amount t hpos hc r hok
    have hideal := hz.idealChargeDeposit_ge hinv _ hshpos.le
    have hopen := Vault.deposit_open_bound v amount false t hpos hc hty v.assetsAvailable hz.assetsTotal_eq r hok
    rw [h9] at hopen
    have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
    have hsh : r.shares.toRat ≤ 9 * 10 ^ 15 + 2 := by
      by_contra h
      push Not at h
      nlinarith [mul_lt_mul_of_pos_right h hbpos]
    linarith

end XRPL.Model.SingleAssetVault
