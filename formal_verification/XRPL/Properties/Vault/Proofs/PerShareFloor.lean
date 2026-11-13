import XRPL.Properties.Vault.Proofs.PerShareValue
import XRPL.Properties.Vault.Proofs.ClawbackShareFloor
import XRPL.Properties.Vault.Proofs.WithdrawUpdates
import XRPL.Properties.Vault.Proofs.DepositChargeFloor

/-! # Withdrawals and clawbacks that keep the per-share value

On a reachable vault a withdrawal or a clawback whose shares are worth a whole number of base units takes at most
that worth, so the per-share value of the shares that remain does not drop. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

open private Vault.withdrawNav_of_cash Vault.withdrawNav_le_total from XRPL.Properties.Vault.Proofs.PerShareValue

/-- A debit of at most the burned shares' worth keeps the net asset value per share. -/
private lemma debit_le_worth (A S x π : ℚ) (hS : 0 < S) (hπ : π ≤ A * x / S) : (A - π) * S ≥ A * (S - x) := by
  have h1 : π * S ≤ A * x := by
    have := mul_le_mul_of_nonneg_right hπ hS.le
    rwa [div_mul_cancel₀ _ hS.ne'] at this
  nlinarith

/-- Proof of the withdrawal line of `Vault.no_dilution`. -/
lemma Vault.Reachable.withdraw_no_dilution_intended_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool)
    (t t0 : UInt32) (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hworth : ∃ k : ℤ, v.idealAssetsWithdraw waive r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨hAA', hz'⟩ := Vault.withdraw_openZone v amount waive t hpos hz hmax r hok
  have hST' := Vault.withdraw_exact_sharesTotal v amount waive t hpos hc hty r hok
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hS'0 : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  rw [hST', hcast] at hS'0
  have hI := hz.idealAssetsWithdraw_eq waive r.shares.toRat
  rw [hz.withdrawNav_eq, hz'.withdrawNav_eq, hAA', hST', hcast]
  have hSpos : 0 < v.sharesTotal.toRat := by linarith
  refine debit_le_worth _ _ _ _ hSpos ?_
  rw [← hI]
  rcases lt_or_eq_of_le (show r.shares.toRat ≤ v.sharesTotal.toRat by linarith) with hlt | hfin
  · -- shares remain: the payout is at most the price, which is at most the worth
    obtain ⟨priced, hpr, hpay, -⟩ :=
      Vault.withdraw_payout_proof v amount waive t t0 hpos hr hc hty hmax r hok (by rw [hcast]; exact hlt)
    have hpc := Vault.Reachable.sharesToAssetsWithdraw_le_cash v t0 hr hmax r.shares priced waive hspos.le hsc
      (by rw [hcast]; exact hlt.le) hpr
    have hle := hz.priced_le_worth hmax r.shares priced waive hspos.le hsc hpr hpc hworth
    have hp0 := (Vault.sharesToAssetsWithdraw_bounds_proof v r.shares priced waive hspos.le hsc
      (Vault.Reachable.withdrawNavExact_proof v t0 hr waive) hpr).1
    have hρ := Vault.earlyExitFeeRateAt_le v t
    have hρ' : (0 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat / 100000 := by positivity
    have hρ1 : ((v.earlyExitFeeRateAt t).toNat : ℚ) / 100000 ≤ 1 := by
      rw [div_le_one (by norm_num)]; exact_mod_cast hρ
    nlinarith
  · -- the final withdrawal pays exactly the worth of every share
    exact le_of_eq (Vault.withdraw_final_payout_proof v amount waive t t0 hpos hr hc hty hmax r hok
      (by rw [hcast]; exact hfin))

/-- Proof of the clawback line of `Vault.no_dilution`. -/
lemma Vault.Reachable.clawback_no_dilution_intended_proof (v : Vault) (assets holderShares : STAmount)
    (waive : Bool) (t0 : UInt32) (hnn : 0 ≤ assets.toRat) (hr : Vault.Reachable v t0)
    (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r))
    (hworth : ∃ k : ℤ, v.idealAssetsWithdraw waive r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  obtain ⟨hsic, hs64, hs0, -⟩ := hcp.form hc hnn hhs hmax
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, -, -, hple, -, hrle, -⟩ :=
    Vault.clawback_recovery_le v assets holderShares waive hnn hmax r hok (Or.inl hsc) hs0
  have hle := hz.priced_le_worth hmax r.shares priced waive hs0 hsc hpr hple hworth
  obtain ⟨hAA', hz'⟩ := Vault.clawback_openZone v assets holderShares waive hnn hc hhs hmax hz r hok
  have hST' := Vault.clawback_exact_sharesTotal v assets holderShares waive hnn hc hhs hmax r hok
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hS'0 : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  rw [hST', hcast] at hS'0
  have hI := hz.idealAssetsWithdraw_eq waive r.shares.toRat
  rw [hz.withdrawNav_eq, hz'.withdrawNav_eq, hAA', hST', hcast]
  have hspos : 0 < r.shares.toRat := by
    rcases lt_or_eq_of_le hs0 with h | h
    · exact h
    · exact absurd h.symm (STAmount.toRat_ne_zero _ (by simpa [STAmount.isZero] using hsnz))
  have hSpos : 0 < v.sharesTotal.toRat := by linarith
  refine debit_le_worth _ _ _ _ hSpos ?_
  rw [← hI]
  exact le_trans hrle hle

/-- A deposit's charge times the share total, from a charge priced at least at the issued shares' worth at the
computed total: at least that worth times the share total. -/
lemma Vault.deposit_charge_mul_of_ge (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical) (navN : Number)
    (hat : v.assetsTotal = .ok navN) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hge : v.idealChargeDepositAt navN.toRat r.shares.toRat ≤ r.assets.toRat) :
    navN.toRat * r.shares.toRat ≤ r.assets.toRat * (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨-, priced, navN', -, -, -, -, -, hshc, hshnt, hshpos, hsad, -, hat', hcl, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  have hc0 := DepAcc.Vault.deposit_charge_nonneg v r.shares priced r.assets navN hshc hshnt hshpos hsad hcl
  have hS0 : (0 : ℚ) ≤ (v.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  by_cases hmz : navN.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero navN hmz, zero_mul]
    exact mul_nonneg hc0 hS0
  have hnpos := (Vault.assetsTotal_pos v navN hat hmz).2
  have hSpos : (0 : ℚ) < (v.toExact.sharesTotal : ℚ) := by
    have hne : v.toExact.sharesTotal ≠ 0 := fun h0 => by
      have := Vault.exact_assetsTotal_eq_zero v h0
      linarith [Vault.assetsTotal_le_exact v navN hat]
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hI : v.idealChargeDepositAt navN.toRat r.shares.toRat =
      navN.toRat * r.shares.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold RawVault.idealChargeDepositAt
    rw [if_neg (ne_of_gt hnpos)]
  rw [hI, div_le_iff₀ hSpos] at hge
  exact hge

/-- A non-final withdrawal from an Open-zone vault, whose burned shares are worth a whole number of base units,
keeps the per-share value. -/
lemma Vault.OpenZone.withdraw_keeps_perShare {v : Vault} (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (amount : WithdrawAmount) (waive : Bool) (t : UInt32) (hpos : 0 < amount.amount.toRat)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < (v.toExact.sharesTotal : ℚ))
    (hworth : ∃ k : ℤ, v.idealAssetsWithdraw waive r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨hAA', hz'⟩ := Vault.withdraw_openZone v amount waive t hpos hz hmax r hok
  have hST' := Vault.withdraw_exact_sharesTotal v amount waive t hpos hc hty r hok
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hI := hz.idealAssetsWithdraw_eq waive r.shares.toRat
  obtain ⟨priced, hpr, hpay⟩ := Vault.withdraw_payout_le_proof v amount waive t hpos hc hty hmax r hok hlt
  have hpc := hz.sharesToAssetsWithdraw_le_cash hmax r.shares priced waive hspos.le hsc hlt.le hpr
  have hle := hz.priced_le_worth hmax r.shares priced waive hspos.le hsc hpr hpc hworth
  have hp0 := (Vault.sharesToAssetsWithdraw_bounds_proof v r.shares priced waive hspos.le hsc
    (hz.withdrawNavExact waive) hpr).1
  have hρ := Vault.earlyExitFeeRateAt_le v t
  have hρ' : (0 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat / 100000 := by positivity
  have hρ1 : ((v.earlyExitFeeRateAt t).toNat : ℚ) / 100000 ≤ 1 := by
    rw [div_le_one (by norm_num)]; exact_mod_cast hρ
  rw [hz.withdrawNav_eq, hz'.withdrawNav_eq, hAA', hST', hcast]
  have hSpos : 0 < v.sharesTotal.toRat := by rw [← hcast]; linarith
  refine debit_le_worth _ _ _ _ hSpos ?_
  rw [← hI]
  nlinarith

/-- A clawback from an Open-zone vault, whose destroyed shares are worth a whole number of base units, keeps the
per-share value. -/
lemma Vault.OpenZone.clawback_keeps_perShare {v : Vault} (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat)
    (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r))
    (hworth : ∃ k : ℤ, v.idealAssetsWithdraw waive r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨rec, hcp, hsnz, -⟩ := Vault.clawback_recovery_cases v assets holderShares waive hnn r hok
  obtain ⟨hsic, hs64, hs0, -⟩ := hcp.form hc hnn hhs hmax
  have hsc : r.shares.Canonical := hsic.canonical (by rw [hs64]; decide)
  obtain ⟨priced, hpr, -, -, hple, -, hrle, -⟩ :=
    Vault.clawback_recovery_le v assets holderShares waive hnn hmax r hok (Or.inl hsc) hs0
  have hle := hz.priced_le_worth hmax r.shares priced waive hs0 hsc hpr hple hworth
  obtain ⟨hAA', hz'⟩ := Vault.clawback_openZone v assets holderShares waive hnn hc hhs hmax hz r hok
  have hST' := Vault.clawback_exact_sharesTotal v assets holderShares waive hnn hc hhs hmax r hok
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hS'0 : (0 : ℚ) ≤ (r.vault'.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  rw [hST', hcast] at hS'0
  have hI := hz.idealAssetsWithdraw_eq waive r.shares.toRat
  rw [hz.withdrawNav_eq, hz'.withdrawNav_eq, hAA', hST', hcast]
  have hspos : 0 < r.shares.toRat := by
    rcases lt_or_eq_of_le hs0 with h | h
    · exact h
    · exact absurd h.symm (STAmount.toRat_ne_zero _ (by simpa [STAmount.isZero] using hsnz))
  have hSpos : 0 < v.sharesTotal.toRat := by linarith
  refine debit_le_worth _ _ _ _ hSpos ?_
  rw [← hI]
  exact le_trans hrle hle

/-- A deposit into an Open-zone vault, whose issued shares are worth a whole number of base units, keeps the per-share
value. -/
lemma Vault.OpenZone.deposit_keeps_perShare {v : Vault} (hz : v.OpenZone) (amountDeposit : STAmount)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1)
    (hworth : ∃ k : ℤ, v.idealChargeDeposit r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨hAA', hz'⟩ := Vault.deposit_openZone v amountDeposit false t hpos hcanon hty hz r hok
  have hST' := Vault.deposit_exact_sharesTotal v amountDeposit false t hpos hcanon hty r hok hSsz
  have hI : v.idealChargeDepositAt v.assetsAvailable.toRat r.shares.toRat = v.idealChargeDeposit r.shares.toRat := by
    rw [← hz.depositNav_eq, RawVault.idealChargeDepositAt_depositNav]
  have h2 := (Vault.deposit_charge_at_proof v amountDeposit t hcanon hpos v.assetsAvailable hz.assetsTotal_eq r
    hok).2.2.2.2
  have hopen := hz.deposit_open amountDeposit false t hpos hcanon hty r hok
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hb : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have h9 : (9 : ℚ) * 10 ^ (15 + v.baseExponent) = 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  obtain ⟨hw, -⟩ := Vault.deposit_charge_worth v amountDeposit t hcanon hpos v.assetsAvailable hz.assetsTotal_eq r hok
    (by rw [hI] at h2 ⊢; nlinarith)
  have hge : v.idealChargeDepositAt v.assetsAvailable.toRat r.shares.toRat ≤ r.assets.toRat := by
    by_cases hint : v.numericType.isIntegral = true
    · exact (hw (by rw [hI]; exact hworth)).2 hint
    -- an IOU charge moves the cash on the base grid, less than one step below a whole worth
    obtain ⟨k, hk⟩ := hworth
    obtain ⟨-, g, hg⟩ := Vault.assetsAvailable_onGrid v
    obtain ⟨-, g', hg'⟩ := Vault.assetsAvailable_onGrid r.vault'
    rw [Vault.deposit_baseExponent v amountDeposit false t hpos r hok] at hg'
    obtain ⟨-, hlo, -, -⟩ := Vault.deposit_charge_total_proof v amountDeposit t hcanon hpos v.assetsAvailable
      hz.assetsTotal_eq r hok
    rw [hI, hk] at hlo ⊢
    have hc : r.assets.toRat = ((g' - g : ℤ) : ℚ) * 10 ^ v.baseExponent := by
      push_cast
      rw [sub_mul, ← hg, ← hg', hAA']
      ring
    rw [hc] at hlo ⊢
    have hlt : ((k - 1 : ℤ) : ℚ) * 10 ^ v.baseExponent < ((g' - g : ℤ) : ℚ) * 10 ^ v.baseExponent := by
      push_cast
      push_cast at hlo
      linarith
    have hlt' : k - 1 < g' - g := by exact_mod_cast lt_of_mul_lt_mul_right hlt hb.le
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k ≤ g' - g)) hb.le
  have := Vault.deposit_charge_mul_of_ge v amountDeposit t hpos hcanon v.assetsAvailable hz.assetsTotal_eq r hok hge
  rw [hz.withdrawNav_eq, hz'.withdrawNav_eq, hAA', hST']
  nlinarith

/-- Proof of the deposit line of `Vault.no_dilution`. -/
lemma Vault.Reachable.deposit_no_dilution_intended_proof (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hr : Vault.Reachable v t0) (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1)
    (hworth : ∃ k : ℤ, v.idealChargeDeposit r.shares.toRat = k * 10 ^ v.baseExponent) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥ v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) :=
  have hz := Vault.Reachable.openZone_proof v t0 hr (Vault.maxValue_fits_of_canonical v amountDeposit hcanon hty)
  hz.deposit_keeps_perShare amountDeposit t hpos hcanon hty r hok hSsz hworth

/-- A cross-multiplied bound is a per-share one, on positive share totals. -/
private lemma perShare_of_cross (N N' S S' : ℚ) (hS : 0 < S) (hS' : 0 < S') (h : N' * S ≥ N * S') :
    N' / S' ≥ N / S := by
  rw [ge_iff_le, div_le_div_iff₀ hS hS']
  linarith

/-- Proof of `Vault.ReachableFromIn.no_dilution`. Every vault along the history stays in the Open zone, where every
step keeps the per-share value. -/
lemma Vault.ReachableFromIn.no_dilution_intended_proof (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (t : UInt32) (n : ℕ) (w : Vault) (h : Vault.ReachableFromIn true v t w n) :
    w.withdrawNav / (w.toExact.sharesTotal : ℚ) ≥ v.withdrawNav / (v.toExact.sharesTotal : ℚ) := by
  rcases Vault.Reachable.maxValue_fits_or_no_shares v t0 hr with hmax | hS
  swap
  · exact Vault.ReachableFromIn.no_dilution_of_no_shares v hS w
  have hz0 := Vault.Reachable.openZone_proof v t0 hr hmax
  suffices H : w.OpenZone ∧ w.numericType = v.numericType ∧
      w.withdrawNav / (w.toExact.sharesTotal : ℚ) ≥ v.withdrawNav / (v.toExact.sharesTotal : ℚ) from H.2.2
  induction h with
  | refl => exact ⟨hz0, rfl, le_refl _⟩
  | deposit u _ t' n amount isDonation r _ _ hc hty hpos hok hSsz hwhole ih =>
    obtain ⟨hz, hnt, hP⟩ := ih
    obtain ⟨_, _, hv⟩ := Vault.deposit_frame u _ _ _ _ r hok
    have hnt' : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hz' := (Vault.deposit_openZone u amount isDonation t' hpos hc hty hz r hok).2
    refine ⟨hz', hnt'.trans hnt, ?_⟩
    have hP0' := Vault.perShareValue_nonneg r.vault'
    -- from a vault without shares the per-share value starts at zero
    have hS0 : (0 : ℚ) ≤ (u.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
    rcases lt_or_eq_of_le hS0 with hSpos | hSz
    swap
    · rw [← hSz, div_zero] at hP
      linarith
    suffices hstep : r.vault'.withdrawNav / (r.vault'.toExact.sharesTotal : ℚ) ≥
        u.withdrawNav / (u.toExact.sharesTotal : ℚ) by
      linarith
    cases isDonation with
    | false =>
      have hST' := Vault.deposit_exact_sharesTotal u amount false t' hpos hc hty r hok hSsz
      have hs0 : 0 ≤ r.shares.toRat := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hshpos, -⟩ :=
          DepAcc.Vault.deposit_success_reduces u amount t' hpos hc r hok
        exact hshpos.le
      have hS'pos : 0 < (r.vault'.toExact.sharesTotal : ℚ) := by rw [hST']; linarith
      exact perShare_of_cross _ _ _ _ hSpos hS'pos
        (hz.deposit_keeps_perShare amount t' hpos hc hty r hok hSsz (hwhole rfl))
    | true =>
      obtain ⟨hlt, hSe⟩ := hz.deposit_donation_no_dilution amount t' hpos hc hty r hok
      rw [hSe]
      exact div_le_div_of_nonneg_right hlt.le hS0
  | withdraw u _ t' n amount holderShares waive r _ _ hc hty _ _ hpos hok _ hlt hwhole ih =>
    obtain ⟨hz, hnt, hP⟩ := ih
    have hmax' : u.numericType.isIntegral = true → u.numericType.maxValue.toNat ≤ maxRep.toNat := hnt ▸ hmax
    obtain ⟨_, _, hv⟩ := Vault.withdraw_frame u _ _ _ _ r hok
    have hnt' : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hz' := (Vault.withdraw_openZone u amount waive t' hpos hz hmax' r hok).2
    refine ⟨hz', hnt'.trans hnt, ?_⟩
    obtain ⟨-, -, hspos⟩ := Vault.withdraw_shares_form u amount waive t' hpos hc hty r hok
    have hST' := Vault.withdraw_exact_sharesTotal u amount waive t' hpos hc hty r hok
    have hSpos : 0 < (u.toExact.sharesTotal : ℚ) := by linarith
    have hS'pos : 0 < (r.vault'.toExact.sharesTotal : ℚ) := by rw [hST']; linarith
    have hd := hz.withdraw_keeps_perShare hmax' amount waive t' hpos hc hty r hok hlt (hwhole rfl)
    have := perShare_of_cross u.withdrawNav r.vault'.withdrawNav (u.toExact.sharesTotal : ℚ)
      (r.vault'.toExact.sharesTotal : ℚ) hSpos hS'pos hd
    linarith
  | clawback u _ t' n assets holderShares waive r _ _ hc _ hhs _ hnn hok _ hlt hwhole ih =>
    obtain ⟨hz, hnt, hP⟩ := ih
    have hmax' : u.numericType.isIntegral = true → u.numericType.maxValue.toNat ≤ maxRep.toNat := hnt ▸ hmax
    obtain ⟨_, _, hv⟩ := Vault.clawback_frame u _ _ _ _ r hok
    have hnt' : r.vault'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hz' := (Vault.clawback_openZone u assets holderShares waive hnn hc hhs hmax' hz r hok).2
    refine ⟨hz', hnt'.trans hnt, ?_⟩
    have hST' := Vault.clawback_exact_sharesTotal u assets holderShares waive hnn hc hhs hmax' r hok
    have hSpos : 0 < (u.toExact.sharesTotal : ℚ) := by
      have := Nat.cast_nonneg (α := ℚ) u.toExact.sharesTotal
      rcases lt_or_eq_of_le this with h | h
      · exact h
      · exfalso
        have : r.shares.toRat < 0 := by rw [h]; exact hlt
        obtain ⟨rec, hcp, -, -⟩ := Vault.clawback_recovery_cases u assets holderShares waive hnn r hok
        linarith [(hcp.form hc hnn hhs hmax').2.2.1]
    have hS'pos : 0 < (r.vault'.toExact.sharesTotal : ℚ) := by rw [hST']; linarith
    have hd := hz.clawback_keeps_perShare hmax' assets holderShares waive hnn hc hhs r hok (hwhole rfl)
    have := perShare_of_cross u.withdrawNav r.vault'.withdrawNav (u.toExact.sharesTotal : ℚ)
      (r.vault'.toExact.sharesTotal : ℚ) hSpos hS'pos hd
    linarith
  | burnShares u _ t' n amount holderShares sharesTotalAmount u' _ _ _ hcan hok ih =>
    obtain ⟨hz, hnt, hP⟩ := ih
    obtain ⟨st', hv⟩ := Vault.burnShares_frame u _ u' hok
    have hnt' : u'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    refine ⟨Vault.burnShares_openZone u _ u' hz hok, hnt'.trans hnt, ?_⟩
    -- a burn runs only on a vault with no cash and nothing deployed
    obtain ⟨hins, -, -⟩ := Vault.canBurnShares_ok_reduces u amount holderShares sharesTotalAmount hcan
    have hAm : u.assetsAvailable.mantissa_ = 0 := by
      unfold Vault.isInsolvent at hins
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hins
      exact hins.1.1
    rw [hz.withdrawNav_eq, Number.toRat_eq_zero_of_mantissa_zero _ hAm, zero_div] at hP
    have := Vault.perShareValue_nonneg u'
    linarith
  | update u _ t' n assetsMaximum blockDeposit u' _ _ _ hok ih =>
    obtain ⟨hz, hnt, hP⟩ := ih
    obtain ⟨_, _, hv⟩ := Vault.update_frame u _ _ u' hok
    have hnt' : u'.numericType = u.numericType := (congrArg RawVault.numericType hv).trans rfl
    have hz' := Vault.update_openZone u _ _ u' hz hok
    refine ⟨hz', hnt'.trans hnt, ?_⟩
    -- an update keeps the cash and the share total
    have hP' : u'.withdrawNav / (u'.toExact.sharesTotal : ℚ) = u.withdrawNav / (u.toExact.sharesTotal : ℚ) := by
      rw [hz'.withdrawNav_eq, hz.withdrawNav_eq, RawVault.WF.toExact_sharesTotal u'.toRawVault u'.wf,
        RawVault.WF.toExact_sharesTotal u.toRawVault u.wf]
      have hAA : u'.assetsAvailable = u.assetsAvailable := (congrArg RawVault.assetsAvailable hv).trans rfl
      have hST : u'.sharesTotal = u.sharesTotal := (congrArg RawVault.sharesTotal hv).trans rfl
      rw [hAA, hST]
    rw [hP']
    exact hP

end XRPL.Model.SingleAssetVault
