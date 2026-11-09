import XRPL.Properties.Vault.Proofs.ClawbackUpdates
import XRPL.Properties.Vault.Proofs.DepositCharge
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Vault.Proofs.Burn
import XRPL.Properties.Vault.Proofs.MaxValueFits

/-! # Per-share value under each operation

On an Open-zone vault the net asset value is the cash, and every operation updates the cash and the
share total exactly. A deposit then takes the issued shares' worth less at most one base step, and a
withdrawal or a clawback pays at most the burned shares' worth, plus `sharesε` of it and half a unit of
its last digit. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepTight

/-- A non-final withdrawal pays nothing, or at most the priced amount plus half a step of its own
grid less half a step of the priced amount's grid. -/
lemma Vault.withdraw_payout_le_priced (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waive = .ok priced ∧
      (r.assets.toRat = 0 ∨
        r.assets.toRat + 1 / 2 * (10 : ℚ) ^ priced.exponent ≤
          priced.toRat + 1 / 2 * (10 : ℚ) ^ r.assets.exponent) := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  obtain ⟨priced, hpr, hcase⟩ := Vault.withdraw_payout_cases v amount waive t hpos hc hty r hok hlt
  refine ⟨priced, hpr, ?_⟩
  rcases hcase with ⟨h0, -⟩ | ⟨aN, fee, pN, -, payout, hlow, haN, hfee, hsub, hpo, hpz, hcl, hfnp, -, -⟩
  · exact Or.inl h0
  right
  obtain ⟨hpc, hp0, hsmall⟩ :=
    Vault.withdraw_priced_facts v _ _ waive hmax (hsic.canonical (by rw [hs64]; decide)) hspos hpr
  have hpt := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).2
  obtain ⟨hav, han⟩ := hpc.toNumber_exact aN haN
  have hrate : (v.earlyExitFeeRateAt t).toNat < 100000 :=
    lt_of_le_of_ne (v.earlyExitFeeRateAt_le t) (fun h => hlow (UInt32.toNat_inj.mp h))
  obtain ⟨hpN0, hpNle, -⟩ := payoutNumber_bounds aN fee pN _ han (hav ▸ hp0) (hav ▸ hsmall) hrate hfee hsub
  rw [hav] at hpNle
  have hpm : payout.mValue ≠ 0 := by simpa [STAmount.isZero] using hpz
  have hfn := (tenthBipsOfValue_upward_facts aN _ fee han (hav ▸ hp0) hfee).1
  have hpNm := STAmount.ofNumber_source_ne_zero _ _ _ _ hpo hpm
  have hpNn := operator_sub_isNormalized _ _ _ _ han hfn hsub hpNm
  have hpNneg := Number.negative_false_of_nonneg _ hpNn hpN0
  obtain ⟨hpayle, -, hpay0⟩ := STAmount.ofNumber_downward_floor_bounds _ _ _ hpNn hpNneg hpo hpm
  have hpayt : payout.mNumericType = v.numericType := STAmount.ofNumber_mNumericType _ _ _ _ hpo
  have hρ0 : (0 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat := Nat.cast_nonneg _
  have hpaypos : 0 < payout.toRat := lt_of_le_of_ne hpay0 (Ne.symm (STAmount.toRat_ne_zero _ hpm))
  have hppos : 0 < priced.toRat := by
    have : priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) ≤ priced.toRat := by nlinarith
    linarith
  have hpPm : priced.mValue ≠ 0 := fun h0 => by
    rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hppos; exact lt_irrefl _ hppos
  have hPc : priced.Canonical := hpc.resolve_right (by simpa [STAmount.isZero] using hpPm)
  -- the clamp keeps the payout's type and never raises it
  have hpcz := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hpo).1
  have hrc := clampToSumExponent_canonicalOrZero _ _ _ _ hpcz.operator_neg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  have hrle := clampToSumExponent_le_abs _ _ _ _ hpcz.operator_neg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hpay0] at hrle
  have hrp : (0 : ℚ) < 10 ^ r.assets.exponent := zpow_pos (by norm_num) _
  have hpp : (0 : ℚ) < 10 ^ priced.exponent := zpow_pos (by norm_num) _
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral payout is a whole amount, kept by the clamp
    have hni : payout.operator_neg.integral = true := by
      unfold STAmount.integral
      rw [(STAmount.operator_neg_fields payout).1, hpayt]
      exact hint
    rw [clampToSumExponent_integral _ _ _ hni, Except.ok.injEq] at hcl
    obtain ⟨-, hoff, -, hrat⟩ := clamp_magnitude payout.operator_neg
    rw [hcl, STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hpay0] at hrat
    have hrexp : r.assets.exponent = payout.exponent := by
      show r.assets.mOffset = payout.mOffset
      rw [← hcl, hoff, (STAmount.operator_neg_fields payout).2.1]
    have hpe0 : priced.exponent = 0 := Vault.sharesToAssetsWithdraw_integral_exponent v _ _ waive hint hpr hpPm
    have hye0 : payout.exponent = 0 := (STAmount.ofNumber_integral_canonical _ _ _ _ hint hpo).1.offset_zero
    rw [hrexp, hye0, hpe0, hrat]
    -- a whole payout below a whole priced amount is at least one unit below it
    by_cases hlt' : payout.toRat < priced.toRat
    · have hPd : priced.toRat.den = 1 := (hPc.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1.den_eq_one
      have hYd : payout.toRat.den = 1 :=
        (STAmount.ofNumber_integral_canonical _ _ _ _ hint hpo).1.den_eq_one
      have := rat_one_le_sub_of_lt _ _ hPd hYd hlt'
      linarith
    · have : payout.toRat ≤ priced.toRat := by nlinarith
      linarith
  have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hPiou : priced.IOUCanonical := hPc.2 (by unfold STAmount.integral; rw [hpt, hvfr]; rfl)
  by_cases hρ : (v.earlyExitFeeRateAt t).toNat = 0
  · -- no fee: the payout is the priced amount, floored onto the grid of the cash it leaves
    obtain ⟨hflo, hfhi⟩ := tenthBipsOfValue_upward_bounds aN _ fee han (hav ▸ hp0) (hav ▸ hsmall) hfee
    rw [hρ, Nat.cast_zero] at hflo hfhi
    have hf0 : fee.toRat = 0 := le_antisymm (by linarith) (by linarith)
    have hfm : fee.mantissa_ = 0 := by
      by_contra h
      exact Number.toRat_ne_zero_of_mantissa_ne_zero _ h hf0
    rw [Number.operator_sub_zero_right aN fee .downward hfn hfm, Except.ok.injEq] at hsub
    subst hsub
    have hY : payout = priced := STAmount.ofNumber_downward_self _ priced
      (STAmount.Canonical.exactCanonical _ hPc) hpt hppos aN han hav payout hpo hpm
    subst hY
    have hrm : r.assets.mValue ≠ 0 := by
      intro h0
      have hrt : r.assets.mNumericType = .fractional := by rw [hrc.2.1, (STAmount.operator_neg_fields _).1, hpt, hvfr]
      rw [STAmount.isFractionalNonPositive_zero _ hrt h0] at hfnp
      exact absurd (Except.ok.inj hfnp) (by decide)
    have hrpos : 0 < r.assets.toRat := lt_of_le_of_ne hrc.2.2 (Ne.symm (STAmount.toRat_ne_zero _ hrm))
    have hRiou : r.assets.IOUCanonical :=
      (hrc.1.resolve_right (by simpa [STAmount.isZero] using hrm)).2
        (by unfold STAmount.integral; rw [hrc.2.1, (STAmount.operator_neg_fields _).1, hpt, hvfr]; rfl)
    obtain ⟨-, e, -, -, -, hfl⟩ := Vault.clamp_floor v payout r.assets hpc (by rw [hpt, hvfr]) hp0 hrm hcl
    exact (STAmount.IOUCanonical.floor_bounds payout r.assets e hPiou hRiou hrpos hfl).1
  -- a fee takes at least `10⁻⁵` of the priced amount, more than one step of its grid
  have hρ1 : (1 : ℚ) ≤ (v.earlyExitFeeRateAt t).toNat := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hρ
  obtain ⟨hP15, -⟩ := STAmount.IOUCanonical.toRat_bounds priced hPiou hppos
  have h15 : (10 : ℚ) ^ (priced.exponent + 15) = 10 ^ priced.exponent * 10 ^ 15 := by
    rw [zpow_add₀ (by norm_num)]; norm_num
  rw [h15] at hP15
  have hfee' : priced.toRat * (1 - (v.earlyExitFeeRateAt t).toNat / 100000) ≤ priced.toRat - priced.toRat / 100000 := by
    nlinarith
  nlinarith

/-- A deposit's charge times the share total, from a charge short of the issued shares' worth by
less than one step: at least that worth less one step per existing share. -/
private lemma Vault.deposit_charge_mul_sharp (v : Vault) (amountDeposit : STAmount) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical) (navN : Number)
    (hat : v.assetsTotal = .ok navN) (r : VaultWithAmounts)
    (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r)) (g : ℤ)
    (hg : v.idealChargeDepositAt navN.toRat r.shares.toRat - (10 : ℚ) ^ g < r.assets.toRat) :
    navN.toRat * r.shares.toRat - (10 : ℚ) ^ g * (v.toExact.sharesTotal : ℚ) ≤
      r.assets.toRat * (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨-, priced, navN', -, -, -, -, -, hshc, hshnt, hshpos, hsad, -, hat', hcl, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  have hc0 := DepAcc.Vault.deposit_charge_nonneg v r.shares priced r.assets navN hshc hshnt hshpos hsad hcl
  have hS0 : (0 : ℚ) ≤ (v.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  have hgp : (0 : ℚ) < 10 ^ g := zpow_pos (by norm_num) _
  by_cases hmz : navN.mantissa_ = 0
  · -- nothing is priced at a zero total
    rw [Number.toRat_eq_zero_of_mantissa_zero navN hmz, zero_mul, zero_sub]
    nlinarith [mul_nonneg hc0 hS0]
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
  rw [hI] at hg
  have := mul_le_mul_of_nonneg_right hg.le hSpos.le
  have heq : (navN.toRat * r.shares.toRat / (v.toExact.sharesTotal : ℚ) - 10 ^ g) *
      (v.toExact.sharesTotal : ℚ) =
        navN.toRat * r.shares.toRat - 10 ^ g * (v.toExact.sharesTotal : ℚ) := by
    field_simp
  linarith

/-- A deposit into an Open-zone vault lowers per-share value by less than one base step spread over the share total
after it. The charge falls short of the issued shares' worth by less than one base step. -/
lemma Vault.OpenZone.deposit_no_dilution {v : Vault} (hz : v.OpenZone) (amountDeposit : STAmount)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hpos).run = .ok (.ok r))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) -
        (10 : ℚ) ^ v.baseExponent * (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨hAA', hz'⟩ := Vault.deposit_openZone v amountDeposit false t hpos hcanon hty hz r hok
  have hST' := Vault.deposit_exact_sharesTotal v amountDeposit false t hpos hcanon hty r hok hSsz
  obtain ⟨-, -, -, -, h5⟩ :=
    Vault.deposit_charge_at_proof v amountDeposit t hcanon hpos v.assetsAvailable hz.assetsTotal_eq r hok
  have hmul := Vault.deposit_charge_mul_sharp v amountDeposit t hpos hcanon v.assetsAvailable hz.assetsTotal_eq
    r hok _ h5
  rw [hz.withdrawNav_eq, hz'.withdrawNav_eq, hAA', hST']
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hS0 : (0 : ℚ) ≤ (v.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  have hs0 : 0 ≤ r.shares.toRat := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hshpos, -⟩ :=
      DepAcc.Vault.deposit_success_reduces v amountDeposit t hpos hcanon r hok
    exact hshpos.le
  have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  have hAS : 0 ≤ v.assetsAvailable.toRat * (v.toExact.sharesTotal : ℚ) := mul_nonneg hA0 hS0
  nlinarith [mul_nonneg hAS hε]

/-- A donation into an Open-zone vault strictly raises per-share value: the cash grows by a
positive amount and the share total does not move. -/
lemma Vault.OpenZone.deposit_donation_no_dilution {v : Vault} (hz : v.OpenZone) (amountDeposit : STAmount)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat) (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit true t hpos).run = .ok (.ok r)) :
    v.withdrawNav < r.vault'.withdrawNav ∧ r.vault'.toExact.sharesTotal = v.toExact.sharesTotal := by
  obtain ⟨ra, amounts, raw, hra, -, -, -, -, -, -⟩ := Vault.deposit_ok_reduces v amountDeposit true t hpos r hok
  obtain ⟨hras, hrsh⟩ := Vault.deposit_donation_proof v amountDeposit ra t hpos hcanon hra r hok
  obtain ⟨-, hrapos⟩ := DepRnd.Vault.roundedDepositAmount_canonical_pos v amountDeposit ra hcanon hra
  obtain ⟨hAA', hz'⟩ := Vault.deposit_openZone v amountDeposit true t hpos hcanon hty hz r hok
  have hs0 : r.shares.toRat = 0 := by
    rw [hrsh]; exact STAmount.zero_toRat _
  have hST' := Vault.deposit_exact_sharesTotal v amountDeposit true t hpos hcanon hty r hok (by
    rw [hs0, add_zero, RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]; exact v.sharesTotal_le_maxRep)
  rw [hs0, add_zero] at hST'
  refine ⟨?_, by exact_mod_cast hST'⟩
  rw [hz.withdrawNav_eq, hz'.withdrawNav_eq, hAA', hras]
  linarith

/-- An Open-zone vault prices a share at its cash over the share total, waived loss or not. -/
lemma Vault.OpenZone.idealAssetsWithdraw_eq {v : Vault} (hz : v.OpenZone) (w : Bool) (x : ℚ) :
    v.idealAssetsWithdraw w x = v.assetsAvailable.toRat * x / v.sharesTotal.toRat := by
  have hAD0 : v.assetsDeployed.toRat = 0 := by rw [hz.assetsDeployed, Number.toRat_zero]
  have hLU0 : v.lossUnrealized.toRat = 0 := by rw [hz.lossUnrealized, Number.toRat_zero]
  unfold RawVault.idealAssetsWithdraw
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  cases w
  · show (v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat) * x / _ = _
    rw [hAD0, hLU0]; ring
  · show (v.assetsAvailable.toRat + v.assetsDeployed.toRat) * x / _ = _
    rw [hAD0]; ring

/-- Proof of the donation line of `Vault.no_dilution`. -/
lemma Vault.deposit_donation_no_dilution_proof (v : Vault) (amountDeposit : STAmount) (t t0 : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hr : Vault.Reachable v t0) (hcanon : amountDeposit.Canonical)
    (hty : amountDeposit.mNumericType = v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit true t hpos).run = .ok (.ok r)) :
    v.withdrawNav < r.vault'.withdrawNav ∧ r.vault'.toExact.sharesTotal = v.toExact.sharesTotal :=
  (Vault.Reachable.openZone_proof v t0 hr hmax).deposit_donation_no_dilution amountDeposit t hpos hcanon hty r hok

/-- The net asset value moves with the cash: deposits, withdrawals and clawbacks write only the
cash and the share total. -/
private lemma Vault.withdrawNav_of_cash (v v' : Vault) (aa' st' : Number)
    (hv : v'.toRawVault = { v.toRawVault with assetsAvailable := aa', sharesTotal := st' }) :
    v'.withdrawNav = v.withdrawNav + (v'.assetsAvailable.toRat - v.assetsAvailable.toRat) := by
  have hAD : v'.assetsDeployed = v.assetsDeployed := (congrArg RawVault.assetsDeployed hv).trans rfl
  have hLU : v'.lossUnrealized = v.lossUnrealized := (congrArg RawVault.lossUnrealized hv).trans rfl
  show v'.assetsAvailable.toRat + v'.assetsDeployed.toRat - v'.lossUnrealized.toRat =
    v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat + _
  rw [hAD, hLU]
  ring

/-- The net asset value is at most the total. -/
private lemma Vault.withdrawNav_le_total (v : Vault) : v.withdrawNav ≤ v.toExact.assetsTotal := by
  show v.toExact.assetsTotal - v.lossUnrealized.toRat ≤ _
  have := v.exact.lossUnrealized_nonneg
  change 0 ≤ v.lossUnrealized.toRat at this
  linarith

end XRPL.Model.SingleAssetVault
