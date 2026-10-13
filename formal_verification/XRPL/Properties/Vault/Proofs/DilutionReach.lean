import XRPL.Properties.Vault.Proofs.Roundtrip
import XRPL.Properties.Vault.Proofs.Dilution.Clawback
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Dilution along a history: relative factors compound, absolute budgets add

Per-share value `withdrawNav / sharesTotal` (`0` on an empty vault) drops at each step
by at most the step's relative factor and its absolute budget divided by the share total
after the step. An empty vault has per-share value `0`, so a deposit into it dilutes no
one; a burn runs only on an asset-less vault, whose per-share value is `0` as well. -/

namespace XRPL.Model.SingleAssetVault.DilG

open XRPL.Model.Protocol

lemma ps_nonneg (x : Vault) : 0 ≤ x.withdrawNav / (x.toExact.sharesTotal : ℚ) :=
  div_nonneg (by unfold RawVault.withdrawNav; exact x.exact.withdraw_nav_nonneg) (Nat.cast_nonneg _)

lemma ps_of_cross (N N' S S' ρ b : ℚ) (hS : 0 < S) (hS' : 0 < S')
    (h : N' * S ≥ N * S' * (1 - ρ) - b * S) :
    N' / S' ≥ N / S * (1 - ρ) - b / S' := by
  rw [ge_iff_le, ← sub_nonneg]
  have heq : N' / S' - (N / S * (1 - ρ) - b / S') =
      (N' * S - (N * S' * (1 - ρ) - b * S)) / (S * S') := by
    field_simp
  rw [heq]
  exact div_nonneg (by linarith) (mul_pos hS hS').le

lemma ps_zero (x : Vault) (h : (x.toExact.sharesTotal : ℚ) = 0) :
    x.withdrawNav / (x.toExact.sharesTotal : ℚ) = 0 := by
  rw [h, div_zero]

/-- A step from an empty vault, or one whose per-share value is already `0`, meets any
nonnegative budget. -/
lemma step_trivial (x x' : Vault) (c b : ℚ) (hb : 0 ≤ b)
    (h0 : x.withdrawNav / (x.toExact.sharesTotal : ℚ) = 0) :
    x'.withdrawNav / (x'.toExact.sharesTotal : ℚ) ≥
      x.withdrawNav / (x.toExact.sharesTotal : ℚ) * c - b := by
  rw [h0, zero_mul]
  have := ps_nonneg x'
  linarith

lemma navx (x : Vault) (h : x.toExact.lossUnrealized = 0) :
    x.withdrawNav = x.toExact.assetsTotal := by
  show x.toExact.assetsTotal - x.toExact.lossUnrealized = _; rw [h, sub_zero]

lemma eps_le : (3 : ℚ) / 10 ^ 18 ≤ depositε := by rw [DepAcc.depositε_eq]; norm_num

lemma deposit_step (u : Vault) (amount : STAmount) (isDonation : Bool) (r : DepositResult)
    (e : ℤ) (hL : u.toExact.lossUnrealized = 0) (hpos : 0 < amount.toRat)
    (hok : u.deposit amount isDonation hpos = .ok r) (herr : r.error = none)
    (hcanon : amount.Canonical)
    (hSsz : (u.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (he : postSumExponent u.assetsTotal amount = .ok e) :
    r.vault'.toExact.lossUnrealized = 0 ∧
    r.vault'.withdrawNav / (r.vault'.toExact.sharesTotal : ℚ) ≥
      u.withdrawNav / (u.toExact.sharesTotal : ℚ) * (1 - depositε) -
        3 / 2 * (10 : ℚ) ^ e / (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨am, aD, sC, cN, sN, at', av', st', hround, -, -, -, hdon, -, -, -, -, -, -, -,
    hamt, hshr, hrv⟩ := DepAcc.Vault.deposit_success_reduces u amount isDonation r hpos hok herr
  have hL' : r.vault'.toExact.lossUnrealized = 0 := by
    have : r.vault'.toRawVault.lossUnrealized = u.toRawVault.lossUnrealized := by rw [hrv]
    show r.vault'.toRawVault.lossUnrealized.toRat = 0
    rw [this]; exact hL
  refine ⟨hL', ?_⟩
  have hb : (0 : ℚ) ≤ 3 / 2 * (10 : ℚ) ^ e / (r.vault'.toExact.sharesTotal : ℚ) := by positivity
  have hS0 : (0 : ℚ) ≤ (u.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  rcases lt_or_eq_of_le hS0 with hSpos | hSz
  swap
  · exact step_trivial u r.vault' _ _ hb (ps_zero u hSz.symm)
  have hP0 := ps_nonneg u
  have hε := eps_le
  obtain ⟨-, -, hS'⟩ := Vault.deposit_vault_updates_proof u amount isDonation hcanon hpos r hok herr
  have hS'' := hS' hSsz
  cases isDonation with
  | false =>
    obtain ⟨-, -, -, -, -, -, hspos, -⟩ := deposit_totals u amount r hcanon hpos hok herr
    have hS'pos : 0 < (r.vault'.toExact.sharesTotal : ℚ) := by rw [hS'']; linarith
    have h49 := Vault.deposit_no_dilution_proof u amount r hcanon hpos hL hSsz hok herr e he
    have := ps_of_cross _ _ _ _ _ _ hSpos hS'pos h49
    have : u.withdrawNav / (u.toExact.sharesTotal : ℚ) * (1 - depositε) ≤
        u.withdrawNav / (u.toExact.sharesTotal : ℚ) * (1 - 3 / 10 ^ 18) :=
      mul_le_mul_of_nonneg_left (by linarith) hP0
    linarith
  | true =>
    obtain ⟨haD, hsC⟩ := hdon rfl
    have hsz : r.sharesIssued.toRat = 0 := by rw [hshr, hsC]; exact STAmount.zero_int64_toRat
    have hSe : (r.vault'.toExact.sharesTotal : ℚ) = (u.toExact.sharesTotal : ℚ) := by
      rw [hS'', hsz, add_zero]
    have hc0 : 0 ≤ r.amountDeposit'.toRat := by
      rw [hamt, haD]
      exact RawVault.roundToVaultExponent_nonneg amount am u.assetsTotal hcanon hpos.le hround
    obtain ⟨hA', -, -⟩ := Vault.deposit_vault_updates_proof u amount true hcanon hpos r hok herr
    have hA'' : |r.vault'.assetsTotal.toRat - (u.toExact.assetsTotal + r.amountDeposit'.toRat)| ≤
        |u.toExact.assetsTotal + r.amountDeposit'.toRat| * depositε := hA'
    have hA0 : 0 ≤ u.toExact.assetsTotal := u.exact.assetsTotal_nonneg
    have hsum0 : 0 ≤ u.toExact.assetsTotal + r.amountDeposit'.toRat := by linarith
    rw [abs_of_nonneg hsum0] at hA''
    have hlo := (abs_le.mp hA'').1
    have hεn : (0 : ℚ) ≤ depositε := le_trans (by norm_num) hε
    have hε1 : depositε ≤ 1 := by rw [DepAcc.depositε_eq]; norm_num
    have hA1 : u.toExact.assetsTotal * (1 - depositε) ≤ r.vault'.toExact.assetsTotal := by
      show _ ≤ r.vault'.assetsTotal.toRat
      nlinarith
    rw [navx _ hL', navx _ hL, hSe]
    have : u.toExact.assetsTotal / (u.toExact.sharesTotal : ℚ) * (1 - depositε) ≤
        r.vault'.toExact.assetsTotal / (u.toExact.sharesTotal : ℚ) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hA1 hS0
    have hb' : (0 : ℚ) ≤ 3 / 2 * (10 : ℚ) ^ e / (u.toExact.sharesTotal : ℚ) := by positivity
    linarith

lemma withdraw_step (u : Vault) (amount : WithdrawAmount) (r : WithdrawResult)
    (hL : u.toExact.lossUnrealized = 0) (hpos : 0 < amount.amount.toRat)
    (hok : u.withdraw amount false hpos = .ok r) (herr : r.error = none)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hmargin : r.sharesBurned.toRat ≤ (u.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (u.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    r.vault'.toExact.lossUnrealized = 0 ∧
    r.vault'.withdrawNav / (r.vault'.toExact.sharesTotal : ℚ) ≥
      u.withdrawNav / (u.toExact.sharesTotal : ℚ) * (1 - depositε) -
        1 / 2 * (10 : ℚ) ^ r.assets'.exponent / (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨cw, an, sta, -, -, -, -, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases u amount false r hpos hok herr
  have hS0 : (0 : ℚ) ≤ (u.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  have hSST : (u.toExact.sharesTotal : ℚ) = u.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal _ u.wf
  have hb : (0 : ℚ) ≤ 1 / 2 * (10 : ℚ) ^ r.assets'.exponent / (r.vault'.toExact.sharesTotal : ℚ) := by
    positivity
  rcases hcase with ⟨hfin, -, -, hrv⟩ | ⟨hfin, hrest⟩
  · -- the final branch cannot run with half the shares left, unless the vault is empty
    have hL' : r.vault'.toExact.lossUnrealized = 0 := by
      have : r.vault'.toRawVault.lossUnrealized = u.toRawVault.lossUnrealized := by rw [hrv]
      show r.vault'.toRawVault.lossUnrealized.toRat = 0
      rw [this]; exact hL
    refine ⟨hL', ?_⟩
    have hbe : r.sharesBurned = sta := by rw [hsb]; exact eq_of_operator_eq _ _ hfin
    obtain ⟨-, -, -, -, hstav⟩ := STAmount.ofNumber_int64_shape _ .to_nearest sta
      u.wf.sharesTotal_norm u.wf.sharesTotal_nonneg u.wf.sharesTotal_int
      (by rw [← hSST]; exact hSfit) hsta
    have hbS : r.sharesBurned.toRat = (u.toExact.sharesTotal : ℚ) := by rw [hbe, hstav, hSST]
    have hSz : (u.toExact.sharesTotal : ℚ) = 0 := by linarith
    exact step_trivial u r.vault' _ _ hb (ps_zero u hSz)
  · obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hrv⟩ := hrest
    have hL' : r.vault'.toExact.lossUnrealized = 0 := by
      have : r.vault'.toRawVault.lossUnrealized = u.toRawVault.lossUnrealized := by rw [hrv]
      show r.vault'.toRawVault.lossUnrealized.toRat = 0
      rw [this]; exact hL
    refine ⟨hL', ?_⟩
    rcases lt_or_eq_of_le hS0 with hSpos | hSz
    swap
    · exact step_trivial u r.vault' _ _ hb (ps_zero u hSz.symm)
    have hfin' : r.sharesBurned.operator_eq sta = false := by rw [hsb]; exact hfin
    obtain ⟨-, -, hS'⟩ := Vault.withdraw_vault_updates_proof u amount false sta r hnn hc hSnt hpos
      hok herr hsta hfin'
    have hS'' : (r.vault'.toExact.sharesTotal : ℚ) =
        (u.toExact.sharesTotal : ℚ) - r.sharesBurned.toRat := by
      rw [RawVault.WF.toExact_sharesTotal _ r.vault'.wf]; exact hS' hSfit
    have hS'pos : 0 < (r.vault'.toExact.sharesTotal : ℚ) := by rw [hS'']; linarith
    have h51 := Vault.withdraw_no_dilution_proof u amount r hL hnn hc hSnt hmargin hSfit hpos
      hok herr
    exact ps_of_cross _ _ _ _ _ _ hSpos hS'pos h51

lemma clawback_step (u : Vault) (assets holderShares : STAmount) (r : ClawbackResult)
    (hL : u.toExact.lossUnrealized = 0) (hnn : 0 ≤ assets.toRat)
    (hok : u.clawback assets holderShares hnn = .ok r) (herr : r.error = none)
    (hc : assets.Canonical)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hmargin : r.sharesDestroyed.toRat ≤ (u.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (u.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    r.vault'.toExact.lossUnrealized = 0 ∧
    r.vault'.withdrawNav / (r.vault'.toExact.sharesTotal : ℚ) ≥
      u.withdrawNav / (u.toExact.sharesTotal : ℚ) * (1 - depositε) -
        1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent / (r.vault'.toExact.sharesTotal : ℚ) := by
  obtain ⟨hS', hLr⟩ := clawback_shares_after u assets holderShares r hc hSic hSc hSnn hSfit hnn
    hok herr
  have hL' : r.vault'.toExact.lossUnrealized = 0 := by
    show r.vault'.toRawVault.lossUnrealized.toRat = 0
    rw [hLr]; exact hL
  refine ⟨hL', ?_⟩
  have hS0 : (0 : ℚ) ≤ (u.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  have hb : (0 : ℚ) ≤ 1 / 2 * (10 : ℚ) ^ r.assetsRecovered.exponent /
      (r.vault'.toExact.sharesTotal : ℚ) := by positivity
  rcases lt_or_eq_of_le hS0 with hSpos | hSz
  swap
  · exact step_trivial u r.vault' _ _ hb (ps_zero u hSz.symm)
  have hS'pos : 0 < (r.vault'.toExact.sharesTotal : ℚ) := by rw [hS']; linarith
  have h52 := Vault.clawback_no_dilution_proof u assets holderShares r hL hc hSic hSc hSnn
    hmargin hSfit hnn hok herr
  exact ps_of_cross _ _ _ _ _ _ hSpos hS'pos h52

lemma burn_step (u u' : Vault) (sharesDestroyed sharesTotalAmount : STAmount)
    (hL : u.toExact.lossUnrealized = 0)
    (hcan : u.canBurnShares = .ok (.assets sharesTotalAmount))
    (hok : u.burnShares sharesDestroyed = .ok u') :
    u'.toExact.lossUnrealized = 0 ∧
    u'.withdrawNav / (u'.toExact.sharesTotal : ℚ) ≥
      u.withdrawNav / (u.toExact.sharesTotal : ℚ) * (1 - depositε) - 0 := by
  have hm : u.assetsTotal.mantissa_ = 0 := by
    by_contra hm
    simp [Vault.canBurnShares, hm, pure, Except.pure] at hcan
  have hA : u.toExact.assetsTotal = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hm
  have hL' : u'.toExact.lossUnrealized = 0 := by
    unfold Vault.burnShares at hok
    obtain ⟨sn, -, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨st, -, hok⟩ := bind_ok_peel _ _ _ hok
    have h := (RawVault.to_lawful_ok hok).1
    show u'.toRawVault.lossUnrealized.toRat = 0
    rw [h]; exact hL
  refine ⟨hL', step_trivial u u' _ _ le_rfl ?_⟩
  rw [navx u hL, hA, zero_div]

lemma compose (Pv Pu Pu' c D b : ℚ) (n : ℕ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hD : 0 ≤ D)
    (hIH : Pu ≥ Pv * c ^ n - D) (hstep : Pu' ≥ Pu * c - b) :
    Pu' ≥ Pv * c ^ (n + 1) - (D + b) := by
  have h1 : Pu * c ≥ (Pv * c ^ n - D) * c := mul_le_mul_of_nonneg_right hIH hc0
  have h2 : D * c ≤ D := by nlinarith
  rw [pow_succ]
  nlinarith

end XRPL.Model.SingleAssetVault.DilG

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DilG

/-- **History dilution.** Along a history of `n` successful, margin-respecting operations
from a vault with no unrealized loss, per-share value is at least the starting one times
`(1 - depositε)^n`, less the accumulated budget `D`. -/
lemma Vault.ReachableFromIn.no_dilution_proof (v : Vault) (n : ℕ) (D : ℚ) (w : Vault)
    (hwL : v.toExact.lossUnrealized = 0)
    (h : Vault.ReachableFromIn v w n D) :
    w.withdrawNav / (w.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav / (v.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n - D := by
  have hc0 : (0 : ℚ) ≤ 1 - depositε := by rw [DepAcc.depositε_eq]; norm_num
  have hc1 : (1 : ℚ) - depositε ≤ 1 := by rw [DepAcc.depositε_eq]; norm_num
  suffices H : w.toExact.lossUnrealized = 0 ∧ 0 ≤ D ∧
      w.withdrawNav / (w.toExact.sharesTotal : ℚ) ≥
        v.withdrawNav / (v.toExact.sharesTotal : ℚ) * (1 - depositε) ^ n - D from H.2.2
  induction h with
  | refl => exact ⟨hwL, le_rfl, by rw [pow_zero, mul_one, sub_zero]⟩
  | deposit u n D amount isDonation r e _ hpos hok herr hcanon hSsz he ih =>
    obtain ⟨hL, hD, hP⟩ := ih
    obtain ⟨hL', hs⟩ := deposit_step u amount isDonation r e hL hpos hok herr hcanon hSsz he
    exact ⟨hL', by positivity, compose _ _ _ _ _ _ _ hc0 hc1 hD hP hs⟩
  | withdraw u n D amount r _ hpos hok herr hnn hc hSnt hmargin hSfit ih =>
    obtain ⟨hL, hD, hP⟩ := ih
    obtain ⟨hL', hs⟩ := withdraw_step u amount r hL hpos hok herr hnn hc hSnt hmargin hSfit
    exact ⟨hL', by positivity, compose _ _ _ _ _ _ _ hc0 hc1 hD hP hs⟩
  | clawback u n D assets holderShares r _ hnn hok herr hc hSic hSc hSnn hmargin hSfit ih =>
    obtain ⟨hL, hD, hP⟩ := ih
    obtain ⟨hL', hs⟩ := clawback_step u assets holderShares r hL hnn hok herr hc hSic hSc hSnn
      hmargin hSfit
    exact ⟨hL', by positivity, compose _ _ _ _ _ _ _ hc0 hc1 hD hP hs⟩
  | burnShares u n D sharesDestroyed sharesTotalAmount u' _ hcan hok ih =>
    obtain ⟨hL, hD, hP⟩ := ih
    obtain ⟨hL', hs⟩ := burn_step u u' sharesDestroyed sharesTotalAmount hL hcan hok
    have := compose _ _ _ _ _ _ _ hc0 hc1 hD hP hs
    rw [add_zero] at this
    exact ⟨hL', hD, this⟩

end XRPL.Model.SingleAssetVault
