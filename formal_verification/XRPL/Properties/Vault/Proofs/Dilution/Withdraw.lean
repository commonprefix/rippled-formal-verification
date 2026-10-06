import XRPL.Properties.Vault.Proofs.WithdrawTight
import XRPL.Properties.Vault.Proofs.ExactUpdates
import XRPL.Properties.Vault.Proofs.DepositAccuracy.Pricing
import XRPL.Properties.Vault.Common.WitnessSupport

/-! # A withdrawal dilutes by at most `depositε` plus half a unit of the payout -/

namespace XRPL.Model.SingleAssetVault.DilG

open XRPL.Model.Protocol

lemma navExact_of_zero (v : Vault) (w : Bool) (hL : v.toExact.lossUnrealized = 0) :
    v.WithdrawNavExact w := by
  have hL0 : v.lossUnrealized = Number.zero := by
    have hmz : v.lossUnrealized.mantissa_ = 0 := by
      by_contra h; exact (Number.toRat_ne_zero_of_mantissa_ne_zero v.lossUnrealized h) hL
    exact Number.eq_zero_of_mantissa_zero v.lossUnrealized v.wf.lossUnrealized_norm hmz
  refine ⟨v.assetsTotal, ?_, ?_⟩
  · cases w with
    | true => exact operator_sub_zero_right _ _
    | false => rw [hL0]; exact operator_sub_zero_right _ _
  · split
    · simp only [RawVault.depositNav, RawVault.toExact]
    · simp only [RawVault.withdrawNav, RawVault.toExact]
      rw [show v.lossUnrealized.toRat = 0 from hL]; ring

/-- The dilution arithmetic of a partial exit: the leaver takes at most the burned
shares' worth `A·b/S` times `1 + ε` plus `h`, the totals drop exactly, and at least half
the shares remain. -/
lemma exit_arith (A S b p h ε : ℚ) (hA : 0 ≤ A) (hS : 0 < S) (hε : 0 ≤ ε)
    (hmargin : b ≤ S / 2) (hp : p ≤ A * b / S * (1 + ε) + h) :
    (A - p) * S ≥ A * (S - b) * (1 - ε) - h * S := by
  have hpS : p * S ≤ A * b * (1 + ε) + h * S := by
    have := mul_le_mul_of_nonneg_right hp hS.le
    have heq : (A * b / S * (1 + ε) + h) * S = A * b * (1 + ε) + h * S := by field_simp
    linarith
  have : A * ε * b ≤ A * ε * (S - b) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hε)
  nlinarith

end XRPL.Model.SingleAssetVault.DilG

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DilG

/-- **Withdrawal dilution.** With at least half the shares remaining, per-share value
drops by at most `depositε` relatively plus half a unit of the payout's last digit per
share. -/
lemma Vault.withdraw_no_dilution_proof (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult)
    (hL : v.toExact.lossUnrealized = 0)
    (hnn : 0 ≤ r.sharesBurned.toRat) (hc : r.sharesBurned.Canonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hmargin : r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) / 2)
    (hSfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hpos : 0 < amount.amount.toRat)
    (hok : v.withdraw amount false hpos = .ok r) (herr : r.error = none) :
    r.vault'.withdrawNav * (v.toExact.sharesTotal : ℚ) ≥
      v.withdrawNav * (r.vault'.toExact.sharesTotal : ℚ) * (1 - depositε) -
        1 / 2 * (10 : ℚ) ^ r.assets'.exponent * (v.toExact.sharesTotal : ℚ) := by
  obtain ⟨cw, an, sta, -, -, -, -, hsta, hsb, -, hcase⟩ :=
    WdAcc.withdraw_ok_cases v amount false r hpos hok herr
  have hS0 : (0 : ℚ) ≤ (v.toExact.sharesTotal : ℚ) := Nat.cast_nonneg _
  have hu : (0 : ℚ) ≤ 1 / 2 * (10 : ℚ) ^ r.assets'.exponent := by positivity
  have hnav : v.withdrawNav = v.toExact.assetsTotal := by
    show v.toExact.assetsTotal - v.toExact.lossUnrealized = _; rw [hL]; ring
  have hA0 : 0 ≤ v.toExact.assetsTotal := v.exact.assetsTotal_nonneg
  have hε : depositε = 1 / 100000000000000000 := DepAcc.depositε_eq
  rcases hcase with ⟨-, -, -, hrv⟩ | ⟨hfin, hrest⟩
  · have hL' : r.vault'.toRawVault.lossUnrealized = v.toRawVault.lossUnrealized := by rw [hrv]
    have hT' : r.vault'.toRawVault.assetsTotal = Number.zero := by rw [hrv]
    have hS' : r.vault'.toRawVault.sharesTotal = Number.zero := by rw [hrv]
    have hnav' : r.vault'.withdrawNav = 0 := by
      show r.vault'.toRawVault.assetsTotal.toRat - r.vault'.toRawVault.lossUnrealized.toRat = 0
      rw [hT', hL']
      have : v.toRawVault.lossUnrealized.toRat = 0 := hL
      rw [this, Number.toRat_eq_zero_of_mantissa_zero _ rfl]; ring
    have hS'0 : ((r.vault'.toExact.sharesTotal : ℕ) : ℚ) = 0 := by
      show ((r.vault'.toRawVault.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = 0
      rw [hS', Number.toRat_eq_zero_of_mantissa_zero _ rfl]; rfl
    rw [hnav', hS'0]
    nlinarith
  · obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hrv⟩ := hrest
    have hfin' : r.sharesBurned.operator_eq sta = false := by rw [hsb]; exact hfin
    have hnavx := navExact_of_zero v false hL
    obtain ⟨-, hup, -⟩ := Vault.withdraw_payout_proof v amount false sta r hnn hc hnavx hpos hok herr
      hsta hfin'
    obtain ⟨hA', -, hS'⟩ := Vault.withdraw_vault_updates_proof v amount false sta r hnn hc hSnt hpos
      hok herr hsta hfin'
    have hL' : r.vault'.toRawVault.lossUnrealized = v.toRawVault.lossUnrealized := by rw [hrv]
    have hnav' : r.vault'.withdrawNav = v.toExact.assetsTotal - r.assets'.toRat := by
      show r.vault'.assetsTotal.toRat - r.vault'.toRawVault.lossUnrealized.toRat = _
      rw [hA', hL']
      have : v.toRawVault.lossUnrealized.toRat = 0 := hL
      rw [this]; ring
    have hS'' : ((r.vault'.toExact.sharesTotal : ℕ) : ℚ) =
        (v.toExact.sharesTotal : ℚ) - r.sharesBurned.toRat := by
      rw [RawVault.WF.toExact_sharesTotal _ r.vault'.wf]; exact hS' hSfit
    rw [hnav', hS'', hnav]
    have hI : v.idealAssetsWithdraw false r.sharesBurned.toRat =
        v.toExact.assetsTotal * r.sharesBurned.toRat / (v.toExact.sharesTotal : ℚ) := by
      unfold RawVault.idealAssetsWithdraw; rw [if_neg (by decide), hnav]
    rw [hI] at hup
    rcases lt_or_eq_of_le hS0 with hSpos | hSz
    · exact exit_arith _ _ _ _ _ _ hA0 hSpos (by rw [hε]; norm_num) hmargin hup
    · have hA : v.toExact.assetsTotal = 0 := (v.exact.empty_shares (by exact_mod_cast hSz.symm)).1
      rw [← hSz, hA]; ring_nf; rfl

end XRPL.Model.SingleAssetVault
