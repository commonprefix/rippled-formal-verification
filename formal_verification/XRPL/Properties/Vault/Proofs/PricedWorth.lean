import XRPL.Properties.Vault.Proofs.ExitOrderPayout
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.MaxValueFits
import XRPL.Properties.Vault.Proofs.WithdrawPricing.Core
import XRPL.Properties.Vault.Proofs.DepositTight.Price
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.NumberBridge

/-! # A withdrawal price against the shares' worth

On an Open-zone vault a nonzero withdrawal price is a whole number of units of its last digit, a grid no coarser
than the base grid, and sits within half a unit plus a tiny 19-digit error of the worth. When the worth is a whole
number of base units, the price can only land on the worth. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A value on the coarser grid `10^b` is also a whole number of steps of the finer grid `10^e`. -/
lemma grid_coarse_steps (k : ℤ) (e b : ℤ) (heb : e ≤ b) :
    ∃ K : ℤ, (k : ℚ) * 10 ^ b = K * 10 ^ e := by
  refine ⟨k * 10 ^ (b - e).toNat, ?_⟩
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]
  congr 2
  ring

/-- Two values on the grid `10^e`, the second also on the coarser grid `10^b`: less than one step above the
second means at most the second. -/
lemma le_of_grid_lt (m : ℕ) (k : ℤ) (e b : ℤ) (heb : e ≤ b) (x y : ℚ) (hx : x = m * 10 ^ e) (hy : y = k * 10 ^ b)
    (hlt : x - y < 10 ^ e) : x ≤ y := by
  have hpos : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  obtain ⟨K, hK⟩ := grid_coarse_steps k e b heb
  rw [hx, hy, hK] at hlt ⊢
  have h1 : ((m : ℚ) - K) * 10 ^ e < 1 * 10 ^ e := by rw [sub_mul, one_mul]; exact hlt
  have h2 : (m : ℚ) - K < 1 := lt_of_mul_lt_mul_right h1 hpos.le
  have h3 : ((m : ℤ) : ℚ) - K < 1 := by push_cast; exact h2
  have h4 : (m : ℤ) - K < 1 := by exact_mod_cast h3
  have h5 : ((m : ℤ) : ℚ) ≤ K := by exact_mod_cast (by omega : (m : ℤ) ≤ K)
  push_cast at h5
  exact mul_le_mul_of_nonneg_right h5 hpos.le

/-- Two values on the grid `10^e`, the first also on the coarser grid `10^b`: less than one step below the
first means at least the first. -/
lemma ge_of_grid_lt (m : ℕ) (k : ℤ) (e b : ℤ) (heb : e ≤ b) (x y : ℚ) (hx : x = m * 10 ^ e) (hy : y = k * 10 ^ b)
    (hlt : y - x < 10 ^ e) : y ≤ x := by
  have hpos : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  obtain ⟨K, hK⟩ := grid_coarse_steps k e b heb
  rw [hx, hy, hK] at hlt ⊢
  have h1 : ((K : ℚ) - m) * 10 ^ e < 1 * 10 ^ e := by rw [sub_mul, one_mul]; exact hlt
  have h2 : (K : ℚ) - m < 1 := lt_of_mul_lt_mul_right h1 hpos.le
  have h3 : (K : ℚ) - ((m : ℤ) : ℚ) < 1 := by push_cast; exact h2
  have h4 : K - (m : ℤ) < 1 := by exact_mod_cast h3
  have h5 : (K : ℚ) ≤ ((m : ℤ) : ℚ) := by exact_mod_cast (by omega : K ≤ (m : ℤ))
  push_cast at h5
  exact mul_le_mul_of_nonneg_right h5 hpos.le

/-- A nonzero withdrawal price on an Open-zone vault is a whole number of `10^e`, no coarser than the base grid, and
within half a unit plus the 19-digit error of the worth, that error below `111/10^4` of a unit. -/
lemma Vault.OpenZone.priced_grid {v : Vault} (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares p : STAmount) (w : Bool) (hnn : 0 ≤ shares.toRat) (hsc : shares.Canonical)
    (hpr : v.sharesToAssetsWithdraw shares w = .ok p) (hpc : p.toRat ≤ v.assetsAvailable.toRat)
    (hpz : p.toRat ≠ 0) :
    p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent ∧ p.exponent ≤ v.baseExponent ∧
      p.toRat ≤ v.idealAssetsWithdraw w shares.toRat * (1 + sharesε) + 1 / 2 * (10 : ℚ) ^ p.exponent ∧
      v.idealAssetsWithdraw w shares.toRat - p.toRat ≤
        v.idealAssetsWithdraw w shares.toRat * sharesε + 1 / 2 * (10 : ℚ) ^ p.exponent ∧
      v.idealAssetsWithdraw w shares.toRat * sharesε < 111 / 10 ^ 4 * (10 : ℚ) ^ p.exponent := by
  set I := v.idealAssetsWithdraw w shares.toRat with hI
  obtain ⟨hp0, hpu, hpl⟩ := Vault.sharesToAssetsWithdraw_bounds_proof v shares p w hnn hsc
    (hz.withdrawNavExact w) hpr
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v shares p w hmax hpr
  have hcash := hz.assetsAvailable_le_openLimit
  have hppos : 0 < p.toRat := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hpm : p.mValue ≠ 0 := fun h => hpz ((STAmount.toRat_eq_zero_iff p).mpr h)
  have hpcan : p.Canonical := hpcz.resolve_right (by simpa [STAmount.isZero] using hpm)
  replace hpl := hpl (by simpa [STAmount.isZero] using hpm)
  have hpv : p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent :=
    STAmount.toRat_of_nonneg p (STAmount.mIsNegative_false_of_pos p hppos)
  have hgpos : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  -- the relative error stays tiny against one unit of a price below `10^16` units
  have hrel : ∀ g : ℚ, 0 < g → p.toRat < 10 ^ 16 * g → I - p.toRat ≤ I * sharesε + 1 / 2 * g →
      I * sharesε < 111 / 10 ^ 4 * g := by
    intro g hg hs hl
    unfold sharesε at *
    have h1 : I * (1 - 11 / 10 ^ 19) < (10 ^ 16 + 1 / 2) * g := by linarith
    have h2 : I < (10 ^ 16 + 1 / 2) * g / (1 - 11 / 10 ^ 19) := by
      rw [lt_div_iff₀ (by norm_num)]; linarith
    have hc : ((10 ^ 16 + 1 / 2) / (1 - 11 / 10 ^ 19) * (11 / 10 ^ 19) : ℚ) ≤ 111 / 10 ^ 4 := by norm_num
    calc I * (11 / 10 ^ 19) < (10 ^ 16 + 1 / 2) * g / (1 - 11 / 10 ^ 19) * (11 / 10 ^ 19) :=
          mul_lt_mul_of_pos_right h2 (by norm_num)
      _ = ((10 ^ 16 + 1 / 2) / (1 - 11 / 10 ^ 19) * (11 / 10 ^ 19)) * g := by ring
      _ ≤ 111 / 10 ^ 4 * g := mul_le_mul_of_nonneg_right hc hg.le
  by_cases hint : v.numericType.isIntegral = true
  · -- integral: the price is a whole number of base units
    have hb0 : v.baseExponent = 0 := v.baseExponent_bounds.2.2 hint
    have hic : p.IntegralCanonical := (hpcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1
    have he : p.exponent = 0 := hic.offset_zero
    have hsmall : p.toRat < 10 ^ 16 * (10 : ℚ) ^ p.exponent := by
      rw [hb0] at hcash
      rw [he]
      norm_num at hcash ⊢
      linarith
    exact ⟨hpv, by rw [he, hb0], hpu, hpl, hrel _ hgpos hsmall hpl⟩
  -- fractional: a 16-digit price on a grid no coarser than the base grid
  have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hio : p.IOUCanonical := hpcan.2 (by unfold STAmount.integral; rw [hpt, hvfr]; rfl)
  have hmlo : (10 ^ 15 : ℚ) ≤ p.mValue.toNat := by exact_mod_cast hio.mant_lo
  have hmhi : (p.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hio.mant_hi
  have hsmall : p.toRat < 10 ^ 16 * (10 : ℚ) ^ p.exponent := by
    rw [hpv]; exact mul_lt_mul_of_pos_right hmhi hgpos
  have hbig : 10 ^ 15 * (10 : ℚ) ^ p.exponent ≤ p.toRat := by
    rw [hpv]; exact mul_le_mul_of_nonneg_right hmlo hgpos.le
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
  exact ⟨hpv, heb, hpu, hpl, hrel _ hgpos hsmall hpl⟩

/-- On an Open-zone vault a withdrawal price never exceeds the worth of the shares when that worth is a whole
number of base units. -/
lemma Vault.OpenZone.priced_le_worth {v : Vault} (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares p : STAmount) (w : Bool) (hnn : 0 ≤ shares.toRat) (hsc : shares.Canonical)
    (hpr : v.sharesToAssetsWithdraw shares w = .ok p) (hpc : p.toRat ≤ v.assetsAvailable.toRat)
    (hworth : ∃ k : ℤ, v.idealAssetsWithdraw w shares.toRat = k * 10 ^ v.baseExponent) :
    p.toRat ≤ v.idealAssetsWithdraw w shares.toRat := by
  by_cases hpz : p.toRat = 0
  · rw [hpz]
    unfold RawVault.idealAssetsWithdraw
    have hnq : 0 ≤ WdPrice.navQ v w := WdPrice.navQ_nonneg v w
    exact div_nonneg (mul_nonneg hnq hnn) (by positivity)
  obtain ⟨hpv, heb, hpu, -, hrel⟩ := hz.priced_grid hmax shares p w hnn hsc hpr hpc hpz
  obtain ⟨k, hk⟩ := hworth
  have hexp : v.idealAssetsWithdraw w shares.toRat * (1 + sharesε) =
      v.idealAssetsWithdraw w shares.toRat + v.idealAssetsWithdraw w shares.toRat * sharesε := by ring
  have hg : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  exact le_of_grid_lt _ k _ _ heb _ _ hpv hk (by linarith)

/-- The facts of one nonzero withdrawal price on any lawful vault, for a worth at the computed net asset value
within the Open limit: the same as `priced_grid`. -/
lemma Vault.priced_grid_total (v : Vault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares p : STAmount) (w : Bool) (nav : Number) (hnav : v.assetsTotalForWithdrawal w = .ok nav)
    (hnn : 0 ≤ shares.toRat) (hsc : shares.Canonical) (hpr : v.sharesToAssetsWithdraw shares w = .ok p)
    (hsmall : v.idealAssetsWithdrawAt nav.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent)
    (hpz : p.toRat ≠ 0) :
    p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent ∧ p.exponent ≤ v.baseExponent ∧
      p.toRat ≤ v.idealAssetsWithdrawAt nav.toRat shares.toRat * (1 + sharesε) + 1 / 2 * (10 : ℚ) ^ p.exponent ∧
      v.idealAssetsWithdrawAt nav.toRat shares.toRat - p.toRat ≤
        v.idealAssetsWithdrawAt nav.toRat shares.toRat * sharesε + 1 / 2 * (10 : ℚ) ^ p.exponent ∧
      v.idealAssetsWithdrawAt nav.toRat shares.toRat * sharesε < 111 / 10 ^ 4 * (10 : ℚ) ^ p.exponent := by
  set I := v.idealAssetsWithdrawAt nav.toRat shares.toRat with hI
  obtain ⟨hp0, hpu, hpl⟩ := Vault.sharesToAssetsWithdraw_total_proof v shares p w nav hnav hnn hsc hpr
  obtain ⟨hpcz, hpt⟩ := Vault.sharesToAssetsWithdraw_form v shares p w hmax hpr
  have hppos : 0 < p.toRat := lt_of_le_of_ne hp0 (Ne.symm hpz)
  have hpm : p.mValue ≠ 0 := fun h => hpz ((STAmount.toRat_eq_zero_iff p).mpr h)
  have hpcan : p.Canonical := hpcz.resolve_right (by simpa [STAmount.isZero] using hpm)
  replace hpl := hpl (by simpa [STAmount.isZero] using hpm)
  have hpv : p.toRat = (p.mValue.toNat : ℚ) * 10 ^ p.exponent :=
    STAmount.toRat_of_nonneg p (STAmount.mIsNegative_false_of_pos p hppos)
  have hgpos : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  have hbpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hI0 : 0 ≤ I := by
    rw [hI]
    unfold RawVault.idealAssetsWithdrawAt
    have := (Vault.assetsTotalForWithdrawal_nonneg v w nav hnav).2
    positivity
  have hε : (sharesε : ℚ) = 11 / 10 ^ 19 := rfl
  by_cases hint : v.numericType.isIntegral = true
  · have hb0 : v.baseExponent = 0 := v.baseExponent_bounds.2.2 hint
    have hic : p.IntegralCanonical := (hpcan.1 (by unfold STAmount.integral; rw [hpt]; exact hint)).1
    have he : p.exponent = 0 := hic.offset_zero
    rw [hb0, zpow_zero, mul_one] at hsmall
    refine ⟨hpv, by rw [he, hb0], hpu, hpl, ?_⟩
    rw [he, zpow_zero, hε]
    nlinarith
  have hvfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hio : p.IOUCanonical := hpcan.2 (by unfold STAmount.integral; rw [hpt, hvfr]; rfl)
  have hmlo : (10 ^ 15 : ℚ) ≤ p.mValue.toNat := by exact_mod_cast hio.mant_lo
  have hmhi : (p.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hio.mant_hi
  have hsm : p.toRat < 10 ^ 16 * (10 : ℚ) ^ p.exponent := by
    rw [hpv]; exact mul_lt_mul_of_pos_right hmhi hgpos
  have hbig : 10 ^ 15 * (10 : ℚ) ^ p.exponent ≤ p.toRat := by
    rw [hpv]; exact mul_le_mul_of_nonneg_right hmlo hgpos.le
  have hrel : I * sharesε < 111 / 10 ^ 4 * (10 : ℚ) ^ p.exponent := by
    rw [hε] at hpl ⊢
    nlinarith
  refine ⟨hpv, ?_, hpu, hpl, hrel⟩
  -- the price stays below `10^16` base units, so its grid is no coarser than the base grid
  by_contra h
  push Not at h
  have h1 : (10 : ℚ) ^ (v.baseExponent + 1) ≤ 10 ^ p.exponent := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (10 : ℚ) ^ (v.baseExponent + 1) = 10 * 10 ^ v.baseExponent := by
    rw [zpow_add_one₀ (by norm_num)]; ring
  rw [hε] at hpu hrel
  nlinarith

/-- On any lawful vault a withdrawal price never exceeds the worth at the computed net asset value when that worth
is a whole number of base units within the Open limit. -/
lemma Vault.priced_le_worth_total (v : Vault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares p : STAmount) (w : Bool) (nav : Number) (hnav : v.assetsTotalForWithdrawal w = .ok nav)
    (hnn : 0 ≤ shares.toRat) (hsc : shares.Canonical) (hpr : v.sharesToAssetsWithdraw shares w = .ok p)
    (hsmall : v.idealAssetsWithdrawAt nav.toRat shares.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent)
    (hworth : ∃ k : ℤ, v.idealAssetsWithdrawAt nav.toRat shares.toRat = k * 10 ^ v.baseExponent) :
    p.toRat ≤ v.idealAssetsWithdrawAt nav.toRat shares.toRat := by
  by_cases hpz : p.toRat = 0
  · rw [hpz]
    unfold RawVault.idealAssetsWithdrawAt
    have := (Vault.assetsTotalForWithdrawal_nonneg v w nav hnav).2
    positivity
  obtain ⟨hpv, heb, hpu, -, hrel⟩ := Vault.priced_grid_total v hmax shares p w nav hnav hnn hsc hpr hsmall hpz
  obtain ⟨k, hk⟩ := hworth
  have hexp : v.idealAssetsWithdrawAt nav.toRat shares.toRat * (1 + sharesε) =
      v.idealAssetsWithdrawAt nav.toRat shares.toRat + v.idealAssetsWithdrawAt nav.toRat shares.toRat * sharesε := by
    ring
  have hg : (0 : ℚ) < 10 ^ p.exponent := zpow_pos (by norm_num) _
  exact le_of_grid_lt _ k _ _ heb _ _ hpv hk (by linarith)

end XRPL.Model.SingleAssetVault
