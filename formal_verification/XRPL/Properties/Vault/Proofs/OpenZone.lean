import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit
import XRPL.Properties.Vault.Proofs.Support.WithdrawPayout
import XRPL.Properties.Vault.Proofs.Support.ComputeClawback
import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Vault.Common.Create
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Protocol.Number.AtExponent

/-! # The Open zone

A vault without loans keeps its cash a whole number of base units within the Open-zone limit
(`9 * 10^(15 + base)`), stored exactly. Every cash update then lands exactly, and the share total is
updated exactly on any vault. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- With nothing deployed the computed total is the cash. -/
lemma Vault.assetsTotal_of_noLending (v : Vault) (hAD : v.assetsDeployed = Number.zero) :
    v.assetsTotal = .ok v.assetsAvailable := by
  unfold RawVault.assetsTotal
  rw [hAD]
  exact Number.operator_add_zero_right _ _

/-- With nothing deployed there is no unrealized loss either, so a withdrawal prices at the cash. -/
lemma Vault.assetsTotalForWithdrawal_of_noLending (v : Vault) (hAD : v.assetsDeployed = Number.zero)
    (waive : Bool) : v.assetsTotalForWithdrawal waive = .ok v.assetsAvailable := by
  have hLU := Vault.lossUnrealized_eq_zero_of_deployed v hAD
  cases waive
  · simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, Vault.assetsTotal_of_noLending v hAD, hLU]
    exact Number.operator_sub_zero _ _
  · simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, Vault.assetsTotal_of_noLending v hAD]
    exact Number.operator_sub_zero _ _

/-- With nothing deployed a withdrawal prices exactly at the cash. -/
lemma Vault.withdrawNavExact_of_noLending (v : Vault) (hAD : v.assetsDeployed = Number.zero) (w : Bool) :
    v.WithdrawNavExact w := by
  have hLU := Vault.lossUnrealized_eq_zero_of_deployed v hAD
  have hAD0 : v.assetsDeployed.toRat = 0 := by rw [hAD, Number.toRat_zero]
  have hLU0 : v.lossUnrealized.toRat = 0 := by rw [hLU, Number.toRat_zero]
  refine ⟨v.assetsAvailable, v.assetsAvailable, Vault.assetsTotal_of_noLending v hAD, ?_, ?_⟩
  · cases w
    · show v.assetsAvailable.operator_sub v.lossUnrealized .to_nearest = _
      rw [hLU]; exact Number.operator_sub_zero _ _
    · exact Number.operator_sub_zero _ _
  · cases w
    · show v.assetsAvailable.toRat = v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat
      rw [hAD0, hLU0]; ring
    · show v.assetsAvailable.toRat = v.assetsAvailable.toRat + v.assetsDeployed.toRat
      rw [hAD0]; ring

/-- An Open-zone vault's total is its cash. -/
lemma Vault.OpenZone.assetsTotal_eq {v : Vault} (hz : v.OpenZone) : v.assetsTotal = .ok v.assetsAvailable :=
  Vault.assetsTotal_of_noLending v hz.assetsDeployed

/-- An Open-zone vault's net asset value is its cash. -/
lemma Vault.OpenZone.withdrawNav_eq {v : Vault} (hz : v.OpenZone) : v.withdrawNav = v.assetsAvailable.toRat := by
  show v.assetsAvailable.toRat + v.assetsDeployed.toRat - v.lossUnrealized.toRat = _
  rw [hz.assetsDeployed, hz.lossUnrealized, Number.toRat_zero]
  ring

/-- An Open-zone vault prices a deposit at its cash. -/
lemma Vault.OpenZone.depositNav_eq {v : Vault} (hz : v.OpenZone) : v.depositNav = v.assetsAvailable.toRat := by
  show v.assetsAvailable.toRat + v.assetsDeployed.toRat = _
  rw [hz.assetsDeployed, Number.toRat_zero, add_zero]

/-- In the Open zone the withdrawal prices at the cash. -/
lemma Vault.OpenZone.assetsTotalForWithdrawal_eq {v : Vault} (hz : v.OpenZone) (waive : Bool) :
    v.assetsTotalForWithdrawal waive = .ok v.assetsAvailable :=
  Vault.assetsTotalForWithdrawal_of_noLending v hz.assetsDeployed waive

/-- An Open-zone vault prices a withdrawal at its cash, exactly. -/
lemma Vault.OpenZone.withdrawNavExact {v : Vault} (hz : v.OpenZone) (w : Bool) : v.WithdrawNavExact w :=
  Vault.withdrawNavExact_of_noLending v hz.assetsDeployed w

/-- An Open-zone vault with cash holds at least one step of its base grid, at least `10⁻¹⁰`. -/
lemma Vault.OpenZone.cash_ge {v : Vault} (hz : v.OpenZone) (hA : 0 < v.assetsAvailable.toRat) :
    (10 : ℚ) ^ v.baseExponent ≤ v.assetsAvailable.toRat ∧ (10 : ℚ) ^ (-10 : ℤ) ≤ v.assetsAvailable.toRat := by
  obtain ⟨k, -, hkv⟩ := hz.cash
  have hk1 : (1 : ℚ) ≤ k := by
    have : k ≠ 0 := fun h => by rw [hkv, h] at hA; simp at hA
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hbp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hbk : (10 : ℚ) ^ v.baseExponent ≤ v.assetsAvailable.toRat := by rw [hkv]; nlinarith
  exact ⟨hbk, le_trans (zpow_le_zpow_right₀ (by norm_num) (Vault.baseExponent_bounds v).1) hbk⟩

/-- An Open-zone vault's cash is at most `9 * 10^15`: the base exponent is never positive. -/
lemma Vault.OpenZone.cash_le {v : Vault} (hz : v.OpenZone) : v.assetsAvailable.toRat ≤ 9 * 10 ^ 15 := by
  obtain ⟨k, hk, hkv⟩ := hz.cash
  have hk' : (k : ℚ) ≤ 9 * 10 ^ 15 := by exact_mod_cast hk
  have hb : (10 : ℚ) ^ v.baseExponent ≤ 10 ^ (0 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (Vault.baseExponent_bounds v).2.1
  rw [zpow_zero] at hb
  rw [hkv]
  calc (k : ℚ) * 10 ^ v.baseExponent ≤ k * 1 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg k)
    _ ≤ 9 * 10 ^ 15 := by rw [mul_one]; exact hk'

/-- A vault with cash has shares, at least one, and at most `2⁶³ - 1`. -/
lemma Vault.sharesTotal_bounds_of_cash (v : Vault) (hA : 0 < v.assetsAvailable.toRat) :
    0 < v.sharesTotal.toRat ∧ 1 ≤ v.sharesTotal.toRat ∧ v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by
  have hSTpos : 0 < v.sharesTotal.toRat := by
    rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
    · exact h
    · exfalso
      have hz := (Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp h.symm
      rw [(v.valid.empty_shares hz).1, Number.toRat_zero] at hA
      exact lt_irrefl _ hA
  exact ⟨hSTpos, rat_one_le_of_den_one_pos _ v.wf.sharesTotal_int hSTpos, v.sharesTotal_le_maxRep⟩

/-- A cash update by whole base units within the Open zone is exact, and the asset stores the
new cash exactly. -/
lemma Vault.adjustAssetsAndShares_units (v : Vault) (assets shares : STAmount) (raw : RawVault) (k : ℕ)
    (hz : v.OpenZone) (hc : assets.CanonicalOrZero)
    (hunits : ∃ j : ℤ, assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hk : k ≤ 9 * 10 ^ 15)
    (hnew : v.assetsAvailable.toRat + assets.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hadj : (v.adjustAssetsAndShares assets shares).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent ∧
      STAmount.isRounded v.numericType raw.assetsAvailable = false := by
  obtain ⟨assetsNum, sharesNum, s, aa', st', hnum, hsnum, hst, hs, haa, rfl⟩ :=
    Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hv, hnorm⟩ := hc.toNumber_exact assetsNum hnum
  obtain ⟨kA, -, hAv⟩ := hz.cash
  obtain ⟨j, hj⟩ := hunits
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hpow : (10 : ℚ) ^ v.baseExponent ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hkj : (kA : ℤ) + j = k := by
    have h1 : (((kA : ℤ) + j : ℤ) : ℚ) * (10 : ℚ) ^ v.baseExponent = ((k : ℤ) : ℚ) * (10 : ℚ) ^ v.baseExponent := by
      push_cast; rw [← hnew, hAv, hj]; ring
    exact_mod_cast mul_right_cancel₀ hpow h1
  -- the sum is exact
  have hsv : s.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent := by
    have h := Number.operator_add_toRat_of_grid _ _ _ kA j v.baseExponent v.wf.assetsAvailable_norm hnorm
      hAv (by rw [hv, hj]) (by rw [hkj]; constructor <;> push_cast <;> omega)
      (by unfold minExponent maxExponent; constructor <;> omega) hs
    rw [h, hkj]; push_cast; rfl
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hnorm hs
  have hs0 : 0 ≤ s.toRat := by rw [hsv]; positivity
  -- the asset stores the sum exactly
  have hsr : STAmount.isRounded v.numericType s = false := by
    by_cases hint : v.numericType.isIntegral = true
    · have hden : s.toRat.den = 1 := by rw [hsv, hbint hint]; simp
      exact STAmount.isRounded_eq_false_of_integral_round _ s aa' hint hsn hs0 hden haa
    · have hfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
      rw [STAmount.isRounded_eq_false_iff _ s hsn hs0, hfr, hsv]
      exact STAmount.representable_fractional_of_units k _ (by omega) (by omega) (by omega)
  have haav := STAmount.roundToNumericType_of_isRounded_false _ s aa' hsn hsr haa
  have haan := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa
  have heq : aa' = s :=
    (Number.operator_eq_iff_eq _ _).mp ((operator_eq_iff aa' s haan hsn).mpr haav)
  subst heq
  exact ⟨hsv, hsr⟩

/-- A charge the inflow check accepts keeps the total below the Open-zone limit plus one base step,
on any lawful vault. The capacity it compares never rounds below the computed total plus the charge. -/
lemma Vault.checkOpenLimit_bound (v : Vault) (charge : STAmount) (hc : charge.CanonicalOrZero)
    (hc0 : 0 ≤ charge.toRat) (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hin : v.checkOpenLimit charge = .ok .tesSUCCESS) :
    navN.toRat + charge.toRat < 9 * (10 : ℚ) ^ (15 + v.baseExponent) + 10 ^ v.baseExponent := by
  obtain ⟨hblo, hbhi, -⟩ := v.baseExponent_bounds
  obtain ⟨hnavn, hAD⟩ := Vault.assetsTotal_ge_deployed v navN hat
  have hnav0 : 0 ≤ navN.toRat := le_trans v.exact.assetsDeployed_nonneg hAD
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  by_contra hge
  push Not at hge
  -- the capacity check would have fired: the total plus the charge is past the limit by a base step
  have key : ∀ amountNum s₁ capacity limit : Number, charge.toNumber .to_nearest = .ok amountNum →
      navN.operator_add v.yieldUnrealized .towards_zero = .ok s₁ →
      s₁.operator_add amountNum .towards_zero = .ok capacity →
      Number.from_rep 9 (15 + v.baseExponent) largeRange.min largeRange.max .to_nearest = .ok limit →
      ¬ capacity.operator_gt limit = true → False := by
    intro amountNum s₁ capacity w hn hs₁ hcapok hlim hng
    obtain ⟨hnv, hnn⟩ := hc.toNumber_exact _ hn
    obtain ⟨w', hw, hwv, hwn⟩ := Number.from_rep_exact (9 : Int64) (15 + v.baseExponent) .to_nearest (by decide)
      (by unfold minExponent; omega) (by unfold maxExponent; omega)
    have hww : w = w' := Except.ok.inj (hlim.symm.trans hw)
    subst hww
    have hpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
    -- the first sum keeps at least the total, and is a normalized `Number`
    obtain ⟨n₁, hlo₁, hs₁v⟩ := operator_add_rounded_towards_zero _ _ _ hnavn v.wf.yieldUnrealized_norm hs₁
    rw [if_pos (by linarith)] at hlo₁
    have hs₁ge : navN.toRat ≤ s₁.toRat := by
      rw [hs₁v]; exact Number.lower_tight _ n₁ hlo₁ navN hnavn (by linarith)
    have hs₁n : s₁.isNormalized := by
      by_cases hY : v.yieldUnrealized.mantissa_ = 0
      · rw [Number.eq_zero_of_mantissa_zero _ v.wf.yieldUnrealized_norm hY, Number.operator_add_zero_right,
          Except.ok.injEq] at hs₁
        rw [← hs₁]; exact hnavn
      · have hYge : v.yieldUnrealized.toRat ≤ s₁.toRat := by
          rw [hs₁v]; exact Number.lower_tight _ n₁ hlo₁ _ v.wf.yieldUnrealized_norm (by linarith)
        have hYpos : 0 < v.yieldUnrealized.toRat :=
          lt_of_le_of_ne hY0 (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hY))
        exact operator_add_isNormalized _ _ _ .towards_zero hnavn v.wf.yieldUnrealized_norm hs₁ (fun h0 => by
          have := Number.toRat_eq_zero_of_mantissa_zero s₁ h0; linarith)
    -- one base step past the limit
    obtain ⟨m, hm, hmv⟩ := Number.exists_normalized_int_mul_pow (9 * 10 ^ 15 + 1) v.baseExponent
      (by constructor <;> norm_num) (by unfold minExponent maxExponent; constructor <;> omega)
    have h9 : 9 * (10 : ℚ) ^ (15 + v.baseExponent) = 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num; ring
    have htruth : 0 ≤ s₁.toRat + amountNum.toRat := by
      rw [hnv]; exact add_nonneg (le_trans hnav0 hs₁ge) hc0
    obtain ⟨n, hlo, hcapv⟩ := operator_add_rounded_towards_zero _ _ _ hs₁n hnn hcapok
    rw [if_pos htruth] at hlo
    have hmle : m.toRat ≤ s₁.toRat + amountNum.toRat := by
      rw [hmv, hnv]; push_cast; rw [h9] at hge; linarith
    have hmn := Number.lower_tight _ n hlo m hm hmle
    have hlt : w.toRat < capacity.toRat := by
      rw [hcapv]
      refine lt_of_lt_of_le ?_ hmn
      rw [hwv, hmv, zpow_add₀ (by norm_num)]
      push_cast
      nlinarith
    -- the capacity compares above the limit, so the check fired
    have hcap0 : capacity.mantissa_ ≠ 0 := by
      intro h0
      have := Number.toRat_eq_zero_of_mantissa_zero capacity h0
      rw [hwv] at hlt
      have : (0 : ℚ) < 9 * 10 ^ (15 + v.baseExponent) := by positivity
      push_cast at hlt
      linarith
    have hcapn := operator_add_isNormalized _ _ _ .towards_zero hs₁n hnn hcapok hcap0
    apply hng
    show w.operator_lt capacity = true
    exact (operator_lt_iff _ _ hwn hcapn).mpr hlt
  simp only [Vault.checkOpenLimit, Vault.exceedsOpenLimit, Vault.openLimit, bind, Except.bind, pure,
    Except.pure, hat] at hin
  walk_ok
  exact key _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›

/-- A charge the inflow check accepts keeps the cash within the Open-zone limit. -/
lemma Vault.checkOpenLimit_openZone (v : Vault) (hz : v.OpenZone) (charge : STAmount)
    (hc : charge.CanonicalOrZero) (j : ℕ) (hj : charge.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hin : v.checkOpenLimit charge = .ok .tesSUCCESS) :
    ∃ k : ℕ, k ≤ 9 * 10 ^ 15 ∧
      v.assetsAvailable.toRat + charge.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨kA, -, hAv⟩ := hz.cash
  have hpos : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  refine ⟨kA + j, ?_, by rw [hAv, hj]; push_cast; ring⟩
  -- the new cash is whole base units below the limit plus one step, so at most the limit
  have hb := Vault.checkOpenLimit_bound v charge hc (by rw [hj]; positivity) _ hz.assetsTotal_eq hin
  have h15 : (10 : ℚ) ^ (15 : ℤ) = 10 ^ 15 := by norm_num
  rw [hAv, hj, zpow_add₀ (by norm_num), h15] at hb
  have hlt : ((kA + j : ℕ) : ℚ) * 10 ^ v.baseExponent < ((9 * 10 ^ 15 + 1 : ℕ) : ℚ) * 10 ^ v.baseExponent := by
    push_cast; linarith
  have hlt' : kA + j < 9 * 10 ^ 15 + 1 := by exact_mod_cast lt_of_mul_lt_mul_right hlt hpos.le
  omega

/-- A vault whose record keeps the balances other than the cash, the asset and the scale stays in
the Open zone once its new cash is whole base units within the limit, stored exactly. -/
lemma Vault.OpenZone.of_fields {v v' : Vault} (hz : v.OpenZone)
    (hAD : v'.assetsDeployed = v.assetsDeployed) (hLU : v'.lossUnrealized = v.lossUnrealized)
    (hYU : v'.yieldUnrealized = v.yieldUnrealized) (hnt : v'.numericType = v.numericType)
    (hsc : v'.scale = v.scale)
    (hcash : ∃ k : ℕ, k ≤ 9 * 10 ^ 15 ∧ v'.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hex : STAmount.isRounded v.numericType v'.assetsAvailable = false) : v'.OpenZone := by
  have hb : v'.baseExponent = v.baseExponent := by
    unfold Vault.baseExponent; rw [hnt, hsc]
  exact ⟨hAD.trans hz.assetsDeployed, hLU.trans hz.lossUnrealized, hYU.trans hz.yieldUnrealized,
    by rw [hb]; exact hcash, by rw [hnt]; exact hex⟩

/-- A vault whose record changed only in its cash and share total stays in the Open zone once its
new cash is whole base units within the limit, stored exactly. -/
lemma Vault.OpenZone.of_cash_update {v v' : Vault} (hz : v.OpenZone) (aa' st' : Number)
    (hv' : v'.toRawVault = { v.toRawVault with assetsAvailable := aa', sharesTotal := st' })
    (hcash : ∃ k : ℕ, k ≤ 9 * 10 ^ 15 ∧ v'.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hex : STAmount.isRounded v.numericType v'.assetsAvailable = false) : v'.OpenZone :=
  Vault.OpenZone.of_fields hz ((congrArg RawVault.assetsDeployed hv').trans rfl)
    ((congrArg RawVault.lossUnrealized hv').trans rfl) ((congrArg RawVault.yieldUnrealized hv').trans rfl)
    ((congrArg RawVault.numericType hv').trans rfl) ((congrArg RawVault.scale hv').trans rfl) hcash hex

/-- A successful deposit, read off the code: the rounded amount, the priced shares and charge,
the inflow check passed, and the record the cash update wrote. -/
lemma Vault.deposit_ok_reduces (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (r : VaultWithAmounts)
    (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    ∃ (roundedAmount : STAmount) (amounts : VaultAmounts) (raw : RawVault),
      (v.roundedDepositAmount amount).run = .ok (.ok roundedAmount) ∧
      (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts) ∧
      v.checkOpenLimit amounts.assets = .ok .tesSUCCESS ∧
      (v.adjustAssetsAndShares amounts.assets amounts.shares).run = .ok (.ok raw) ∧
      r.vault'.toRawVault = raw ∧ r.assets = amounts.assets ∧ r.shares = amounts.shares := by
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  have hin : Vault.checkOpenLimit _ _ = .ok _ := ‹_›
  have hne : ¬ (_ != TER.tesSUCCESS) = true := ‹_›
  rcases Vault.checkOpenLimit_codes _ _ _ hin with h | h <;> subst h
  · exact ⟨_, _, _, ‹_›, ‹_›, hin, ‹_›, (RawVault.to_lawful_ok ‹_›).1, rfl, rfl⟩
  · exact absurd (by decide) hne

/-- A deposit adds exactly the issued shares to the share total, when the sum stays within the MPT
maximum. -/
lemma Vault.deposit_exact_sharesTotal (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (r : VaultWithAmounts) (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r))
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.shares.toRat ≤ 2 ^ 63 - 1) :
    (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal + r.shares.toRat := by
  obtain ⟨ra, amounts, raw, hra, hcomp, -, hadj, hraw, -, hrsh⟩ :=
    Vault.deposit_ok_reduces v amount isDonation t hpos r hok
  obtain ⟨_, -, -, hraz⟩ := roundedDepositAmount_rounded v amount ra hra
  obtain ⟨hra1, -, hra3⟩ := v.roundedDepositAmount_form amount ra hc hty hra
  have hrac : ra.Canonical := hra1.resolve_right (by simp [hraz])
  have hrapos : 0 < ra.toRat :=
    lt_of_le_of_ne hra3 (Ne.symm (STAmount.toRat_ne_zero ra (ne_of_beq_false hraz)))
  obtain ⟨hic, h64, h0⟩ := computeDeposit_shares_form v ra isDonation amounts hrac hrapos hcomp
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hcast' := RawVault.WF.toExact_sharesTotal r.vault'.toRawVault r.vault'.wf
  rw [hrsh] at hSsz ⊢
  have hst := Vault.adjustAssetsAndShares_sharesTotal v _ _ raw
    (Or.inl (hic.canonical (by rw [h64]; decide))) hic.den_eq_one
    (by linarith [v.wf.sharesTotal_nonneg]) (by rw [← hcast]; linarith) hadj
  have hST : r.vault'.sharesTotal = raw.sharesTotal := congrArg RawVault.sharesTotal hraw
  rw [hcast', show r.vault'.toRawVault.sharesTotal = raw.sharesTotal from hST, hst, hcast]

/-- A deposit into an Open-zone vault adds exactly its charge to the cash, and the vault stays
in the Open zone. -/
lemma Vault.deposit_openZone (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hz : v.OpenZone) (r : VaultWithAmounts)
    (hok : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.assets.toRat ∧ r.vault'.OpenZone := by
  obtain ⟨ra, amounts, raw, hra, hcomp, hin, hadj, hraw, hras, -⟩ :=
    Vault.deposit_ok_reduces v amount isDonation t hpos r hok
  have hmax := Vault.maxValue_fits_of_canonical v amount hc hty
  obtain ⟨hra1, hra2, -⟩ := v.roundedDepositAmount_form amount ra hc hty hra
  obtain ⟨hac, -, -⟩ := computeDeposit_assets_form v ra isDonation amounts hra1 hra2 hmax hcomp
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  -- the charge is whole base units: the clamp puts it on a grid never finer than the base
  have hunits : ∃ j : ℕ, amounts.assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent := by
    cases isDonation
    · obtain ⟨assets, _, -, -, hs2a, -, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
      obtain ⟨hfa, hfty⟩ := sharesToAssetsDeposit_form v _ _ hmax hs2a
      exact clampToSumExponent_units _ _ _ _ hfa (by omega) (by omega)
        (fun hi => le_of_eq (hbint (by rw [← hfty]; exact hi))) hcl
    · obtain ⟨_, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
      exact clampToSumExponent_units _ _ _ _ hra1 (by omega) (by omega)
        (fun hi => le_of_eq (hbint (by rw [← hra2]; exact hi))) hcl
  obtain ⟨j, hj⟩ := hunits
  obtain ⟨k, hk, hkv⟩ := Vault.checkOpenLimit_openZone v hz _ hac j hj hin
  obtain ⟨haav, haar⟩ :=
    Vault.adjustAssetsAndShares_units v _ _ raw k hz hac ⟨j, by rw [hj]; push_cast; rfl⟩ hk hkv hadj
  obtain ⟨aa', st', hfr⟩ := Vault.adjustAssetsAndShares_frame v _ _ raw hadj
  have hv' := hraw.trans hfr
  have hAA : r.vault'.assetsAvailable = raw.assetsAvailable := congrArg RawVault.assetsAvailable hraw
  refine ⟨by rw [hAA, haav, ← hkv, hras], Vault.OpenZone.of_fields hz ((congrArg RawVault.assetsDeployed hv').trans rfl)
    ((congrArg RawVault.lossUnrealized hv').trans rfl) ((congrArg RawVault.yieldUnrealized hv').trans rfl)
    ((congrArg RawVault.numericType hv').trans rfl) ((congrArg RawVault.scale hv').trans rfl) ⟨k, hk, by rw [hAA, haav]⟩
    (by rw [hAA]; exact haar)⟩

/-- A debit of whole base units the cash covers leaves an Open-zone cash: the update is exact,
whole base units within the limit, stored exactly. -/
lemma Vault.debit_openZone (v : Vault) (payout shares : STAmount) (raw : RawVault) (hz : v.OpenZone)
    (hc : payout.CanonicalOrZero) (j : ℕ) (hj : payout.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hle : payout.toRat ≤ v.assetsAvailable.toRat)
    (hadj : (v.adjustAssetsAndShares payout.operator_neg shares).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat = v.assetsAvailable.toRat - payout.toRat ∧
      (∃ k : ℕ, k ≤ 9 * 10 ^ 15 ∧ raw.assetsAvailable.toRat = (k : ℚ) * (10 : ℚ) ^ v.baseExponent) ∧
      STAmount.isRounded v.numericType raw.assetsAvailable = false := by
  obtain ⟨kA, hkA, hAv⟩ := hz.cash
  have hpow : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hjk : j ≤ kA := by
    have : (j : ℚ) * 10 ^ v.baseExponent ≤ (kA : ℚ) * 10 ^ v.baseExponent := by rw [← hj, ← hAv]; exact hle
    exact_mod_cast le_of_mul_le_mul_right this hpow
  have hnew : v.assetsAvailable.toRat + payout.operator_neg.toRat =
      ((kA - j : ℕ) : ℚ) * (10 : ℚ) ^ v.baseExponent := by
    rw [STAmount.operator_neg_toRat, hAv, hj, Nat.cast_sub hjk]; ring
  obtain ⟨haav, haar⟩ := Vault.adjustAssetsAndShares_units v _ _ raw (kA - j) hz hc.operator_neg
    ⟨-(j : ℤ), by rw [STAmount.operator_neg_toRat, hj]; push_cast; ring⟩ (by omega) hnew hadj
  refine ⟨?_, ⟨kA - j, by omega, haav⟩, haar⟩
  rw [haav, ← hnew, STAmount.operator_neg_toRat]; ring

/-- A successful withdrawal, read off the code: the record its cash update wrote. -/
lemma Vault.withdraw_ok_reduces (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    ∃ raw : RawVault, (v.adjustAssetsAndShares r.assets.operator_neg r.shares.operator_neg).run = .ok (.ok raw) ∧
      r.vault'.toRawVault = raw := by
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals exact ⟨_, ‹_›, (RawVault.to_lawful_ok ‹_›).1⟩

/-- A successful withdrawal leaves the share total less the burned shares, exactly. -/
lemma Vault.withdraw_sharesTotal (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.vault'.sharesTotal.toRat = v.sharesTotal.toRat - r.shares.toRat := by
  obtain ⟨raw, hadj, hraw⟩ := Vault.withdraw_ok_reduces v amount waive t hpos r hok
  obtain ⟨hsc, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  have hshc : r.shares.Canonical := hsc.canonical (by rw [hs64]; decide)
  have habs := STAmount.IntegralCanonical.abs_le_int64 hsc hs64
  rw [abs_of_pos hspos] at habs
  have hST0 := v.wf.sharesTotal_nonneg
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSTle : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1 := by
    have h := v.exact.sharesTotal_representable
    norm_num at h ⊢
    exact_mod_cast h
  have h := Vault.adjustAssetsAndShares_sharesTotal v _ _ raw
    (STAmount.CanonicalOrZero.operator_neg (Or.inl hshc))
    (by rw [STAmount.operator_neg_toRat]; simpa using hsc.den_eq_one)
    (by rw [STAmount.operator_neg_toRat]; linarith)
    (by rw [STAmount.operator_neg_toRat, ← hcast]; linarith) hadj
  rw [STAmount.operator_neg_toRat] at h
  rw [show r.vault'.sharesTotal = raw.sharesTotal from congrArg RawVault.sharesTotal hraw, h]
  ring

/-- A successful withdrawal leaves the exact share total less the burned shares. -/
lemma Vault.withdraw_exact_sharesTotal (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat := by
  rw [RawVault.WF.toExact_sharesTotal r.vault'.toRawVault r.vault'.wf,
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  exact Vault.withdraw_sharesTotal v amount waive t hpos hc hty r hok

/-- The payout of a successful withdrawal from an Open-zone vault is a canonical-or-zero amount
of whole base units that the cash covers, debited by the cash update the vault records. -/
lemma Vault.withdraw_payout_units (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.assets.CanonicalOrZero ∧ (∃ j : ℕ, r.assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent) ∧
      r.assets.toRat ≤ v.assetsAvailable.toRat ∧ ∃ raw : RawVault,
        (v.adjustAssetsAndShares r.assets.operator_neg r.shares.operator_neg).run = .ok (.ok raw) ∧
          r.vault'.toRawVault = raw := by
  suffices H : r.assets.CanonicalOrZero ∧ (∃ j : ℕ, r.assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent) ∧
      r.assets.toRat ≤ v.assetsAvailable.toRat from
    ⟨H.1, H.2.1, H.2.2, Vault.withdraw_ok_reduces v amount waive t hpos r hok⟩
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- a 100% fee pays nothing
  all_goals try
    have hz := STAmount.zero_canonicalOrZero v.numericType
    exact ⟨hz.1, ⟨0, by rw [STAmount.zero_toRat _]; simp⟩,
      by rw [STAmount.zero_toRat _]; exact v.exact.assetsAvailable_nonneg⟩
  -- the final withdrawal pays all the cash, which the asset stores exactly
  all_goals try
    have hp : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok _ := ‹_›
    have hpc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1
    have hfe := Vault.final_payout_exact v _ hz.cashExact hmax hp
    obtain ⟨kA, -, hAv⟩ := hz.cash
    exact ⟨hpc, ⟨kA, by rw [hfe, hAv]⟩, le_of_eq hfe⟩
  -- the fee path pays the payout clamped onto the grid of the cash, which the cash covers
  all_goals try
    have hp : STAmount.ofNumber v.numericType _ .downward = .ok _ := ‹_›
    have hcl : clampToSumExponent v.assetsAvailable _ v.baseExponent = .ok _ := ‹_›
    obtain ⟨hpc, hpty⟩ := STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp
    have hcf := (clampToSumExponent_canonicalOrZero _ _ _ _ hpc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 hcl).1
    obtain ⟨j, hj⟩ := clampToSumExponent_units _ _ _ _ hpc.operator_neg v.baseExponent_range.1
      v.baseExponent_range.2 (fun hi => le_of_eq (v.baseExponent_bounds.2.2 (by
        unfold STAmount.integral at hi; rwa [(STAmount.operator_neg_fields _).1, hpty] at hi))) hcl
    have hkeep := Vault.payout_keeps_cash v _ _ hcf ‹_› ‹_›
    rw [STAmount.operator_neg_toRat] at hkeep
    exact ⟨hcf, ⟨j, hj⟩, by linarith⟩
  -- a zero payout skips the fee
  all_goals
    have hnf : STAmount.operator_eq _ _ = false := ‹_›
    have hzs : ¬ (STAmount.operator_eq _ _ = false ∧ STAmount.isZero _ = false) := ‹_›
    have hz0 := Bool.of_not_eq_false (fun h => hzs ⟨hnf, h⟩)
    have h0 := (STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz0)
    exact ⟨Or.inr hz0, ⟨0, by rw [h0]; simp⟩, by rw [h0]; exact v.exact.assetsAvailable_nonneg⟩

/-- A withdrawal from an Open-zone vault subtracts exactly its payout from the cash, and the vault
stays in the Open zone. -/
lemma Vault.withdraw_openZone (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hz : v.OpenZone)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧ r.vault'.OpenZone := by
  obtain ⟨hc, ⟨j, hj⟩, hle, raw, hadj, hraw⟩ := Vault.withdraw_payout_units v amount waive t hpos hz hmax r hok
  obtain ⟨hval, hcash, hex⟩ := Vault.debit_openZone v _ _ raw hz hc j hj hle hadj
  obtain ⟨aa', st', hfr⟩ := Vault.adjustAssetsAndShares_frame v _ _ raw hadj
  have hAA : r.vault'.assetsAvailable = raw.assetsAvailable := congrArg RawVault.assetsAvailable hraw
  exact ⟨by rw [hAA, hval], Vault.OpenZone.of_cash_update hz aa' st' (hraw.trans hfr) (by rw [hAA]; exact hcash)
    (by rw [hAA]; exact hex)⟩

/-- A successful clawback, read off the code: the priced amounts, and the record the cash
update wrote. -/
lemma Vault.clawback_ok_reduces (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    ∃ (amounts : VaultAmounts) (raw : RawVault),
      (computeClawback v assets holderShares waive).run = .ok (.ok amounts) ∧
      (v.adjustAssetsAndShares amounts.assets.operator_neg amounts.shares.operator_neg).run = .ok (.ok raw) ∧
      r.vault'.toRawVault = raw ∧ r.assets = amounts.assets ∧ r.shares = amounts.shares := by
  simp only [Vault.clawback] at hok
  unfold_ter at hok
  walk_ok
  exact ⟨_, _, ‹_›, ‹_›, (RawVault.to_lawful_ok ‹_›).1, rfl, rfl⟩

/-- A successful clawback leaves the exact share total less the destroyed shares. -/
lemma Vault.clawback_exact_sharesTotal (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    (r.vault'.toExact.sharesTotal : ℚ) = v.toExact.sharesTotal - r.shares.toRat := by
  obtain ⟨amounts, raw, hcomp, hadj, hraw, -, hrsh⟩ := Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  obtain ⟨hic, h64, h0, -, -⟩ := computeClawback_amounts_form v _ _ waive _ hc hnn hhs hmax hcomp
  have hb := abs_le.mp (hic.abs_le_int64 h64)
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hcast' := RawVault.WF.toExact_sharesTotal r.vault'.toRawVault r.vault'.wf
  have hst := Vault.adjustAssetsAndShares_sharesTotal v _ _ raw
    (STAmount.CanonicalOrZero.operator_neg (Or.inl (hic.canonical (by rw [h64]; decide))))
    (by rw [STAmount.operator_neg_toRat, Rat.neg_den]; exact hic.den_eq_one)
    (by rw [STAmount.operator_neg_toRat]; linarith [v.wf.sharesTotal_nonneg])
    (by rw [STAmount.operator_neg_toRat]; linarith [v.sharesTotal_le_maxRep]) hadj
  have hST : r.vault'.sharesTotal = raw.sharesTotal := congrArg RawVault.sharesTotal hraw
  rw [hcast', show r.vault'.toRawVault.sharesTotal = raw.sharesTotal from hST, hst, hcast,
    STAmount.operator_neg_toRat, hrsh]
  ring

/-- The recovery of a clawback from an Open-zone vault is whole base units. -/
private lemma computeClawback_assets_units (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (amounts : VaultAmounts) (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat)
    (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hcomp : (computeClawback v assets holderShares waive).run = .ok (.ok amounts)) :
    ∃ j : ℕ, amounts.assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨rec, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v assets holderShares waive amounts hcomp
  obtain ⟨-, -, -, hrc, -, -⟩ := hpr.form hc hnn hhs hmax
  rcases hrec with ⟨hz, heq⟩ | ⟨-, hcl, -⟩
  · refine ⟨0, ?_⟩
    rw [heq, (STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz)]; simp
  · -- the recovery is in the vault's asset, so an integral one sits at the integral base exponent
    have hrty : rec.mNumericType = v.numericType := by
      cases hpr with
      | direct _ _ _ _ hs2a _ _ => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).2
      | capped _ _ _ _ _ _ _ _ _ _ _ _ _ hs2a _ _ => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).2
    exact clampToSumExponent_units _ _ _ _ hrc.operator_neg v.baseExponent_range.1 v.baseExponent_range.2
      (fun hi => le_of_eq (v.baseExponent_bounds.2.2 (by
        unfold STAmount.integral at hi; rwa [(STAmount.operator_neg_fields _).1, hrty] at hi))) hcl

/-- A clawback recovers a nonnegative amount. -/
lemma Vault.clawback_assets_nonneg (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    0 ≤ r.assets.toRat := by
  obtain ⟨amounts, -, hcomp, -, -, hras, -⟩ := Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  obtain ⟨j, hj⟩ := computeClawback_assets_units v _ _ waive _ hc hnn hhs hmax hcomp
  rw [hras, hj]
  positivity

/-- A clawback from an Open-zone vault subtracts exactly its recovery from the cash, and the
vault stays in the Open zone. -/
lemma Vault.clawback_openZone (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hc : assets.CanonicalOrZero) (hhs : holderShares.ShareBalance)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hz : v.OpenZone) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    r.vault'.assetsAvailable.toRat = v.assetsAvailable.toRat - r.assets.toRat ∧ r.vault'.OpenZone := by
  obtain ⟨amounts, raw, hcomp, hadj, hraw, hras, -⟩ := Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  obtain ⟨-, -, -, hac, hcash0⟩ := computeClawback_amounts_form v _ _ waive _ hc hnn hhs hmax hcomp
  obtain ⟨j, hj⟩ := computeClawback_assets_units v _ _ waive _ hc hnn hhs hmax hcomp
  rw [STAmount.operator_neg_toRat] at hcash0
  obtain ⟨hval, hcash, hex⟩ := Vault.debit_openZone v _ _ raw hz hac j hj (by linarith) hadj
  obtain ⟨aa', st', hfr⟩ := Vault.adjustAssetsAndShares_frame v _ _ raw hadj
  have hAA : r.vault'.assetsAvailable = raw.assetsAvailable := congrArg RawVault.assetsAvailable hraw
  exact ⟨by rw [hAA, hval, hras], Vault.OpenZone.of_cash_update hz aa' st' (hraw.trans hfr)
    (by rw [hAA]; exact hcash) (by rw [hAA]; exact hex)⟩

/-- A burn keeps the cash, so the vault stays in the Open zone. -/
lemma Vault.burnShares_openZone (v : Vault) (sharesDestroyed : STAmount) (v' : Vault) (hz : v.OpenZone)
    (hok : (v.burnShares sharesDestroyed).run = .ok (.ok v')) : v'.OpenZone := by
  obtain ⟨st', hv'⟩ := Vault.burnShares_frame v sharesDestroyed v' hok
  obtain ⟨k, hk, hkv⟩ := hz.cash
  have hAA : v'.assetsAvailable = v.assetsAvailable := (congrArg RawVault.assetsAvailable hv').trans rfl
  exact Vault.OpenZone.of_fields hz ((congrArg RawVault.assetsDeployed hv').trans rfl)
    ((congrArg RawVault.lossUnrealized hv').trans rfl) ((congrArg RawVault.yieldUnrealized hv').trans rfl)
    ((congrArg RawVault.numericType hv').trans rfl) ((congrArg RawVault.scale hv').trans rfl)
    ⟨k, hk, by rw [hAA]; exact hkv⟩ (by rw [hAA]; exact hz.cashExact)

/-- An update keeps every balance, so the vault stays in the Open zone. -/
lemma Vault.update_openZone (v : Vault) (assetsMaximum : Option Number) (blockDeposit unblockDeposit : Bool)
    (v' : Vault) (hz : v.OpenZone) (hok : v.update assetsMaximum blockDeposit unblockDeposit = .ok v') :
    v'.OpenZone := by
  obtain ⟨_, _, hv'⟩ := Vault.update_frame v assetsMaximum blockDeposit unblockDeposit v' hok
  obtain ⟨k, hk, hkv⟩ := hz.cash
  have hAA : v'.assetsAvailable = v.assetsAvailable := (congrArg RawVault.assetsAvailable hv').trans rfl
  exact Vault.OpenZone.of_fields hz ((congrArg RawVault.assetsDeployed hv').trans rfl)
    ((congrArg RawVault.lossUnrealized hv').trans rfl) ((congrArg RawVault.yieldUnrealized hv').trans rfl)
    ((congrArg RawVault.numericType hv').trans rfl) ((congrArg RawVault.scale hv').trans rfl)
    ⟨k, hk, by rw [hAA]; exact hkv⟩ (by rw [hAA]; exact hz.cashExact)

/-- A created vault starts empty, in the Open zone. -/
lemma Vault.create_openZone {scale : Option UInt8} {assetsMaximum : Option Number}
    {schedule : Option VaultSchedule} {earlyExitFeeRate : Option TenthBips32}
    {ownerCanBlockDeposit : Bool} {nt : NumericType} {v : Vault}
    (h : Vault.create scale assetsMaximum schedule earlyExitFeeRate ownerCanBlockDeposit nt = .ok v) :
    v.OpenZone := by
  have hv := Vault.create_ok_toRawVault h
  have hAA : v.assetsAvailable = Number.zero := (congrArg RawVault.assetsAvailable hv).trans rfl
  exact ⟨(congrArg RawVault.assetsDeployed hv).trans rfl, (congrArg RawVault.lossUnrealized hv).trans rfl,
    (congrArg RawVault.yieldUnrealized hv).trans rfl, ⟨0, by norm_num, by rw [hAA, Number.toRat_zero]; simp⟩,
    by rw [hAA]; exact STAmount.isRounded_zero _⟩

end XRPL.Model.SingleAssetVault
