import XRPL.Properties.Vault.Proofs.WithdrawPricing.Core

/-! # Accuracy of the `sharesToAssetsWithdraw` pricing

The payout is packed `.to_nearest`, so it can exceed the shares' worth by half a ULP of
the result on top of the interior stage error. -/

namespace XRPL.Model.SingleAssetVault.WdPrice

open XRPL.Model.Protocol

lemma ideal_eq (v : Vault) (w : Bool) (s : ℚ) :
    v.idealAssetsWithdraw w s = navQ v w * s / v.sharesTotal.toRat := by
  unfold RawVault.idealAssetsWithdraw
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]

lemma nav_exact (v : Vault) (w : Bool) (nav : Number) (hnav : v.WithdrawNavExact w)
    (hsub : v.assetsTotal.operator_sub (lossOp v w) .to_nearest = .ok nav) :
    nav.toRat = navQ v w := by
  obtain ⟨nv, hnv, hq⟩ := hnav
  have : v.assetsTotal.operator_sub (lossOp v w) .to_nearest = .ok nv := by
    cases w <;> exact hnv
  rw [show nav = nv from Except.ok.inj (hsub.symm.trans this)]; exact hq

lemma eta_le : (12 / (2 ^ 63 - 3) : ℚ) ≤ depositε := by
  rw [WdAcc.depositε_val]; norm_num

lemma toRat_of_mValue_zero (p : STAmount) (h : p.mValue = 0) : p.toRat = 0 :=
  (STAmount.toRat_eq_zero_iff _).mpr h

lemma frac_of_not_integral (v : Vault) (h : ¬ v.numericType.isIntegral = true) :
    v.numericType = .fractional := by
  cases hnt : v.numericType with
  | fractional => rfl
  | integral => rw [hnt] at h; exact absurd rfl h

/-- The priced payout exceeds the shares' worth by at most the stage error plus half a
unit on an integral vault, or by a `½ · 10⁻¹⁵ + 2 · 10⁻¹⁸` slice of the worth on a
fractional one. -/
lemma price_le_gated (v : Vault) (sh p : STAmount) (w : Bool) (hnn : 0 ≤ sh.toRat)
    (hc : sh.Canonical) (hnav : v.WithdrawNavExact w)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) :
    p.toRat ≤ (if v.numericType.isIntegral then
        v.idealAssetsWithdraw w sh.toRat * (1 + depositε) + 1 / 2
      else v.idealAssetsWithdraw w sh.toRat *
        (1 + (1 / 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ) + 2 * (10 : ℚ) ^ (-18 : ℤ))) := by
  obtain ⟨nav, hsub, -, hpnn, hcase⟩ := price_spec v sh p w hnn hc hok
  have hI0 := WdAcc.ideal_nonneg v w _ hnn
  have hε : depositε = 1 / 100000000000000000 := WdAcc.depositε_val
  have h15 : (1 / 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ) + 2 * (10 : ℚ) ^ (-18 : ℤ) =
      1 / 2000000000000000 + 2 / 1000000000000000000 := by norm_num
  rw [add_assoc 1, h15, hε]
  by_cases hp0 : p.mValue = 0
  · rw [toRat_of_mValue_zero _ hp0]
    split <;> positivity
  rcases hcase with hp0' | ⟨-, -, an, -, hb, hh⟩
  · exact absurd hp0' hp0
  rw [nav_exact v w nav hnav hsub, ← ideal_eq] at hb
  set I := v.idealAssetsWithdraw w sh.toRat
  obtain ⟨-, hb2⟩ := abs_le.mp hb
  obtain ⟨-, hh2⟩ := abs_le.mp hh
  split
  · rename_i hint
    obtain ⟨-, hoff, -⟩ := WdAcc.price_integral_shape v sh p w hint hok
    rw [show p.exponent = 0 from hoff, zpow_zero] at hh2
    nlinarith
  · rename_i hint
    have hpc : p.IOUCanonical := by
      rcases (WdAcc.price_fczr v sh p w (frac_of_not_integral v hint) hc hok).2 with h | h
      · exact h
      · exact absurd h hp0
    have hU : (10 : ℚ) ^ (15 : ℤ) * (10 : ℚ) ^ p.exponent ≤ p.toRat := by
      rw [← abs_of_nonneg hpnn, STAmount.abs_toRat]
      have h1 : ((10 ^ 15 : ℕ) : ℚ) ≤ (p.mValue.toNat : ℚ) := by exact_mod_cast hpc.mant_lo
      have : (10 : ℚ) ^ (15 : ℤ) = ((10 ^ 15 : ℕ) : ℚ) := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h1015 : (10 : ℚ) ^ (15 : ℤ) = 1000000000000000 := by norm_num
    rw [h1015] at hU
    have hc' : (1 + 12 / (2 ^ 63 - 3) : ℚ) * (2000000000000000 / 1999999999999999) ≤
        1 + (1 / 2000000000000000 + 2 / 1000000000000000000) := by norm_num
    have hp : p.toRat ≤ (1 + 12 / (2 ^ 63 - 3)) * I * (2000000000000000 / 1999999999999999) := by
      nlinarith
    nlinarith

/-- `toNumber` of the priced payout is normalized and value-exact. -/
lemma price_toNumber (v : Vault) (sh p : STAmount) (w : Bool) (an : Number) (hc : sh.Canonical)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) (han : p.toNumber .to_nearest = .ok an) :
    an.isNormalized ∧ an.toRat = p.toRat := by
  by_cases hint : v.numericType.isIntegral = true
  · obtain ⟨hpnt, hpoff, hpmv⟩ := WdAcc.price_integral_shape v sh p w hint hok
    obtain ⟨sn, hsn, hsnv, hsnn, -⟩ := STAmount.toNumber_offset_zero_exact p .to_nearest
      (by rw [hpnt]; exact hint) hpoff hpmv
    obtain rfl := Except.ok.inj (hsn.symm.trans han)
    exact ⟨hsnn, hsnv⟩
  · rcases (WdAcc.price_fczr v sh p w (frac_of_not_integral v hint) hc hok).2 with h | h
    · obtain ⟨sn, hsn, hsnv, hsnn⟩ := STAmount.toNumber_iou_exact p .to_nearest h
      obtain rfl := Except.ok.inj (hsn.symm.trans han)
      exact ⟨hsnn, hsnv⟩
    · rw [STAmount.toNumber_zero_eq p _ an h han, Number.toRat_zero, toRat_of_mValue_zero _ h]
      exact ⟨Or.inl rfl, rfl⟩

/-- Under the gated margin the `assetsAvailable` guard does not fire. -/
lemma guard_false (v : Vault) (sh p : STAmount) (an : Number) (w : Bool) (hnn : 0 ≤ sh.toRat)
    (hc : sh.Canonical) (hnav : v.WithdrawNavExact w)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) (han : p.toNumber .to_nearest = .ok an)
    (hmargin : (if v.numericType.isIntegral then
        v.idealAssetsWithdraw w sh.toRat * (1 + depositε) + 1 / 2
      else v.idealAssetsWithdraw w sh.toRat *
        (1 + (1 / 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ) + 2 * (10 : ℚ) ^ (-18 : ℤ))) ≤
      v.toExact.assetsAvailable) :
    v.assetsAvailable.operator_lt an = false := by
  obtain ⟨hann, hanv⟩ := price_toNumber v sh p w an hc hok han
  have hle := price_le_gated v sh p w hnn hc hnav hok
  cases hlt : v.assetsAvailable.operator_lt an with
  | false => rfl
  | true =>
    have := (operator_lt_iff _ _ v.wf.assetsAvailable_norm hann).mp hlt
    have hA : v.toExact.assetsAvailable = v.assetsAvailable.toRat := rfl
    linarith
end XRPL.Model.SingleAssetVault.WdPrice

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WdPrice

/-- Proof of `Vault.sharesToAssetsWithdraw_bounds`. -/
lemma Vault.sharesToAssetsWithdraw_bounds_proof (v : Vault) (shares assets : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    0 ≤ assets.toRat ∧
    assets.toRat ≤ v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) +
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent ∧
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * depositε +
          (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent) := by
  obtain ⟨nav, hsub, -, hpnn, hcase⟩ := price_spec v shares assets waiveUnrealizedLoss hnn hc hok
  have hN := nav_exact v waiveUnrealizedLoss nav hnav hsub
  have hI0 := WdAcc.ideal_nonneg v waiveUnrealizedLoss _ hnn
  have hU : (0 : ℚ) < (10 : ℚ) ^ assets.exponent := zpow_pos (by norm_num) _
  have hε : (0 : ℚ) ≤ depositε := by rw [WdAcc.depositε_val]; norm_num
  refine ⟨hpnn, ?_⟩
  rcases hcase with hp0 | ⟨-, -, an, -, hb, hh⟩
  · rw [toRat_of_mValue_zero _ hp0]
    refine ⟨by nlinarith, fun hz => ?_⟩
    simp [STAmount.isZero, hp0] at hz
  rw [hN, ← ideal_eq] at hb
  set I := v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hh1, hh2⟩ := abs_le.mp hh
  have hIe : I * (12 / (2 ^ 63 - 3)) ≤ I * depositε := mul_le_mul_of_nonneg_left eta_le hI0
  exact ⟨by nlinarith, fun _ => by nlinarith⟩

/-- Proof of `Vault.sharesToAssetsWithdraw_total`. -/
lemma Vault.sharesToAssetsWithdraw_total_proof (v : Vault) (shares assets : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hnn : 0 ≤ shares.toRat) (hc : shares.Canonical)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    assets.toRat ≤
      (v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat +
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ)) * (1 + depositε) +
      (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent ∧
    (assets.isZero = false →
      v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat - assets.toRat ≤
        v.navSlack * shares.toRat / (v.toExact.sharesTotal : ℚ) * (1 + depositε) +
          (1 / 2 : ℚ) * (10 : ℚ) ^ assets.exponent) := by
  obtain ⟨nav, hsub, hN0, hpnn, hcase⟩ := price_spec v shares assets waiveUnrealizedLoss hnn hc hok
  rw [RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, ideal_eq]
  have hU : (0 : ℚ) < (10 : ℚ) ^ assets.exponent := zpow_pos (by norm_num) _
  have hε : depositε = 1 / 100000000000000000 := WdAcc.depositε_val
  have hslack : v.navSlack = depositε * (v.assetsTotal.toRat + v.assetsTotal.toRat) := rfl
  set a := v.assetsTotal.toRat
  have ha0 : 0 ≤ a := v.exact.assetsTotal_nonneg
  have hq0 := navQ_nonneg v waiveUnrealizedLoss
  have hqa := navQ_le v waiveUnrealizedLoss
  set q := navQ v waiveUnrealizedLoss
  set ST := v.sharesTotal.toRat
  have hST0 : 0 ≤ ST := v.wf.sharesTotal_nonneg
  set s := shares.toRat
  have hk0 : 0 ≤ s / ST := div_nonneg hnn hST0
  have hI : q * s / ST = q * (s / ST) := by ring
  have hS : v.navSlack * s / ST = v.navSlack * (s / ST) := by ring
  rw [hI, hS, hslack, hε]
  rw [hε] at hslack
  rcases hcase with hp0 | ⟨hm, -, an, -, hb, hh⟩
  · rw [toRat_of_mValue_zero _ hp0]
    refine ⟨?_, fun hz => by simp [STAmount.isZero, hp0] at hz⟩
    have : 0 ≤ q * (s / ST) := mul_nonneg hq0 hk0
    have : 0 ≤ 1 / 100000000000000000 * (a + a) * (s / ST) := by positivity
    nlinarith
  have hnw := nav_within v waiveUnrealizedLoss nav hsub hm
  obtain ⟨hw1, hw2⟩ := abs_le.mp hnw
  have hP : nav.toRat * s / ST = nav.toRat * (s / ST) := by ring
  rw [hP] at hb
  set N := nav.toRat
  set k := s / ST
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  obtain ⟨hh1, hh2⟩ := abs_le.mp hh
  have hNk : 0 ≤ N * k := mul_nonneg hN0 hk0
  have hqk : 0 ≤ q * k := mul_nonneg hq0 hk0
  have hak : q * k ≤ a * k := mul_le_mul_of_nonneg_right hqa hk0
  have hNq : N * k ≤ q * k + q * k * (6 / (2 ^ 63 - 3)) := by nlinarith
  have hNq' : q * k - q * k * (6 / (2 ^ 63 - 3)) ≤ N * k := by nlinarith
  constructor
  · nlinarith
  · intro _; nlinarith

/-- Proof of `Vault.withdraw_under_available`. -/
lemma Vault.withdraw_under_available_proof (v : Vault) (shares : STAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hpos : 0 < shares.toRat) (hc : shares.Canonical)
    (hnav : v.WithdrawNavExact waiveUnrealizedLoss)
    (hok : v.withdraw (.vaultShares shares) waiveUnrealizedLoss hpos = .ok r)
    (hmargin : (if v.numericType.isIntegral then
        v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat * (1 + depositε) + 1 / 2
      else v.idealAssetsWithdraw waiveUnrealizedLoss shares.toRat *
        (1 + (1 / 2 : ℚ) * (10 : ℚ) ^ (-15 : ℤ) + 2 * (10 : ℚ) ^ (-18 : ℤ))) ≤
      v.toExact.assetsAvailable) :
    r.error ≠ some .tecINSUFFICIENT_FUNDS := by
  intro hbad
  simp only [Vault.withdraw, computeWithdrawByShares, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hok
  walk_ok
  all_goals first
    | exact absurd ‹v.assetsAvailable.operator_lt _ = true› (by
        rw [guard_false v shares _ _ waiveUnrealizedLoss hpos.le hc hnav ‹_› ‹_› hmargin]
        decide)
    | simp_all [WithdrawResult.rejected]

end XRPL.Model.SingleAssetVault
