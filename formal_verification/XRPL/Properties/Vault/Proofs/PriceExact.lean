import XRPL.Properties.Vault.Proofs.WithdrawPricing.Core
import XRPL.Properties.Vault.Proofs.DepositTight.Price
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.NumberBridge

/-! # Exact prices

When the worth and the worth times the share total both fit a 19-digit `Number`, the two `.to_nearest` stages of a
price lose nothing. The price is then the worth rounded once to the asset's own grid, within half a unit. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A `mul` then `div` pipeline whose product and quotient are both normalized `Number`s returns the quotient. -/
lemma pipe_exact (x sn NS an ST : Number) (hx : x.isNormalized) (hsn : sn.isNormalized) (hST : ST.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hsm : sn.mantissa_ ≠ 0) (hSTm : ST.mantissa_ ≠ 0)
    (hmul : x.operator_mul sn .to_nearest = .ok NS) (hdiv : NS.operator_div ST .to_nearest = .ok an)
    (hprod : ∃ p : Number, p.isNormalized ∧ p.toRat = x.toRat * sn.toRat)
    (hquot : ∃ q : Number, q.isNormalized ∧ q.toRat = x.toRat * sn.toRat / ST.toRat)
    (hpos : 0 < x.toRat * sn.toRat / ST.toRat) :
    an.isNormalized ∧ an.toRat = x.toRat * sn.toRat / ST.toRat := by
  obtain ⟨p, hpn, hpv⟩ := hprod
  have hNSv : NS.toRat = x.toRat * sn.toRat :=
    Number.RoundsToRepresentable.eq_of_representable NS _ (operator_mul_rounded_to_nearest _ _ _ hx hsn hmul)
      p hpn hpv
  have hxs : x.toRat * sn.toRat ≠ 0 := fun h => by rw [h, zero_div] at hpos; exact lt_irrefl _ hpos
  have hNSm : NS.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hNSv]; exact hxs)
  have hNSn := operator_mul_result_isNormalized _ _ _ _ hx hsn hxm hsm hmul hNSm
  obtain ⟨q, hqn, hqv⟩ := hquot
  have h := operator_div_rounded_to_nearest _ _ _ hNSn hST hdiv
  rw [hNSv] at h
  have hanv := Number.RoundsToRepresentable.eq_of_representable an _ h q hqn hqv
  have hanm : an.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hanv]; exact ne_of_gt hpos)
  exact ⟨operator_div_result_isNormalized _ _ _ _ hNSn hST hNSm hSTm hdiv hanm, hanv⟩

/-- A withdrawal price of shares with a positive worth `W` at the computed net asset value, whose product and quotient
are exact `Number`s, converts `W` itself to the asset. -/
lemma WdPrice.price_exact (v : Vault) (sh p : STAmount) (w : Bool) (nav : Number)
    (hnav : v.assetsTotalForWithdrawal w = .ok nav) (hc : sh.Canonical)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p)
    (hexact : (∃ q : Number, q.isNormalized ∧
        q.toRat = v.idealAssetsWithdrawAt nav.toRat sh.toRat * (v.toExact.sharesTotal : ℚ)) ∧
      ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealAssetsWithdrawAt nav.toRat sh.toRat)
    (hW : 0 < v.idealAssetsWithdrawAt nav.toRat sh.toRat) :
    ∃ an : Number, an.isNormalized ∧ an.negative_ = false ∧
      an.toRat = v.idealAssetsWithdrawAt nav.toRat sh.toRat ∧
      STAmount.ofNumber v.numericType an .to_nearest = .ok p := by
  obtain ⟨nav', hsub, hnavn, hcase⟩ := WdPrice.price_cases v sh p w hok
  rw [hnav, Except.ok.injEq] at hsub
  subst hsub
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hideal : v.idealAssetsWithdrawAt nav.toRat sh.toRat = nav.toRat * sh.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealAssetsWithdrawAt; rw [hcast]
  rw [hideal] at hW hexact ⊢
  rw [hcast] at hexact
  rcases hcase with ⟨hm0, -⟩ | ⟨hm, sn, NS, an, hsn, hmul, hdiv, hof⟩
  · rw [Number.toRat_eq_zero_of_mantissa_zero nav hm0, zero_mul, zero_div] at hW
    exact absurd hW (lt_irrefl 0)
  obtain ⟨sn0, hsn0, hsnv, hsnn⟩ := STAmount.toNumber_exact_canonical sh .to_nearest
    (STAmount.Canonical.exactCanonical sh hc)
  obtain rfl := Except.ok.inj (hsn0.symm.trans hsn)
  have hST0 : v.sharesTotal.toRat ≠ 0 := fun h => by rw [h, div_zero] at hW; exact lt_irrefl _ hW
  have hsh0 : sh.toRat ≠ 0 := fun h => by rw [h, mul_zero, zero_div] at hW; exact lt_irrefl _ hW
  obtain ⟨⟨p₁, hp₁n, hp₁v⟩, ⟨q₁, hq₁n, hq₁v⟩⟩ := hexact
  rw [div_mul_cancel₀ _ hST0] at hp₁v
  rw [← hsnv] at hp₁v hq₁v hW
  obtain ⟨hann, hanv⟩ := pipe_exact nav sn0 NS an v.sharesTotal hnavn hsnn v.wf.sharesTotal_norm hm
    (Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsnv]; exact hsh0))
    (Number.mantissa_ne_zero_of_toRat_ne_zero hST0) hmul hdiv ⟨p₁, hp₁n, hp₁v⟩ ⟨q₁, hq₁n, hq₁v⟩ hW
  refine ⟨an, hann, Number.negative_false_of_pos an (by rw [hanv]; exact hW), by rw [hanv, hsnv], hof⟩

/-- A nonzero withdrawal price whose product and quotient are exact `Number`s is within half a unit of its own last
digit of the shares' worth at the computed net asset value. -/
lemma WdPrice.price_exact_half (v : Vault) (sh p : STAmount) (w : Bool) (nav : Number)
    (hnav : v.assetsTotalForWithdrawal w = .ok nav) (hnn : 0 ≤ sh.toRat) (hc : sh.Canonical)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p) (hp : p.isZero = false)
    (hexact : (∃ q : Number, q.isNormalized ∧
        q.toRat = v.idealAssetsWithdrawAt nav.toRat sh.toRat * (v.toExact.sharesTotal : ℚ)) ∧
      ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealAssetsWithdrawAt nav.toRat sh.toRat) :
    |p.toRat - v.idealAssetsWithdrawAt nav.toRat sh.toRat| ≤ 1 / 2 * (10 : ℚ) ^ p.exponent := by
  have hpm : p.mValue ≠ 0 := by simpa [STAmount.isZero] using hp
  -- a nonzero price comes from a positive worth
  obtain ⟨nav', hnav', -, -, hcase⟩ := WdPrice.price_spec v sh p w hnn hc hok
  rw [hnav, Except.ok.injEq] at hnav'
  subst hnav'
  obtain ⟨-, -, an₀, han₀, hb, -, -, -⟩ := hcase.resolve_left hpm
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hideal : v.idealAssetsWithdrawAt nav.toRat sh.toRat = nav.toRat * sh.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealAssetsWithdrawAt; rw [hcast]
  have hW : 0 < v.idealAssetsWithdrawAt nav.toRat sh.toRat := by
    rw [hideal]
    by_contra h
    push Not at h
    have hε : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
    obtain ⟨-, h2⟩ := abs_le.mp hb
    nlinarith
  obtain ⟨an, hann, hneg, hanv, hof⟩ := WdPrice.price_exact v sh p w nav hnav hc hok hexact hW
  rw [← hanv]
  exact (WdPrice.ofNumber_half v.numericType an p hann hneg hof hpm).1

/-- An integral withdrawal price whose product and quotient are exact `Number`s is within half a unit of the shares'
worth at the computed net asset value, a zero price included. -/
lemma WdPrice.price_exact_integral (v : Vault) (sh p : STAmount) (w : Bool) (nav : Number)
    (hint : v.numericType.isIntegral = true)
    (hnav : v.assetsTotalForWithdrawal w = .ok nav) (hnn : 0 ≤ sh.toRat) (hc : sh.Canonical)
    (hok : v.sharesToAssetsWithdraw sh w = .ok p)
    (hexact : (∃ q : Number, q.isNormalized ∧
        q.toRat = v.idealAssetsWithdrawAt nav.toRat sh.toRat * (v.toExact.sharesTotal : ℚ)) ∧
      ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealAssetsWithdrawAt nav.toRat sh.toRat) :
    |p.toRat - v.idealAssetsWithdrawAt nav.toRat sh.toRat| ≤ 1 / 2 := by
  have hW0 : 0 ≤ v.idealAssetsWithdrawAt nav.toRat sh.toRat := by
    unfold RawVault.idealAssetsWithdrawAt
    exact div_nonneg (mul_nonneg (Vault.assetsTotalForWithdrawal_nonneg v w nav hnav).2 hnn) (Nat.cast_nonneg _)
  rcases lt_or_eq_of_le hW0 with hW | hW
  · obtain ⟨an, hann, hneg, hanv, hof⟩ := WdPrice.price_exact v sh p w nav hnav hc hok hexact hW
    rw [← hanv]
    exact STAmount.ofNumber_integral_within_half v.numericType an p hint hann hneg hof
  -- a zero worth prices nothing
  obtain ⟨nav', hnav', -, hp0, hcase⟩ := WdPrice.price_spec v sh p w hnn hc hok
  rw [hnav, Except.ok.injEq] at hnav'
  subst hnav'
  rw [← hW]
  rcases hcase with hpm | ⟨-, -, an₀, han₀, hb, -, -, -⟩
  · rw [(STAmount.toRat_eq_zero_iff _).mpr hpm]; norm_num
  · have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have hideal : v.idealAssetsWithdrawAt nav.toRat sh.toRat = nav.toRat * sh.toRat / v.sharesTotal.toRat := by
      unfold RawVault.idealAssetsWithdrawAt; rw [hcast]
    rw [← hideal, ← hW, zero_mul, sub_zero, abs_le] at hb
    linarith [hb.2]

/-- A nonempty deposit charge whose product and quotient are exact `Number`s converts the issued shares' worth at the
computed total itself to the asset. -/
lemma DepTight.charge_exact (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64) (hshpos : 0 < shares.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN) (hmz : navN.mantissa_ ≠ 0)
    (hsad : sharesToAssetsDeposit v shares = .ok c)
    (hexact : (∃ q : Number, q.isNormalized ∧
        q.toRat = v.idealChargeDepositAt navN.toRat shares.toRat * (v.toExact.sharesTotal : ℚ)) ∧
      ∃ q : Number, q.isNormalized ∧ q.toRat = v.idealChargeDepositAt navN.toRat shares.toRat) :
    ∃ Q : Number, Q.isNormalized ∧ Q.negative_ = false ∧
      Q.toRat = v.idealChargeDepositAt navN.toRat shares.toRat ∧
      STAmount.ofNumber v.numericType Q .to_nearest = .ok c := by
  have hnav_pos : 0 < navN.toRat := (Vault.assetsTotal_pos v navN hat hmz).2
  have hST_pos : 0 < v.sharesTotal.toRat := lt_of_lt_of_le one_pos (Vault.sharesTotal_one_le v navN hat hmz)
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hideal : v.idealChargeDepositAt navN.toRat shares.toRat = navN.toRat * shares.toRat / v.sharesTotal.toRat := by
    unfold RawVault.idealChargeDepositAt
    rw [if_neg (ne_of_gt hnav_pos), hcast]
  rw [hideal, hcast] at hexact
  rw [hideal]
  unfold sharesToAssetsDeposit at hsad
  obtain ⟨navN', hat', hsad⟩ := bind_ok_peel _ _ _ hsad
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  rw [if_neg hmz] at hsad
  obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  rw [hceq] at hc
  have hnavnorm : navN.isNormalized := (Vault.assetsTotal_ge_deployed v navN hat).1
  obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
    STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
  obtain rfl : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
  have hpos : 0 < navN.toRat * shares.toRat / v.sharesTotal.toRat := by positivity
  obtain ⟨⟨p₁, hp₁n, hp₁v⟩, ⟨q₁, hq₁n, hq₁v⟩⟩ := hexact
  rw [div_mul_cancel₀ _ (ne_of_gt hST_pos)] at hp₁v
  rw [← hsnval] at hp₁v hq₁v hpos
  obtain ⟨hQn, hQv⟩ := pipe_exact navN sn P Q v.sharesTotal hnavnorm hsnnorm v.wf.sharesTotal_norm hmz
    (Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsnval]; exact ne_of_gt hshpos))
    (Number.mantissa_ne_zero_of_toRat_ne_zero (ne_of_gt hST_pos)) hP hQ ⟨p₁, hp₁n, hp₁v⟩ ⟨q₁, hq₁n, hq₁v⟩ hpos
  exact ⟨Q, hQn, Number.negative_false_of_pos Q (by rw [hQv]; exact hpos), by rw [hQv, hsnval], hc⟩

end XRPL.Model.SingleAssetVault
