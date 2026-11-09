import XRPL.Properties.Lending.Ledger.Common.SettledVault
import XRPL.Properties.Lending.Ledger.Common.AssetsTotalExponent
import XRPL.Properties.Lending.Loan.Common.RoundTotal
import XRPL.Properties.Lending.Loan.Common.ManageRoundToExponent
import XRPL.Properties.Vault.Proofs.WithdrawFee
import XRPL.Properties.Vault.Proofs.PerShareValue
import XRPL.Properties.Vault.Proofs.Support.ExactCash

/-! # A holder redeems part of a settled vault

With no early-exit fee, shares worth at least one unit at the scale of the cash price between that unit and the cash,
so the dust check, the clamp and the cash update of a redemption that leaves other shares all succeed. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a settled vault shares worth one unit at the scale of the cash or more price between that unit and the
cash. The 19-digit price sits within `2·10⁻¹⁸` times their worth, too close for the rounding to cross either bound. -/
private lemma Vault.Settled.price_part (v : Vault) (hz : v.Settled)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (shares : STAmount) (waive : Bool) (hc : shares.Canonical) (hs1 : 1 ≤ shares.toRat)
    (hle : shares.toRat ≤ v.toExact.sharesTotal) (hA : 0 < v.assetsAvailable.toRat) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (hworth : (10 : ℚ) ^ max v.baseExponent cash.exponent ≤
      shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal) :
    ∃ p, v.sharesToAssetsWithdraw shares waive = .ok p ∧
      (10 : ℚ) ^ max v.baseExponent cash.exponent ≤ p.toRat ∧ p.toRat ≤ v.assetsAvailable.toRat := by
  have hAAn := v.wf.assetsAvailable_norm
  have hAAtop := hz.cash_top
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds v
  have hcv := Vault.final_payout_exact v cash hz.cashExact hmax hcash
  have hcm : cash.mValue ≠ 0 := fun h => by rw [(STAmount.toRat_eq_zero_iff _).mpr h] at hcv; linarith
  have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ hAAn hA.le hcash hcm
  have hct := STAmount.ofNumber_mNumericType _ _ _ _ hcash
  set E := max v.baseExponent cash.exponent with hE
  have hE10 : (-10 : ℤ) ≤ E := le_trans hblo (le_max_left _ _)
  obtain ⟨an, hann, hanpos, hb2, hprice⟩ := Vault.price_quotient v shares waive hc
    (hz.assetsTotalForWithdrawal_eq waive) hs1 hle (hz.cash_ge hA).2 hz.cash_lt
    (le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) hworth)
  set V := shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal with hV
  have hVE : (10 : ℚ) ^ E ≤ V := hworth
  have hVle : V ≤ v.assetsAvailable.toRat := by
    have hS1 : (1 : ℚ) ≤ v.toExact.sharesTotal := le_trans hs1 hle
    rw [hV, div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨hb3, hb4⟩ := abs_le.mp hb2
  have hpE : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
  by_cases hint : v.numericType.isIntegral = true
  · -- a whole-number asset: the quotient rounds to a whole number between one and the cash
    have hcoff : cash.exponent = 0 := (hcE.resolve_left (fun hio => by
      have := hio.is_fractional; rw [hct] at this; rw [this] at hint; exact absurd hint (by decide))).1.offset_zero
    have hE0 : E = 0 := by rw [hE, hbint hint, hcoff]; rfl
    rw [hE0, zpow_zero] at hVE
    rw [hE0, zpow_zero]
    have hfit := hz.cashFit hint
    obtain ⟨p, hp, hp1, hpA, -⟩ := Vault.integral_price_ok v hz.cashExact hint an hann (by linarith)
      (by linarith) (by linarith)
    exact ⟨p, hprice p hp, hp1, hpA⟩
  -- an IOU asset
  have hfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hio : cash.IOUCanonical := hcE.resolve_right (fun h => by
    have := h.1.is_integral; rw [hct] at this; exact hint this)
  have hE80 : E ≤ 80 := max_le (by omega) hio.exp_hi
  obtain ⟨p, hp⟩ : ∃ p, STAmount.ofNumber v.numericType an .to_nearest = .ok p := by
    rw [hfr]; exact STAmount.ofNumber_fractional_ok_below an hann hanpos (by nlinarith)
  have hpm : p.mValue ≠ 0 := STAmount.ofNumber_frac_ne_zero_of_ge an .to_nearest p hann
    (le_trans (le_trans (by norm_num : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ (-10 : ℤ) / 2)
      (div_le_div_of_nonneg_right (zpow_le_zpow_right₀ (by norm_num) hE10) (by norm_num))) (by linarith))
    (hfr ▸ hp)
  refine ⟨p, hprice p hp, ?_, ?_⟩
  · -- one unit at the scale of the cash is an IOU amount, which the price does not round below
    set a : STAmount := ⟨.fractional, kMinValue, E - 15, false⟩ with ha_def
    have hkm : kMinValue.toNat = 10 ^ 15 := by decide
    have haio : a.IOUCanonical :=
      ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
        by show (-96 : ℤ) ≤ E - 15; omega, by show E - 15 ≤ 80; omega⟩
    have hav : a.toRat = 10 ^ E := by
      rw [STAmount.toRat_of_nonneg a rfl]
      show (kMinValue.toNat : ℚ) * 10 ^ (E - 15) = _
      rw [hkm, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
      push_cast
      field_simp
    by_cases hge : (10 : ℚ) ^ E ≤ an.toRat
    · have h := STAmount.ofNumber_to_nearest_ge_of_canonical _ an p a hann hanpos.le (Or.inl haio)
        (by rw [hfr]) (by rw [hav]; exact hge) hp hpm
      rwa [hav] at h
    · push Not at hge
      have hae : a.exponent = E - 15 := rfl
      have hnear : |an.toRat - a.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (a.exponent - 1) := by
        rw [hav, hae, abs_of_neg (by linarith), show E - 15 - 1 = E - 16 by ring,
          zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
        have h1 : (1 / 2 : ℚ) * (10 ^ E / 10 ^ (16 : ℤ)) = 10 ^ E * (1 / (2 * 10 ^ 16)) := by
          rw [show (10 : ℚ) ^ (16 : ℤ) = 10 ^ 16 by norm_num]; ring
        rw [h1]
        nlinarith
      have h := STAmount.ofNumber_to_nearest_eq_of_near_canonical _ an p a hann hanpos.le (Or.inl haio)
        (by rw [hfr]) (by rw [hav]; exact hpE) hnear hp hpm
      rw [h, hav]
  · -- the price never rounds past the cash, an IOU amount stored exactly
    by_cases hanle : an.toRat ≤ v.assetsAvailable.toRat
    · rw [← hcv]
      exact STAmount.ofNumber_to_nearest_le_of_canonical _ an p cash hann hanpos.le hcE hct
        (by rw [hcv]; exact hanle) hp hpm
    push Not at hanle
    have hnear : |an.toRat - cash.toRat| < (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) := by
      rw [hcv, abs_of_pos (by linarith)]
      have hu : (1 / 2 : ℚ) * (10 : ℚ) ^ (cash.exponent - 1) = (10 : ℚ) ^ cash.exponent / 20 := by
        rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
      rw [hu]
      obtain ⟨-, hhi⟩ := STAmount.IOUCanonical.toRat_bounds cash hio (by rw [hcv]; exact hA)
      rw [hcv] at hhi
      have h16 : (10 : ℚ) ^ (cash.exponent + 16) = 10 ^ cash.exponent * 10 ^ 16 := by
        rw [zpow_add₀ (by norm_num)]; norm_num
      rw [h16] at hhi
      linarith
    have heq := STAmount.ofNumber_to_nearest_eq_of_near_canonical _ an p cash hann hanpos.le hcE hct
      (by rw [hcv]; exact hA) hnear hp hpm
    rw [heq, hcv]

/-- Paying out a nonnegative amount a cash stored exactly covers never raises the cash. The cash is stored
exactly, so rounding the cash left into the asset never lands above it. -/
lemma Vault.debit_le_of_exact (v : Vault) (hexact : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (c shares : STAmount) (raw : RawVault) (hc : c.CanonicalOrZero) (hc0 : 0 ≤ c.toRat)
    (hcA : c.toRat ≤ v.assetsAvailable.toRat)
    (hadj : (v.adjustAssetsAndShares c.operator_neg shares).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat ≤ v.assetsAvailable.toRat := by
  have hAAn := v.wf.assetsAvailable_norm
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, rfl⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hv, hnorm⟩ :=
    STAmount.CanonicalOrZero.toNumber_exact (STAmount.CanonicalOrZero.operator_neg hc) assetsNum hnum
  rw [STAmount.operator_neg_toRat] at hv
  have hr := operator_add_rounded_to_nearest _ _ _ hAAn hnorm hs
  rw [hv, ← sub_eq_add_neg] at hr
  have hsn := operator_add_isNormalized_to_nearest_sz _ _ _ hAAn hnorm hs
  have hs0 : 0 ≤ s.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg _ _ hr (by linarith)
  have hsle : s.toRat ≤ v.assetsAvailable.toRat :=
    Number.RoundsToRepresentable.le_of_le_normalized _ _ hr _ hAAn (by linarith)
  show aa'.toRat ≤ _
  unfold STAmount.roundToNumericType at haa
  cases hof : STAmount.ofNumber v.numericType s .to_nearest with
  | error e => rw [hof] at haa; exact absurd haa (by simp)
  | ok st =>
    rw [hof] at haa
    simp only at haa
    rw [(STAmount.CanonicalOrZero.toNumber_exact (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hof).1 aa' haa).1]
    by_cases hst0 : st.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero _ hst0]; exact hAA0
    obtain ⟨cash, hcash⟩ := Vault.cash_ok_of_exact hexact
    have hcv := Vault.final_payout_exact v cash hexact hmax hcash
    by_cases hcm : cash.mValue = 0
    · -- no cash leaves only a zero value, which converts to zero
      have hA0 : v.assetsAvailable.toRat = 0 := by rw [← hcv, STAmount.toRat_eq_zero_of_mValue_zero _ hcm]
      have hsz : s = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hsn).mp (by linarith)
      subst hsz
      exact absurd (STAmount.ofNumber_source_ne_zero _ _ _ st hof hst0) (by decide)
    have hcE := STAmount.ofNumber_exactCanonical _ _ _ _ hAAn hAA0 hcash hcm
    have hct := STAmount.ofNumber_mNumericType _ _ _ _ hcash
    rw [← hcv]
    exact STAmount.ofNumber_to_nearest_le_of_canonical _ s st cash hsn hs0 hcE hct (by rw [hcv]; exact hsle) hof
      hst0

/-- On a settled vault a redemption of some but not all shares succeeds and never raises the cash at a time
without an early-exit fee, when the shares are worth at least one unit at the scale of the cash, or there is no cash. -/
lemma Vault.Settled.withdraw_part_ok (v : Vault) (t : UInt32) (hz : v.Settled)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) (waive : Bool)
    (hopen : (v.earlyExitFeeRate.isNone && v.phase t == .investment) = false)
    (hfee : v.earlyExitFeeRateAt t = 0)
    (shares : STAmount) (hc : shares.Canonical) (hty : shares.mNumericType = .int64)
    (hpos : 0 < (WithdrawAmount.vaultShares shares).amount.toRat)
    (hlt : shares.toRat < v.toExact.sharesTotal)
    (hworth : 0 < v.assetsAvailable.toRat →
      ∀ E, numberExponent v.assetsAvailable v.baseExponent v.numericType = .ok E →
        (10 : ℚ) ^ E ≤ shares.toRat * v.assetsAvailable.toRat / v.toExact.sharesTotal) :
    ∃ r : VaultWithAmounts, (v.withdraw (.vaultShares shares) waive t hpos).run = .ok (.ok r) ∧
      r.shares = shares ∧ r.vault'.assetsAvailable.toRat ≤ v.assetsAvailable.toRat := by
  have hspos : 0 < shares.toRat := hpos
  have hsic : shares.IntegralCanonical := (hc.1 (by simp only [STAmount.integral, hty]; decide)).1
  have hs1 : 1 ≤ shares.toRat := rat_one_le_of_den_one_pos _ hsic.den_eq_one hspos
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAAn := v.wf.assetsAvailable_norm
  have hnav := hz.assetsTotalForWithdrawal_eq waive
  -- the share total as an amount, which the shares fall short of: the withdrawal is not final
  obtain ⟨S, hS⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest v.wf.sharesTotal_norm
    (Number.negative_false_of_nonneg _ v.wf.sharesTotal_norm v.wf.sharesTotal_nonneg) (Vault.sharesTotal_le_maxRep v)
  have hnf : shares.operator_eq S = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact absurd ((Vault.isFinalWithdrawal_iff v shares S hsic hty hspos hS).mp h) (ne_of_lt hlt)
  have hsz : shares.isZero = false := by
    simp only [STAmount.isZero, beq_eq_false_iff_ne]
    intro h0
    rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hspos
    exact lt_irrefl _ hspos
  rcases eq_or_lt_of_le hAA0 with hAAz | hApos
  · -- no cash: the shares price at zero and nothing is paid
    have hAm : v.assetsAvailable.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp hAAz.symm
    have hAz : v.assetsAvailable = Number.zero := Number.eq_zero_of_mantissa_zero _ hAAn hAm
    have hpr := Vault.sharesToAssetsWithdraw_zero_nav_proof v shares waive _ hnav hAm
    have hcomp := computeWithdraw_shares_ok_of_price v shares _ waive hsz hpr
    obtain ⟨hzc, hzt⟩ := STAmount.zero_canonicalOrZero v.numericType
    obtain ⟨pN, haN⟩ := STAmount.CanonicalOrZero.toNumber_ok hzc
    obtain ⟨hpNv, hpNn⟩ := STAmount.CanonicalOrZero.toNumber_exact hzc pN haN
    have hz0 : (STAmount.zero v.numericType).toRat = 0 :=
      (STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)
    have hpNz : pN = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hpNn).mp (by rw [hpNv, hz0])
    subst hpNz
    have hpz : (STAmount.zero v.numericType).isZero = true := by
      simp [STAmount.isZero, STAmount.zero_mValue]
    have hne : v.assetsAvailable.operator_ne Number.zero = false := by rw [hAz]; decide
    have hdust : v.checkDebitNotDust Number.zero = .ok .tesSUCCESS := by
      simp [Vault.checkDebitNotDust, show Number.zero.operator_eq Number.zero = true by decide]
      rfl
    have hge : v.assetsAvailable.operator_lt Number.zero = false := by rw [hAz]; decide
    obtain ⟨raw, hadj⟩ := Vault.adjust_ok_of_exact v hz.cashExact hmax _ shares hzc hzt (by rw [hz0])
      (by rw [hz0]; exact hAA0) hsic hty hspos.le hlt.le
    have hlaw := Vault.withdraw_update_lawful v _ shares raw hmax ⟨0, by rw [hz0]; simp⟩ hzc
      (by rw [STAmount.operator_neg_toRat, hz0]; linarith) hsic hty hspos.le hlt.le
      (fun h => absurd h (ne_of_lt hlt)) hadj
    obtain ⟨v', hv', hraw⟩ := RawVault.to_lawful_ok_of hlaw.1 hlaw.2
    refine ⟨{ vault' := v', assets := STAmount.zero v.numericType, shares := shares }, ?_, rfl, ?_⟩
    swap
    · show v'.toRawVault.assetsAvailable.toRat ≤ _
      rw [hraw]
      exact Vault.debit_le_of_exact v hz.cashExact hmax _ _ raw hzc (by rw [hz0]) (by rw [hz0]; exact hAA0) hadj
    simp only [ExceptT.run] at hcomp hadj
    simp only [Vault.withdraw]
    unfold_ter
    simp [hopen, hcomp, hS, hnf, haN, hnav, hpz, hne, hdust, hge, hadj, hv',
      show (TER.tesSUCCESS != TER.tesSUCCESS) = false by decide]
  -- positive cash: the shares price between one unit at the scale of the cash and the cash
  obtain ⟨cash, hcash⟩ := Vault.cash_ok_of_exact hz.cashExact
  have hE := Vault.cash_exponent_of_exact hz.cashExact hmax hApos cash hcash
  obtain ⟨p, hpr, hplo, hphi⟩ := Vault.Settled.price_part v hz hmax shares waive hc hs1 hlt.le hApos cash hcash
    (hworth hApos _ hE)
  obtain ⟨r, hrun, hrs, hcl, hadj⟩ := Vault.withdraw_part_ok_of_price v t hmax hz.assetsDeployed hz.lossUnrealized
    hz.cashExact waive hopen hfee shares hc hty hpos hlt hApos cash hcash p hpr hplo hphi
  refine ⟨r, hrun, hrs, ?_⟩
  -- the cash does not grow: the payout is a nonnegative amount at most the price
  have hp0 : 0 ≤ p.toRat := le_trans (zpow_pos (by norm_num) _).le hplo
  have hpn := STAmount.CanonicalOrZero.operator_neg (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hpr).1
  have hbr := v.baseExponent_range
  obtain ⟨hcc, -, hc0⟩ := clampToSumExponent_canonicalOrZero _ _ _ _ hpn hbr.1 hbr.2 hcl
  have hle := clampToSumExponent_le_abs _ _ _ _ hpn hbr.1 hbr.2 hcl
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hp0] at hle
  exact Vault.debit_le_of_exact v hz.cashExact hmax _ _ _ hcc hc0 (by linarith) hadj

end XRPL.Model.SingleAssetVault
