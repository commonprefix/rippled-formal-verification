import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.DepositChargeFloor
import XRPL.Properties.Vault.Proofs.DepositTight.Upper
import XRPL.Properties.Vault.Proofs.ClawbackRecovery
import XRPL.Properties.Vault.Proofs.ShareWorth

/-! # Internal errors of a deposit, a withdrawal and a clawback

A deposit returns `tecINTERNAL` only when the priced shares are worth more than the rounded amount. They exceed the
ideal share count by a relative `sharesOverε` at most, so the worth exceeds the amount by a relative `2.2·10⁻¹⁸` at
most, which a to-nearest price drops for any IOU amount and any integral amount up to `2.28·10^17` units. A withdrawal
has no `tecINTERNAL` exit. A clawback returns it only when the shares the cash names are priced above the cash, and on
a reachable vault those shares are at most the share total, so their price is at most the cash. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepTight

/-- A whole value below another whole value plus one is at most it. -/
private lemma whole_le_of_lt_add_one (x y : ℚ) (hx : x.den = 1) (hy : y.den = 1) (h : x < y + 1) : x ≤ y := by
  have hx' : (x.num : ℚ) = x := Rat.coe_int_num_of_den_eq_one hx
  have hy' : (y.num : ℚ) = y := Rat.coe_int_num_of_den_eq_one hy
  rw [← hx', ← hy'] at h ⊢
  have h1 : x.num < y.num + 1 := by exact_mod_cast h
  exact_mod_cast (show x.num ≤ y.num by omega)

/-- A deposit computation rejected with `tecINTERNAL` priced its nonzero shares above the amount. -/
private lemma computeDeposit_internal_reduces (v : Vault) (amount : STAmount) (isDonation : Bool)
    (hok : (computeDeposit v amount isDonation).run = .ok (.error .tecINTERNAL)) :
    isDonation = false ∧ ∃ shares assets : STAmount, assetsToSharesDeposit v amount = .ok shares ∧
      shares.isZero = false ∧ sharesToAssetsDeposit v shares = .ok assets ∧ assets.operator_gt amount = .ok true := by
  simp only [computeDeposit] at hok
  unfold_ter at hok
  walk_ok
  subst_vars
  exact ⟨by simpa using ‹(!isDonation) = true›, _, _, ‹_›, by simpa using ‹¬ STAmount.isZero _ = true›, ‹_›, ‹_›⟩

/-- A deposit rejected with `tecINTERNAL` priced the shares of its rounded amount above that amount. -/
private lemma Vault.deposit_internal_reduces (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    (t : UInt32) (hpos : 0 < amountDeposit.toRat)
    (hok : (v.deposit amountDeposit isDonation t hpos).run = .ok (.error .tecINTERNAL)) :
    isDonation = false ∧ ∃ ra shares assets : STAmount, (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra) ∧
      assetsToSharesDeposit v ra = .ok shares ∧ shares.isZero = false ∧
      sharesToAssetsDeposit v shares = .ok assets ∧ assets.operator_gt ra = .ok true := by
  simp only [Vault.deposit] at hok
  unfold_ter at hok
  walk_ok
  · rcases Vault.checkOpenLimit_codes _ _ _ ‹_› with h | h <;> exact absurd h (by decide)
  · rcases Vault.adjustAssetsAndShares_codes _ _ _ _ ‹_› with h | h <;> exact absurd h (by decide)
  · obtain ⟨hd, shares, assets, h⟩ := computeDeposit_internal_reduces v _ isDonation ‹_›
    exact ⟨hd, _, shares, assets, ‹_›, h⟩
  · exact absurd (Vault.roundedDepositAmount_rejected_code_proof v amountDeposit _ ‹_›) (by decide)

/-- The price of the shares a positive canonical amount buys is at most that amount, for an integral amount up to
`2.28·10^17` units. -/
private lemma Vault.deposit_charge_le_rounded (v : Vault) (ra shares c : STAmount)
    (hrc : ra.Canonical) (hrp : 0 < ra.toRat) (hrt : ra.mNumericType = v.numericType)
    (hsmall : v.numericType.isIntegral = true → ra.toRat ≤ 228 * 10 ^ 15)
    (hs : assetsToSharesDeposit v ra = .ok shares) (hsz : shares.isZero = false)
    (hp : sharesToAssetsDeposit v shares = .ok c) :
    c.toRat ≤ ra.toRat := by
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v ra shares hs
  have hshpos := assetsToSharesDeposit_pos v ra shares hrc hrp hs hsz
  obtain ⟨navN, hat⟩ : ∃ navN, v.assetsTotal = .ok navN := by
    have h := hs
    unfold assetsToSharesDeposit at h
    obtain ⟨navN, hat, -⟩ := bind_ok_peel _ _ _ h
    exact ⟨navN, hat⟩
  by_cases hcm : c.mValue = 0
  · rw [(STAmount.toRat_eq_zero_iff _).mpr hcm]; exact hrp.le
  by_cases hmz : navN.mantissa_ = 0
  · -- an empty vault prices the shares exactly, at most the amount
    obtain ⟨hIs, -, hshv⟩ := empty_shares_floor v ra shares hrc hrp navN hat hmz hs hsz
    rw [hIs] at hshv
    have hfl := Int.floor_le (ra.toRat * (10 : ℚ) ^ (v.scale.toNat : ℤ))
    by_cases hint : v.numericType.isIntegral = true
    · rw [(charge_empty_integral v shares c hint hshc hshnt hshpos navN hat hmz hp).2, hshv]
      rw [v.wf.scale_integral hint] at hfl ⊢
      simpa using hfl
    · have hcv := empty_frac_charge_exact v ra shares c (by simpa using hint) navN hat hmz hrc hrp
        (by rw [hrt]; exact NumericType.eq_fractional_of_not_integral (by simpa using hint)) hs hsz hp
      have hA0 : v.toExact.assetsTotal = 0 := (Vault.assetsTotal_eq_zero_iff v navN hat).mp hmz
      unfold RawVault.idealChargeDeposit at hcv
      rw [if_pos hA0, hshv] at hcv
      rw [hcv, div_le_iff₀ (by positivity), ← zpow_natCast]
      exact hfl
  -- a nonempty vault: the shares exceed the ideal by at most `sharesOverε`, so their worth the amount as well
  obtain ⟨q, hqv, hqb, -⟩ := shares_spec_exact v ra shares hrc hrp navN hat hs hsz
  obtain ⟨-, hnavpos⟩ := Vault.assetsTotal_pos v navN hat hmz
  have hS1 := Vault.sharesTotal_one_le v navN hat hmz
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have hSpos : (0 : ℚ) < v.toExact.sharesTotal := by rw [hST]; linarith
  have hsle : shares.toRat ≤ v.idealSharesDepositAt navN.toRat ra.toRat * (1 + sharesOverε) := by
    rw [hqv]
    have h1 := Int.floor_le q
    have h2 := (abs_le.mp hqb).2
    linarith
  have hIcle : v.idealChargeDepositAt navN.toRat shares.toRat ≤ ra.toRat * (1 + sharesOverε) := by
    unfold RawVault.idealChargeDepositAt
    unfold RawVault.idealSharesDepositAt at hsle
    rw [if_neg (ne_of_gt hnavpos)] at hsle ⊢
    rw [div_le_iff₀ hSpos]
    calc navN.toRat * shares.toRat
        ≤ navN.toRat * (v.toExact.sharesTotal * ra.toRat / navN.toRat * (1 + sharesOverε)) :=
          mul_le_mul_of_nonneg_left hsle hnavpos.le
      _ = ra.toRat * (1 + sharesOverε) * v.toExact.sharesTotal := by field_simp
  obtain ⟨Q, hQc, hIcpos, hQcases⟩ := charge_nonempty v shares c hshc hshnt hshpos navN hat hmz hp
  rcases hQcases with ⟨-, hQn, hQneg, hQb⟩ | ⟨hQm, -⟩
  swap
  · exact absurd hQm (STAmount.ofNumber_source_ne_zero _ Q .to_nearest c hQc hcm)
  have hεnn : (0 : ℚ) ≤ sharesε := by unfold sharesε; norm_num
  obtain ⟨hQlo, hQhi⟩ := abs_le.mp hQb
  have hQle : Q.toRat ≤ ra.toRat * (1 + sharesOverε) * (1 + sharesε) := by nlinarith
  have hQ0 : 0 ≤ Q.toRat := by
    have hε1 : sharesε ≤ 1 := by unfold sharesε; norm_num
    nlinarith
  unfold sharesOverε sharesε at hQle
  by_cases hint : v.numericType.isIntegral = true
  · -- an integral price is within half a unit of `Q`, so below the amount plus one
    have hh := abs_le.mp (STAmount.ofNumber_integral_within_half v.numericType Q c hint hQn hQneg hQc)
    have hra := hsmall hint
    have hlt : c.toRat < ra.toRat + 1 := by linarith
    have hcden :=
      STAmount.IntegralCanonical.den_eq_one c (sharesToAssetsDeposit_integral_canonical v shares c hint hp).1
    have hrint : ra.integral = true := by unfold STAmount.integral; rw [hrt]; exact hint
    have hrden := STAmount.IntegralCanonical.den_eq_one ra (hrc.1 hrint).1
    exact whole_le_of_lt_add_one _ _ hcden hrden hlt
  -- an IOU price rounds `Q` to nearest, and `Q` is at most the amount or within a twentieth of its last digit
  have hvfr := NumericType.eq_fractional_of_not_integral (by simpa using hint)
  have hrexact := STAmount.Canonical.exactCanonical ra hrc
  by_cases hle : Q.toRat ≤ ra.toRat
  · exact STAmount.ofNumber_to_nearest_le_of_canonical v.numericType Q c ra hQn hQ0 hrexact hrt hle hQc hcm
  push Not at hle
  have hrio : ra.IOUCanonical := hrc.2 (by unfold STAmount.integral; rw [hrt, hvfr]; rfl)
  obtain ⟨-, hrhi⟩ := STAmount.IOUCanonical.toRat_bounds ra hrio hrp
  have hu : (0 : ℚ) < 10 ^ ra.exponent := zpow_pos (by norm_num) _
  have h16 : (10 : ℚ) ^ (ra.exponent + 16) = 10 ^ 16 * 10 ^ ra.exponent := by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  have h1 : (10 : ℚ) ^ (ra.exponent - 1) = 10 ^ ra.exponent / 10 := by
    rw [zpow_sub₀ (by norm_num)]; norm_num
  rw [h16] at hrhi
  have hnear : |Q.toRat - ra.toRat| < 1 / 2 * (10 : ℚ) ^ (ra.exponent - 1) := by
    rw [abs_of_pos (by linarith), h1]
    linarith
  exact (STAmount.ofNumber_to_nearest_eq_of_near_canonical v.numericType Q c ra hQn hQ0 hrexact hrt hrp hnear hQc
    hcm).le

/-- Deposit on any lawful vault of a canonical amount of its asset, an integral one at most `2.28·10^17` units ->
never `tecINTERNAL`. -/
lemma Vault.deposit_no_internal_proof (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amountDeposit.toRat) (hc : amountDeposit.Canonical) (hty : amountDeposit.mNumericType = v.numericType)
    (hsmall : v.numericType.isIntegral = true → amountDeposit.toRat ≤ 228 * 10 ^ 15) :
    (v.deposit amountDeposit isDonation t hpos).run ≠ .ok (.error .tecINTERNAL) := by
  intro hok
  obtain ⟨-, ra, shares, c, hra, hs, hsz, hp, hgt⟩ :=
    Vault.deposit_internal_reduces v amountDeposit isDonation t hpos hok
  obtain ⟨hrcz, hrt, hr0⟩ := v.roundedDepositAmount_form amountDeposit ra hc hty hra
  obtain ⟨navN, hat, -, hrz⟩ := roundedDepositAmount_rounded v amountDeposit ra hra
  have hrm : ra.mValue ≠ 0 := by simpa [STAmount.isZero] using hrz
  have hrc : ra.Canonical := hrcz.resolve_right (by simpa using hrz)
  have hrp : 0 < ra.toRat := lt_of_le_of_ne hr0 (Ne.symm (STAmount.toRat_ne_zero _ hrm))
  -- an integral amount is not rounded
  have hsmall' : v.numericType.isIntegral = true → ra.toRat ≤ 228 * 10 ^ 15 := by
    intro hint
    have hai : amountDeposit.integral = true := by unfold STAmount.integral; rw [hty]; exact hint
    rw [Vault.roundedDepositAmount_integral_proof v amountDeposit navN hai hpos hat] at hra
    obtain rfl : amountDeposit = ra := Except.ok.inj (Except.ok.inj hra)
    exact hsmall hint
  have hle := Vault.deposit_charge_le_rounded v ra shares c hrc hrp hrt hsmall' hs hsz hp
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v ra shares hs
  have hct := sharesToAssetsDeposit_mNumericType v shares c hp
  have hcmp : STAmount.areComparable c ra = true := by
    unfold STAmount.areComparable; rw [hct, hrt]; exact beq_self_eq_true _
  have hrneg : ra.mIsNegative = false := STAmount.mIsNegative_false_of_pos ra hrp
  -- a zero price is never above a positive amount
  have hzero : c.mValue ≠ 0 := by
    intro hcm
    have hcmp' : STAmount.areComparable ra c = true := by rwa [STAmount.areComparable_comm]
    simp only [STAmount.operator_gt, STAmount.operator_lt, hcmp', hcm, hrneg] at hgt
    cases hcn : c.mIsNegative <;> simp_all
  rcases sharesToAssetsDeposit_exactCanonical_or_zero v shares c hshc hshnt hp with hexact | hcm
  · rw [STAmount.operator_gt_eq c ra (STAmount.CmpFaithful.ofExactCanonical c ra hexact
      (STAmount.Canonical.exactCanonical ra hrc) hcmp (fun h => absurd h hzero) (fun h => absurd h hrm))] at hgt
    have := of_decide_eq_true (Except.ok.inj hgt)
    linarith
  · exact hzero hcm

/-- Withdrawal on any lawful vault -> never `tecINTERNAL`: no check returns it. -/
lemma Vault.withdraw_no_internal_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) :
    (v.withdraw amount waive t hpos).run ≠ .ok (.error .tecINTERNAL) := by
  intro hok
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (rcases computeWithdraw_codes v _ waive _ ‹_› with h | h <;> exact absurd h (by decide))
  all_goals try (rcases Vault.checkDebitNotDust_codes _ _ _ ‹_› with h | h | h <;> exact absurd h (by decide))
  all_goals try (rcases Vault.adjustAssetsAndShares_codes _ _ _ _ ‹_› with h | h <;> exact absurd h (by decide))

/-- A clawback computation rejected with `tecINTERNAL` priced the shares the cash names above the cash. -/
private lemma computeClawback_internal_reduces (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hok : (computeClawback v assets holderShares waive).run = .ok (.error .tecINTERNAL)) :
    ∃ (cash shares recovered : STAmount) (n : Number),
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash ∧
      assetsToSharesWithdraw v cash true waive = .ok shares ∧
      v.sharesToAssetsWithdraw shares waive = .ok recovered ∧
      recovered.toNumber .to_nearest = .ok n ∧ n.operator_gt v.assetsAvailable = true := by
  simp only [computeClawback] at hok
  unfold_ter at hok
  walk_ok
  exact ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩

/-- A clawback rejected with `tecINTERNAL` priced the shares the cash names above the cash. -/
private lemma Vault.clawback_internal_reduces (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.error .tecINTERNAL)) :
    ∃ (cash shares recovered : STAmount) (n : Number),
      STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash ∧
      assetsToSharesWithdraw v cash true waive = .ok shares ∧
      v.sharesToAssetsWithdraw shares waive = .ok recovered ∧
      recovered.toNumber .to_nearest = .ok n ∧ n.operator_gt v.assetsAvailable = true := by
  simp only [Vault.clawback] at hok
  unfold_ter at hok
  walk_ok
  · rcases Vault.checkDebitNotDust_codes _ _ _ ‹_› with h | h | h <;> exact absurd h (by decide)
  · rcases Vault.adjustAssetsAndShares_codes _ _ _ _ ‹_› with h | h <;> exact absurd h (by decide)
  · exact computeClawback_internal_reduces v assets holderShares waive ‹_›

/-- The cash converted to the asset keeps its value: a lawful vault stores its cash exactly. -/
lemma Vault.cash_ofNumber_toRat (v : Vault) (cash : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash) :
    cash.toRat = v.assetsAvailable.toRat := by
  have h := v.valid.assetsAvailable_representable
  unfold STAmount.isRounded STAmount.equalAfterNumberConvert at h
  rw [hcash] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hsn : cash.toNumber .to_nearest with
  | error e => rw [hsn] at h; exact absurd h (by simp)
  | ok n =>
    rw [hsn] at h
    have heq : n.operator_eq v.assetsAvailable = true := by simpa using h
    have hnv : n.toRat = cash.toRat := by
      by_cases hz : cash.mValue = 0
      · exact (STAmount.toNumber_zero_facts cash _ n hz hsn).1
      · exact (STAmount.toNumber_exact_of cash n (STAmount.ofNumber_exactCanonical _ _ _ cash
          v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg hcash hz) hsn).1
    rw [← hnv]
    exact (operator_eq_iff n v.assetsAvailable (STAmount.toNumber_isNormalized cash _ n hsn)
      v.wf.assetsAvailable_norm).mp heq

/-- On a reachable vault the price of the shares its cash names is a canonical amount at most the cash. -/
private lemma Vault.Reachable.cash_price_le (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0) (waive : Bool)
    (cash shares recovered : STAmount)
    (hcash : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok cash)
    (hs : assetsToSharesWithdraw v cash true waive = .ok shares)
    (hp : v.sharesToAssetsWithdraw shares waive = .ok recovered) :
    recovered.CanonicalOrZero ∧ recovered.toRat ≤ v.assetsAvailable.toRat := by
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hST := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  rcases (Nat.cast_nonneg v.toExact.sharesTotal : (0 : ℚ) ≤ _).lt_or_eq with hS | hS
  swap
  · -- no shares: the vault holds nothing, so the price is zero
    have hz : v.sharesTotal = Number.zero :=
      (Number.toRat_eq_zero_iff_eq_zero v.wf.sharesTotal_norm).mp (by rw [← hST, ← hS])
    obtain ⟨hAA, hAD⟩ := v.valid.empty_shares hz
    obtain ⟨nav, hnav, -, hcase⟩ := WdPrice.price_cases v shares recovered waive hp
    rw [Vault.assetsTotalForWithdrawal_of_noLending v hAD waive, Except.ok.injEq] at hnav
    subst hnav
    rcases hcase with ⟨-, rfl⟩ | ⟨hm, -⟩
    · exact ⟨(STAmount.zero_canonicalOrZero _).1, by rw [STAmount.zero_toRat]; exact hA0⟩
    · exact absurd (by rw [hAA]; rfl) hm
  have hmax := Vault.Reachable.maxValue_fits v t0 hr hS
  have hz := Vault.Reachable.openZone_proof v t0 hr hmax
  have hinv := Vault.Reachable.sharesTotal_le_cash_proof v t0 hr
  have hnav := hz.assetsTotalForWithdrawal_eq waive
  have hb : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨k, hk, hkv⟩ := hz.cash
  have hk' : (k : ℚ) ≤ 9 * 10 ^ 15 := by exact_mod_cast hk
  have hA9 : v.assetsAvailable.toRat ≤ 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rw [hkv]; exact mul_le_mul_of_nonneg_right hk' hb.le
  -- the cash is stored exactly, and covers a base unit per share
  have hcv : cash.toRat = v.assetsAvailable.toRat :=
    Vault.cash_ofNumber_toRat v cash hcash
  have hApos : 0 < v.assetsAvailable.toRat := lt_of_lt_of_le (mul_pos hS hb) hinv
  -- the shares the cash names are at most the share total
  obtain ⟨hsic, hsty⟩ := assetsToSharesWithdraw_int64_canonical v cash shares true waive hs
  have hscan : shares.Canonical := hsic.canonical (by rw [hsty]; decide)
  have hcc := (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hcash).1
  have hs0 : 0 ≤ shares.toRat :=
    assetsToSharesWithdraw_nonneg v cash shares waive hcc (by rw [hcv]; exact hA0) hs
  have hsS : shares.toRat ≤ v.toExact.sharesTotal := by
    by_cases hsz : shares.isZero = true
    · rw [(STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hsz)]; exact hS.le
    have hcpos : 0 < cash.toRat := by rw [hcv]; exact hApos
    have hcC : cash.Canonical := hcc.resolve_right (fun h => by
      rw [(STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using h)] at hcpos
      exact lt_irrefl _ hcpos)
    obtain ⟨hden, -, hup, -⟩ := WdTight.shares_bounds v cash shares waive _ hnav hcpos hcC hs (by simpa using hsz)
    have hid : v.idealSharesWithdrawAt v.assetsAvailable.toRat cash.toRat = v.toExact.sharesTotal := by
      unfold RawVault.idealSharesWithdrawAt
      rw [hcv]; field_simp
    have hS9 : (v.toExact.sharesTotal : ℚ) ≤ 9 * 10 ^ 15 := by
      by_contra h
      push Not at h
      nlinarith [mul_lt_mul_of_pos_right h hb]
    rw [hid] at hup
    have hlt : shares.toRat < (v.toExact.sharesTotal : ℚ) + 1 := by unfold sharesε at hup; nlinarith
    have hsint : (shares.toRat.num : ℚ) = shares.toRat := Rat.coe_int_num_of_den_eq_one hden
    rw [← hsint] at hlt ⊢
    have h1 : shares.toRat.num < (v.toExact.sharesTotal : ℤ) + 1 := by exact_mod_cast hlt
    exact_mod_cast (show shares.toRat.num ≤ (v.toExact.sharesTotal : ℤ) by omega)
  -- the worth of those shares is at most the cash, and the price lands within a step of it
  set I := v.idealAssetsWithdrawAt v.assetsAvailable.toRat shares.toRat with hI
  have hIle : I ≤ v.assetsAvailable.toRat := by
    rw [hI]
    unfold RawVault.idealAssetsWithdrawAt
    rw [div_le_iff₀ hS]
    exact mul_le_mul_of_nonneg_left hsS hA0
  refine ⟨(Vault.sharesToAssetsWithdraw_form v shares recovered waive hmax hp).1, ?_⟩
  by_cases hpz : recovered.toRat = 0
  · rw [hpz]; exact hA0
  obtain ⟨hpv, heb, hpu, -, hrel⟩ := Vault.priced_grid_total v hmax shares recovered waive _ hnav hs0 hscan hp
    (le_trans hIle hA9) hpz
  have hexp : I * (1 + sharesε) = I + I * sharesε := by ring
  have hg : (0 : ℚ) < 10 ^ recovered.exponent := zpow_pos (by norm_num) _
  exact le_of_grid_lt _ (k : ℤ) _ _ heb _ _ hpv (by rw [hkv]; push_cast; rfl) (by linarith)

/-- Clawback on a reachable vault -> never `tecINTERNAL`. -/
lemma Vault.Reachable.clawback_no_internal_proof (v : Vault) (t0 : UInt32) (hr : Vault.Reachable v t0)
    (assets holderShares : STAmount) (waive : Bool) (hnn : 0 ≤ assets.toRat) :
    (v.clawback assets holderShares waive hnn).run ≠ .ok (.error .tecINTERNAL) := by
  intro hok
  obtain ⟨cash, shares, recovered, n, hcash, hs, hp, hn, hgt⟩ :=
    Vault.clawback_internal_reduces v assets holderShares waive hnn hok
  obtain ⟨hrc, hle⟩ := Vault.Reachable.cash_price_le v t0 hr waive cash shares recovered hcash hs hp
  obtain ⟨hv, hnorm⟩ := hrc.toNumber_exact n hn
  have hlt : v.assetsAvailable.toRat < n.toRat :=
    (operator_lt_iff _ _ v.wf.assetsAvailable_norm hnorm).mp (by simpa [Number.operator_gt] using hgt)
  linarith

end XRPL.Model.SingleAssetVault
