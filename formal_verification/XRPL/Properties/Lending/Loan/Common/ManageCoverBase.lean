import XRPL.Properties.Lending.Loan.Common.ManageCover
import XRPL.Properties.Lending.Loan.Common.ManageRoundToExponent
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent
import XRPL.Properties.Vault.Proofs.Support.EarlyExitFee

/-! # The cover a default pays on the base grid

Below the coarsening threshold, with AssetsAvailable a whole number of base units, the cover is the
capped liquidation amount floored to whole base units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A nonnegative `Number` with exponent below `-99` is below `10 ^ b` for a scale of at least `-81`. -/
private lemma lt_pow_of_exponent (n : Number) (b : Int) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (hb : (-81 : ℤ) ≤ b) (hlt : n.exponent_ < -99) : n.toRat < 10 ^ b := by
  by_cases hm : n.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero n hm]; exact zpow_pos (by norm_num) _
  obtain ⟨-, hhi⟩ := hn.mantissaBounds_nat hm
  have hmq : (n.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hhi
  have hv := Number.toRat_of_nonneg n (Number.negative_false_of_nonneg n hn h0)
  have h1 : (10 : ℚ) ^ n.exponent_ * 10 ^ 19 ≤ 10 ^ b := by
    rw [show (10 : ℚ) ^ 19 = 10 ^ (19 : ℤ) by norm_num, ← zpow_add₀ (by norm_num)]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (0 : ℚ) < 10 ^ n.exponent_ := zpow_pos (by norm_num) _
  rw [hv]; nlinarith

/-- Rounding a value below `10^(16 + b)` towards zero to a fractional asset keeps its floor on the grid `10^b`. -/
private lemma roundToNumericType_towards_zero_floor (x c : Number) (b : Int) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hb : (-81 : ℤ) ≤ b) (hlt : x.toRat < 10 ^ (16 + b))
    (h : STAmount.roundToNumericType .fractional x .towards_zero = .ok c) :
    ⌊c.toRat / 10 ^ b⌋ = ⌊x.toRat / 10 ^ b⌋ := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber .fractional x .towards_zero with
  | error e => rw [hof] at h; exact absurd h (by simp)
  | ok ret =>
    rw [hof] at h
    have hcv := (STAmount.ofNumber_toNumber_exact .fractional x _ _ ret c hx (by simp [NumericType.isIntegral])
      hof h).1
    rw [hcv]
    by_cases hrz : ret.mValue = 0
    · -- a zero IOU amount comes from a value below one unit of the grid
      rw [STAmount.toRat_eq_zero_of_mValue_zero ret hrz, zero_div, Int.floor_zero]
      symm
      rw [Int.floor_eq_iff]
      have hsmall : x.toRat < 10 ^ b := by
        by_cases hm : x.mantissa_ = 0
        · rw [Number.toRat_eq_zero_of_mantissa_zero x hm]; exact hp
        exact lt_pow_of_exponent x b hx h0 hb (by
          by_contra hc'
          exact STAmount.ofNumber_iou_ne_zero_of_exponent x _ ret hx hm (by omega) hof hrz)
      exact ⟨by simpa using div_nonneg h0 hp.le, by rw [div_lt_iff₀ hp]; simpa using hsmall⟩
    · have hnz := STAmount.ofNumber_source_ne_zero .fractional x _ ret hof hrz
      rw [STAmount.ofNumber_iou_floor x ret .towards_zero (Or.inr rfl) hx hnz h0 hof hrz, floor_grid_floor_of_le]
      have h1 := Number.pow_exponent_add_le_toRat x hx h0 hnz
      have h3 : (10 : ℚ) ^ (x.exponent_ + 18) < 10 ^ (16 + b) := lt_of_le_of_lt h1 hlt
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h3
      omega

/-- On the base grid the cover is the capped liquidation amount floored to whole base units. Same asset,
AssetsAvailable in whole base units, and AssetsAvailable plus the cap at least a unit below `10^16` base units. -/
lemma Loan.defaultCover_at_base (loan : Loan) (v : Vault) (dc minimumCover liquidationAmount : Number) (a : ℕ)
    (h : loan.defaultCover v = .ok dc)
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hnt : loan.broker.numericType = v.numericType)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat ≤ (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    dc.toRat = (⌊min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨mc, liq, c, st, hmc, hl, hc, hst, hdc⟩ := Loan.defaultCover_parts loan v dc h
  rw [hmin, Except.ok.injEq] at hmc
  subst hmc
  rw [hliq, Except.ok.injEq] at hl
  subst hl
  have hb := loan.broker.exact
  have hpo0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  obtain ⟨hmcn, hmc0⟩ := tenthBipsOfValue_upward_facts _ _ _ loan.broker.wf.debtTotal_norm hb.debtTotal_nonneg hmin
  obtain ⟨hliqn, hliq0⟩ := tenthBipsOfValue_upward_facts _ _ _ hmcn hmc0 hliq
  obtain ⟨hm1, hm1n⟩ := Number.min_toRat _ _ hliqn loan.wf.principalOutstanding_norm
  obtain ⟨hm2, hm2n⟩ := Number.min_toRat _ _ hm1n loan.broker.wf.coverAvailable_norm
  set capped := Number.min (Number.min liquidationAmount loan.principalOutstanding) loan.broker.coverAvailable
  have hcapv : capped.toRat = min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat := by rw [hm2, hm1]
  have hcap0 : 0 ≤ capped.toRat := by rw [hcapv]; exact le_min (le_min hliq0 hpo0) hb.coverAvailable_nonneg
  rw [← hcapv] at hroom ⊢
  obtain ⟨hc0, hcle, hcn⟩ := STAmount.roundToNumericType_towards_zero_le _ _ _ hm2n hcap0 hc
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds v
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  rw [(sumRoundAndSubtract_downward_le _ _ _ _ _ v.wf.assetsAvailable_norm hA0 hcn hc0
    (Vault.baseExponent_range v) hst).2 dc hdc |>.1]
  cases hntv : loan.broker.numericType with
  | fractional =>
    rw [hntv] at hc hst
    have hlt : capped.toRat < 10 ^ (16 + v.baseExponent) := by linarith
    rw [sumRoundAndSubtract_at_base _ _ _ _ a v.wf.assetsAvailable_norm haa hcn hc0 ⟨by omega, hbhi⟩
      (by linarith) hst, roundToNumericType_towards_zero_floor capped c _ hm2n hcap0 (by omega) hlt hc]
  | integral mv mo ms msh =>
    have hint : loan.broker.numericType.isIntegral = true := by rw [hntv]; rfl
    have hb0 : v.baseExponent = 0 := hbint (by rw [← hnt]; exact hint)
    rw [hb0, zpow_zero, div_one, mul_one]
    have hcfl : c.toRat = (⌊capped.toRat⌋ : ℚ) := by
      unfold STAmount.roundToNumericType at hc
      cases hof : STAmount.ofNumber loan.broker.numericType capped .towards_zero with
      | error e => rw [hof] at hc; exact absurd hc (by simp)
      | ok ret =>
        rw [hof] at hc
        have hcv := (STAmount.ofNumber_toNumber_exact _ capped _ _ ret c hm2n (fun _ => hcap0) hof hc).1
        have hneg := Number.negative_false_of_nonneg capped hm2n hcap0
        obtain ⟨iv, hiv, hr⟩ := STAmount.ofNumber_integral_toRat _ capped _ ret hint hneg hof
        rw [Number.to_rep_towards_zero capped hneg] at hiv
        obtain ⟨h1, h2⟩ := Number.to_rep_downward_floor capped iv hm2n hneg hiv
        rw [hcv, hr]
        have : ⌊capped.toRat⌋ = iv.toInt := by rw [Int.floor_eq_iff]; exact ⟨h1, h2⟩
        rw [this]
    -- the integral credit is the amount itself
    unfold sumRoundAndSubtract at hst
    rw [if_pos hint] at hst
    obtain ⟨x, hx, hst⟩ := bind_ok_peel _ _ _ hst
    have hxs : x = st := Except.ok.inj hst
    subst hxs
    have hneg := Number.negative_false_of_nonneg c hcn hc0
    obtain ⟨iv, hiv, hr⟩ := STAmount.ofNumber_integral_toRat _ c _ x hint hneg hx
    obtain ⟨h1, h2⟩ := Number.to_rep_downward_floor c iv hcn hneg hiv
    rw [hr]
    rw [hcfl] at h1 h2
    have : iv.toInt = ⌊capped.toRat⌋ := by
      have h1' : iv.toInt ≤ ⌊capped.toRat⌋ := by exact_mod_cast h1
      have h2' : ⌊capped.toRat⌋ < iv.toInt + 1 := by exact_mod_cast h2
      omega
    rw [this]

/-- The capped liquidation amount is not negative. -/
lemma Loan.cappedCover_nonneg (loan : Loan) (minimumCover liquidationAmount : Number)
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount) :
    0 ≤ min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat := by
  have hb := loan.broker.exact
  obtain ⟨hmcn, hmc0⟩ := tenthBipsOfValue_upward_facts _ _ _ loan.broker.wf.debtTotal_norm hb.debtTotal_nonneg hmin
  obtain ⟨-, hliq0⟩ := tenthBipsOfValue_upward_facts _ _ _ hmcn hmc0 hliq
  exact le_min (le_min hliq0 loan.exact.principalOutstanding_nonneg) hb.coverAvailable_nonneg

variable (loan : Loan) (v : Vault)

/-- A default on the base grid: the cover is the capped liquidation amount floored to whole base units,
and AssetsAvailable' is AssetsAvailable plus that cover, exactly. -/
lemma Loan.manageDefault_at_base (minimumCover liquidationAmount : Number) (a : ℕ) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hnt : loan.broker.numericType = v.numericType)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat ≤ (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    r.amountToPool.toRat = (⌊min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat / 10 ^ v.baseExponent⌋ : ℚ) * 10 ^ v.baseExponent ∧
    r.pool'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.amountToPool.toRat := by
  obtain ⟨i, _, _, raw, _, -, hdc, hadj, hpool, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  have hdcv := Loan.defaultCover_at_base loan v _ _ _ a hdc hmin hliq hnt haa hroom
  refine ⟨hdcv, ?_⟩
  obtain ⟨aa', _, _, _, _, hs, -, -, hraw⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  have haa' : r.pool'.assetsAvailable = aa' := by rw [show r.pool'.assetsAvailable =
    r.pool'.toRawVault.assetsAvailable from rfl, hpool, hraw]
  rw [haa']
  obtain ⟨aa, h1, h2⟩ := hs.cash
  have hdn := Loan.defaultCover_isNormalized loan v _ hdc
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds v
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _

  set capped := min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat
  have hcap0 : 0 ≤ capped := Loan.cappedCover_nonneg loan _ _ hmin hliq
  obtain ⟨kn, hkn⟩ : ∃ kn : ℕ, (kn : ℤ) = ⌊capped / 10 ^ v.baseExponent⌋ :=
    ⟨_, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (div_nonneg hcap0 hp.le))⟩
  have hk1 : (kn : ℚ) * 10 ^ v.baseExponent ≤ capped := by
    have := Int.floor_le (capped / 10 ^ v.baseExponent)
    rw [← hkn, le_div_iff₀ hp] at this
    exact_mod_cast this
  have hdcv' : r.amountToPool.toRat = (kn : ℚ) * 10 ^ v.baseExponent := by rw [hdcv, ← hkn]; norm_cast
  have hK : a + kn < 10 ^ 16 := by
    have hpow16 : (10 : ℚ) ^ (16 + v.baseExponent) = (10 : ℚ) ^ 16 * 10 ^ v.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    have h1 : ((a + kn : ℕ) : ℚ) * 10 ^ v.baseExponent < (10 : ℚ) ^ 16 * 10 ^ v.baseExponent := by
      push_cast; rw [haa] at hroom; nlinarith
    have h2 : ((a + kn : ℕ) : ℚ) < (10 : ℚ) ^ 16 := lt_of_mul_lt_mul_right h1 hp.le
    exact_mod_cast h2

  -- the sum is exact, and the asset holds it
  obtain ⟨w, hw, hwv⟩ := Number.exists_units_normalized (a + kn) v.baseExponent hK ⟨by omega, hbhi⟩
  have haav := Number.operator_add_exact_of_fits v.wf.assetsAvailable_norm hdn h1
    ⟨w, hw, by rw [hwv, haa, hdcv']; push_cast; ring⟩
  have hann := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hdn h1
  have hann0 : 0 ≤ aa.toRat := by rw [haav, haa, hdcv']; positivity
  have hrep : STAmount.isRounded v.numericType aa = false := by
    by_cases hint : v.numericType.isIntegral = true
    · refine STAmount.isRounded_eq_false_of_integral_round _ _ _ hint hann hann0 ?_ h2
      rw [haav, haa, hdcv', hbint hint]
      simp only [zpow_zero, mul_one]
      norm_cast
    · have hfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint)
      rw [STAmount.isRounded_eq_false_iff _ _ hann hann0, hfr, haav, haa, hdcv', ← add_mul]
      have := STAmount.representable_fractional_of_units (a + kn) v.baseExponent hK (by omega) (by omega)
      push_cast at this
      exact this
  rw [STAmount.roundToNumericType_of_isRounded_false _ _ _ hann hrep h2, haav]

/-- Proof body of the base-grid nonnegative part of `Lending.manageDefault_cover`. A default on the base grid never
moves assets from the vault to the cover. -/
lemma Loan.manageDefault_cover_nonneg_at_base (minimumCover liquidationAmount : Number) (a : ℕ)
    (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hnt : loan.broker.numericType = v.numericType)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat ≤ (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    0 ≤ r.amountToPool.toRat := by
  rw [(Loan.manageDefault_at_base loan v _ _ a r hok hmin hliq hnt haa hroom).1]
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have h0 := Int.floor_nonneg.mpr (div_nonneg (Loan.cappedCover_nonneg loan _ _ hmin hliq) hp.le)
  have h0' : (0 : ℚ) ≤ (⌊min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat / 10 ^ v.baseExponent⌋ : ℚ) := by exact_mod_cast h0
  positivity

/-- Proof body of the base-grid lower bound part of `Lending.manageDefault_cover`. A default on the base grid pays
less than one base unit under the capped liquidation amount, and the scale of AssetsAvailable' is the base scale. -/
lemma Loan.manageDefault_cover_lower_bound_at_base (minimumCover liquidationAmount : Number) (a : ℕ)
    (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hnt : loan.broker.numericType = v.numericType)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat ≤ (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat -
        r.amountToPool.toRat < 10 ^ v.baseExponent ∧
      ∀ e, numberExponent r.pool'.assetsAvailable v.baseExponent v.numericType = .ok e → e = v.baseExponent := by
  obtain ⟨hdc, haa'⟩ := Loan.manageDefault_at_base loan v _ _ a r hok hmin hliq hnt haa hroom
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  set capped := min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat
  have hcap0 : 0 ≤ capped := Loan.cappedCover_nonneg loan _ _ hmin hliq
  have hfl := Int.lt_floor_add_one (capped / 10 ^ v.baseExponent)
  rw [div_lt_iff₀ hp] at hfl
  have hfl' := Int.floor_le (capped / 10 ^ v.baseExponent)
  rw [le_div_iff₀ hp] at hfl'
  refine ⟨by rw [hdc]; linarith, fun e he => ?_⟩
  obtain ⟨hblo, -, hbint⟩ := Vault.baseExponent_bounds v
  refine numberExponent_at_base _ _ _ e r.pool'.wf.assetsAvailable_norm r.pool'.exact.assetsAvailable_nonneg
    (by omega) hbint ?_ he
  change r.pool'.assetsAvailable.toRat < _
  rw [haa', hdc]
  linarith

/-- On the base grid a default takes PrincipalOutstanding − defaultCovered off AssetsTotal and adds defaultCovered
to AssetsAvailable, when the new AssetsDeployed fits a `Number`. -/
lemma Loan.manageDefault_vault_at_base (minimumCover liquidationAmount : Number) (a : ℕ)
    (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hnt : loan.broker.numericType = v.numericType)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
      loan.broker.coverAvailable.toRat ≤ (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent)
    (hdeployed : ∃ w : Number, w.isNormalized ∧
      w.toRat = v.assetsDeployed.toRat - loan.principalOutstanding.toRat) :
    r.pool'.toExact.assetsTotal =
        v.toExact.assetsTotal - (loan.principalOutstanding.toRat - r.amountToPool.toRat) ∧
      r.pool'.assetsAvailable.toRat = v.assetsAvailable.toRat + r.amountToPool.toRat := by
  obtain ⟨-, haa'⟩ := Loan.manageDefault_at_base loan v _ _ a r hok hmin hliq hnt haa hroom
  obtain ⟨_, -, hs⟩ := Loan.manageDefault_sums loan v r hok
  have hd := Number.operator_sub_exact_of_fits v.wf.assetsDeployed_norm loan.wf.principalOutstanding_norm
    hs.deployed hdeployed
  refine ⟨?_, haa'⟩
  show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
    v.assetsAvailable.toRat + v.assetsDeployed.toRat - (loan.principalOutstanding.toRat - r.amountToPool.toRat)
  rw [haa', hd]
  ring

/-- Proof body of the base-grid monotone part of `Lending.manageDefault_cover`. On the base grid a larger
CoverAvailable, all else equal, never lowers AssetsTotal by more. -/
lemma Loan.manageDefault_cover_monotone_at_base (loan₁ loan₂ : Loan) (minimumCover liquidationAmount : Number)
    (a : ℕ) (r₁ r₂ : LoanWithAmounts Vault)
    (hloan : loan₂.toRawLoan = { loan₁.toRawLoan with broker := loan₂.broker })
    (hbroker : loan₂.broker.toRawLoanBroker =
      { loan₁.broker.toRawLoanBroker with coverAvailable := loan₂.broker.coverAvailable })
    (hle : loan₁.broker.coverAvailable.toRat ≤ loan₂.broker.coverAvailable.toRat)
    (hok₁ : (loan₁.manageDefault v).run = .ok (.ok r₁)) (hok₂ : (loan₂.manageDefault v).run = .ok (.ok r₂))
    (hmin : tenthBipsOfValue loan₁.broker.debtTotal loan₁.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan₁.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hnt : loan₁.broker.numericType = v.numericType)
    (haa : v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent)
    (hroom : v.assetsAvailable.toRat + min (min liquidationAmount.toRat loan₁.principalOutstanding.toRat)
      loan₂.broker.coverAvailable.toRat ≤ (10 : ℚ) ^ (16 + v.baseExponent) - 10 ^ v.baseExponent) :
    v.toExact.assetsTotal - r₂.pool'.toExact.assetsTotal ≤ v.toExact.assetsTotal - r₁.pool'.toExact.assetsTotal := by
  -- the second loan differs only in CoverAvailable
  have hpo : loan₂.principalOutstanding = loan₁.principalOutstanding := by
    rw [show loan₂.principalOutstanding = loan₂.toRawLoan.principalOutstanding from rfl, hloan]
  have hb : ∀ f : RawLoanBroker → Prop, f { loan₁.broker.toRawLoanBroker with
      coverAvailable := loan₂.broker.coverAvailable } → f loan₂.broker.toRawLoanBroker := fun f hf => by
    rw [hbroker]; exact hf
  have hdt : loan₂.broker.debtTotal = loan₁.broker.debtTotal := hb (·.debtTotal = loan₁.broker.debtTotal) rfl
  have hcm : loan₂.broker.coverRateMinimum = loan₁.broker.coverRateMinimum :=
    hb (·.coverRateMinimum = loan₁.broker.coverRateMinimum) rfl
  have hcl : loan₂.broker.coverRateLiquidation = loan₁.broker.coverRateLiquidation :=
    hb (·.coverRateLiquidation = loan₁.broker.coverRateLiquidation) rfl
  have hnt₂ : loan₂.broker.numericType = v.numericType := by
    rw [← hnt]; exact hb (·.numericType = loan₁.broker.numericType) rfl
  have hmin₂ : tenthBipsOfValue loan₂.broker.debtTotal loan₂.broker.coverRateMinimum .upward = .ok minimumCover := by
    rw [hdt, hcm]; exact hmin
  have hliq₂ : tenthBipsOfValue minimumCover loan₂.broker.coverRateLiquidation .upward = .ok liquidationAmount := by
    rw [hcl]; exact hliq

  -- both defaults are on the base grid, with covers in the order of their caps
  set c₁ := min (min liquidationAmount.toRat loan₁.principalOutstanding.toRat) loan₁.broker.coverAvailable.toRat
  set c₂ := min (min liquidationAmount.toRat loan₁.principalOutstanding.toRat) loan₂.broker.coverAvailable.toRat
  have hc : c₁ ≤ c₂ := min_le_min_left _ hle
  obtain ⟨hdc₁, haa₁⟩ := Loan.manageDefault_at_base loan₁ v _ _ a r₁ hok₁ hmin hliq hnt haa (by linarith)
  obtain ⟨hdc₂, haa₂⟩ := Loan.manageDefault_at_base loan₂ v _ _ a r₂ hok₂ hmin₂ hliq₂ hnt₂ haa
    (by rw [hpo]; exact hroom)
  rw [hpo] at hdc₂
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hfl : ⌊c₁ / 10 ^ v.baseExponent⌋ ≤ ⌊c₂ / 10 ^ v.baseExponent⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right hc hp.le)
  have hfl' : (⌊c₁ / 10 ^ v.baseExponent⌋ : ℚ) ≤ ⌊c₂ / 10 ^ v.baseExponent⌋ := by exact_mod_cast hfl
  have hdle : r₁.amountToPool.toRat ≤ r₂.amountToPool.toRat := by
    rw [hdc₁, hdc₂]; exact mul_le_mul_of_nonneg_right hfl' hp.le

  obtain ⟨_, -, hs₁⟩ := Loan.manageDefault_sums loan₁ v r₁ hok₁
  obtain ⟨_, -, hs₂⟩ := Loan.manageDefault_sums loan₂ v r₂ hok₂
  have hd₁ := hs₁.deployed
  have hd₂ := hs₂.deployed
  simp only [Loan.defaultChange] at hd₁ hd₂
  rw [hpo, hd₁, Except.ok.injEq] at hd₂
  show v.assetsAvailable.toRat + v.assetsDeployed.toRat -
      (r₂.pool'.assetsAvailable.toRat + r₂.pool'.assetsDeployed.toRat) ≤
    v.assetsAvailable.toRat + v.assetsDeployed.toRat - (r₁.pool'.assetsAvailable.toRat + r₁.pool'.assetsDeployed.toRat)
  rw [haa₁, haa₂, hd₂]
  linarith

end XRPL.Model.Lending
