import XRPL.Properties.Lending.Ledger.Common.VaultGrid
import XRPL.Properties.Vault.Proofs.DepositLimit
import XRPL.Properties.Lending.Ledger.Common.BrokerProofs

/-! # Only a payment raises the vault scale

On an IOU vault the scale is above the base scale exactly when AssetsAvailable + AssetsDeployed reaches `10^16` base
units, and an XRP or MPT vault never leaves its base scale. On the base grid of an IOU vault every update below
`10^16` base units is exact, and only a payment can cross it. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts WithdrawAmount)

open private add_downward_ge from XRPL.Properties.Lending.Common.SumRounding
open private STAmount.roundToNumericType_le_stored from XRPL.Properties.Lending.Ledger.Common.VaultOutflow
open private LendingTx.preflight_vaultDeposit from XRPL.Properties.Lending.Ledger.Common.VaultGrid
open private Loan.create_principalOutstanding from XRPL.Properties.Lending.Loan.Common.AcceptProofs
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- The vault scale reads the computed total at the base exponent. -/
private lemma Vault.exponent_ok (v : Vault) (nt : NumericType) (e : Int) (h : AssetPool.exponent v nt = .ok e) :
    ∃ assetsTotal, v.assetsTotal = .ok assetsTotal ∧ numberExponent assetsTotal v.baseExponent nt = .ok e := by
  unfold AssetPool.exponent at h
  obtain ⟨at', hat, h⟩ := bind_ok_peel _ _ _ h
  exact ⟨at', hat, h⟩

/-- The computed total rounds AssetsAvailable + AssetsDeployed down: it is at most the sum, and at least every
`Number` at or below the sum. -/
private lemma Vault.assetsTotal_bounds (v : Vault) (at' : Number) (h : v.assetsTotal = .ok at') :
    at'.isNormalized ∧ at'.toRat ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat ∧
      ∀ w : Number, w.isNormalized → w.toRat ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat →
        w.toRat ≤ at'.toRat := by
  have hAA0 := v.exact.assetsAvailable_nonneg
  have hAD0 := v.exact.assetsDeployed_nonneg
  unfold RawVault.assetsTotal at h
  refine ⟨Number.operator_add_isNormalized_any _ _ _ _ v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm h,
    (Number.operator_add_downward_nonneg_le _ _ _ v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm hAA0 hAD0 h).1,
    fun w hw hwt => add_downward_ge _ _ _ w v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm hAA0 hAD0 h hw hwt⟩

/-- `10^(16 + b)` is a `Number`. -/
private lemma Number.exists_open_line (b : Int) (hb : -10 ≤ b ∧ b ≤ 0) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (10 : ℚ) ^ (16 + b) := by
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) b (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  refine ⟨w, hw, ?_⟩
  rw [hwv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
  push_cast
  norm_num

/-- A vault at its base scale holds less than `10^16` base units. -/
private lemma Vault.total_lt_of_scale (v : Vault) (e : Int) (hfr : v.numericType = .fractional)
    (he : AssetPool.exponent v v.numericType = .ok e) (hle : e ≤ v.baseExponent) :
    v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent) := by
  obtain ⟨hb, -⟩ := Vault.baseExponent_grid v
  have hb0 := v.baseExponent_bounds.2.1
  obtain ⟨at', hat, hn⟩ := Vault.exponent_ok v _ e he
  obtain ⟨hatn, -, hge⟩ := Vault.assetsTotal_bounds v at' hat
  rw [hfr] at hn
  have hee : e = v.baseExponent := le_antisymm hle (numberExponent_ge _ _ _ _ hn)
  have hlt := numberExponent_frac_lt at' _ e hatn (by omega) hn
  rw [hee, add_comm] at hlt
  by_contra hc
  push Not at hc
  obtain ⟨w, hw, hwv⟩ := Number.exists_open_line _ ⟨hb, hb0⟩
  have := hge w hw (by rw [hwv]; exact hc)
  rw [hwv] at this
  linarith

/-- A vault above its base scale holds at least `10^16` base units. -/
private lemma Vault.total_ge_of_scale (v : Vault) (e : Int) (hfr : v.numericType = .fractional)
    (he : AssetPool.exponent v v.numericType = .ok e) (hgt : v.baseExponent < e) :
    10 ^ (16 + v.baseExponent) ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  obtain ⟨hb, -⟩ := Vault.baseExponent_grid v
  obtain ⟨at', hat, hn⟩ := Vault.exponent_ok v _ e he
  obtain ⟨hatn, hle, -⟩ := Vault.assetsTotal_bounds v at' hat
  have hat0 : 0 ≤ at'.toRat := by
    have := (Number.operator_add_downward_nonneg_le _ _ _ v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm
      v.exact.assetsAvailable_nonneg v.exact.assetsDeployed_nonneg hat).2
    exact this
  rw [hfr] at hn
  obtain ⟨-, hbig⟩ := numberExponent_frac_lower at' _ e hatn hat0 (by omega) hn hgt
  have : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 10 ^ (e + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith

/-- An integral vault never leaves its base scale. -/
private lemma Vault.scale_integral (v : Vault) (e : Int) (hint : v.numericType.isIntegral = true)
    (he : AssetPool.exponent v v.numericType = .ok e) : e ≤ v.baseExponent := by
  obtain ⟨at', -, hn⟩ := Vault.exponent_ok v _ e he
  have h1 := XRPL.Model.SingleAssetVault.numberExponent_integral_le at' _ _ e hint hn
  have h0 := v.baseExponent_bounds.2.2 hint
  omega

/-- A whole number of base units below `10^16` of them is a value an IOU vault's asset stores exactly. -/
private lemma Vault.isRounded_false_of_grid (v : Vault) (x : Number) (hfr : v.numericType = .fractional)
    (hx : Number.OnGrid v.baseExponent x) (h0 : 0 ≤ x.toRat) (hlt : x.toRat < 10 ^ (16 + v.baseExponent)) :
    STAmount.isRounded v.numericType x = false := by
  obtain ⟨hxn, k, hk⟩ := hx
  obtain ⟨hb, -⟩ := Vault.baseExponent_grid v
  have hb0 := v.baseExponent_bounds.2.1
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hk0 : 0 ≤ k := by
    have : (0 : ℚ) ≤ (k : ℚ) * 10 ^ v.baseExponent := hk ▸ h0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hk16 : k < 10 ^ 16 := by
    have : (k : ℚ) * 10 ^ v.baseExponent < ((10 ^ 16 : ℤ) : ℚ) * 10 ^ v.baseExponent := by
      rw [← hk, show ((10 ^ 16 : ℤ) : ℚ) = (10 : ℚ) ^ 16 by norm_num, ← open_line_eq]; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  rw [STAmount.isRounded_eq_false_iff _ _ hxn h0, hfr, hk]
  have := STAmount.representable_fractional_of_units k.toNat v.baseExponent (by omega) (by omega) (by omega)
  rwa [show ((k.toNat : ℕ) : ℚ) = (k : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk0] at this

/-- On the base grid below `10^16` base units, the computed total is AssetsAvailable + AssetsDeployed. -/
private lemma Vault.assetsTotal_eq_of_grid (v : Vault) (at' : Number) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (h : v.assetsTotal = .ok at') : at'.toRat = v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨-, hle, hge⟩ := Vault.assetsTotal_bounds v at' h
  obtain ⟨⟨_, a, ha⟩, ⟨_, c, hc⟩⟩ := hv
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hsum : v.assetsAvailable.toRat + v.assetsDeployed.toRat = ((a + c : ℤ) : ℚ) * 10 ^ v.baseExponent := by
    rw [ha, hc]; push_cast; ring
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have h0 : 0 ≤ a + c := by
    have : (0 : ℚ) ≤ ((a + c : ℤ) : ℚ) * 10 ^ v.baseExponent := by
      rw [← hsum]; linarith
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have h16 : a + c < 10 ^ 16 := by
    have : ((a + c : ℤ) : ℚ) * 10 ^ v.baseExponent < ((10 ^ 16 : ℤ) : ℚ) * 10 ^ v.baseExponent := by
      rw [← hsum, show ((10 ^ 16 : ℤ) : ℚ) = (10 : ℚ) ^ 16 by norm_num, ← open_line_eq]; exact hS
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (a + c) _ ⟨by omega, by omega⟩ hsr
  have := hge w hw (by rw [hwv, hsum])
  rw [hwv, ← hsum] at this
  linarith

/-- A cash update below `10^16` base units writes at most its sum, and at most zero for a negative sum:
on the base grid the sum is exact and the asset stores it. -/
private lemma Vault.cash_update_le (v : Vault) (cash aa aa' : Number) (hfr : v.numericType = .fractional)
    (hv : Number.OnGrid v.baseExponent v.assetsAvailable) (hc : Number.OnGrid v.baseExponent cash)
    (hlt : v.assetsAvailable.toRat + cash.toRat < 10 ^ (16 + v.baseExponent))
    (hs : v.assetsAvailable.operator_add cash .to_nearest = .ok aa)
    (hr : STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa') :
    aa'.toRat ≤ max (v.assetsAvailable.toRat + cash.toRat) 0 := by
  have hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hfr]; intro h'; cases h'
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have han := operator_add_isNormalized_to_nearest_sz _ _ _ hv.1 hc.1 hs
  have hR := operator_add_rounded_to_nearest _ _ _ hv.1 hc.1 hs
  by_cases hneg : v.assetsAvailable.toRat + cash.toRat < 0
  · -- the sum rounds to at most zero, and so does its rounding to the asset
    have haa0 : aa.toRat ≤ Number.zero.toRat := Number.roundsToRepresentable_le aa _ hR Number.zero
      Number.zero_isNormalized (by rw [Number.toRat_zero]; linarith)
    have := STAmount.roundToNumericType_le_stored v.numericType Number.zero aa aa' hmax Number.zero_isNormalized
      (by rw [Number.toRat_zero]) (STAmount.isRounded_zero _) han haa0 hr
    rw [Number.toRat_zero] at this
    exact le_trans this (le_max_right _ _)
  · push Not at hneg
    have hT : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 2 ^ 63 * 10 ^ v.baseExponent := by
      rw [open_line_eq]; exact mul_le_mul_of_nonneg_right (by norm_num) hp.le
    have haav : aa.toRat = v.assetsAvailable.toRat + cash.toRat :=
      Number.add_exact_of_grid hv hc (by nlinarith) (by linarith) hsr hs
    have hag : Number.OnGrid v.baseExponent aa := Number.OnGrid.add hv hc hsr hs
    have hst := Vault.isRounded_false_of_grid v aa hfr hag (by rw [haav]; exact hneg) (by rw [haav]; exact hlt)
    have := STAmount.roundToNumericType_le_stored _ aa aa aa' hmax han (by rw [haav]; exact hneg) hst han le_rfl hr
    rw [haav] at this
    exact le_trans this (le_max_left _ _)

/-- A balance change below `10^16` base units bounds the new total: AssetsAvailable gains at most the cash
and AssetsDeployed gains exactly the deployed amount. -/
private lemma Vault.adjustBalances_total_le (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v) (hc : Number.OnGrid v.baseExponent c.cash)
    (hd : Number.OnGrid v.baseExponent c.deployed)
    (hlt : v.assetsAvailable.toRat + c.cash.toRat < 10 ^ (16 + v.baseExponent))
    (hdlo : -(2 ^ 63 * (10 : ℚ) ^ v.baseExponent) < v.assetsDeployed.toRat + c.deployed.toRat)
    (hdhi : v.assetsDeployed.toRat + c.deployed.toRat < 2 ^ 63 * (10 : ℚ) ^ v.baseExponent)
    (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat ≤ max (v.assetsAvailable.toRat + c.cash.toRat) 0 ∧
      raw.assetsDeployed.toRat = v.assetsDeployed.toRat + c.deployed.toRat := by
  obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv v c raw h
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨aa, haa, hround⟩ := hs.cash
  exact ⟨Vault.cash_update_le v _ _ _ hfr hv.1 hc hlt haa hround,
    Number.add_exact_of_grid hv.2 hd hdlo hdhi hsr hs.deployed⟩

/-- A vault written from a raw record has that record's AssetsAvailable and AssetsDeployed. -/
private lemma Vault.total_of_raw {v' : Vault} {raw : RawVault} (h : raw.to_lawful = .ok v') :
    v'.assetsAvailable.toRat + v'.assetsDeployed.toRat = raw.assetsAvailable.toRat + raw.assetsDeployed.toRat := by
  have hraw := (RawVault.to_lawful_ok h).1
  rw [show v'.assetsAvailable = v'.toRawVault.assetsAvailable from rfl,
    show v'.assetsDeployed = v'.toRawVault.assetsDeployed from rfl, hraw]

/-- A balance change that moves no cash and deploys nothing never raises the total. -/
private lemma Vault.poolAdjust_zero_total_le (v v' : Vault) (c : PoolBalanceChange) (hfr : v.numericType = .fractional)
    (hv : Vault.OnBaseGrid v) (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hc : c.cash = Number.zero) (hd : c.deployed = Number.zero) (h : AssetPool.adjustBalances v c = .ok (.ok v')) :
    v'.assetsAvailable.toRat + v'.assetsDeployed.toRat ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  obtain ⟨raw, hadj, hlaw⟩ := Vault.poolAdjust_ok_inv v c v' h
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hT : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 2 ^ 63 * 10 ^ v.baseExponent := by
    rw [open_line_eq]; exact mul_le_mul_of_nonneg_right (by norm_num) hp.le
  obtain ⟨h1, h2⟩ := Vault.adjustBalances_total_le v c raw hfr hv (by rw [hc]; exact Number.OnGrid.zero _)
    (by rw [hd]; exact Number.OnGrid.zero _) (by rw [hc, Number.toRat_zero]; linarith)
    (by rw [hd, Number.toRat_zero]; nlinarith) (by rw [hd, Number.toRat_zero]; linarith) hadj
  rw [hc, Number.toRat_zero, add_zero, max_eq_left hAA0] at h1
  rw [hd, Number.toRat_zero, add_zero] at h2
  rw [Vault.total_of_raw hlaw]
  linarith

/-- A new loan never raises the total: its principal leaves AssetsAvailable and joins AssetsDeployed exactly. -/
private lemma Loan.create_total_le (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithDisbursement Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (h : (Loan.create broker v principal rates fees schedule ao pending).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  obtain ⟨_, loanState, _, principal', _, hchecks, hround, hpool, -, -⟩ := Loan.create_ok_inv broker v principal
    rates fees schedule ao pending r h
  have hpo := Loan.create_principalOutstanding broker v principal rates fees schedule ao pending r hp hpos.le hst h
  have hls := Loan.create_loanScale_proof broker v principal rates fees schedule ao pending r hp hpos hst hnt h
  have hpg : Number.OnGrid v.baseExponent principal := by
    rw [← hpo, ← hls]; exact (Loan.principal_onGrid r.loan').1
  have hpg' := STAmount.roundToNumericType_onGrid_none _ _ _ _ _ hpg (by have := Vault.baseExponent_grid v; omega)
    (by rw [hnt, hfr]; intro h'; cases h') hround
  have hpv : principal'.toRat = principal.toRat := STAmount.roundToNumericType_of_isRounded_false _ _ _ hp hst hround
  -- LoanSet checks that AssetsAvailable covers the principal
  have hfunds : principal.toRat ≤ v.assetsAvailable.toRat := by
    have hf := hchecks.funds
    by_contra hc
    push Not at hc
    rw [(operator_lt_iff _ _ v.wf.assetsAvailable_norm hp).mpr hc] at hf
    cases hf
  obtain ⟨raw, hadj, hlaw⟩ := Vault.poolAdjust_ok_inv v _ r.pool' hpool
  have hp' : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hT : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 2 ^ 63 * 10 ^ v.baseExponent := by
    rw [open_line_eq]; exact mul_le_mul_of_nonneg_right (by norm_num) hp'.le
  have hcash :
      (Loan.createChange principal principal' loanState.interestDue pending).cash.toRat = -principal.toRat := by
    show principal'.operator_neg.toRat = _; rw [Number.toRat_neg, hpv]
  obtain ⟨h1, h2⟩ := Vault.adjustBalances_total_le v _ raw hfr hv hpg'.neg hpg (by rw [hcash]; linarith)
    (by show _ < v.assetsDeployed.toRat + principal.toRat; nlinarith)
    (by show v.assetsDeployed.toRat + principal.toRat < _; linarith) hadj
  rw [hcash, max_eq_left (by linarith)] at h1
  have h2' : raw.assetsDeployed.toRat = v.assetsDeployed.toRat + principal.toRat := h2
  rw [Vault.total_of_raw hlaw]
  linarith

/-- An accept never raises the total: it moves no cash and deploys nothing. -/
private lemma Loan.accept_total_le (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (h : (loan.accept v).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact Vault.poolAdjust_zero_total_le v _ _ hfr hv hS rfl rfl ‹_›

/-- An impairment change never raises the total: it moves no cash and deploys nothing. -/
private lemma Loan.changeImpairment_total_le (loan : Loan) (v : Vault) (impaired : Bool) (r : LoanWithPool Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (h : (Loan.changeImpairment loan v impaired).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_zero_total_le v _ _ hfr hv hS rfl rfl ‹_›

/-- Taking a whole number of base units below `2^63` of them off AssetsDeployed is exact, and the vault's
re-check keeps the result at least zero, so the amount is at most AssetsDeployed. -/
private lemma Vault.deployed_take (v : Vault) (x : Number) (raw : RawVault) {v' : Vault} (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hx : Number.OnGrid v.baseExponent x) (hx0 : 0 ≤ x.toRat) (hx63 : x.toRat < 2 ^ 63 * 10 ^ v.baseExponent)
    (hd : v.assetsDeployed.operator_add x.operator_neg .to_nearest = .ok raw.assetsDeployed)
    (hlaw : raw.to_lawful = .ok v') :
    raw.assetsDeployed.toRat = v.assetsDeployed.toRat - x.toRat ∧ x.toRat ≤ v.assetsDeployed.toRat := by
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid v
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hT : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 2 ^ 63 * 10 ^ v.baseExponent := by
    rw [open_line_eq]; exact mul_le_mul_of_nonneg_right (by norm_num) hp.le
  have hex := Number.add_exact_of_grid hv.2 hx.neg (by rw [Number.toRat_neg]; linarith)
    (by rw [Number.toRat_neg]; linarith) hsr hd
  rw [Number.toRat_neg] at hex
  have hnn : 0 ≤ raw.assetsDeployed.toRat := by
    have hraw := (RawVault.to_lawful_ok hlaw).1
    have := v'.exact.assetsDeployed_nonneg
    rwa [show v'.toExact.assetsDeployed = v'.toRawVault.assetsDeployed.toRat from rfl, hraw] at this
  exact ⟨by rw [hex]; ring, by linarith⟩

/-- A pending delete never raises the total: the principal leaves AssetsDeployed and returns to AssetsAvailable
exactly. -/
private lemma Loan.delete_total_le (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hls : loan.loanScale = v.baseExponent) (hnt : loan.broker.numericType = v.numericType)
    (h : (loan.delete v).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  by_cases hp : loan.isPending = true
  · obtain ⟨principal', raw, _, hround, hadj, hlaw, -, -⟩ := Loan.delete_pending_ok_inv loan v r hp h
    obtain ⟨hpg, hp63⟩ := Loan.principal_onGrid loan
    rw [hls] at hpg hp63
    have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv v _ raw hadj
    obtain ⟨hdx, hle⟩ := Vault.deployed_take v _ raw hv hS hpg hp0 hp63 hs.deployed hlaw
    -- the principal is below `10^16` base units, so the asset stores it and returns it exactly
    have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
    have hst := Vault.isRounded_false_of_grid v _ hfr hpg hp0 (by linarith)
    rw [hnt] at hround
    have hpv : principal'.toRat = loan.principalOutstanding.toRat :=
      STAmount.roundToNumericType_of_isRounded_false _ _ _ loan.wf.principalOutstanding_norm hst hround
    have hpg' := STAmount.roundToNumericType_onGrid_none _ _ _ _ _ hpg (by have := Vault.baseExponent_grid v; omega)
      (by rw [hfr]; intro h'; cases h') hround
    obtain ⟨aa, haa, hr⟩ := hs.cash
    have hcash := Vault.cash_update_le v _ _ _ hfr hv.1 hpg' (by rw [hpv]; linarith) haa hr
    rw [hpv, max_eq_left (by linarith)] at hcash
    rw [Vault.total_of_raw hlaw]
    linarith
  · simp only [Loan.delete, Bool.not_eq_true] at h hp
    rw [hp] at h
    unfold_ter at h
    walk_ok
    exact le_rfl

/-- A default never raises the total: the cover it adds is at most the principal it takes off
AssetsDeployed. -/
private lemma Loan.manageDefault_total_le (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hls : loan.loanScale = v.baseExponent) (hnt : loan.broker.numericType = v.numericType)
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  obtain ⟨_, _, _, raw, _, -, hdc, hadj, hraw, -⟩ := Loan.manageDefault_ok_parts loan v r h
  obtain ⟨mc, liq, cov, st, hmc, hliq, -, hsrs, hst⟩ := Loan.defaultCover_parts loan v _ hdc
  have hdcle := Loan.defaultCover_le loan v _ mc liq hdc hmc hliq
  have hdcpo : r.amountToPool.toRat ≤ loan.principalOutstanding.toRat :=
    le_trans hdcle (le_trans (min_le_left _ _) (min_le_right _ _))
  obtain ⟨hb, -⟩ := Vault.baseExponent_grid v
  have hdcg := sumRoundAndSubtract_onGrid _ _ _ _ _ st _ hv.1 ⟨hb, v.baseExponent_bounds.2.1⟩
    (by rw [hnt, hfr]; intro h'; cases h') hsrs hst
  obtain ⟨hpg, hp63⟩ := Loan.principal_onGrid loan
  rw [hls] at hpg hp63
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv v _ raw hadj
  have hlaw : raw.to_lawful = .ok r.pool' := by
    rw [← hraw]; unfold RawVault.to_lawful; exact dif_pos ⟨r.pool'.wf, r.pool'.valid⟩
  obtain ⟨hdx, hle⟩ := Vault.deployed_take v _ raw hv hS hpg hp0 hp63 hs.deployed hlaw
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  obtain ⟨aa, haa, hr⟩ := hs.cash
  have hcash := Vault.cash_update_le v _ _ _ hfr hv.1 hdcg (by linarith) haa hr
  rw [show r.pool'.assetsAvailable = r.pool'.toRawVault.assetsAvailable from rfl,
    show r.pool'.assetsDeployed = r.pool'.toRawVault.assetsDeployed from rfl, hraw]
  have hdx' : raw.assetsDeployed.toRat = v.assetsDeployed.toRat - loan.principalOutstanding.toRat := hdx
  have hcash' : raw.assetsAvailable.toRat ≤ max (v.assetsAvailable.toRat + r.amountToPool.toRat) 0 := hcash
  rcases le_total 0 (v.assetsAvailable.toRat + r.amountToPool.toRat) with h0 | h0
  · rw [max_eq_left h0] at hcash'; linarith
  · rw [max_eq_right h0] at hcash'; linarith

open XRPL.Model.SingleAssetVault in
/-- A deposit stays below `10^16` base units: the inflow check keeps the total plus the charge within the Open-zone
limit plus one base unit, and on the base grid the charge lands exactly. -/
private lemma Vault.deposit_total_lt (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (r : VaultWithAmounts) (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    r.vault'.assetsAvailable.toRat + r.vault'.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent) := by
  obtain ⟨ra, amounts, raw, hra, hcomp, hin, hadj, hraw, -, -⟩ :=
    Vault.deposit_ok_reduces v amount isDonation t hpos r h
  have hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hfr]; intro h'; cases h'
  obtain ⟨hrac, hraty, -⟩ := Vault.roundedDepositAmount_form v amount ra hc hty hra
  obtain ⟨hcf, -, hc0⟩ := computeDeposit_assets_form v ra isDonation amounts hrac hraty hmax hcomp
  have hcharge : ∃ k : ℤ, amounts.assets.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
    cases isDonation
    · obtain ⟨assets, assetsTotal, -, -, hsta, -, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ (sharesToAssetsDeposit_form v amounts.shares assets hmax hsta).1 hcl
    · obtain ⟨assetsTotal, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ hrac hcl
  -- the inflow check bounds the computed total plus the charge
  obtain ⟨navN, hat⟩ : ∃ navN, v.assetsTotal = .ok navN := by
    cases hat : v.assetsTotal with
    | ok n => exact ⟨n, rfl⟩
    | error e =>
      simp only [Vault.checkOpenLimit, hat, bind, Except.bind] at hin
      cases hin
  have hbound := Vault.checkOpenLimit_bound v amounts.assets hcf hc0 navN hat hin
  rw [Vault.assetsTotal_eq_of_grid v navN hv hS hat] at hbound
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, hrw⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hnv, hnn⟩ := hcf.toNumber_exact assetsNum hnum
  obtain ⟨k, hk⟩ := hcharge
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hlim : 9 * (10 : ℚ) ^ (15 + v.baseExponent) + 10 ^ v.baseExponent < 10 ^ (16 + v.baseExponent) := by
    rw [open_line_eq, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; nlinarith
  have hcash := Vault.cash_update_le v assetsNum s aa' hfr hv.1 ⟨hnn, k, by rw [hnv, hk]⟩ (by rw [hnv]; linarith)
    hs haa
  rw [hnv, max_eq_left (by linarith)] at hcash
  rw [show r.vault'.assetsAvailable = r.vault'.toRawVault.assetsAvailable from rfl,
    show r.vault'.assetsDeployed = r.vault'.toRawVault.assetsDeployed from rfl, hraw, hrw]
  show aa'.toRat + v.assetsDeployed.toRat < _
  linarith

/-- A stored loan refreshed with its broker is at the base scale, on a broker of the vault's asset. -/
private lemma LendingLedger.ScaleInv.refreshed {l : LendingLedger} (hinv : l.ScaleInv) {i : Nat} {e : LoanEntry}
    {broker : LoanBroker} {loan : Loan} (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some broker)
    (hw : e.loan.withBroker broker = .ok loan) :
    loan.loanScale = l.vault.baseExponent ∧ loan.broker.numericType = l.vault.numericType := by
  have hraw := Loan.withBroker_eq hw
  refine ⟨?_, ?_⟩
  · rw [show loan.loanScale = loan.toRawLoan.loanScale from rfl, hraw]; exact hinv.loanScale i e he
  · rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]; exact hinv.brokers _ broker hb

/-- Every transaction but a payment keeps an IOU vault below `10^16` base units. -/
private lemma LendingLedger.total_lt_step (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (hfr : l.vault.numericType = .fractional)
    (hS : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ (16 + l.vault.baseExponent))
    (hpay : ¬ ∃ i pt amount, tx = .loanPay i pt amount) :
    l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat < 10 ^ (16 + l.vault.baseExponent) := by
  have hgrid := hr.gridInv
  have hv := hgrid.grid hfr
  have hinv := hgrid.scale
  have hpre := (LendingLedger.apply_checked h).1
  have hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hfr]; intro h'; cases h'
  by_cases hvt : tx.isVault = true
  · -- withdrawals and clawbacks only lower AssetsAvailable
    by_cases hout : (∃ holder amount, tx = .vaultWithdraw holder amount) ∨
        ∃ holder assets, tx = .vaultClawback holder assets
    · obtain ⟨-, hle, hAD⟩ := LendingLedger.lent_out_protected_proof l l' tx hr hmax hout h
      rw [hAD]; linarith
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hvt h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    have hAD := (l.applyVault_keepsLending tx u hu).assetsDeployed
    cases tx with
    | vaultDeposit hd amount isDonation =>
      obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit l hd amount isDonation hfr hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · unfold_ter at hu
        walk_ok
        exact Vault.deposit_total_lt _ _ _ _ _ hc hty hfr hv hS _ ‹_›
      · cases hu
    | vaultWithdraw hd amount => exact absurd (Or.inl ⟨hd, amount, rfl⟩) hout
    | vaultClawback hd assets => exact absurd (Or.inr ⟨hd, assets, rfl⟩) hout
    | vaultBurnShares hd amount =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
      rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)]
      exact hS
    | vaultSet m b =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
      rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)]
      exact hS
    | _ => simp only [LendingTx.isVault] at hvt; cases hvt
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact hS
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    show u.vault.assetsAvailable.toRat + u.vault.assetsDeployed.toRat < _
    refine lt_of_le_of_lt ?_ hS
    cases tx with
    | loanSet i principal rates fees pi pt gp sd twoStep ao =>
      obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
      simp only [LendingLedger.applyLoan] at hu
      obtain ⟨broker, r, hb', hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
      have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
      exact Loan.create_total_le _ _ _ _ _ _ _ _ r hfr hv hS hpn hpos hst (hinv.brokers i broker hb') hcr
    | loanAccept i =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_accept_inv u i hu
      exact Loan.accept_total_le _ _ _ hfr hv hS hr'
    | loanDelete i =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_delete_inv u i hu
      obtain ⟨hls, hnt⟩ := hinv.refreshed he hb' hw
      exact Loan.delete_total_le _ _ _ hfr hv hS hls hnt hr'
    | loanManage i action =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_manage_inv u i action hu
      obtain ⟨hls, hnt⟩ := hinv.refreshed he hb' hw
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤ _
      cases action with
      | impair =>
        simp only [Loan.manage, Loan.manageImpair] at hr'
        unfold_ter at hr'
        walk_ok
        exact Loan.changeImpairment_total_le loan _ true _ hfr hv hS ‹_›
      | unimpair => exact Loan.changeImpairment_total_le loan _ false r hfr hv hS hr'
      | default =>
        simp only [Loan.manage] at hr'
        unfold_ter at hr'
        walk_ok'
        exact Loan.manageDefault_total_le loan _ _ hfr hv hS hls hnt ‹_›
    | loanPay i paymentType amount => exact absurd ⟨i, paymentType, amount, rfl⟩ hpay
    | _ => simp only [LendingLedger.applyLoan] at hu; cases hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hvt hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hS
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact hS

/-- Proof body of `Lending.vault_scale_changes`. -/
lemma LendingLedger.vault_scale_changes_proof (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (e e' : Int)
    (he : AssetPool.exponent l.vault l.vault.numericType = .ok e)
    (he' : AssetPool.exponent l'.vault l'.vault.numericType = .ok e')
    (hle : e ≤ l.vault.baseExponent) (hgt : l'.vault.baseExponent < e') :
    ∃ i pt amount, tx = .loanPay i pt amount := by
  by_contra hpay
  have hbe := LendingLedger.apply_baseExponent h
  have hnt := LendingLedger.apply_numericType h
  cases hi : l.vault.numericType.isIntegral
  · -- an IOU vault would cross `10^16` base units
    have hfr : l.vault.numericType = .fractional := NumericType.eq_fractional_of_not_integral hi
    have hS := Vault.total_lt_of_scale l.vault e hfr he hle
    have hS' := Vault.total_ge_of_scale l'.vault e' (hnt.trans hfr) he' hgt
    have hlt := LendingLedger.total_lt_step l l' tx hr h hfr hS hpay
    rw [hbe] at hS'
    linarith
  · -- an integral vault never leaves its base scale
    have := Vault.scale_integral l'.vault e' (by rw [hnt]; exact hi) he'
    omega

end XRPL.Model.Lending
