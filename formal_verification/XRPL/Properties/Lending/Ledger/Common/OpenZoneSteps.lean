import XRPL.Properties.Lending.Ledger.Common.BaseGrid
import XRPL.Properties.Lending.Ledger.Common.LoansInv
import XRPL.Properties.Lending.Ledger.Common.ReachableFromIn
import XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
import XRPL.Properties.Lending.Loan.Common.InterestDue
import XRPL.Properties.Lending.Loan.Common.YieldValue

/-! # AssetsTotal + YieldUnrealized inside the Open zone

Deposits, new loans and accepts pass the Open-limit check. While the vault is not coarsened no other transaction
raises AssetsTotal + YieldUnrealized, except a payment by what it collects beyond the schedule. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts WithdrawAmount)

open private Vault.total_of_raw Vault.deployed_take Vault.assetsTotal_eq_of_grid Vault.assetsTotal_bounds
  from XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
open private STAmount.roundToNumericType_le_stored from XRPL.Properties.Lending.Ledger.Common.VaultOutflow
open private LendingTx.preflight_vaultDeposit from XRPL.Properties.Lending.Ledger.Common.VaultGrid
open private Loan.create_principalOutstanding from XRPL.Properties.Lending.Loan.Common.AcceptProofs
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Loan.canAccept_open from XRPL.Properties.Lending.Loan.Common.YieldValue

/-- A whole number of base units below `10^16` of them is a value the vault's asset stores exactly. -/
lemma Vault.isRounded_false_of_grid' (v : Vault) (hasset : Vault.HoldsAsset v) (x : Number)
    (hx : Number.OnGrid v.baseExponent x) (h0 : 0 ≤ x.toRat) (hlt : x.toRat < 10 ^ (16 + v.baseExponent)) :
    STAmount.isRounded v.numericType x = false := by
  obtain ⟨hxn, k, hk⟩ := hx
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hk0 : 0 ≤ k := by
    have : (0 : ℚ) ≤ (k : ℚ) * 10 ^ v.baseExponent := hk ▸ h0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hk16 : k < 10 ^ 16 := by
    have : (k : ℚ) * 10 ^ v.baseExponent < ((10 ^ 16 : ℤ) : ℚ) * 10 ^ v.baseExponent := by
      rw [← hk, show ((10 ^ 16 : ℤ) : ℚ) = (10 : ℚ) ^ 16 by norm_num, ← open_line_eq]; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  refine hasset.isRounded_units x k.toNat hxn (by omega) ?_
  rw [hk]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hk0).symm

/-- A cash update below `10^16` base units writes at most its sum, and at most zero for a negative sum:
on the base grid the sum is exact and the asset stores it. -/
private lemma Vault.cash_update_le' (v : Vault) (cash aa aa' : Number) (hasset : Vault.HoldsAsset v)
    (hv : Number.OnGrid v.baseExponent v.assetsAvailable) (hc : Number.OnGrid v.baseExponent cash)
    (hlt : v.assetsAvailable.toRat + cash.toRat < 10 ^ (16 + v.baseExponent))
    (hs : v.assetsAvailable.operator_add cash .to_nearest = .ok aa)
    (hr : STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa') :
    aa'.toRat ≤ max (v.assetsAvailable.toRat + cash.toRat) 0 := by
  have hmax := hasset.maxValue_le
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
    have hst := Vault.isRounded_false_of_grid' v hasset aa hag (by rw [haav]; exact hneg) (by rw [haav]; exact hlt)
    have := STAmount.roundToNumericType_le_stored _ aa aa aa' hmax han (by rw [haav]; exact hneg) hst han le_rfl hr
    rw [haav] at this
    exact le_trans this (le_max_left _ _)

/-- A balance change below `10^16` base units bounds the new total: AssetsAvailable gains at most the cash
and AssetsDeployed gains exactly the deployed amount. -/
private lemma Vault.adjustBalances_total_le' (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v) (hc : Number.OnGrid v.baseExponent c.cash)
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
  exact ⟨Vault.cash_update_le' v _ _ _ hasset hv.1 hc hlt haa hround,
    Number.add_exact_of_grid hv.2 hd hdlo hdhi hsr hs.deployed⟩

/-- A balance change that moves no cash and deploys nothing never raises the total. -/
private lemma Vault.poolAdjust_zero_total_le' (v v' : Vault) (c : PoolBalanceChange) (hasset : Vault.HoldsAsset v)
    (hv : Vault.OnBaseGrid v) (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hc : c.cash = Number.zero) (hd : c.deployed = Number.zero) (h : AssetPool.adjustBalances v c = .ok (.ok v')) :
    v'.assetsAvailable.toRat + v'.assetsDeployed.toRat ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  obtain ⟨raw, hadj, hlaw⟩ := Vault.poolAdjust_ok_inv v c v' h
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hT : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 2 ^ 63 * 10 ^ v.baseExponent := by
    rw [open_line_eq]; exact mul_le_mul_of_nonneg_right (by norm_num) hp.le
  obtain ⟨h1, h2⟩ := Vault.adjustBalances_total_le' v c raw hasset hv (by rw [hc]; exact Number.OnGrid.zero _)
    (by rw [hd]; exact Number.OnGrid.zero _) (by rw [hc, Number.toRat_zero]; linarith)
    (by rw [hd, Number.toRat_zero]; nlinarith) (by rw [hd, Number.toRat_zero]; linarith) hadj
  rw [hc, Number.toRat_zero, add_zero, max_eq_left hAA0] at h1
  rw [hd, Number.toRat_zero, add_zero] at h2
  rw [Vault.total_of_raw hlaw]
  linarith

/-- A new loan never raises the total: its principal leaves AssetsAvailable and joins AssetsDeployed exactly. -/
private lemma Loan.create_total_le' (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
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
    (fun h' => v.baseExponent_bounds.2.2 (by rw [← hnt]; exact h')) hround
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
  obtain ⟨h1, h2⟩ := Vault.adjustBalances_total_le' v _ raw hasset hv hpg'.neg hpg (by rw [hcash]; linarith)
    (by show _ < v.assetsDeployed.toRat + principal.toRat; nlinarith)
    (by show v.assetsDeployed.toRat + principal.toRat < _; linarith) hadj
  rw [hcash, max_eq_left (by linarith)] at h1
  have h2' : raw.assetsDeployed.toRat = v.assetsDeployed.toRat + principal.toRat := h2
  rw [Vault.total_of_raw hlaw]
  linarith

/-- An accept moves no cash and deploys nothing. -/
private lemma Loan.accept_total_le' (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (h : (loan.accept v).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact Vault.poolAdjust_zero_total_le' v _ _ hasset hv hS rfl rfl ‹_›

/-- An impairment change moves no cash and deploys nothing. -/
private lemma Loan.changeImpairment_total_le' (loan : Loan) (v : Vault) (impaired : Bool) (r : LoanWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (h : (Loan.changeImpairment loan v impaired).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_zero_total_le' v _ _ hasset hv hS rfl rfl ‹_›

/-- A delete never raises the total. A pending one moves its principal from AssetsDeployed back to AssetsAvailable
exactly, an active one moves nothing. -/
private lemma Loan.delete_total_le' (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
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
    have hst := Vault.isRounded_false_of_grid' v hasset _ hpg hp0 (by linarith)
    rw [hnt] at hround
    have hpv : principal'.toRat = loan.principalOutstanding.toRat :=
      STAmount.roundToNumericType_of_isRounded_false _ _ _ loan.wf.principalOutstanding_norm hst hround
    have hpg' := STAmount.roundToNumericType_onGrid_none _ _ _ _ _ hpg (by have := Vault.baseExponent_grid v; omega)
      (fun h' => v.baseExponent_bounds.2.2 h') hround
    obtain ⟨aa, haa, hr⟩ := hs.cash
    have hcash := Vault.cash_update_le' v _ _ _ hasset hv.1 hpg' (by rw [hpv]; linarith) haa hr
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
private lemma Loan.manageDefault_total_le' (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
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
    (fun h' => v.baseExponent_bounds.2.2 (by rw [← hnt]; exact h')) hsrs hst
  obtain ⟨hpg, hp63⟩ := Loan.principal_onGrid loan
  rw [hls] at hpg hp63
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv v _ raw hadj
  have hlaw : raw.to_lawful = .ok r.pool' := by
    rw [← hraw]; unfold RawVault.to_lawful; exact dif_pos ⟨r.pool'.wf, r.pool'.valid⟩
  obtain ⟨hdx, hle⟩ := Vault.deployed_take v _ raw hv hS hpg hp0 hp63 hs.deployed hlaw
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  obtain ⟨aa, haa, hr⟩ := hs.cash
  have hcash := Vault.cash_update_le' v _ _ _ hasset hv.1 hdcg (by linarith) haa hr
  rw [show r.pool'.assetsAvailable = r.pool'.toRawVault.assetsAvailable from rfl,
    show r.pool'.assetsDeployed = r.pool'.toRawVault.assetsDeployed from rfl, hraw]
  have hdx' : raw.assetsDeployed.toRat = v.assetsDeployed.toRat - loan.principalOutstanding.toRat := hdx
  have hcash' : raw.assetsAvailable.toRat ≤ max (v.assetsAvailable.toRat + r.amountToPool.toRat) 0 := hcash
  rcases le_total 0 (v.assetsAvailable.toRat + r.amountToPool.toRat) with h0 | h0
  · rw [max_eq_left h0] at hcash'; linarith
  · rw [max_eq_right h0] at hcash'; linarith

/-- What the Open-limit check lets through, on the base grid. When the check passes for a nonnegative
amount `x`, the computed AssetsTotal plus YieldUnrealized plus `x` is at most the Open limit. -/
lemma Vault.exceedsOpenLimit_false_total (v : Vault) (x atot : Number) (hx : x.isNormalized) (hx0 : 0 ≤ x.toRat)
    (hat : v.assetsTotal = .ok atot) (hatn : atot.isNormalized) (hat0 : 0 ≤ atot.toRat)
    (hatg : ∃ k : ℤ, atot.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (hYg : ∃ k : ℤ, v.yieldUnrealized.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (hxg : ∃ k : ℤ, x.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (h : v.exceedsOpenLimit x = .ok false) :
    atot.toRat + v.yieldUnrealized.toRat + x.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨hblo, hbhi, -⟩ := v.baseExponent_bounds
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit at h
  obtain ⟨atot', hat', h⟩ := bind_ok_peel _ _ _ h
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  obtain ⟨s₁, hs₁, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨capacity, hcap, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨limit, hlim, h⟩ := bind_ok_peel _ _ _ h
  have hgt : capacity.operator_gt limit = false := by
    simp only [pure, Except.pure, Except.ok.injEq] at h; exact h
  obtain ⟨w, hw, hwv, hwn⟩ := Number.from_rep_exact (9 : Int64) (15 + v.baseExponent) .to_nearest (by decide)
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hww : limit = w := by
    unfold XRPL.Model.SingleAssetVault.Vault.openLimit at hlim
    exact Except.ok.inj (hlim.symm.trans hw)
  subst hww
  have hlimv : limit.toRat = 9 * 10 ^ 15 * 10 ^ v.baseExponent := by
    rw [hwv, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; push_cast; ring
  by_contra hgt'
  push Not at hgt'
  -- one base unit past the limit, which the whole sum reaches
  obtain ⟨ka, hka⟩ := hatg
  obtain ⟨ky, hky⟩ := hYg
  obtain ⟨kx, hkx⟩ := hxg
  have hk1 : 9 * 10 ^ 15 + 1 ≤ ka + ky + kx := by
    have h1 : ((9 * 10 ^ 15 : ℤ) : ℚ) * 10 ^ v.baseExponent < ((ka + ky + kx : ℤ) : ℚ) * 10 ^ v.baseExponent := by
      push_cast; rw [add_mul, add_mul, ← hka, ← hky, ← hkx]; linarith
    have := lt_of_mul_lt_mul_right h1 hp.le
    exact_mod_cast this
  obtain ⟨m, hm, hmv⟩ := Number.exists_normalized_int_mul_pow (9 * 10 ^ 15 + 1) v.baseExponent
    (by constructor <;> norm_num) (by unfold minExponent maxExponent; constructor <;> omega)
  obtain ⟨n₁, hlo₁, hs₁v⟩ := operator_add_rounded_towards_zero _ _ _ hatn v.wf.yieldUnrealized_norm hs₁
  rw [if_pos (by linarith)] at hlo₁
  have hs₁n := Number.operator_add_isNormalized_any _ _ _ _ hatn v.wf.yieldUnrealized_norm hs₁
  have hs₁ge : m.toRat ≤ s₁.toRat + x.toRat := by
    by_cases hle : m.toRat ≤ atot.toRat + v.yieldUnrealized.toRat
    · rw [hs₁v]; linarith [Number.lower_tight _ n₁ hlo₁ m hm hle]
    · push Not at hle
      -- below the step the sum is a whole number of base units below `2^63`, so it is exact
      have hj : ka + ky < 9 * 10 ^ 15 + 1 := by
        have h1 : ((ka + ky : ℤ) : ℚ) * 10 ^ v.baseExponent < ((9 * 10 ^ 15 + 1 : ℤ) : ℚ) * 10 ^ v.baseExponent := by
          rw [hmv] at hle; push_cast at hle ⊢; rw [add_mul, ← hka, ← hky]; linarith
        exact_mod_cast lt_of_mul_lt_mul_right h1 hp.le
      have hj0 : 0 ≤ ka + ky := by
        have h1 : (0 : ℚ) ≤ ((ka + ky : ℤ) : ℚ) * 10 ^ v.baseExponent := by
          push_cast; rw [add_mul, ← hka, ← hky]; linarith
        exact_mod_cast nonneg_of_mul_nonneg_left h1 hp
      obtain ⟨u, hu, huv⟩ := Number.exists_normalized_int_mul_pow (ka + ky) v.baseExponent
        ⟨by omega, by omega⟩ (by unfold minExponent maxExponent; constructor <;> omega)
      have huv' : u.toRat = atot.toRat + v.yieldUnrealized.toRat := by rw [huv, hka, hky]; push_cast; ring
      have h1 := Number.lower_tight _ n₁ hlo₁ u hu (by rw [huv'])
      rw [← hs₁v, huv'] at h1
      have h2 : m.toRat ≤ atot.toRat + v.yieldUnrealized.toRat + x.toRat := by
        rw [hmv, hka, hky, hkx]
        have : ((9 * 10 ^ 15 + 1 : ℤ) : ℚ) ≤ ((ka + ky + kx : ℤ) : ℚ) := by exact_mod_cast hk1
        push_cast at this ⊢
        nlinarith
      linarith
  obtain ⟨n, hlo, hcapv⟩ := operator_add_rounded_towards_zero _ _ _ hs₁n hx hcap
  rw [if_pos (by linarith [show (0 : ℚ) ≤ m.toRat by rw [hmv]; positivity])] at hlo
  have hmn := Number.lower_tight _ n hlo m hm hs₁ge
  have hlt : limit.toRat < capacity.toRat := by
    rw [hcapv, hlimv]
    refine lt_of_lt_of_le ?_ hmn
    rw [hmv]; push_cast; nlinarith
  have hcap0 : capacity.mantissa_ ≠ 0 := by
    intro h0
    have := Number.toRat_eq_zero_of_mantissa_zero capacity h0
    rw [hlimv] at hlt
    have : (0 : ℚ) < 9 * 10 ^ 15 * 10 ^ v.baseExponent := by positivity
    linarith
  have hcapn := operator_add_isNormalized _ _ _ .towards_zero hs₁n hx hcap hcap0
  have : capacity.operator_gt limit = true := (operator_lt_iff _ _ hwn hcapn).mpr hlt
  rw [this] at hgt
  exact absurd hgt (by decide)

/-- A yield the Open-limit check passed lands inside the Open zone. On the base grid YieldUnrealized takes
the yield exactly, so any total at most AssetsTotal plus the new yield is at most the Open limit. -/
private lemma Vault.yield_open (v : Vault) (x yu' : Number) (T : ℚ) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized) (hx : Number.OnGrid v.baseExponent x)
    (hx0 : 0 ≤ x.toRat) (hcheck : v.exceedsOpenLimit x = .ok false)
    (hadd : v.yieldUnrealized.operator_add x .to_nearest = .ok yu')
    (hT : T ≤ v.assetsAvailable.toRat + v.assetsDeployed.toRat) :
    T + yu'.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid v
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hcheck' := hcheck
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit at hcheck'
  obtain ⟨atot, hat, -⟩ := bind_ok_peel _ _ _ hcheck'
  have hatv := Vault.assetsTotal_eq_of_grid v atot hv hS hat
  obtain ⟨hatn, -, -⟩ := Vault.assetsTotal_bounds v atot hat
  obtain ⟨⟨-, a, ha⟩, ⟨-, d, hd⟩⟩ := hv
  have hb := Vault.exceedsOpenLimit_false_total v x atot hx.1 hx0 hat hatn
    (by rw [hatv]; linarith)
    ⟨a + d, by rw [hatv, ha, hd]; push_cast; ring⟩ hYg.2 hx.2 hcheck
  rw [hatv] at hb
  have hT63 : 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent < 2 ^ 63 * 10 ^ v.baseExponent :=
    mul_lt_mul_of_pos_right (by norm_num) hp
  have hyv : yu'.toRat = v.yieldUnrealized.toRat + x.toRat :=
    Number.add_exact_of_grid hYg hx (by nlinarith) (by linarith) hsr hadd
  rw [hyv]
  linarith

/-- A yield of at most zero leaves YieldUnrealized at most where it was. -/
private lemma Vault.yield_le_of_nonpos (v : Vault) (x yu' : Number) (hx : x.isNormalized) (hx0 : x.toRat ≤ 0)
    (hadd : v.yieldUnrealized.operator_add x .to_nearest = .ok yu') :
    yu'.toRat ≤ v.yieldUnrealized.toRat :=
  Number.roundsToRepresentable_le yu' _ (operator_add_rounded_to_nearest _ _ _ v.wf.yieldUnrealized_norm hx hadd)
    v.yieldUnrealized v.wf.yieldUnrealized_norm (by linarith)

/-- A new loan stays in the Open zone. It keeps AssetsTotal, a pending loan books no yield, and an active
loan's interest passed the Open-limit check. -/
private lemma Loan.create_openZone (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized)
    (har : ∃ n : ℕ, v.assetsReserved.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (h : (Loan.create broker v principal rates fees schedule ao pending).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat + r.pool'.yieldUnrealized.toRat ≤
      max (v.assetsAvailable.toRat + v.assetsDeployed.toRat + v.yieldUnrealized.toRat)
        (9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent) := by
  have hAT := Loan.create_total_le' broker v principal rates fees schedule ao pending r hasset hv hS hp hpos hst hnt h
  have hls := Loan.create_loanScale_proof broker v principal rates fees schedule ao pending r hp hpos hst hnt h
  obtain ⟨-, -, hPO, -, -⟩ := Loan.create_reserved broker v principal rates fees schedule ao pending r hp hpos hst
    hnt har h
  obtain ⟨props, loanState, _, principal', broker', aa', ad', lu', ar', yu', hchecks, -, hsums, hpool, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees schedule ao pending r h
  have hyu : r.pool'.yieldUnrealized = yu' := by
    rw [show r.pool'.yieldUnrealized = r.pool'.toRawVault.yieldUnrealized from rfl, hpool]
  have hy := hsums.yield
  rw [hyu]
  cases pending
  · -- an active loan books its interest, which the check passed
    simp only [Loan.createChange, Bool.false_eq_true, ↓reduceIte] at hy
    obtain ⟨hiN, hi0⟩ := Loan.create_checkedInterest_nonneg broker v principal rates fees schedule ao false r props
      loanState _ broker' hp hpos hst h hchecks hl hb
    have hsb := Loan.loanScale_bounds r.loan'
    rw [hls] at hsb
    obtain ⟨ht, hpg, hm⟩ := Loan.outstanding_onGrid r.loan'
    rw [hls] at ht hpg hm
    have hTV : r.loan'.totalValueOutstanding = props.totalValueOutstanding := by
      show r.loan'.toRawLoan.totalValueOutstanding = _; rw [hl]; rfl
    have hMF : r.loan'.managementFeeOutstanding = props.managementFeeOutstanding := by
      show r.loan'.toRawLoan.managementFeeOutstanding = _; rw [hl]; rfl
    rw [hTV] at ht
    rw [hMF] at hm
    have hpr : Number.OnGrid v.baseExponent principal := by
      obtain ⟨-, k, hk⟩ := hpg
      exact ⟨hp, k, by rw [← hPO]; exact hk⟩
    have hig : Number.OnGrid v.baseExponent loanState.interestDue := by
      have hs := hchecks.state
      unfold LoanState.build at hs
      obtain ⟨d, hd, hs⟩ := bind_ok_peel _ _ _ hs
      obtain ⟨i, hi, hs⟩ := bind_ok_peel _ _ _ hs
      simp only [pure, Except.pure, Except.ok.injEq] at hs
      subst hs
      exact Number.OnGrid.sub (Number.OnGrid.sub ht hpr hsb hd) hm hsb hi
    have := Vault.yield_open v _ _ _ hv hS hYg hig hi0 hchecks.open_zone hy hAT
    exact le_max_of_le_right this
  · -- a pending loan books nothing
    simp only [Loan.createChange, ↓reduceIte, Number.operator_add_zero_right, Except.ok.injEq] at hy
    rw [← hy]
    exact le_max_of_le_left (by linarith)

/-- An accept stays in the Open zone. It keeps AssetsTotal, and the interest it books passed the Open-limit
check. -/
private lemma Loan.accept_openZone (loan : Loan) (v : Vault) (t : UInt32) (r : LoanWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized) (hls : loan.loanScale = v.baseExponent)
    (hc : loan.canAccept v t = .ok .tesSUCCESS) (h : (loan.accept v).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat + r.pool'.yieldUnrealized.toRat ≤
      max (v.assetsAvailable.toRat + v.assetsDeployed.toRat + v.yieldUnrealized.toRat)
        (9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent) := by
  have hAT := Loan.accept_total_le' loan v r hasset hv hS h
  obtain ⟨i, hi, ho⟩ := Loan.canAccept_open loan v t hc
  have hig := Loan.interestDue_onGrid loan i hi
  rw [hls] at hig
  obtain ⟨y, hy, hyg, hyv, -, -⟩ := Loan.accept_yieldValue loan v t r hc h
  have hyi : y = i := Number.isNormalized.toRat_inj hyg.1 hig.1 (by rw [hyv, Loan.interestDue_toExact loan i hi])
  subst hyi
  by_cases hy0 : 0 ≤ y.toRat
  · exact le_max_of_le_right (Vault.yield_open v _ _ _ hv hS hYg hig hy0 ho hy hAT)
  · push Not at hy0
    have := Vault.yield_le_of_nonpos v y _ hig.1 hy0.le hy
    exact le_max_of_le_left (by linarith)


/-- A check that passed read the Open-limit capacity of the charge as not exceeded. -/
lemma Vault.checkOpenLimit_ok_inv (v : Vault) (amount : STAmount)
    (hin : v.checkOpenLimit amount = .ok .tesSUCCESS) :
    ∃ amountNum, amount.toNumber .to_nearest = .ok amountNum ∧ v.exceedsOpenLimit amountNum = .ok false := by
  unfold XRPL.Model.SingleAssetVault.Vault.checkOpenLimit at hin
  obtain ⟨at', -, hin⟩ := bind_ok_peel _ _ _ hin
  obtain ⟨n, hn, hin⟩ := bind_ok_peel _ _ _ hin
  obtain ⟨e, -, hin⟩ := bind_ok_peel _ _ _ hin
  refine ⟨n, hn, ?_⟩
  split at hin
  · cases hin
  · obtain ⟨_, -, hin⟩ := bind_ok_peel _ _ _ hin
    obtain ⟨b, hb, hin⟩ := bind_ok_peel _ _ _ hin
    cases b
    · exact hb
    · simp at hin

/-- A deposit that passed its preflight deposits a canonical amount of the vault's asset. -/
lemma LendingTx.preflight_vaultDeposit' (l : LendingLedger) (h : Nat) (amount : STAmount) (isDonation : Bool)
    (hasset : Vault.HoldsAsset l.vault)
    (hpre : ((LendingTx.vaultDeposit h amount isDonation).preflight l).isTesSuccess = true) :
    amount.Canonical ∧ amount.mNumericType = l.vault.numericType := by
  cases hnt : l.vault.numericType.isIntegral
  · exact LendingTx.preflight_vaultDeposit l h amount isDonation (NumericType.eq_fractional_of_not_integral hnt) hpre
  simp only [LendingTx.preflight] at hpre
  split at hpre
  · rename_i hc
    simp only [Bool.and_eq_true, isCanonicalAmount, isPositiveAmount, hnt, if_true, beq_iff_eq,
      decide_eq_true_eq] at hc
    obtain ⟨⟨hty, hoff, hm⟩, -⟩ := hc
    have hint : amount.integral = true := by unfold STAmount.integral; rw [hty]; exact hnt
    refine ⟨⟨fun _ => ⟨⟨by rw [hty]; exact hnt, hoff, by rw [hty]; exact hm⟩,
      by rw [hty]; exact hasset.maxValue_le hnt⟩, fun h' => absurd hint (by rw [h']; decide)⟩, hty⟩
  · exact absurd hpre (by rw [show TER.temBAD_AMOUNT.isTesSuccess = false from rfl]; decide)

open XRPL.Model.SingleAssetVault in
/-- A deposit stays in the Open zone: the inflow check keeps AssetsTotal plus YieldUnrealized plus the charge
within the Open limit, and on the base grid the charge lands exactly. -/
private lemma Vault.deposit_openZone (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized)
    (r : VaultWithAmounts) (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    r.vault'.assetsAvailable.toRat + r.vault'.assetsDeployed.toRat + r.vault'.yieldUnrealized.toRat ≤
      9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨ra, amounts, raw, hra, hcomp, hin, hadj, hraw, -, -⟩ :=
    Vault.deposit_ok_reduces v amount isDonation t hpos r h
  have hmax := hasset.maxValue_le
  obtain ⟨hrac, hraty, -⟩ := Vault.roundedDepositAmount_form v amount ra hc hty hra
  obtain ⟨hcf, -, hc0⟩ := computeDeposit_assets_form v ra isDonation amounts hrac hraty hmax hcomp
  have hcharge : ∃ k : ℤ, amounts.assets.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
    cases isDonation
    · obtain ⟨assets, assetsTotal, -, -, hsta, -, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ (sharesToAssetsDeposit_form v amounts.shares assets hmax hsta).1 hcl
    · obtain ⟨assetsTotal, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ hrac hcl
  obtain ⟨amountNum, hnum, hex⟩ := Vault.checkOpenLimit_ok_inv v _ hin
  obtain ⟨hnv, hnn⟩ := hcf.toNumber_exact amountNum hnum
  obtain ⟨k, hk⟩ := hcharge
  have hex' := hex
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit at hex'
  obtain ⟨atot, hat, -⟩ := bind_ok_peel _ _ _ hex'
  have hatv := Vault.assetsTotal_eq_of_grid v atot hv hS hat
  obtain ⟨hatn, -, -⟩ := Vault.assetsTotal_bounds v atot hat
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  obtain ⟨a, ha⟩ := hv.1.2
  obtain ⟨d, hd⟩ := hv.2.2
  have hb := Vault.exceedsOpenLimit_false_total v amountNum atot hnn (by rw [hnv]; exact hc0) hat hatn
    (by rw [hatv]; linarith) ⟨a + d, by rw [hatv, ha, hd]; push_cast; ring⟩ hYg.2 ⟨k, by rw [hnv, hk]⟩ hex
  rw [hatv, hnv] at hb
  obtain ⟨assetsNum, _, s, aa', _, hnum', -, -, hs, haa, hrw⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  rw [hnum, Except.ok.injEq] at hnum'
  subst hnum'
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hlim : 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent < 10 ^ (16 + v.baseExponent) := by
    rw [open_line_eq]; nlinarith
  have hcash := Vault.cash_update_le' v amountNum s aa' hasset hv.1 ⟨hnn, k, by rw [hnv, hk]⟩
    (by rw [hnv]; linarith) hs haa
  rw [hnv, max_eq_left (by linarith)] at hcash
  rw [show r.vault'.assetsAvailable = r.vault'.toRawVault.assetsAvailable from rfl,
    show r.vault'.assetsDeployed = r.vault'.toRawVault.assetsDeployed from rfl,
    show r.vault'.yieldUnrealized = r.vault'.toRawVault.yieldUnrealized from rfl, hraw, hrw]
  show aa'.toRat + v.assetsDeployed.toRat + v.yieldUnrealized.toRat ≤ _
  linarith


/-- A transaction on a reachable ledger that is not coarsened keeps AssetsTotal + YieldUnrealized within the
larger of its old value and the Open limit, plus the interest a payment collects beyond the schedule. -/
lemma LendingLedger.openZone_step (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (hnc : l.NotCoarsened) :
    l'.vault.toRawVault.toExact.assetsTotal + l'.vault.yieldUnrealized.toRat ≤
      max (l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat) l.openLimit +
        l.extraInterest tx l' := by
  -- a payment moves the sum by what it collects
  by_cases hpay : ∃ i pt amount, tx = .loanPay i pt amount
  · obtain ⟨i, pt, amount, rfl⟩ := hpay
    simp only [LendingLedger.extraInterest]
    have := le_max_right 0 ((l'.vault.toRawVault.toExact.assetsTotal - l.vault.toRawVault.toExact.assetsTotal) -
      (l.vault.yieldUnrealized.toRat - l'.vault.yieldUnrealized.toRat))
    have := le_max_left (l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat) l.openLimit
    linarith
  have hx := LendingLedger.extraInterest_nonneg l tx l'
  suffices hmain : l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat + l'.vault.yieldUnrealized.toRat ≤
      max (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat) l.openLimit by
    show l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat + l'.vault.yieldUnrealized.toRat ≤
      max (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat) l.openLimit +
        l.extraInterest tx l'
    linarith
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  obtain ⟨hAAg, hADg, -, -, hYg, -⟩ := LendingLedger.base_grid_proof l hr hmax
  have hv : Vault.OnBaseGrid l.vault := ⟨hAAg, hADg⟩
  have hS : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ (16 + l.vault.baseExponent) := by
    rw [open_line_eq]; exact hnc
  have hinv := hr.scaleInv
  have hpre := (LendingLedger.apply_checked h).1
  have hY0 : 0 ≤ l.vault.yieldUnrealized.toRat := l.vault.exact.yieldUnrealized_nonneg
  have hkeep : ∀ v' : Vault, v'.assetsAvailable.toRat + v'.assetsDeployed.toRat ≤
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat →
      v'.yieldUnrealized.toRat ≤ l.vault.yieldUnrealized.toRat →
      v'.assetsAvailable.toRat + v'.assetsDeployed.toRat + v'.yieldUnrealized.toRat ≤
        max (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat)
          l.openLimit :=
    fun v' h1 h2 => le_max_of_le_left (by linarith)
  by_cases hvt : tx.isVault = true
  · -- withdrawals and clawbacks only lower AssetsAvailable
    by_cases hout : (∃ holder amount, tx = .vaultWithdraw holder amount) ∨
        ∃ holder assets, tx = .vaultClawback holder assets
    · obtain ⟨-, hle, hAD⟩ := LendingLedger.lent_out_protected_proof l l' tx hr hmax hout h
      obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hvt h
      have hvault : (l.commitVault u).vault = u.vault := by
        unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
      have hYU := (l.applyVault_keepsLending tx u hu).yieldUnrealized
      rw [hvault] at hle hAD ⊢
      exact hkeep _ (by rw [hAD]; linarith) (by rw [hYU])
    obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hvt h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    have hk := l.applyVault_keepsLending tx u hu
    cases tx with
    | vaultDeposit hd amount isDonation =>
      obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit' l hd amount isDonation hasset hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · unfold_ter at hu
        walk_ok
        exact le_max_of_le_right (Vault.deposit_openZone _ _ _ _ _ hc hty hasset hv hS hYg _ ‹_›)
      · cases hu
    | vaultWithdraw hd amount => exact absurd (Or.inl ⟨hd, amount, rfl⟩) hout
    | vaultClawback hd assets => exact absurd (Or.inr ⟨hd, assets, rfl⟩) hout
    | vaultBurnShares hd amount =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
      exact hkeep _ (by rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)])
        (by rw [(congrArg RawVault.yieldUnrealized hf :)])
    | vaultSet m b ub =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
      exact hkeep _ (by rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)])
        (by rw [(congrArg RawVault.yieldUnrealized hf :)])
    | _ => simp only [LendingTx.isVault] at hvt; cases hvt
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact hkeep _ le_rfl le_rfl
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    show u.vault.assetsAvailable.toRat + u.vault.assetsDeployed.toRat + u.vault.yieldUnrealized.toRat ≤ _
    cases tx with
    | loanSet i principal rates fees pi pt gp sd twoStep ao =>
      obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
      simp only [LendingLedger.applyLoan] at hu
      obtain ⟨broker, r, hb', hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
      have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
      exact Loan.create_openZone _ _ _ _ _ _ _ _ r hasset hv hS hYg hr.reservedInv.grid hpn hpos hst
        (hinv.brokers i broker hb') hcr
    | loanAccept i =>
      obtain ⟨e, broker, loan, r, he, hb', hw, hc, hr', rfl⟩ := l.applyLoan_accept_inv u i hu
      obtain ⟨hls, -⟩ := hr.loanAt_scale ⟨e, broker, he, hb', hw⟩
      exact Loan.accept_openZone _ _ _ _ hasset hv hS hYg hls hc hr'
    | loanDelete i =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_delete_inv u i hu
      obtain ⟨hls, hnt⟩ := hr.loanAt_scale ⟨e, broker, he, hb', hw⟩
      exact hkeep _ (Loan.delete_total_le' _ _ _ hasset hv hS hls hnt hr') (by rw [Loan.delete_yield _ _ _ hr'])
    | loanManage i action =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_manage_inv u i action hu
      obtain ⟨hls, hnt⟩ := hr.loanAt_scale ⟨e, broker, he, hb', hw⟩
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat + r.pool'.yieldUnrealized.toRat ≤ _
      cases action with
      | impair =>
        have hy := Loan.manageImpair_yield loan _ _ r hr'
        simp only [Loan.manage, Loan.manageImpair] at hr'
        unfold_ter at hr'
        walk_ok
        exact hkeep _ (Loan.changeImpairment_total_le' loan _ true _ hasset hv hS ‹_›) (by rw [hy])
      | unimpair =>
        exact hkeep _ (Loan.changeImpairment_total_le' loan _ false r hasset hv hS hr')
          (by rw [Loan.manageUnimpair_yield loan _ r hr'])
      | default =>
        -- the defaulted loan's interest is at least zero, so YieldUnrealized does not grow
        obtain ⟨s, hls'⟩ := hr.loansInv
        obtain ⟨t, -, hreach⟩ := hls'.reachable i e he
        have hi0 : 0 ≤ loan.toExact.interestDue := by
          have hraw := Loan.withBroker_eq hw
          have := Loan.Reachable.interestDue_nonneg hreach
          show 0 ≤ loan.toRawLoan.totalValueOutstanding.toRat - loan.toRawLoan.principalOutstanding.toRat -
            loan.toRawLoan.managementFeeOutstanding.toRat
          rw [hraw]
          exact this
        simp only [Loan.manage] at hr'
        unfold_ter at hr'
        walk_ok'
        rename_i rd hrd
        obtain ⟨y, hy, hyg, hyv, -⟩ := Loan.manageDefault_yieldValue loan _ rd hrd
        refine hkeep _ (Loan.manageDefault_total_le' loan _ _ hasset hv hS hls hnt hrd) ?_
        exact Vault.yield_le_of_nonpos _ _ _ (Number.operator_neg_isNormalized _ hyg.1)
          (by rw [Number.toRat_neg, hyv]; linarith) hy
    | loanPay i paymentType amount => exact absurd ⟨i, paymentType, amount, rfl⟩ hpay
    | _ => simp only [LendingLedger.applyLoan] at hu; cases hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hvt hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hkeep _ le_rfl le_rfl
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact hkeep _ le_rfl le_rfl


/-- The ledger a VaultCreate makes holds nothing. -/
private lemma LendingLedger.Genesis.empty {g : LendingLedger} (hg : g.Genesis) :
    g.vault.assetsAvailable.toRat = 0 ∧ g.vault.assetsDeployed.toRat = 0 ∧ g.vault.yieldUnrealized.toRat = 0 := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  have hraw := XRPL.Model.SingleAssetVault.Vault.create_ok_toRawVault hcreate
  rw [show g.vault.assetsAvailable = g.vault.toRawVault.assetsAvailable from rfl,
    show g.vault.assetsDeployed = g.vault.toRawVault.assetsDeployed from rfl,
    show g.vault.yieldUnrealized = g.vault.toRawVault.yieldUnrealized from rfl, hraw]
  exact ⟨Number.toRat_zero, Number.toRat_zero, Number.toRat_zero⟩

/-- Proof body of `Lending.Reachable.within_open_zone`. -/
lemma LendingLedger.within_open_zone_proof (genesis l : LendingLedger) (txs : List LendingTx) (x : ℚ)
    (hg : genesis.Genesis) (hrun : genesis.ReachableFromIn txs l x)
    (hnc : ∀ (pre : List LendingTx) (tx : LendingTx) (l₁ : LendingLedger) (x₁ : ℚ), pre ++ [tx] <+: txs →
      genesis.ReachableFromIn pre l₁ x₁ → l₁.NotCoarsened) :
    l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat ≤ l.openLimit + x := by
  induction hrun with
  | refl =>
    obtain ⟨h1, h2, h3⟩ := hg.empty
    show genesis.vault.assetsAvailable.toRat + genesis.vault.assetsDeployed.toRat +
      genesis.vault.yieldUnrealized.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ genesis.vault.baseExponent + 0
    rw [h1, h2, h3]
    have : (0 : ℚ) < 10 ^ genesis.vault.baseExponent := zpow_pos (by norm_num) _
    linarith
  | @step txs₀ l₀ l₁ x₀ tx hprev hok ih =>
    have ih' := ih (fun pre t l₂ x₂ hpre hr => hnc pre t l₂ x₂ (hpre.trans (List.prefix_append _ _)) hr)
    have hstep := LendingLedger.openZone_step l₀ l₁ tx (hprev.reachable hg) hok
      (hnc txs₀ tx l₀ x₀ (List.prefix_refl _) hprev)
    have hx0 := hprev.extraInterest_nonneg
    have hlim : l₁.openLimit = l₀.openLimit := by
      unfold LendingLedger.openLimit; rw [LendingLedger.apply_baseExponent hok]
    have hlim0 : 0 ≤ l₀.openLimit := by unfold LendingLedger.openLimit; positivity
    rw [hlim]
    have : max (l₀.vault.toRawVault.toExact.assetsTotal + l₀.vault.yieldUnrealized.toRat) l₀.openLimit ≤
        l₀.openLimit + x₀ := max_le ih' (by linarith)
    linarith

end XRPL.Model.Lending
