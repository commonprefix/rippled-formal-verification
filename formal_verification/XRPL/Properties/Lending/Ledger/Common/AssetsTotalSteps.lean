import XRPL.Properties.Lending.Ledger.Common.OpenZoneSteps
import XRPL.Properties.Lending.Loan.Common.PaidAmounts

/-! # AssetsTotal without losses

On a reachable ledger that is not coarsened, only a default, a VaultWithdraw or a VaultClawback lowers AssetsTotal.
A payment credits at least its principal, and a credit crossing `10^16` base units would coarsen the vault. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts WithdrawAmount)

open private Loan.unimpairIfImpaired Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private Vault.total_of_raw Vault.deployed_take Vault.assetsTotal_eq_of_grid Vault.assetsTotal_bounds
  from XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
open private Loan.create_principalOutstanding from XRPL.Properties.Lending.Loan.Common.AcceptProofs
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- A cash update between zero and `10^16` base units writes its sum exactly. On the base grid the sum is
exact and the asset stores it. -/
private lemma Vault.cash_update_eq (v : Vault) (cash aa aa' : Number) (hasset : Vault.HoldsAsset v)
    (hv : Number.OnGrid v.baseExponent v.assetsAvailable) (hc : Number.OnGrid v.baseExponent cash)
    (h0 : 0 ≤ v.assetsAvailable.toRat + cash.toRat)
    (hlt : v.assetsAvailable.toRat + cash.toRat < 10 ^ (16 + v.baseExponent))
    (hs : v.assetsAvailable.operator_add cash .to_nearest = .ok aa)
    (hr : STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa') :
    aa'.toRat = v.assetsAvailable.toRat + cash.toRat := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have han := operator_add_isNormalized_to_nearest_sz _ _ _ hv.1 hc.1 hs
  have hT : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 2 ^ 63 * 10 ^ v.baseExponent := by
    rw [open_line_eq]; exact mul_le_mul_of_nonneg_right (by norm_num) hp.le
  have haav : aa.toRat = v.assetsAvailable.toRat + cash.toRat :=
    Number.add_exact_of_grid hv hc (by nlinarith) (by linarith) hsr hs
  have hag : Number.OnGrid v.baseExponent aa := Number.OnGrid.add hv hc hsr hs
  have hst := Vault.isRounded_false_of_grid' v hasset aa hag (by rw [haav]; exact h0) (by rw [haav]; exact hlt)
  rw [STAmount.roundToNumericType_of_isRounded_false _ _ _ han hst hr, haav]

/-- A balance change that keeps AssetsAvailable between zero and `10^16` base units writes the new AssetsAvailable
and AssetsDeployed exactly. -/
private lemma Vault.adjustBalances_total_eq (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v) (hc : Number.OnGrid v.baseExponent c.cash)
    (hd : Number.OnGrid v.baseExponent c.deployed) (h0 : 0 ≤ v.assetsAvailable.toRat + c.cash.toRat)
    (hlt : v.assetsAvailable.toRat + c.cash.toRat < 10 ^ (16 + v.baseExponent))
    (hdlo : -(2 ^ 63 * (10 : ℚ) ^ v.baseExponent) < v.assetsDeployed.toRat + c.deployed.toRat)
    (hdhi : v.assetsDeployed.toRat + c.deployed.toRat < 2 ^ 63 * (10 : ℚ) ^ v.baseExponent)
    (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    raw.assetsAvailable.toRat = v.assetsAvailable.toRat + c.cash.toRat ∧
      raw.assetsDeployed.toRat = v.assetsDeployed.toRat + c.deployed.toRat := by
  obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv v c raw h
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨aa, haa, hround⟩ := hs.cash
  exact ⟨Vault.cash_update_eq v _ _ _ hasset hv.1 hc h0 hlt haa hround,
    Number.add_exact_of_grid hv.2 hd hdlo hdhi hsr hs.deployed⟩

/-- A balance change that moves no cash and deploys nothing keeps the total exactly. -/
private lemma Vault.poolAdjust_zero_total_eq (v v' : Vault) (c : PoolBalanceChange) (hasset : Vault.HoldsAsset v)
    (hv : Vault.OnBaseGrid v) (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hc : c.cash = Number.zero) (hd : c.deployed = Number.zero) (h : AssetPool.adjustBalances v c = .ok (.ok v')) :
    v'.assetsAvailable.toRat + v'.assetsDeployed.toRat = v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  obtain ⟨raw, hadj, hlaw⟩ := Vault.poolAdjust_ok_inv v c v' h
  have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hT : (10 : ℚ) ^ (16 + v.baseExponent) ≤ 2 ^ 63 * 10 ^ v.baseExponent := by
    rw [open_line_eq]; exact mul_le_mul_of_nonneg_right (by norm_num) hp.le
  obtain ⟨h1, h2⟩ := Vault.adjustBalances_total_eq v c raw hasset hv (by rw [hc]; exact Number.OnGrid.zero _)
    (by rw [hd]; exact Number.OnGrid.zero _) (by rw [hc, Number.toRat_zero]; linarith)
    (by rw [hc, Number.toRat_zero]; linarith) (by rw [hd, Number.toRat_zero]; nlinarith)
    (by rw [hd, Number.toRat_zero]; linarith) hadj
  rw [hc, Number.toRat_zero, add_zero] at h1
  rw [hd, Number.toRat_zero, add_zero] at h2
  rw [Vault.total_of_raw hlaw]
  linarith

/-- A new loan keeps the total exactly: its principal leaves AssetsAvailable and joins AssetsDeployed. -/
private lemma Loan.create_total_eq (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (h : (Loan.create broker v principal rates fees schedule ao pending).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
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
  obtain ⟨h1, h2⟩ := Vault.adjustBalances_total_eq v _ raw hasset hv hpg'.neg hpg (by rw [hcash]; linarith)
    (by rw [hcash]; linarith)
    (by show _ < v.assetsDeployed.toRat + principal.toRat; nlinarith)
    (by show v.assetsDeployed.toRat + principal.toRat < _; linarith) hadj
  rw [hcash] at h1
  have h2' : raw.assetsDeployed.toRat = v.assetsDeployed.toRat + principal.toRat := h2
  rw [Vault.total_of_raw hlaw]
  linarith


/-- An accept moves no cash and deploys nothing. -/
private lemma Loan.accept_total_eq (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (h : (loan.accept v).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact Vault.poolAdjust_zero_total_eq v _ _ hasset hv hS rfl rfl ‹_›

/-- An impairment change moves no cash and deploys nothing. -/
private lemma Loan.changeImpairment_total_eq (loan : Loan) (v : Vault) (impaired : Bool) (r : LoanWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (h : (Loan.changeImpairment loan v impaired).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_zero_total_eq v _ _ hasset hv hS rfl rfl ‹_›

/-- A delete keeps the total exactly: a pending loan's principal leaves AssetsDeployed and returns to
AssetsAvailable. -/
private lemma Loan.delete_total_eq (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hls : loan.loanScale = v.baseExponent) (hnt : loan.broker.numericType = v.numericType)
    (h : (loan.delete v).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
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
    have hcash := Vault.cash_update_eq v _ _ _ hasset hv.1 hpg' (by rw [hpv]; linarith) (by rw [hpv]; linarith) haa hr
    rw [hpv] at hcash
    rw [Vault.total_of_raw hlaw]
    linarith
  · simp only [Loan.delete, Bool.not_eq_true] at h hp
    rw [hp] at h
    unfold_ter at h
    walk_ok
    rfl

open XRPL.Model.SingleAssetVault in
/-- A deposit never lowers AssetsTotal: the inflow check keeps the charge inside the Open zone, and on the base
grid it lands exactly. -/
private lemma Vault.deposit_total_ge (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hS : v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent))
    (hYg : Number.OnGrid v.baseExponent v.yieldUnrealized)
    (r : VaultWithAmounts) (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    v.assetsAvailable.toRat + v.assetsDeployed.toRat ≤
      r.vault'.assetsAvailable.toRat + r.vault'.assetsDeployed.toRat := by
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
  have hcash := Vault.cash_update_eq v amountNum s aa' hasset hv.1 ⟨hnn, k, by rw [hnv, hk]⟩
    (by rw [hnv]; linarith) (by rw [hnv]; linarith) hs haa
  rw [hnv] at hcash
  rw [show r.vault'.assetsAvailable = r.vault'.toRawVault.assetsAvailable from rfl,
    show r.vault'.assetsDeployed = r.vault'.toRawVault.assetsDeployed from rfl, hraw, hrw]
  show _ ≤ aa'.toRat + v.assetsDeployed.toRat
  linarith


/-- A floor onto the `10^s` grid stays at or above a grid point under the value, or above a power of ten the
value reaches. -/
private lemma floor_mul_ge (x g : ℚ) (s : ℤ) (hg : g ≤ x)
    (h : (∃ k : ℤ, g = k * 10 ^ s) ∨ ∃ j : ℕ, g ≤ 10 ^ j * 10 ^ s ∧ 10 ^ j * 10 ^ s ≤ x) :
    g ≤ (⌊x / 10 ^ s⌋ : ℚ) * 10 ^ s := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  rcases h with ⟨k, hk⟩ | ⟨j, hj1, hj2⟩
  · have hkx : (k : ℚ) ≤ x / 10 ^ s := by rw [le_div_iff₀ hp, ← hk]; exact hg
    have : k ≤ ⌊x / 10 ^ s⌋ := Int.le_floor.mpr hkx
    rw [hk]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hp.le
  · have hjx : ((10 ^ j : ℤ) : ℚ) ≤ x / 10 ^ s := by rw [le_div_iff₀ hp]; push_cast; exact hj2
    have : (10 ^ j : ℤ) ≤ ⌊x / 10 ^ s⌋ := Int.le_floor.mpr hjx
    calc g ≤ 10 ^ j * 10 ^ s := hj1
      _ ≤ (⌊x / 10 ^ s⌋ : ℚ) * 10 ^ s := mul_le_mul_of_nonneg_right (by exact_mod_cast this) hp.le

/-- A normalized nonzero `Number` at least zero is at least `10^18` units at its exponent. -/
private lemma Number.pow_le_of_normalized (n : Number) (hn : n.isNormalized) (hm : n.mantissa_ ≠ 0)
    (h0 : 0 ≤ n.toRat) : (10 : ℚ) ^ (18 : ℕ) * 10 ^ n.exponent_ ≤ n.toRat := by
  obtain ⟨hlo, -⟩ := hn.mantissaBounds_nat hm
  rw [Number.toRat_of_nonneg n (Number.negative_false_of_nonneg n hn h0)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlo) (zpow_pos (by norm_num) _).le

/-- A downward sum never lands below a positive representable value under the exact sum, for operands of either
sign. -/
private lemma add_downward_ge_any (x y r w : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_add y .downward = .ok r) (hw : w.isNormalized) (hw0 : 0 < w.toRat)
    (hwt : w.toRat ≤ x.toRat + y.toRat) : w.toRat ≤ r.toRat := by
  by_cases hr0 : r.mantissa_ = 0
  · exfalso
    have hwm : w.mantissa_ ≠ 0 := fun h => by rw [Number.toRat_eq_zero_of_mantissa_zero w h] at hw0; linarith
    have hwmin := Number.pow_le_of_normalized w hw hwm hw0.le
    have hwe := Number.exponent_ge_min w hw hwm
    have hmin : (10 : ℚ) ^ (18 : ℕ) * 10 ^ minExponent ≤ (10 : ℚ) ^ (18 : ℕ) * 10 ^ w.exponent_ :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hwe) (by positivity)
    by_cases hy_guard : y.operator_eq Number.zero = true
    · have hrx : r = x := by
        unfold Number.operator_add at hok; rw [if_pos hy_guard] at hok; exact (Except.ok.inj hok).symm
      rw [Number.toRat_eq_zero_of_mantissa_zero y (Number.mantissa_eq_zero_of_operator_eq_zero hy_guard), ← hrx,
        Number.toRat_eq_zero_of_mantissa_zero r hr0] at hwt
      linarith
    by_cases hx_guard : x.operator_eq Number.zero = true
    · have hry : r = y := by
        unfold Number.operator_add at hok; rw [if_neg hy_guard, if_pos hx_guard] at hok
        exact (Except.ok.inj hok).symm
      rw [Number.toRat_eq_zero_of_mantissa_zero x (Number.mantissa_eq_zero_of_operator_eq_zero hx_guard), ← hry,
        Number.toRat_eq_zero_of_mantissa_zero r hr0] at hwt
      linarith
    by_cases heq : x.operator_eq y.operator_neg = true
    · have h := (operator_eq_iff _ _ hx (Number.operator_neg_isNormalized y hy)).mp heq
      rw [Number.toRat_neg] at h
      linarith
    have hxm : x.mantissa_ ≠ 0 := fun h => hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
    have hym : y.mantissa_ ≠ 0 := fun h => hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
    by_cases hsign : x.negative_ = y.negative_
    · obtain ⟨_, _, _, _, _, hspec⟩ := operator_add_algorithmic_facts_same_sign_anyMode x y r _ hx hy hxm hym
        hsign heq hok
      exact hspec.result_mant_ne hr0
    · have hsmall := operator_add_underflow_truth_small x y r _ hx hy hxm hym hsign heq hok hr0
      have := (abs_lt.mp hsmall).2
      linarith
  · obtain ⟨n, hn, hv⟩ := operator_add_rounded_downward x y r hx hy hok hr0
    rw [hv]
    exact Number.lower_tight _ n hn w hw hwt

/-- A downward IOU conversion keeps a value past a grid point: the 16-digit floor of a nonnegative value at
least `g` is at least `g`, when `g` is on the grid of the value's 16th digit or at most `10^(15 + s)` there. -/
private lemma STAmount.ofNumber_frac_downward_ge (n : Number) (st : STAmount) (g : ℚ) (hn : n.isNormalized)
    (hg0 : (10 : ℚ) ^ (-81 : ℤ) ≤ g) (hg : g ≤ n.toRat)
    (hgrid : ∀ s : ℤ, s = n.exponent_ + 3 → (∃ k : ℤ, g = k * 10 ^ s) ∨ g ≤ 10 ^ (15 : ℕ) * 10 ^ s)
    (h : STAmount.ofNumber .fractional n .downward = .ok st) : g ≤ st.toRat := by
  have hp81 : (0 : ℚ) < 10 ^ (-81 : ℤ) := zpow_pos (by norm_num) _
  have h0 : 0 ≤ n.toRat := by linarith
  have hm : n.mantissa_ ≠ 0 := fun h' => by rw [Number.toRat_eq_zero_of_mantissa_zero n h'] at hg; linarith
  have hsz : st.mValue ≠ 0 := by
    intro hz
    have := STAmount.ofNumber_fractional_zero_below_min .fractional n st .downward rfl hn
      (Number.negative_false_of_nonneg n hn h0) hm h hz
    linarith
  have hR := STAmount.ofNumber_iou_downward_floor n st hn hm h0 h hsz
  unfold RoundsToRepresentableAt at hR
  change st.toRat = _ at hR
  rw [hR]
  have hlow := Number.pow_le_of_normalized n hn hm h0
  refine floor_mul_ge _ _ _ hg ?_
  rcases hgrid _ rfl with hk | hle
  · exact Or.inl hk
  · refine Or.inr ⟨15, hle, ?_⟩
    have : (10 : ℚ) ^ (15 : ℕ) * 10 ^ (n.exponent_ + 3) = 10 ^ (18 : ℕ) * 10 ^ n.exponent_ := by
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
    rw [this]; exact hlow

/-- A fractional amount canonical or zero and above zero is canonical. -/
private lemma STAmount.FracCanonZero.canonical_of_pos {s : STAmount} (h : s.FracCanonZero) (hpos : 0 < s.toRat) :
    s.IOUCanonical := by
  rcases h.2 with hc | hz
  · exact hc
  · rw [STAmount.toRat_eq_zero_of_mValue_zero s hz] at hpos; exact absurd hpos (lt_irrefl _)

/-- `10^a · 10^s` as one power. -/
private lemma pow_grid (a : ℕ) (s : ℤ) : (10 : ℚ) ^ (s + a) = ((10 ^ a : ℕ) : ℤ) * 10 ^ s := by
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]; push_cast; ring

/-- A credit that crosses `10^16` base units leaves AssetsAvailable at `10^16` base units or above. When
AssetsAvailable plus the amount reaches `10^16` base units, the floored credit still takes AssetsAvailable there. -/
private lemma vault_credit_cross (A c : Number) (b : Int) (st : STAmount) (cr aa a' : Number)
    (hA : A.isNormalized) (hAg : ∃ k : ℤ, A.toRat = k * 10 ^ b) (hA0 : 0 ≤ A.toRat)
    (hAW : A.toRat < 10 ^ 16 * 10 ^ b) (hc : c.isNormalized) (hb : -10 ≤ b ∧ b ≤ 0)
    (hcross : 10 ^ 16 * 10 ^ b ≤ A.toRat + c.toRat)
    (h : sumRoundAndSubtract A c b .fractional .downward = .ok st) (hcr : st.toNumber .to_nearest = .ok cr)
    (haa : A.operator_add cr .to_nearest = .ok aa)
    (ha' : STAmount.roundToNumericType .fractional aa .to_nearest = .ok a') :
    10 ^ 16 * 10 ^ b ≤ a'.toRat := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hW0 : (0 : ℚ) < 10 ^ 16 * 10 ^ b := by positivity
  have hpb : (10 : ℚ) ^ (-81 : ℤ) ≤ 10 ^ b := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hbW : (10 : ℚ) ^ b ≤ 10 ^ 16 * 10 ^ b := le_mul_of_one_le_left hp.le (by norm_num)
  obtain ⟨Wn, hWn, hWv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) b (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hWv' : Wn.toRat = 10 ^ 16 * 10 ^ b := by rw [hWv]; push_cast; ring
  unfold sumRoundAndSubtract at h
  rw [if_neg (by decide)] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum, hsum, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d, hd, hst⟩ := bind_ok_peel _ _ _ h
  have hErange := postSumExponent_range _ _ _ _ _ (by omega) (by omega) hE
  obtain ⟨s0, hs0, hne⟩ := postSumExponent_reduces _ _ _ _ _ hE

  have hsumn := Number.operator_add_isNormalized_any _ _ _ _ hA hc hsum
  have hsumW : 10 ^ 16 * 10 ^ b ≤ sum.toRat := by
    rw [← hWv']
    exact add_downward_ge_any A c sum Wn hA hc hsum hWn (by rw [hWv']; exact hW0) (by rw [hWv']; exact hcross)
  have hsumE : (10 : ℚ) ^ E ≤ sum.toRat := by
    by_cases hEb : E = b
    · rw [hEb]; linarith
    · have hlt : b < E := lt_of_le_of_ne hErange.1 (Ne.symm hEb)
      have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hs0
      have hs00 : 0 ≤ s0.toRat := operator_add_nonneg _ _ _ hA hc hs0 (by linarith)
      obtain ⟨-, hbig⟩ := numberExponent_frac_lower s0 b E hs0n hs00 (by omega) hne hlt
      obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (E + 14) (by constructor <;> norm_num)
        ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
      rw [show ((1 : ℤ) : ℚ) = 1 by norm_num, one_mul] at hwv
      have h1415 : (10 : ℚ) ^ (E + 14) < 10 ^ (E + 15) := zpow_lt_zpow_right₀ (by norm_num) (by omega)
      have hge14 : (10 : ℚ) ^ (E + 14) ≤ A.toRat + c.toRat := by
        by_contra hlt14
        push Not at hlt14
        have := operator_add_le_of_le_normalized _ _ _ _ hA hc hs0 hw (by rw [hwv]; linarith)
        rw [hwv] at this
        linarith
      have := add_downward_ge_any A c sum w hA hc hsum hw (by rw [hwv]; positivity) (by rw [hwv]; exact hge14)
      rw [hwv] at this
      have : (10 : ℚ) ^ E ≤ 10 ^ (E + 14) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith

  unfold STAmount.roundToNumericType at hsum'
  cases hret : STAmount.ofNumber .fractional sum .downward with
  | error e => rw [hret] at hsum'; cases hsum'
  | ok ret =>
  rw [hret] at hsum'
  simp only at hsum'
  have hretf := STAmount.ofNumber_fractional_fczr sum _ ret hret
  have hret_int : ret.integral = false := by unfold STAmount.integral; rw [hretf.1]; rfl
  rw [if_neg (by rw [hret_int]; decide)] at hsum'
  cases hrd : STAmount.roundToExponent ret E .downward with
  | error e => rw [hrd] at hsum'; cases hsum'
  | ok rd =>
  rw [hrd] at hsum'
  simp only at hsum'
  have hretW : 10 ^ 16 * 10 ^ b ≤ ret.toRat := by
    refine STAmount.ofNumber_frac_downward_ge sum ret _ hsumn (le_trans hpb hbW) hsumW (fun s hs => ?_) hret
    by_cases hsb : s ≤ 16 + b
    · refine Or.inl ⟨((10 ^ (16 + b - s).toNat : ℕ) : ℤ), ?_⟩
      rw [← pow_grid, show s + ((16 + b - s).toNat : ℕ) = 16 + b by omega, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
    · refine Or.inr ?_
      calc (10 : ℚ) ^ 16 * 10 ^ b = 10 ^ (16 + b) := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
        _ ≤ 10 ^ (s + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 10 ^ (15 : ℕ) * 10 ^ s := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
  have hretE : (10 : ℚ) ^ E ≤ ret.toRat := by
    refine STAmount.ofNumber_frac_downward_ge sum ret _ hsumn (zpow_le_zpow_right₀ (by norm_num) (by omega)) hsumE
      (fun s hs => ?_) hret
    by_cases hsE : s ≤ E
    · refine Or.inl ⟨((10 ^ (E - s).toNat : ℕ) : ℤ), ?_⟩
      rw [← pow_grid, show s + ((E - s).toNat : ℕ) = E by omega]
    · refine Or.inr ?_
      calc (10 : ℚ) ^ E ≤ 10 ^ (s + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 10 ^ (15 : ℕ) * 10 ^ s := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
  have hretc := STAmount.FracCanonZero.canonical_of_pos hretf (by linarith)
  have hR := STAmount.roundToExponent_rounded_of_scale ret rd E .downward hretc (by omega) hErange.2.2 hrd
  unfold RoundsToRepresentableAt at hR
  change rd.toRat = _ at hR
  have hrdW : 10 ^ 16 * 10 ^ b ≤ rd.toRat := by
    rw [hR]
    refine floor_mul_ge _ _ _ hretW ?_
    by_cases hEb : E ≤ 16 + b
    · refine Or.inl ⟨((10 ^ (16 + b - E).toNat : ℕ) : ℤ), ?_⟩
      rw [← pow_grid, show E + ((16 + b - E).toNat : ℕ) = 16 + b by omega, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
    · refine Or.inr ⟨0, ?_, by simpa using hretE⟩
      rw [pow_zero, one_mul]
      calc (10 : ℚ) ^ 16 * 10 ^ b = 10 ^ (16 + b) := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
        _ ≤ 10 ^ E := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hrdf := STAmount.roundToExponent_fczr ret rd E .downward hretf hrd
  have hsum'v := STAmount.FracCanonZero.toNumber_val hrdf .downward sum' hsum'
  have hsum'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ (show STAmount.roundToNumericType .fractional
    sum .downward (some E) = .ok sum' by unfold STAmount.roundToNumericType; rw [hret]; simp only
                                         rw [if_neg (by rw [hret_int]; decide), hrd]; exact hsum')
  have hsum'W : 10 ^ 16 * 10 ^ b ≤ sum'.toRat := by rw [hsum'v]; exact hrdW

  obtain ⟨kA, hkA⟩ := hAg
  have hkA0 : 0 ≤ kA := by
    have : (0 : ℚ) ≤ (kA : ℚ) * 10 ^ b := hkA ▸ hA0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hkA16 : kA < 10 ^ 16 := by
    have : (kA : ℚ) * 10 ^ b < ((10 ^ 16 : ℤ) : ℚ) * 10 ^ b := by rw [← hkA]; push_cast; exact hAW
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  obtain ⟨R, hR', hRv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16 - kA) b ⟨by omega, by omega⟩
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hRv' : R.toRat = 10 ^ 16 * 10 ^ b - A.toRat := by rw [hRv, hkA]; push_cast; ring
  have hRb : (10 : ℚ) ^ b ≤ R.toRat := by
    rw [hRv]
    have : (1 : ℤ) ≤ 10 ^ 16 - kA := by omega
    exact le_mul_of_one_le_left hp.le (by exact_mod_cast this)
  have hdn : d.isNormalized := Number.operator_sub_isNormalized_any _ _ _ _ hsum'n hA hd
  have hdR : R.toRat ≤ d.toRat := by
    unfold Number.operator_sub at hd
    refine add_downward_ge_any sum' A.operator_neg d R hsum'n (Number.operator_neg_isNormalized A hA) hd hR'
      (by linarith) ?_
    rw [Number.toRat_neg, hRv']; linarith

  have hstR : R.toRat ≤ st.toRat := by
    refine STAmount.ofNumber_frac_downward_ge d st _ hdn (le_trans hpb hRb) hdR (fun s hs => ?_) hst
    by_cases hsb : s ≤ b
    · refine Or.inl ⟨(10 ^ 16 - kA) * ((10 ^ (b - s).toNat : ℕ) : ℤ), ?_⟩
      rw [hRv]; push_cast
      have h10 : (10 : ℚ) ^ b = 10 ^ (b - s).toNat * 10 ^ s := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), show (((b - s).toNat : ℕ) : ℤ) + s = b by omega]
      rw [h10]; ring
    · refine Or.inr ?_
      calc R.toRat ≤ 10 ^ 16 * 10 ^ b := by linarith
        _ = 10 ^ (16 + b) := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
        _ ≤ 10 ^ (s + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 10 ^ (15 : ℕ) * 10 ^ s := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
  have hstf := STAmount.ofNumber_fractional_fczr d _ st hst
  have hcrv := STAmount.FracCanonZero.toNumber_val hstf .to_nearest cr hcr
  have hcrn : cr.isNormalized := STAmount.toNumber_isNormalized st _ cr hcr

  have haaW : 10 ^ 16 * 10 ^ b ≤ aa.toRat := by
    rw [← hWv']
    exact Number.roundsToRepresentable_ge aa _ (operator_add_rounded_to_nearest _ _ _ hA hcrn haa) Wn hWn
      (by rw [hWv', hcrv]; linarith)
  have haan := operator_add_isNormalized_to_nearest_sz _ _ _ hA hcrn haa
  unfold STAmount.roundToNumericType at ha'
  cases hof : STAmount.ofNumber .fractional aa .to_nearest with
  | error e => rw [hof] at ha'; cases ha'
  | ok r =>
  rw [hof] at ha'
  simp only at ha'
  have hrf := STAmount.ofNumber_fractional_fczr aa _ r hof
  have haa0 : 0 ≤ aa.toRat := by linarith
  have haam : aa.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero aa h0] at haaW; linarith
  have hrz : r.mValue ≠ 0 := by
    intro hz
    have := STAmount.ofNumber_fractional_zero_below_min .fractional aa r .to_nearest rfl haan
      (Number.negative_false_of_nonneg aa haan haa0) haam hof hz
    linarith
  rw [STAmount.FracCanonZero.toNumber_val hrf .to_nearest a' ha']
  have hrc : r.IOUCanonical := hrf.2.resolve_right hrz
  have hN := STAmount.ofNumber_to_nearest_neighbour .fractional aa r haan haa0 hof (Or.inr hrz)
  unfold RoundsToRepresentableAt at hN
  change r.toRat = _ ∨ r.toRat = _ at hN
  have hp' : (0 : ℚ) < 10 ^ r.exponent := zpow_pos (by norm_num) _
  rcases hN with hfl | hce
  · rw [hfl]
    refine floor_mul_ge _ _ _ haaW ?_
    by_cases heb : r.exponent ≤ 16 + b
    · refine Or.inl ⟨((10 ^ (16 + b - r.exponent).toNat : ℕ) : ℤ), ?_⟩
      rw [← pow_grid, show r.exponent + ((16 + b - r.exponent).toNat : ℕ) = 16 + b by omega,
        zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num
    · refine Or.inr ⟨15, ?_, ?_⟩
      · calc (10 : ℚ) ^ 16 * 10 ^ b = 10 ^ (16 + b) := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
          _ ≤ 10 ^ (r.exponent + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 10 ^ (15 : ℕ) * 10 ^ r.exponent := by rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
      · -- the floor is a canonical amount, at least `10^15` steps, and at most the value
        have hr15 : (10 : ℚ) ^ (15 : ℕ) * 10 ^ r.exponent ≤ r.toRat := by
          rw [STAmount.toRat_of_nonneg r (STAmount.mIsNegative_false_of_nonneg r (by rw [hfl]; positivity) hrz)]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrc.mant_lo) (zpow_pos (by norm_num) _).le
        have hfle : (⌊aa.toRat / 10 ^ r.exponent⌋ : ℚ) * 10 ^ r.exponent ≤ aa.toRat := by
          have := Int.floor_le (aa.toRat / 10 ^ r.exponent)
          rw [le_div_iff₀ hp'] at this
          exact this
        rw [hfl] at hr15
        linarith
  · rw [hce]
    have := Int.le_ceil (aa.toRat / 10 ^ r.exponent)
    rw [div_le_iff₀ hp'] at this
    linarith


/-- Clearing a payment's impairment keeps AssetsAvailable, AssetsDeployed, the asset and the base scale. -/
private lemma Loan.unimpairIfImpaired_balances (loan : Loan) (v v1 : Vault) (l1 : Loan)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (h : (Loan.unimpairIfImpaired loan v).run = .ok (.ok { loan' := l1, pool' := v1 })) :
    v1.assetsAvailable.toRat = v.assetsAvailable.toRat ∧ v1.assetsDeployed.toRat = v.assetsDeployed.toRat ∧
      v1.numericType = v.numericType ∧ v1.baseExponent = v.baseExponent := by
  have hbe := Loan.unimpairIfImpaired_baseExponent loan v v1 l1 h
  cases himp : loan.isImpaired
  · rw [Loan.unimpairIfImpaired_not loan v himp] at h
    obtain rfl : v = v1 := by injection h with h; injection h with h; injection h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [Loan.unimpairIfImpaired_impaired loan v himp] at h
    split at h
    · cases h
    · cases h
    · rename_i v1' hadj
      injection h with h
      injection h with h
      injection h with _ hv
      subst hv
      obtain ⟨hs, hnt, -⟩ := Vault.poolAdjust_sums v v1' _ hadj
      obtain ⟨aa, haa, hround⟩ := hs.cash
      rw [Number.operator_add_zero_right, Except.ok.injEq] at haa
      subst haa
      have hd := hs.deployed
      rw [Number.operator_add_zero_right, Except.ok.injEq] at hd
      exact ⟨STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm hst hround,
        by rw [hd], hnt, hbe⟩

/-- A payment never lowers AssetsTotal on a reachable ledger whose vault is not coarsened before or after it.
The vault gains the principal and the interest paid and gives up the principal from AssetsDeployed. -/
private lemma LendingLedger.pay_total_ge (l l' : LendingLedger) (i : Nat) (pt : LoanPaymentType) (amount : Number)
    (hr : l.Reachable) (h : (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) (hnc : l.NotCoarsened)
    (hnc' : l'.NotCoarsened) :
    l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤
      l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat := by
  have hbe' := LendingLedger.apply_baseExponent h
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, broker, loan, r, he, hb, hw, -, hpay, rfl⟩ := l.applyLoan_pay_inv u i pt amount hu
  change r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ r.pool'.baseExponent
    at hnc'
  change r.pool'.baseExponent = l.vault.baseExponent at hbe'
  rw [hbe'] at hnc'
  show _ ≤ r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  obtain ⟨hAAg, hADg, -, -, -, -⟩ := LendingLedger.base_grid_proof l hr hmax
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale ⟨e, broker, he, hb, hw⟩
  obtain ⟨hblo, hbhi, hbint⟩ := l.vault.baseExponent_bounds
  obtain ⟨-, hsr⟩ := Vault.baseExponent_grid l.vault
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  have hT : 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ≤ 2 ^ 63 * 10 ^ l.vault.baseExponent :=
    mul_le_mul_of_nonneg_right (by norm_num) hp.le
  unfold LendingLedger.NotCoarsened at hnc

  obtain ⟨p, hp', hs⟩ := Loan.pay_ok loan l.vault pt amount l.now r hpay
  obtain ⟨-, hu', hst, -, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now p hp'
  obtain ⟨hpAA, hpAD, hpnt, hpbe⟩ := Loan.unimpairIfImpaired_balances loan l.vault p.pool loan.unimpaired
    (hr.storesAvailable hmax) hu'
  obtain ⟨toPool, yd, toBroker, cover', debt', raw, broker', hsums, hadj, hlaw, -, -, -, -⟩ :=
    UnsettledPayment.settle_ok p r hs
  have hpb : p.loan.broker = loan.broker := hst.broker
  obtain ⟨hPg, hIg⟩ := Loan.payInstalments_onGrid loan l.vault pt amount l.now p (by rw [hls]; omega) hp'
  rw [hls] at hPg hIg
  have hparts := hsums.parts
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hparts
  obtain ⟨⟨hP0s, hI0s⟩, -⟩ := hparts
  have hP0 := Number.toRat_nonneg_of_not_signum_neg _ hPg.1 hP0s
  have hI0 := Number.toRat_nonneg_of_not_signum_neg _ hIg.1 hI0s
  obtain ⟨tot, credit, htot, hcred, hto⟩ := hsums.toPool
  rw [hpb, hnt, hpbe] at hcred
  obtain ⟨hsa, -⟩ := Vault.adjustBalances_ok_inv p.pool _ raw hadj
  obtain ⟨aa, haa, hround⟩ := hsa.cash
  have hdep := hsa.deployed
  rw [Vault.total_of_raw hlaw]
  have hraw := (RawVault.to_lawful_ok hlaw).1
  have hrAD0 : 0 ≤ raw.assetsDeployed.toRat := by
    have := r.pool'.exact.assetsDeployed_nonneg
    rwa [show r.pool'.toExact.assetsDeployed = r.pool'.toRawVault.assetsDeployed.toRat from rfl, hraw] at this
  have hrAA0 : 0 ≤ raw.assetsAvailable.toRat := by
    have := r.pool'.exact.assetsAvailable_nonneg
    rwa [show r.pool'.toExact.assetsAvailable = r.pool'.toRawVault.assetsAvailable.toRat from rfl, hraw] at this
  have hnc'' : raw.assetsAvailable.toRat + raw.assetsDeployed.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent := by
    rw [← Vault.total_of_raw hlaw]; exact hnc'
  have hpAAg : Number.OnGrid p.pool.baseExponent p.pool.assetsAvailable := by
    obtain ⟨k, hk⟩ := hAAg.2
    exact ⟨p.pool.wf.assetsAvailable_norm, k, by rw [hpAA, hk, hpbe]⟩
  have hpADg : Number.OnGrid p.pool.baseExponent p.pool.assetsDeployed := by
    obtain ⟨k, hk⟩ := hADg.2
    exact ⟨p.pool.wf.assetsDeployed_norm, k, by rw [hpAD, hk, hpbe]⟩
  rw [hpbe] at hpAAg hpADg
  -- the principal never exceeds AssetsDeployed, so taking it off is exact
  have hPAD : p.amounts.principalPaid.toRat ≤ l.vault.assetsDeployed.toRat := by
    by_contra hgt
    push Not at hgt
    obtain ⟨kD, hkD⟩ := hADg.2
    obtain ⟨kP, hkP⟩ := hPg.2
    have hlt : kD < kP := by
      have : (kD : ℚ) * 10 ^ l.vault.baseExponent < (kP : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [← hkD, ← hkP]; exact hgt
      exact_mod_cast lt_of_mul_lt_mul_right this hp.le
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (-1) l.vault.baseExponent (by norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    have hR := operator_add_rounded_to_nearest _ _ _ p.pool.wf.assetsDeployed_norm
      (Number.operator_neg_isNormalized _ hPg.1) hdep
    have := Number.roundsToRepresentable_le _ _ hR w hw (by
      rw [hwv, Number.toRat_neg, hpAD, hkD, hkP]
      have : ((kD - kP : ℤ) : ℚ) ≤ -1 := by exact_mod_cast (by omega : kD - kP ≤ -1)
      push_cast at this ⊢
      nlinarith)
    rw [hwv] at this
    push_cast at this
    linarith
  have hPdeploy : raw.assetsDeployed.toRat = l.vault.assetsDeployed.toRat - p.amounts.principalPaid.toRat := by
    have := Number.add_exact_of_grid hpADg hPg.neg (by rw [Number.toRat_neg, hpAD]; nlinarith)
      (by rw [Number.toRat_neg, hpAD]; linarith) hsr hdep
    rw [this, Number.toRat_neg, hpAD]; ring
  rw [hPdeploy]
  have htotn := operator_add_isNormalized_to_nearest_sz _ _ _ hPg.1 hIg.1 htot
  have htot0 : 0 ≤ tot.toRat := operator_add_nonneg _ _ _ hPg.1 hIg.1 htot (by linarith)
  have htotP : p.amounts.principalPaid.toRat ≤ tot.toRat :=
    Number.roundsToRepresentable_ge tot _ (operator_add_rounded_to_nearest _ _ _ hPg.1 hIg.1 htot) _ hPg.1 (by linarith)
  have hpasset : Vault.HoldsAsset p.pool := by unfold Vault.HoldsAsset; rw [hpnt]; exact hasset
  rw [hpnt] at hround
  cases hint : l.vault.numericType.isIntegral
  · -- an IOU vault: the credit lands exactly unless it crosses `10^16` base units, and the vault is not coarsened
    -- after the payment
    have hfr := NumericType.eq_fractional_of_not_integral hint
    rw [hfr] at hcred hround
    by_cases hcross : 10 ^ 16 * 10 ^ l.vault.baseExponent ≤ p.pool.assetsAvailable.toRat + tot.toRat
    · exfalso
      have := vault_credit_cross p.pool.assetsAvailable tot l.vault.baseExponent credit toPool aa raw.assetsAvailable
        p.pool.wf.assetsAvailable_norm hpAAg.2 (by rw [hpAA]; exact hAA0) (by rw [hpAA]; linarith) htotn
        ⟨hblo, hbhi⟩ hcross hcred hto haa hround
      linarith
    push Not at hcross
    have hPI : tot.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat := by
      by_contra hne
      have hbig : 2 ^ 63 * 10 ^ l.vault.baseExponent ≤ p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat :=
        by
        by_contra hsmall
        push Not at hsmall
        exact hne (Number.add_exact_of_grid hPg hIg (by nlinarith) hsmall hsr htot)
      obtain ⟨Wn, hWn, hWv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16) l.vault.baseExponent
        (by constructor <;> norm_num) ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
      have := Number.roundsToRepresentable_ge tot _ (operator_add_rounded_to_nearest _ _ _ hPg.1 hIg.1 htot) Wn hWn
        (by rw [hWv]; push_cast; linarith)
      rw [hWv] at this
      push_cast at this
      rw [hpAA] at hcross
      linarith
    obtain ⟨kA, hkA⟩ := hpAAg.2
    have hkA0 : 0 ≤ kA := by
      have : (0 : ℚ) ≤ (kA : ℚ) * 10 ^ l.vault.baseExponent := by rw [← hkA, hpAA]; exact hAA0
      exact_mod_cast nonneg_of_mul_nonneg_left this hp
    have hroom : p.pool.assetsAvailable.toRat + tot.toRat ≤
        (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent := by
      obtain ⟨kP, hkP⟩ := hPg.2
      obtain ⟨kI, hkI⟩ := hIg.2
      have hsum : p.pool.assetsAvailable.toRat + tot.toRat = ((kA + kP + kI : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [hPI, hkA, hkP, hkI]; push_cast; ring
      have hk : kA + kP + kI < 10 ^ 16 := by
        have : ((kA + kP + kI : ℤ) : ℚ) * 10 ^ l.vault.baseExponent <
            ((10 ^ 16 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
          rw [← hsum]; push_cast; exact hcross
        exact_mod_cast lt_of_mul_lt_mul_right this hp.le
      rw [hsum, open_line_eq]
      have : ((kA + kP + kI : ℤ) : ℚ) ≤ 10 ^ 16 - 1 := by
        have : kA + kP + kI ≤ 10 ^ 16 - 1 := by omega
        exact_mod_cast this
      nlinarith
    have hcv := sumRoundAndSubtract_at_base _ _ _ credit kA.toNat p.pool.wf.assetsAvailable_norm
      (by rw [hkA]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hkA0).symm) htotn htot0 ⟨by omega, hbhi⟩ hroom hcred
    obtain ⟨-, htn⟩ := sumRoundAndSubtract_downward_le _ _ _ _ credit p.pool.wf.assetsAvailable_norm
      (by rw [hpAA]; exact hAA0) htotn htot0 (Vault.baseExponent_range l.vault) hcred
    obtain ⟨htv, htnn⟩ := htn toPool hto
    have hPpool : p.amounts.principalPaid.toRat ≤ toPool.toRat := by
      rw [htv, hcv]
      exact floor_mul_ge _ _ _ htotP (Or.inl hPg.2)
    have htoPg : Number.OnGrid l.vault.baseExponent toPool := ⟨htnn, ⌊tot.toRat / 10 ^ l.vault.baseExponent⌋,
      by rw [htv, hcv]⟩
    have htoP_le : toPool.toRat ≤ tot.toRat := by
      rw [htv, hcv]
      have := Int.floor_le (tot.toRat / 10 ^ l.vault.baseExponent)
      rw [le_div_iff₀ hp] at this
      exact this
    have hAAp : raw.assetsAvailable.toRat = p.pool.assetsAvailable.toRat + toPool.toRat := by
      refine Vault.cash_update_eq p.pool toPool aa raw.assetsAvailable hpasset (by rw [hpbe]; exact hpAAg)
        (by rw [hpbe]; exact htoPg) (by rw [hpAA]; linarith) ?_ haa (by rw [hpnt, hfr]; exact hround)
      rw [hpbe, open_line_eq, hpAA]
      rw [hpAA] at hcross
      linarith
    rw [hAAp, hpAA]
    linarith
  · -- an XRP or MPT vault: the credit is the sum floored to a whole unit, and lands at least on the principal
    have hb0 : l.vault.baseExponent = 0 := hbint hint
    unfold sumRoundAndSubtract at hcred
    rw [if_pos hint] at hcred
    obtain ⟨x, hx, hcred⟩ := bind_ok_peel _ _ _ hcred
    obtain rfl : x = credit := Except.ok.inj hcred
    have htneg := Number.negative_false_of_nonneg tot htotn htot0
    obtain ⟨iv, hiv, hxv⟩ := STAmount.ofNumber_integral_toRat _ tot _ x hint htneg hx
    obtain ⟨hfl1, hfl2⟩ := Number.to_rep_downward_floor tot iv htotn htneg hiv
    obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ x hint hx
    have hsmall : x.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 := hic.in_range
      rw [hty] at h1
      have := hmax hint
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨sn, hsn, hsnv, -⟩ := STAmount.toNumber_integral_small_exact x .to_nearest hic hsmall
    rw [hsn, Except.ok.injEq] at hto
    subst hto
    have hcrn : sn.isNormalized := STAmount.toNumber_isNormalized x _ sn hsn
    -- the principal is a whole unit at most the sum, so at most its floor
    obtain ⟨kP, hkP⟩ := hPg.2
    rw [hb0, zpow_zero, mul_one] at hkP
    have hPiv : p.amounts.principalPaid.toRat ≤ sn.toRat := by
      rw [hsnv, hxv, hkP]
      have : (kP : ℚ) < iv.toInt + 1 := by rw [← hkP]; linarith
      have : kP ≤ iv.toInt := by
        have : kP < iv.toInt + 1 := by exact_mod_cast this
        omega
      exact_mod_cast this
    obtain ⟨kA, hkA⟩ := hpAAg.2
    rw [hb0, zpow_zero, mul_one] at hkA
    have hkA0 : 0 ≤ kA := by
      have : (0 : ℚ) ≤ (kA : ℚ) := by rw [← hkA, hpAA]; exact hAA0
      exact_mod_cast this
    have hW1 : 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent = 10 ^ 16 := by rw [hb0, zpow_zero, mul_one]
    have hkAP : kA + kP < 2 ^ 63 := by
      have h1 : ((kA + kP : ℤ) : ℚ) < 2 ^ 63 := by
        push_cast; rw [← hkA, ← hkP, hpAA]; rw [hW1] at hnc; linarith
      exact_mod_cast h1
    have hkP0 : 0 ≤ kP := by
      have : (0 : ℚ) ≤ (kP : ℚ) := by rw [← hkP]; exact hP0
      exact_mod_cast this
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (kA + kP) 0 ⟨by omega, hkAP⟩
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    rw [zpow_zero, mul_one] at hwv
    have hcrv : (w.toRat : ℚ) = p.pool.assetsAvailable.toRat + p.amounts.principalPaid.toRat := by
      rw [hwv, hkA, hkP]; push_cast; ring
    have haaw : w.toRat ≤ aa.toRat :=
      Number.roundsToRepresentable_ge aa _
        (operator_add_rounded_to_nearest _ _ _ p.pool.wf.assetsAvailable_norm hcrn haa) w hw (by rw [hcrv]; linarith)
    have haan := operator_add_isNormalized_to_nearest_sz _ _ _ p.pool.wf.assetsAvailable_norm hcrn haa
    -- rounding to the asset lands on the floor or the ceiling, both at least that whole number
    unfold STAmount.roundToNumericType at hround
    cases hof : STAmount.ofNumber l.vault.numericType aa .to_nearest with
    | error e => rw [hof] at hround; cases hround
    | ok rr =>
    rw [hof] at hround
    simp only at hround
    obtain ⟨hic', hty'⟩ := STAmount.ofNumber_integral_canonical _ _ _ rr hint hof
    have hsmall' : rr.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 := hic'.in_range
      rw [hty'] at h1
      have := hmax hint
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨sn', hsn', hsnv', -⟩ := STAmount.toNumber_integral_small_exact rr .to_nearest hic' hsmall'
    rw [hsn', Except.ok.injEq] at hround
    have hN := STAmount.ofNumber_to_nearest_neighbour _ aa rr haan (by rw [hcrv] at haaw; linarith) hof (Or.inl hint)
    unfold RoundsToRepresentableAt at hN
    change rr.toRat = _ ∨ rr.toRat = _ at hN
    rw [show rr.exponent = rr.mOffset from rfl, hic'.offset_zero, zpow_zero, div_one, mul_one, mul_one] at hN
    have hge : w.toRat ≤ sn'.toRat := by
      rw [hsnv']
      rcases hN with hfl | hce
      · rw [hfl, hwv]
        exact_mod_cast Int.le_floor.mpr (by rw [← hwv]; exact_mod_cast haaw)
      · rw [hce]; exact haaw.trans (Int.le_ceil _)
    rw [hcrv, hpAA, hround] at hge
    linarith

/-- A transaction that is not a default, a withdrawal or a clawback never lowers AssetsTotal on a reachable
ledger that is not coarsened before or after it. -/
lemma LendingLedger.noLoss_step (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (hnc : l.NotCoarsened) (hnc' : l'.NotCoarsened)
    (hout : tx.isOutflow = false) :
    l.vault.toRawVault.toExact.assetsTotal ≤ l'.vault.toRawVault.toExact.assetsTotal := by
  show l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤
    l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat
  by_cases hpay : ∃ i pt amount, tx = .loanPay i pt amount
  · obtain ⟨i, pt, amount, rfl⟩ := hpay
    exact LendingLedger.pay_total_ge l l' i pt amount hr h hnc hnc'
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  obtain ⟨hAAg, hADg, -, -, hYg, -⟩ := LendingLedger.base_grid_proof l hr hmax
  have hv : Vault.OnBaseGrid l.vault := ⟨hAAg, hADg⟩
  have hS : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ (16 + l.vault.baseExponent) := by
    rw [open_line_eq]; exact hnc
  have hinv := hr.scaleInv
  have hpre := (LendingLedger.apply_checked h).1
  by_cases hvt : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hvt h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    cases tx with
    | vaultDeposit hd amount isDonation =>
      obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit' l hd amount isDonation hasset hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · unfold_ter at hu
        walk_ok
        exact Vault.deposit_total_ge _ _ _ _ _ hc hty hasset hv hS hYg _ ‹_›
      · cases hu
    | vaultWithdraw hd amount => simp [LendingTx.isOutflow] at hout
    | vaultClawback hd assets => simp [LendingTx.isOutflow] at hout
    | vaultBurnShares hd amount =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
      rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)]
    | vaultSet m b ub =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
      rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)]
    | _ => simp only [LendingTx.isVault] at hvt; cases hvt
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact le_rfl
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    show _ ≤ u.vault.assetsAvailable.toRat + u.vault.assetsDeployed.toRat
    cases tx with
    | loanSet i principal rates fees pi pt gp sd twoStep ao =>
      obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
      simp only [LendingLedger.applyLoan] at hu
      obtain ⟨broker, r, hb', hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
      have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
      exact (Loan.create_total_eq _ _ _ _ _ _ _ _ r hasset hv hS hpn hpos hst (hinv.brokers i broker hb') hcr).ge
    | loanAccept i =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_accept_inv u i hu
      exact (Loan.accept_total_eq _ _ _ hasset hv hS hr').ge
    | loanDelete i =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_delete_inv u i hu
      obtain ⟨hls, hnt⟩ := hr.loanAt_scale ⟨e, broker, he, hb', hw⟩
      exact (Loan.delete_total_eq _ _ _ hasset hv hS hls hnt hr').ge
    | loanManage i action =>
      obtain ⟨e, broker, loan, r, he, hb', hw, -, hr', rfl⟩ := l.applyLoan_manage_inv u i action hu
      show _ ≤ r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat
      cases action with
      | impair =>
        simp only [Loan.manage, Loan.manageImpair] at hr'
        unfold_ter at hr'
        walk_ok
        exact (Loan.changeImpairment_total_eq loan _ true _ hasset hv hS ‹_›).ge
      | unimpair => exact (Loan.changeImpairment_total_eq loan _ false r hasset hv hS hr').ge
      | default => simp [LendingTx.isOutflow] at hout
    | loanPay i paymentType amount => exact absurd ⟨i, paymentType, amount, rfl⟩ hpay
    | _ => simp only [LendingLedger.applyLoan] at hu; cases hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hvt hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact le_rfl
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact le_rfl

/-- Proof body of `Lending.Reachable.no_loss_without_default`. -/
lemma LendingLedger.no_loss_without_default_proof (start l : LendingLedger) (txs : List LendingTx) (x : ℚ)
    (hr : start.Reachable) (hrun : start.ReachableFromIn txs l x) (hout : ∀ tx ∈ txs, tx.isOutflow = false)
    (hnc : ∀ (pre : List LendingTx) (l₁ : LendingLedger) (x₁ : ℚ), pre <+: txs →
      start.ReachableFromIn pre l₁ x₁ → l₁.NotCoarsened) :
    start.vault.toRawVault.toExact.assetsTotal ≤ l.vault.toRawVault.toExact.assetsTotal := by
  induction hrun with
  | refl => exact le_rfl
  | @step txs₀ l₀ l₁ x₀ tx hprev hok ih =>
    have ih' := ih (fun t ht => hout t (List.mem_append_left _ ht))
      (fun pre l₂ x₂ hpre hr' => hnc pre l₂ x₂ (hpre.trans (List.prefix_append _ _)) hr')
    have hstep := LendingLedger.noLoss_step l₀ l₁ tx (hprev.reachable_of hr) hok
      (hnc txs₀ l₀ x₀ (List.prefix_append _ _) hprev)
      (hnc (txs₀ ++ [tx]) l₁ _ (List.prefix_refl _) (.step tx hprev hok))
      (hout tx (List.mem_append_right _ (List.mem_singleton_self _)))
    exact ih'.trans hstep

end XRPL.Model.Lending
