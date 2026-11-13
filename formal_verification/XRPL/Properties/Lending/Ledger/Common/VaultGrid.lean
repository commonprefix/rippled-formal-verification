import XRPL.Properties.Lending.Loan.Common.PayPrincipal
import XRPL.Properties.Lending.Common.GridRounding
import XRPL.Properties.Lending.Ledger.Common.LossInv
import XRPL.Properties.Lending.Loan.Common.ManageCoverBase
import XRPL.Properties.Lending.Loan.Common.AcceptProofs
import XRPL.Properties.Vault.Proofs.OpenZone
import XRPL.Properties.Lending.Ledger.Common.VaultOutflow
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # AssetsAvailable and AssetsDeployed on the base grid

Every amount a transaction adds to AssetsAvailable or AssetsDeployed of an IOU vault is a whole number of base units,
and the roundings of such sums stay whole numbers of base units, so a reachable IOU vault keeps both on the grid. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts WithdrawAmount)

open private STAmount.ofNumber_integral_small from XRPL.Properties.Lending.Loan.Common.Grid
open private Loan.create_principalOutstanding from XRPL.Properties.Lending.Loan.Common.AcceptProofs
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Vault.withdraw_payout_nonneg Vault.clawback_payout_nonneg
  from XRPL.Properties.Lending.Ledger.Common.VaultOutflow

/-- AssetsAvailable and AssetsDeployed are whole numbers of base units. -/
def Vault.OnBaseGrid (v : Vault) : Prop :=
  Number.OnGrid v.baseExponent v.assetsAvailable ∧ Number.OnGrid v.baseExponent v.assetsDeployed

/-- A balance change whose cash and deployed amounts are grid points writes grid points. -/
private lemma Vault.adjustBalances_onBaseGrid (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v) (hc : Number.OnGrid v.baseExponent c.cash)
    (hd : Number.OnGrid v.baseExponent c.deployed) (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    Number.OnGrid v.baseExponent raw.assetsAvailable ∧ Number.OnGrid v.baseExponent raw.assetsDeployed := by
  obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv v c raw h
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨aa, haa, hround⟩ := hs.cash
  exact ⟨STAmount.roundToNumericType_onGrid_none _ _ _ _ _ (Number.OnGrid.add hv.1 hc hsr haa) (by omega)
    (by rw [hfr]; intro h'; cases h') hround, Number.OnGrid.add hv.2 hd hsr hs.deployed⟩

/-- A vault written from a raw record with the old asset and scale is on the base grid when the record's
AssetsAvailable and AssetsDeployed are. -/
private lemma Vault.onBaseGrid_of_raw {v v' : Vault} {raw : RawVault} (hraw : v'.toRawVault = raw)
    (hnt : raw.numericType = v.numericType) (hsc : raw.scale = v.scale)
    (h : Number.OnGrid v.baseExponent raw.assetsAvailable ∧ Number.OnGrid v.baseExponent raw.assetsDeployed) :
    Vault.OnBaseGrid v' := by
  have hbe : v'.baseExponent = v.baseExponent := by
    unfold XRPL.Model.SingleAssetVault.Vault.baseExponent
    rw [show v'.numericType = v'.toRawVault.numericType from rfl, show v'.scale = v'.toRawVault.scale from rfl,
      hraw, hnt, hsc]
  unfold Vault.OnBaseGrid
  rw [hbe, show v'.assetsAvailable = v'.toRawVault.assetsAvailable from rfl,
    show v'.assetsDeployed = v'.toRawVault.assetsDeployed from rfl, hraw]
  exact h

/-- A pool update whose cash and deployed amounts are grid points keeps the vault on the base grid. -/
private lemma Vault.poolAdjust_onBaseGrid (v v' : Vault) (c : PoolBalanceChange) (hfr : v.numericType = .fractional)
    (hv : Vault.OnBaseGrid v) (hc : Number.OnGrid v.baseExponent c.cash) (hd : Number.OnGrid v.baseExponent c.deployed)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : Vault.OnBaseGrid v' := by
  obtain ⟨raw, hadj, hlaw⟩ := Vault.poolAdjust_ok_inv v c v' h
  have hraw := (RawVault.to_lawful_ok hlaw).1
  have heq := (Vault.adjustBalances_ok_inv v c raw hadj).2
  exact Vault.onBaseGrid_of_raw hraw (by rw [heq]) (by rw [heq])
    (Vault.adjustBalances_onBaseGrid v c raw hfr hv hc hd hadj)

/-- A new loan keeps the vault on the base grid: its principal is a whole number of base units. -/
private lemma Loan.create_onBaseGrid (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (ao pending : Bool) (r : LoanWithDisbursement Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v) (hp : principal.isNormalized)
    (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (h : (Loan.create broker v principal rates fees schedule ao pending).run = .ok (.ok r)) :
    Vault.OnBaseGrid r.pool' := by
  obtain ⟨_, _, _, principal', _, -, hround, hpool, -, -⟩ := Loan.create_ok_inv broker v principal rates fees schedule
    ao pending r h
  have hpo := Loan.create_principalOutstanding broker v principal rates fees schedule ao pending r hp hpos.le hst h
  have hls := Loan.create_loanScale_proof broker v principal rates fees schedule ao pending r hp hpos hst hnt h
  have hpg : Number.OnGrid v.baseExponent principal := by
    rw [← hpo, ← hls]; exact (Loan.principal_onGrid r.loan').1
  have hpg' := STAmount.roundToNumericType_onGrid_none _ _ _ _ _ hpg (by have := Vault.baseExponent_grid v; omega)
    (by rw [hnt, hfr]; intro h'; cases h') hround
  exact Vault.poolAdjust_onBaseGrid v r.pool' _ hfr hv hpg'.neg hpg hpool

/-- An accept keeps the vault on the base grid: it moves no cash and deploys nothing. -/
private lemma Loan.accept_onBaseGrid (loan : Loan) (v : Vault) (r : LoanWithDisbursement Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v) (h : (loan.accept v).run = .ok (.ok r)) :
    Vault.OnBaseGrid r.pool' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  exact Vault.poolAdjust_onBaseGrid v _ _ hfr hv (Number.OnGrid.zero _) (Number.OnGrid.zero _) ‹_›

/-- A delete keeps the vault on the base grid: a pending loan returns its principal, a paid-off one moves
nothing. -/
private lemma Loan.delete_onBaseGrid (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v) (hls : loan.loanScale = v.baseExponent)
    (hnt : loan.broker.numericType = v.numericType) (h : (loan.delete v).run = .ok (.ok r)) :
    Vault.OnBaseGrid r.pool' := by
  by_cases hp : loan.isPending = true
  · obtain ⟨principal', raw, _, hround, hadj, hlaw, -, -⟩ := Loan.delete_pending_ok_inv loan v r hp h
    have hpg : Number.OnGrid v.baseExponent loan.principalOutstanding := hls ▸ (Loan.principal_onGrid loan).1
    have hpg' := STAmount.roundToNumericType_onGrid_none _ _ _ _ _ hpg
      (by have := Vault.baseExponent_grid v; omega) (by rw [hnt, hfr]; intro h'; cases h') hround
    have heq := (Vault.adjustBalances_ok_inv v _ raw hadj).2
    exact Vault.onBaseGrid_of_raw (RawVault.to_lawful_ok hlaw).1 (by rw [heq]) (by rw [heq])
      (Vault.adjustBalances_onBaseGrid v _ raw hfr hv hpg' hpg.neg hadj)
  · simp only [Loan.delete, Bool.not_eq_true] at h hp
    rw [hp] at h
    unfold_ter at h
    walk_ok
    exact hv

/-- An impairment change keeps the vault on the base grid: it moves no cash and deploys nothing. -/
private lemma Loan.changeImpairment_onBaseGrid (loan : Loan) (v : Vault) (impaired : Bool) (r : LoanWithPool Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v)
    (h : (Loan.changeImpairment loan v impaired).run = .ok (.ok r)) : Vault.OnBaseGrid r.pool' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_onBaseGrid v _ _ hfr hv (Number.OnGrid.zero _) (Number.OnGrid.zero _) ‹_›

/-- A default keeps the vault on the base grid: the cover it adds is floored at the scale of AssetsAvailable after
the default. -/
private lemma Loan.manageDefault_onBaseGrid (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v) (hls : loan.loanScale = v.baseExponent)
    (hnt : loan.broker.numericType = v.numericType) (h : (loan.manageDefault v).run = .ok (.ok r)) :
    Vault.OnBaseGrid r.pool' := by
  obtain ⟨_, _, _, raw, _, -, hdc, hadj, hraw, -⟩ := Loan.manageDefault_ok_parts loan v r h
  have hdcg : Number.OnGrid v.baseExponent r.amountToPool := by
    unfold Loan.defaultCover at hdc
    obtain ⟨_, -, hdc⟩ := bind_ok_peel _ _ _ hdc
    obtain ⟨_, -, hdc⟩ := bind_ok_peel _ _ _ hdc
    obtain ⟨_, -, hdc⟩ := bind_ok_peel _ _ _ hdc
    obtain ⟨st, hst, hdc⟩ := bind_ok_peel _ _ _ hdc
    obtain ⟨hb, -⟩ := Vault.baseExponent_grid v
    exact sumRoundAndSubtract_onGrid _ _ _ _ _ st _ hv.1 ⟨hb, v.baseExponent_bounds.2.1⟩
      (by rw [hnt, hfr]; intro h'; cases h') hst hdc
  have hpg : Number.OnGrid v.baseExponent loan.principalOutstanding := hls ▸ (Loan.principal_onGrid loan).1
  have heq := (Vault.adjustBalances_ok_inv v _ raw hadj).2
  exact Vault.onBaseGrid_of_raw hraw (by rw [heq]) (by rw [heq])
    (Vault.adjustBalances_onBaseGrid v _ raw hfr hv hdcg hpg.neg hadj)

/-- A payment keeps the vault on the base grid: the credit is floored at the scale of AssetsAvailable after the
payment, and the principal it pays is whole base units. -/
private lemma Loan.pay_onBaseGrid (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (hfr : v.numericType = .fractional) (hv : Vault.OnBaseGrid v)
    (hls : loan.loanScale = v.baseExponent) (hnt : loan.broker.numericType = v.numericType)
    (h : (loan.pay v pt amount now).run = .ok (.ok r)) : Vault.OnBaseGrid r.pool' := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨hpg, -, -⟩ := Loan.payInstalments_paidOn loan v pt amount now p
    ⟨by rw [hls]; omega, by rw [hls]; exact v.baseExponent_bounds.2.1⟩ hp
  obtain ⟨toPool, yieldDelta, _, _, _, raw, _, hsums, hadj, hlaw, -, -, -, -⟩ := UnsettledPayment.settle_ok p r hs
  -- the unimpair step moves no cash and deploys nothing
  have hpool : Vault.OnBaseGrid p.pool ∧ p.pool.numericType = v.numericType ∧ p.pool.scale = v.scale := by
    cases himp : loan.isImpaired
    · rw [Loan.unimpairIfImpaired_not loan v himp] at hu
      obtain rfl : v = p.pool := by injection hu with hu; injection hu with hu; injection hu
      exact ⟨hv, rfl, rfl⟩
    · rw [Loan.unimpairIfImpaired_impaired loan v himp] at hu
      split at hu
      · cases hu
      · cases hu
      · rename_i v1 hadj1
        obtain rfl : v1 = p.pool := by injection hu with hu; injection hu with hu; injection hu
        obtain ⟨-, hnt1, hsc1⟩ := Vault.poolAdjust_sums v p.pool _ hadj1
        exact ⟨Vault.poolAdjust_onBaseGrid v p.pool _ hfr hv (Number.OnGrid.zero _) (Number.OnGrid.zero _) hadj1,
          hnt1, hsc1⟩
  obtain ⟨hpv, hpnt, hpsc⟩ := hpool
  have hbe : p.pool.baseExponent = v.baseExponent := by
    unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hpnt, hpsc]
  obtain ⟨_, credit, -, hsrs, hcredit⟩ := hsums.toPool
  have hbnt : p.loan.broker.numericType = p.pool.numericType := by
    rw [show p.loan.broker = loan.broker from hst.broker, hnt, hpnt]
  have hcg : Number.OnGrid p.pool.baseExponent toPool := by
    exact sumRoundAndSubtract_onGrid _ _ _ _ _ credit _ hpv.1 ⟨by omega, by rw [hbe]; exact v.baseExponent_bounds.2.1⟩
      (by rw [hbnt, hpnt, hfr]; intro h'; cases h') hsrs hcredit
  have hdg : Number.OnGrid p.pool.baseExponent p.amounts.principalPaid.operator_neg := by
    rw [hbe, ← hls]; exact hpg.neg
  have heq := (Vault.adjustBalances_ok_inv p.pool _ raw hadj).2
  have hres := Vault.onBaseGrid_of_raw (RawVault.to_lawful_ok hlaw).1 (by rw [heq]) (by rw [heq])
    (Vault.adjustBalances_onBaseGrid p.pool _ raw (hpnt.trans hfr) hpv hcg hdg hadj)
  exact hres

/-- A cash update by an amount on the base grid keeps AssetsAvailable on the base grid. -/
private lemma Vault.adjustAssetsAndShares_onGrid (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hfr : v.numericType = .fractional) (hv : Number.OnGrid v.baseExponent v.assetsAvailable)
    (hc : assets.CanonicalOrZero) (hk : ∃ k : ℤ, assets.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.ok raw)) :
    Number.OnGrid v.baseExponent raw.assetsAvailable := by
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, rfl⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw h
  obtain ⟨hnv, hnn⟩ := hc.toNumber_exact assetsNum hnum
  obtain ⟨k, hk⟩ := hk
  exact STAmount.roundToNumericType_onGrid_none _ _ _ _ _
    (Number.OnGrid.add hv ⟨hnn, k, by rw [hnv, hk]⟩ hsr hs) (by omega) (by rw [hfr]; intro h'; cases h') haa

open XRPL.Model.SingleAssetVault in
/-- A deposit keeps AssetsAvailable on the base grid: its charge is clamped onto the base grid. -/
private lemma Vault.deposit_onGrid (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hfr : v.numericType = .fractional) (hv : Number.OnGrid v.baseExponent v.assetsAvailable)
    (r : VaultWithAmounts) (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    Number.OnGrid v.baseExponent r.vault'.assetsAvailable := by
  obtain ⟨ra, amounts, raw, hra, hcomp, -, hadj, hraw, -, -⟩ := Vault.deposit_ok_reduces v amount isDonation t hpos r h
  have hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hfr]; intro h'; cases h'
  obtain ⟨hrac, hraty, -⟩ := Vault.roundedDepositAmount_form v amount ra hc hty hra
  obtain ⟨hcf, -, -⟩ := computeDeposit_assets_form v ra isDonation amounts hrac hraty hmax hcomp
  have hcharge : ∃ k : ℤ, amounts.assets.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
    cases isDonation
    · obtain ⟨assets, assetsTotal, -, -, hsta, -, -, hcl, -⟩ := computeDeposit_success_reduces v ra amounts hcomp
      obtain ⟨hf1, -⟩ := sharesToAssetsDeposit_form v amounts.shares assets hmax hsta
      exact Vault.clamp_grid v _ _ _ hf1 hcl
    · obtain ⟨assetsTotal, -, -, hcl, -⟩ := computeDeposit_donation_reduces v ra amounts hcomp
      exact Vault.clamp_grid v _ _ _ hrac hcl
  rw [show r.vault'.assetsAvailable = r.vault'.toRawVault.assetsAvailable from rfl, hraw]
  exact Vault.adjustAssetsAndShares_onGrid v _ _ raw hfr hv hcf hcharge hadj

open XRPL.Model.SingleAssetVault in
/-- A withdrawal pays a whole number of base units when AssetsAvailable is one. -/
private lemma Vault.withdraw_payout_grid (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hfr : v.numericType = .fractional)
    (hv : Number.OnGrid v.baseExponent v.assetsAvailable) (r : VaultWithAmounts)
    (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    ∃ k : ℤ, r.assets.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
  have hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hfr]; intro h'; cases h'
  simp only [XRPL.Model.SingleAssetVault.Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- a 100% fee pays nothing
  all_goals try exact ⟨0, by rw [(STAmount.toRat_eq_zero_iff _).mpr (STAmount.zero_mValue _)]; simp⟩
  -- the final withdrawal pays all of AssetsAvailable
  all_goals try
    have hp : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok _ := ‹_›
    rw [hfr] at hp
    exact STAmount.ofNumber_frac_grid _ _ _ _ hv (by have := Vault.baseExponent_grid v; omega) hp
  -- the fee path pays the payout clamped onto the base grid
  all_goals try
    have hp : STAmount.ofNumber v.numericType _ .downward = .ok _ := ‹_›
    have hcl : clampToSumExponent v.assetsAvailable _ v.baseExponent = .ok _ := ‹_›
    exact Vault.clamp_grid v _ _ _ (STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hp).1.operator_neg hcl
  -- a zero payout skips the fee
  all_goals
    have hnf : STAmount.operator_eq _ _ = false := ‹_›
    have hzs : ¬ (STAmount.operator_eq _ _ = false ∧ STAmount.isZero _ = false) := ‹_›
    have hz0 := Bool.of_not_eq_false (fun h => hzs ⟨hnf, h⟩)
    exact ⟨0, by rw [(STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz0)]; simp⟩

open XRPL.Model.SingleAssetVault in
/-- A clawback recovers a whole number of base units. -/
private lemma Vault.clawback_payout_grid (v : Vault) (assets holderShares : STAmount) (waive : Bool)
    (hnn : 0 ≤ assets.toRat) (hfr : v.numericType = .fractional) (r : VaultWithAmounts)
    (hok : (v.clawback assets holderShares waive hnn).run = .ok (.ok r)) :
    ∃ k : ℤ, r.assets.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
  have hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hfr]; intro h'; cases h'
  obtain ⟨amounts, raw, hcomp, -, -, hras, -⟩ := Vault.clawback_ok_reduces v assets holderShares waive hnn r hok
  rw [hras]
  obtain ⟨recovered, _, hpr, -, -, hrec⟩ := computeClawback_success_reduces v assets holderShares waive amounts hcomp
  have hrc : recovered.CanonicalOrZero := by
    cases hpr with
    | direct _ _ _ _ hs2a _ _ => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).1
    | capped _ _ _ _ _ _ _ _ _ _ _ _ _ hs2a _ _ => exact (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax hs2a).1
  rcases hrec with ⟨hz, heq⟩ | ⟨-, hcl, -⟩
  · rw [heq]; exact ⟨0, by rw [(STAmount.toRat_eq_zero_iff _).mpr (beq_iff_eq.mp hz)]; simp⟩
  · exact Vault.clamp_grid v _ _ _ hrc.operator_neg hcl

/-- A debit of a whole number of base units keeps AssetsAvailable on the base grid. -/
private lemma Vault.debit_onGrid (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hfr : v.numericType = .fractional) (hv : Number.OnGrid v.baseExponent v.assetsAvailable)
    (hc : assets.CanonicalOrZero) (hk : ∃ k : ℤ, assets.toRat = (k : ℚ) * 10 ^ v.baseExponent)
    (h : (v.adjustAssetsAndShares assets.operator_neg shares).run = .ok (.ok raw)) :
    Number.OnGrid v.baseExponent raw.assetsAvailable := by
  obtain ⟨k, hk⟩ := hk
  exact Vault.adjustAssetsAndShares_onGrid v _ _ raw hfr hv hc.operator_neg
    ⟨-k, by rw [STAmount.operator_neg_toRat, hk]; push_cast; ring⟩ h

/-- A loan transaction keeps an IOU vault on the base grid. -/
private lemma LendingLedger.applyLoan_onBaseGrid (l : LendingLedger) (hinv : l.ScaleInv) (tx : LendingTx)
    (hpre : (tx.preflight l).isTesSuccess = true) (u : LoanEffect) (hu : (l.applyLoan tx).run = .ok (.ok u))
    (hfr : l.vault.numericType = .fractional) (hv : Vault.OnBaseGrid l.vault) : Vault.OnBaseGrid u.vault := by
  have hloan : ∀ (i : Nat) (e : LoanEntry) (broker : LoanBroker) (loan : Loan), l.loan? i = some e →
      l.broker? e.brokerIndex = some broker → e.loan.withBroker broker = .ok loan →
      loan.loanScale = l.vault.baseExponent ∧ loan.broker.numericType = l.vault.numericType := by
    intro i e broker loan he hb hw
    have hraw := Loan.withBroker_eq hw
    refine ⟨?_, ?_⟩
    · rw [show loan.loanScale = loan.toRawLoan.loanScale from rfl, hraw]; exact hinv.loanScale i e he
    · rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]; exact hinv.brokers _ broker hb
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
    exact Loan.create_onBaseGrid _ _ _ _ _ _ _ _ r hfr hv hpn hpos hst (hinv.brokers i broker hb) hcr
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    exact Loan.accept_onBaseGrid _ _ _ hfr hv hr
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_delete_inv u i hu
    obtain ⟨hls, hnt⟩ := hloan i e broker loan he hb hw
    exact Loan.delete_onBaseGrid _ _ _ hfr hv hls hnt hr
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    obtain ⟨hls, hnt⟩ := hloan i e broker loan he hb hw
    show Vault.OnBaseGrid r.pool'
    cases action with
    | impair =>
      simp only [Loan.manage, Loan.manageImpair] at hr
      unfold_ter at hr
      walk_ok
      exact Loan.changeImpairment_onBaseGrid loan _ true _ hfr hv ‹_›
    | unimpair => exact Loan.changeImpairment_onBaseGrid loan _ false r hfr hv hr
    | default =>
      simp only [Loan.manage] at hr
      unfold_ter at hr
      walk_ok'
      exact Loan.manageDefault_onBaseGrid loan _ _ hfr hv hls hnt ‹_›
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    obtain ⟨hls, hnt⟩ := hloan i e broker loan he hb hw
    exact Loan.pay_onBaseGrid loan _ _ _ _ r hfr hv hls hnt hr
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- A deposit that passed its preflight deposits a canonical amount of the vault's asset. -/
private lemma LendingTx.preflight_vaultDeposit (l : LendingLedger) (h : Nat) (amount : STAmount) (isDonation : Bool)
    (hfr : l.vault.numericType = .fractional)
    (hpre : ((LendingTx.vaultDeposit h amount isDonation).preflight l).isTesSuccess = true) :
    amount.Canonical ∧ amount.mNumericType = l.vault.numericType := by
  simp only [LendingTx.preflight] at hpre
  split at hpre
  · rename_i hc
    simp only [Bool.and_eq_true, isCanonicalAmount, isPositiveAmount, hfr, NumericType.isIntegral,
      Bool.false_eq_true, if_false, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨hty, hm⟩, -, hnz⟩ := hc
    rcases hm with hm | ⟨⟨⟨hlo, hhi⟩, helo⟩, hehi⟩
    · exact absurd hm hnz
    · refine ⟨⟨fun hi => ?_, fun _ => ⟨hty, hlo, hhi, helo, hehi⟩⟩, by rw [hty, hfr]⟩
      exfalso
      unfold STAmount.integral at hi
      rw [hty] at hi
      cases hi
  · exact absurd hpre (by rw [show TER.temBAD_AMOUNT.isTesSuccess = false from rfl]; decide)

/-- A vault transaction keeps AssetsAvailable of an IOU vault on the base grid. -/
private lemma LendingLedger.applyVault_onGrid (l : LendingLedger) (tx : LendingTx)
    (hpre : (tx.preflight l).isTesSuccess = true) (u : VaultEffect) (h : (l.applyVault tx).run = .ok (.ok u))
    (hfr : l.vault.numericType = .fractional) (hv : Number.OnGrid l.vault.baseExponent l.vault.assetsAvailable) :
    Number.OnGrid l.vault.baseExponent u.vault.assetsAvailable := by
  have hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat := by
    rw [hfr]; intro h'; cases h'
  cases tx with
  | vaultDeposit hd amount isDonation =>
    obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit l hd amount isDonation hfr hpre
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      exact Vault.deposit_onGrid _ _ _ _ _ hc hty hfr hv _ ‹_›
    · cases h
  | vaultWithdraw hd amount =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals
        have hw : (l.vault.withdraw _ _ _ _).run = .ok (.ok _) := (Vault.withdraw_holder_ok _ _ _ _ _ _ _ ‹_›).1
        obtain ⟨hc, -, raw, hadj, hraw⟩ := Vault.withdraw_payout_nonneg _ _ _ _ _ hmax _ hw
        rw [show VaultWithAmounts.vault' _ = _ from rfl]
        rw [show (VaultWithAmounts.vault' _).assetsAvailable = (VaultWithAmounts.vault' _).toRawVault.assetsAvailable
          from rfl, hraw]
        exact Vault.debit_onGrid _ _ _ raw hfr hv hc (Vault.withdraw_payout_grid _ _ _ _ _ hfr hv _ hw) hadj
    · cases h
  | vaultClawback hd assets =>
    simp only [LendingLedger.applyVault] at h
    split at h
    · unfold_ter at h
      walk_ok
      all_goals
        have hw : (l.vault.clawback _ _ _ _).run = .ok (.ok _) := ‹_›
        obtain ⟨hc, -, raw, hadj, hraw⟩ := Vault.clawback_payout_nonneg _ _ _ _ _ hmax _ hw
        rw [show (VaultWithAmounts.vault' _).assetsAvailable = (VaultWithAmounts.vault' _).toRawVault.assetsAvailable
          from rfl, hraw]
        exact Vault.debit_onGrid _ _ _ raw hfr hv hc (Vault.clawback_payout_grid _ _ _ _ _ hfr _ hw) hadj
    · cases h
  | vaultBurnShares hd amount =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
    rw [(congrArg RawVault.assetsAvailable hf :)]
    exact hv
  | vaultSet m b =>
    simp only [LendingLedger.applyVault] at h
    unfold_ter at h
    walk_ok
    obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ ‹_›
    rw [(congrArg RawVault.assetsAvailable hf :)]
    exact hv
  | _ => simp only [LendingLedger.applyVault] at h; cases h

/-- What every reachable ledger keeps about the base grid: brokers and loans stay at the vault's asset and
scale, and an IOU vault keeps AssetsAvailable and AssetsDeployed whole numbers of base units. -/
structure LendingLedger.GridInv (l : LendingLedger) : Prop where
  scale : l.ScaleInv
  grid : l.vault.numericType = .fractional → Vault.OnBaseGrid l.vault

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.GridInv.step {l l' : LendingLedger} (hinv : l.GridInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.GridInv := by
  refine ⟨hinv.scale.step h, fun hfr' => ?_⟩
  have hpre := (LendingLedger.apply_checked h).1
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault] at hfr' ⊢
    have hfr : l.vault.numericType = .fractional := hk.numericType ▸ hfr'
    have hbe : u.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hk.numericType, hk.scale]
    obtain ⟨hAA, hAD⟩ := hinv.grid hfr
    unfold Vault.OnBaseGrid
    rw [hbe, hk.assetsDeployed]
    exact ⟨l.applyVault_onGrid tx hpre u hu hfr hAA, hAD⟩
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact hinv.grid hfr'
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    have hs := l.applyLoan_keepsSettings tx u hu
    have hfr : l.vault.numericType = .fractional := hs.numericType ▸ hfr'
    exact l.applyLoan_onBaseGrid hinv.scale tx hpre u hu hfr (hinv.grid hfr)
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact hinv.grid hfr'
  · -- close moves the close time forward
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact hinv.grid hfr'

/-- A new vault holds and lends nothing. -/
lemma LendingLedger.Genesis.gridInv {g : LendingLedger} (hg : g.Genesis) : g.GridInv := by
  refine ⟨hg.scaleInv, fun _ => ?_⟩
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold XRPL.Model.SingleAssetVault.Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  unfold Vault.OnBaseGrid
  rw [show g.vault.assetsAvailable = Number.zero from (congrArg RawVault.assetsAvailable hraw :),
    show g.vault.assetsDeployed = Number.zero from (congrArg RawVault.assetsDeployed hraw :)]
  exact ⟨Number.OnGrid.zero _, Number.OnGrid.zero _⟩

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.gridInv {l : LendingLedger} (hr : l.Reachable) : l.GridInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.gridInv) (fun _ _ _ hi ha => hi.step ha) hr

end XRPL.Model.Lending
