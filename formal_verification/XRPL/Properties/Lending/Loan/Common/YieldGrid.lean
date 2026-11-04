import XRPL.Properties.Lending.Loan.Common.Debt

/-! # What loan operations add to YieldUnrealized

A loan operation adds to YieldUnrealized a loan's interestDue, its negation, or the change in it, each a whole
number of LoanScale units, or leaves YieldUnrealized as it was. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- A vault update without a yield change keeps YieldUnrealized. -/
lemma Vault.poolAdjust_yield_zero (v v' : Vault) (c : PoolBalanceChange) (hc : c.yield = Number.zero)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : v'.yieldUnrealized = v.yieldUnrealized := by
  have hr := (Vault.poolAdjust_adjustSums v c v' h).yield
  rw [hc, Number.operator_add_zero_right] at hr
  exact (Except.ok.inj hr).symm

/-- The outstanding amounts of a lawful loan are whole LoanScale units. -/
lemma Loan.outstanding_onGrid (l : Loan) :
    Number.OnGrid l.loanScale l.totalValueOutstanding ∧ Number.OnGrid l.loanScale l.principalOutstanding ∧
      Number.OnGrid l.loanScale l.managementFeeOutstanding := by
  have he := Loan.exact l
  have heg := Loan.grid l
  obtain ⟨_, -, ht⟩ := UnitsAt.of_atExponent l.wf.totalValueOutstanding_norm heg.totalValueOutstanding_atExponent
  obtain ⟨_, -, hp⟩ := UnitsAt.of_atExponent l.wf.principalOutstanding_norm heg.principalOutstanding_atExponent
  obtain ⟨_, -, hm⟩ := UnitsAt.of_atExponent l.wf.managementFeeOutstanding_norm
    heg.managementFeeOutstanding_atExponent
  exact ⟨ht.onGrid, hp.onGrid, hm.onGrid⟩

/-- A lawful loan's interestDue is whole LoanScale units. -/
lemma Loan.interestDue_onGrid (l : Loan) (i : Number) (h : l.interestDue = .ok i) : Number.OnGrid l.loanScale i := by
  obtain ⟨ht, hp, hm⟩ := Loan.outstanding_onGrid l
  have hsb := Loan.loanScale_bounds l
  unfold RawLoan.interestDue at h
  obtain ⟨d, hd, h⟩ := bind_ok_peel _ _ _ h
  exact Number.OnGrid.sub (Number.OnGrid.sub ht hp hsb hd) hm hsb h

/-- A new loan adds a whole number of base units to YieldUnrealized. -/
lemma Loan.create_yieldStep (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithPool Vault)
    (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (har : ∃ n : ℕ, v.assetsReserved.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ y, Number.OnGrid v.baseExponent y ∧
      v.yieldUnrealized.operator_add y .to_nearest = .ok r.pool'.yieldUnrealized := by
  have hls := Loan.create_loanScale_proof broker v principal rates fees schedule allowsOverpayment pending r hp hpos
    hst hnt hok
  obtain ⟨-, -, hPO, -, -⟩ := Loan.create_reserved broker v principal rates fees schedule allowsOverpayment
    pending r hp hpos hst hnt har hok
  obtain ⟨props, loanState, _, principal', broker', aa', ad', lu', ar', yu', hchecks, -, hsums, hpool, hl, -⟩ :=
    Loan.create_pool_sums broker v principal rates fees schedule allowsOverpayment pending r hok
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
  -- PrincipalRequested is the stored principal, so on the grid too
  have hpr : Number.OnGrid v.baseExponent principal := by
    obtain ⟨-, k, hk⟩ := hpg
    exact ⟨hp, k, by rw [← hPO]; exact hk⟩
  have hi : Number.OnGrid v.baseExponent loanState.interestDue := by
    have hs := hchecks.state
    unfold LoanState.build at hs
    obtain ⟨d, hd, hs⟩ := bind_ok_peel _ _ _ hs
    obtain ⟨i, hi, hs⟩ := bind_ok_peel _ _ _ hs
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    subst hs
    exact Number.OnGrid.sub (Number.OnGrid.sub ht hpr hsb hd) hm hsb hi
  refine ⟨if pending then Number.zero else loanState.interestDue, ?_, ?_⟩
  · split
    · exact Number.OnGrid.zero _
    · exact hi
  · rw [show r.pool'.yieldUnrealized = r.pool'.toRawVault.yieldUnrealized from rfl, hpool]
    exact hsums.yield

/-- An accept adds a whole number of LoanScale units to YieldUnrealized. -/
lemma Loan.accept_yieldStep (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.accept v).run = .ok (.ok r)) :
    ∃ y, Number.OnGrid loan.loanScale y ∧
      v.yieldUnrealized.operator_add y .to_nearest = .ok r.pool'.yieldUnrealized := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hi := ‹loan.interestDue = Except.ok _›
  exact ⟨_, Loan.interestDue_onGrid loan _ hi,
    (Vault.poolAdjust_adjustSums v _ _ ‹AssetPool.adjustBalances v _ = Except.ok (Except.ok _)›).yield⟩

/-- Impair and unimpair keep YieldUnrealized. -/
private lemma Loan.changeImpairment_yield (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) : r.pool'.yieldUnrealized = v.yieldUnrealized := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_yield_zero v _ _ rfl ‹AssetPool.adjustBalances v _ = Except.ok (Except.ok _)›

/-- Impair keeps YieldUnrealized. -/
lemma Loan.manageImpair_yield (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) : r.pool'.yieldUnrealized = v.yieldUnrealized := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_yield loan v true r ‹_›

/-- Unimpair keeps YieldUnrealized. -/
lemma Loan.manageUnimpair_yield (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.manageUnimpair v).run = .ok (.ok r)) : r.pool'.yieldUnrealized = v.yieldUnrealized :=
  Loan.changeImpairment_yield loan v false r h

/-- A default moves YieldUnrealized by a whole number of LoanScale units. -/
lemma Loan.manageDefault_yieldStep (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    ∃ y, Number.OnGrid loan.loanScale y ∧
      v.yieldUnrealized.operator_add y .to_nearest = .ok r.pool'.yieldUnrealized := by
  obtain ⟨i, _, _, raw, _, hi, -, hadj, hraw, -, -, -, -, -⟩ := Loan.manageDefault_ok_parts loan v r h
  obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  refine ⟨i.operator_neg, (Loan.interestDue_onGrid loan i hi).neg, ?_⟩
  rw [show r.pool'.yieldUnrealized = r.pool'.toRawVault.yieldUnrealized from rfl, hraw, heq]
  exact hs.yield

/-- A delete keeps YieldUnrealized. -/
lemma Loan.delete_yield (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) : r.pool'.yieldUnrealized = v.yieldUnrealized := by
  cases hp : loan.isPending
  · rw [Loan.delete_active_vault loan v r hp h]
  · obtain ⟨principal', raw, _, -, hadj, hv', -, -⟩ := Loan.delete_pending_ok_inv loan v r hp h
    obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
    have hy := hs.yield
    rw [show (loan.deleteChange principal').yield = Number.zero from rfl, Number.operator_add_zero_right] at hy
    rw [show r.pool'.yieldUnrealized = r.pool'.toRawVault.yieldUnrealized from rfl,
      (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv').1, heq]
    exact (Except.ok.inj hy).symm

/-- A payment moves YieldUnrealized by a whole number of LoanScale units. -/
lemma Loan.pay_yieldStep (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (r : LoanWithAmounts Vault) (h : (loan.pay v pt amount now).run = .ok (.ok r)) :
    ∃ y, Number.OnGrid loan.loanScale y ∧
      v.yieldUnrealized.operator_add y .to_nearest = .ok r.pool'.yieldUnrealized := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v pt amount now r h
  obtain ⟨-, hu, hst, hsi, -⟩ := Loan.payInstalments_ok loan v pt amount now p hp
  obtain ⟨_, yd, _, _, _, raw, _, hsums, hadj, hv', -, -, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hpool := Vault.poolAdjust_ok _ _ raw r.pool' hadj hv'
  obtain ⟨i', hi', hyd⟩ := hsums.yield
  have hls : p.loan.loanScale = loan.loanScale := hst.loanScale
  have hsb := Loan.loanScale_bounds loan
  have hg1 := Loan.interestDue_onGrid p.loan i' hi'
  have hg2 := Loan.interestDue_onGrid loan _ hsi
  rw [hls] at hg1
  have hYU : p.pool.yieldUnrealized = v.yieldUnrealized := by
    cases himp : loan.isImpaired
    · rw [Loan.unimpairIfImpaired_not loan v himp] at hu
      obtain rfl : v = p.pool := by injection hu with hu; injection hu with hu; injection hu
      rfl
    · rw [Loan.unimpairIfImpaired_impaired loan v himp] at hu
      split at hu
      · cases hu
      · cases hu
      · rename_i v1 hadj1
        obtain rfl : v1 = p.pool := by injection hu with hu; injection hu with hu; injection hu
        exact Vault.poolAdjust_yield_zero v _ _ rfl hadj1
  refine ⟨yd, Number.OnGrid.sub hg1 hg2 hsb hyd, ?_⟩
  rw [← hYU]
  exact (Vault.poolAdjust_adjustSums _ _ _ hpool).yield

end XRPL.Model.Lending
