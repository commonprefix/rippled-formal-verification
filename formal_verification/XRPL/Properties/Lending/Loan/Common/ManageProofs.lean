import XRPL.Properties.Lending.Loan.Common.ManageExits

/-! # Proof bodies for the impair, unimpair and default updates

What a successful action writes to the loan, the vault and the broker. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private scale_room from XRPL.Properties.Lending.Loan.LoanValid

/-- A successful impair: the loan was late, the vault update wrote the record the pool holds,
and the loan is the flagged one. -/
lemma Loan.manageImpair_ok_parts (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (hok : (loan.manageImpair v now).run = .ok (.ok r)) :
    loan.nextPaymentDueDate < now ∧ ∃ raw, (v.adjustBalances { loss := loan.principalOutstanding }).run =
      .ok (.ok raw) ∧ r.pool'.toRawVault = raw ∧ r.loan'.toRawLoan = { loan.toRawLoan with isImpaired := true } := by
  by_cases hlate : loan.nextPaymentDueDate < now
  · rw [Loan.manageImpair_run loan v now hlate] at hok
    refine ⟨hlate, ?_⟩
    split at hok
    · simp at hok
    · simp at hok
    · rename_i v' hpool
      split at hok
      · simp at hok
      · rename_i loan' hl
        simp only [Except.ok.injEq] at hok
        subst hok
        obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v _ _ hpool
        exact ⟨raw, hadj, (RawVault.to_lawful_ok hv').1, (RawLoan.to_lawful_ok hl).1⟩
  · rw [Loan.manageImpair_not_late_proof loan v now (by simpa using hlate)] at hok
    exact absurd hok (by simp)

/-- A successful unimpair: the vault update wrote the record the pool holds, and the loan is the
cleared one. -/
private lemma Loan.manageUnimpair_ok_parts (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (hok : (loan.manageUnimpair v).run = .ok (.ok r)) :
    ∃ raw, (v.adjustBalances { loss := loan.principalOutstanding.operator_neg }).run = .ok (.ok raw) ∧
      r.pool'.toRawVault = raw ∧ r.loan'.toRawLoan = { loan.toRawLoan with isImpaired := false } := by
  rw [Loan.manageUnimpair_run loan v] at hok
  split at hok
  · simp at hok
  · simp at hok
  · rename_i v' hpool
    split at hok
    · simp at hok
    · rename_i loan' hl
      simp only [Except.ok.injEq] at hok
      subst hok
      obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v _ _ hpool
      exact ⟨raw, hadj, (RawVault.to_lawful_ok hv').1, (RawLoan.to_lawful_ok hl).1⟩

/-- A successful default: the interest and the cover computed, the vault update wrote the record the pool holds,
DebtTotal dropped by the principal and CoverAvailable by the cover, and the loan is the closed one. -/
lemma Loan.manageDefault_ok_parts (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r)) :
    ∃ (interestDue debtTotal' coverAvailable' : Number) (raw : RawVault) (broker' : LoanBroker),
      loan.interestDue = .ok interestDue ∧ loan.defaultCover v = .ok r.amountToPool ∧
      (v.adjustBalances (loan.defaultChange interestDue r.amountToPool)).run = .ok (.ok raw) ∧
      r.pool'.toRawVault = raw ∧
      loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok debtTotal' ∧
      loan.broker.coverAvailable.operator_sub r.amountToPool .to_nearest = .ok coverAvailable' ∧
      broker'.toRawLoanBroker = loan.defaultedBroker debtTotal' coverAvailable' ∧
      r.loan'.toRawLoan = loan.defaultedLoan broker' ∧ r.amountToBroker = Number.zero := by
  rw [Loan.manageDefault_run loan v] at hok
  split at hok
  · simp at hok
  rename_i interestDue hi
  split at hok
  · simp at hok
  rename_i dc hdc
  split at hok
  · simp at hok
  · simp at hok
  rename_i v' hpool
  split at hok
  · simp at hok
  rename_i debtTotal' hdebt
  split at hok
  · simp at hok
  rename_i coverAvailable' hcover
  split at hok
  · simp at hok
  rename_i broker' hbroker
  split at hok
  · simp at hok
  rename_i loan' hl
  simp only [Except.ok.injEq] at hok
  subst hok
  obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v _ _ hpool
  exact ⟨_, _, _, raw, broker', hi, hdc, hadj, (RawVault.to_lawful_ok hv').1, hdebt, hcover,
    (RawLoanBroker.to_lawful_ok hbroker).1, (RawLoan.to_lawful_ok hl).1, rfl⟩

/-- A successful default wrote its five new balances into the vault record. -/
lemma Loan.manageDefault_vault_record (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r)) :
    r.pool'.toRawVault = { v.toRawVault with
      assetsAvailable := r.pool'.assetsAvailable
      assetsDeployed := r.pool'.assetsDeployed
      assetsReserved := r.pool'.assetsReserved
      lossUnrealized := r.pool'.lossUnrealized
      yieldUnrealized := r.pool'.yieldUnrealized } := by
  obtain ⟨_, _, _, raw, _, -, -, hadj, hpool, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  obtain ⟨_, _, _, _, _, -, -, -, hraw⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  rw [hpool, hraw]

/-- A successful vault update writes LossUnrealized plus its change. -/
private lemma loss_of_update (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (hadj : (v.adjustBalances c).run = .ok (.ok raw)) :
    v.lossUnrealized.operator_add c.loss .to_nearest = .ok raw.lossUnrealized := by
  obtain ⟨_, _, _, _, _, hs, -, -, rfl⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  exact hs.loss

/-- An update that only moves LossUnrealized leaves every other field as it is, when AssetsAvailable
fits the asset. -/
private lemma loss_only_record (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (hc : c.cash = Number.zero) (hd : c.deployed = Number.zero) (hr : c.reserved = Number.zero)
    (hy : c.yield = Number.zero) (haa : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hadj : (v.adjustBalances c).run = .ok (.ok raw)) :
    raw = { v.toRawVault with lossUnrealized := raw.lossUnrealized } := by
  obtain ⟨aa', ad', lu', ar', yu', hs, -, -, rfl⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  have hd' := hs.deployed
  have hy' := hs.yield
  have hr' := hs.reserved
  rw [hd] at hd'
  rw [hy] at hy'
  rw [hr] at hr'
  obtain ⟨aa, h1, h2⟩ := hs.cash
  rw [hc] at h1
  rw [Number.eq_of_add_zero h1] at h2
  have haa' : aa' = v.assetsAvailable :=
    Number.isNormalized.toRat_inj (STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2) v.wf.assetsAvailable_norm
      (STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm haa h2)
  rw [Number.eq_of_add_zero hd', Number.eq_of_add_zero hy', Number.eq_of_add_zero hr', haa']

/-- A successful default wrote the five new balances of its change into the vault the pool holds. -/
lemma Loan.manageDefault_sums (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r)) :
    ∃ interestDue, loan.interestDue = .ok interestDue ∧
      Vault.AdjustSums v (loan.defaultChange interestDue r.amountToPool) r.pool'.assetsAvailable
        r.pool'.assetsDeployed r.pool'.lossUnrealized r.pool'.assetsReserved r.pool'.yieldUnrealized := by
  obtain ⟨i, _, _, raw, _, hi, -, hadj, hpool, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  obtain ⟨_, _, _, _, _, hs, -, -, hraw⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  refine ⟨i, hi, ?_⟩
  rw [hpool.trans hraw]
  exact hs

/-- A successful default lowers DebtTotal by the principal and CoverAvailable by the cover. -/
private lemma default_broker (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r)) :
    loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok r.loan'.broker.debtTotal ∧
      loan.broker.coverAvailable.operator_sub r.amountToPool .to_nearest = .ok r.loan'.broker.coverAvailable := by
  obtain ⟨_, d, c, _, b, -, -, -, -, hd, hc, hb, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  have hbr : r.loan'.broker = b := by
    rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]; rfl
  rw [hbr, show b.debtTotal = b.toRawLoanBroker.debtTotal from rfl,
    show b.coverAvailable = b.toRawLoanBroker.coverAvailable from rfl, hb]
  exact ⟨hd, hc⟩

variable (loan : Loan) (v : Vault) (now : UInt32)

/-- An impair changes only LossUnrealized in the vault, when AssetsAvailable fits the asset. -/
lemma Loan.manageImpair_record (r : LoanWithPool Vault) (hok : (loan.manageImpair v now).run = .ok (.ok r))
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    r.pool'.toRawVault = { v.toRawVault with lossUnrealized := r.pool'.lossUnrealized } ∧
      v.lossUnrealized.operator_add loan.principalOutstanding .to_nearest = .ok r.pool'.lossUnrealized := by
  obtain ⟨-, raw, hadj, hpool, -⟩ := Loan.manageImpair_ok_parts loan v now r hok
  have hl := loss_of_update v _ raw hadj
  have hraw := loss_only_record v _ raw rfl rfl rfl rfl haa hadj
  rw [← hpool] at hl hraw
  exact ⟨hraw, hl⟩

/-- The impair step of the loan and LossUnrealized part of `Lending.impair_updates`. -/
lemma Loan.manageImpair_loss_proof (r : LoanWithPool Vault) (hok : (loan.manageImpair v now).run = .ok (.ok r))
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = v.lossUnrealized.toRat + loan.principalOutstanding.toRat) :
    r.loan'.toRawLoan = { loan.toRawLoan with isImpaired := true } ∧
      r.pool'.lossUnrealized.toRat = v.lossUnrealized.toRat + loan.principalOutstanding.toRat ∧
      r.pool'.toRawVault = { v.toRawVault with lossUnrealized := r.pool'.lossUnrealized } := by
  obtain ⟨-, raw, hadj, hpool, hloan⟩ := Loan.manageImpair_ok_parts loan v now r hok
  have hl := loss_of_update v _ raw hadj
  have hraw := loss_only_record v _ raw rfl rfl rfl rfl haa hadj
  rw [← hpool] at hl hraw
  exact ⟨hloan, Number.operator_add_exact_of_fits v.wf.lossUnrealized_norm loan.wf.principalOutstanding_norm hl
    hexact, hraw⟩

/-- Proof body of `manageUnimpair_loss`. -/
lemma Loan.manageUnimpair_loss_proof (r : LoanWithPool Vault) (hok : (loan.manageUnimpair v).run = .ok (.ok r))
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = v.lossUnrealized.toRat - loan.principalOutstanding.toRat) :
    r.loan'.toRawLoan = { loan.toRawLoan with isImpaired := false } ∧
      r.pool'.lossUnrealized.toRat = v.lossUnrealized.toRat - loan.principalOutstanding.toRat ∧
      r.pool'.toRawVault = { v.toRawVault with lossUnrealized := r.pool'.lossUnrealized } := by
  obtain ⟨raw, hadj, hpool, hloan⟩ := Loan.manageUnimpair_ok_parts loan v r hok
  have hl := loss_of_update v _ raw hadj
  have hraw := loss_only_record v _ raw rfl rfl rfl rfl haa hadj
  rw [← hpool] at hl hraw
  exact ⟨hloan, Number.operator_sub_exact_of_fits v.wf.lossUnrealized_norm loan.wf.principalOutstanding_norm hl
    hexact, hraw⟩

/-- A default leaves SharesTotal as it is. -/
lemma Loan.manageDefault_sharesTotal (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r)) :
    r.pool'.sharesTotal = v.sharesTotal := by
  obtain ⟨_, _, _, raw, _, -, -, hadj, hpool, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  obtain ⟨_, _, _, _, _, -, -, -, hraw⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  rw [show r.pool'.sharesTotal = r.pool'.toRawVault.sharesTotal from rfl, hpool, hraw]

/-- The default step of the loan part of `Lending.default_updates`. -/
lemma Loan.manageDefault_closes_proof (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r)) :
    r.loan'.principalOutstanding = Number.zero ∧ r.loan'.totalValueOutstanding = Number.zero ∧
      r.loan'.managementFeeOutstanding = Number.zero ∧ r.loan'.paymentRemaining = 0 ∧
      r.loan'.nextPaymentDueDate = 0 ∧ r.loan'.isDefault = true := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  have h : ∀ f : RawLoan → Prop, f (loan.defaultedLoan _) → f r.loan'.toRawLoan := fun f hf => by rw [hloan]; exact hf
  exact ⟨h (·.principalOutstanding = Number.zero) rfl, h (·.totalValueOutstanding = Number.zero) rfl,
    h (·.managementFeeOutstanding = Number.zero) rfl, h (·.paymentRemaining = 0) rfl,
    h (·.nextPaymentDueDate = 0) rfl, h (·.isDefault = true) rfl⟩

/-- A default -> YieldUnrealized' = YieldUnrealized − interestDue. -/
lemma Loan.manageDefault_yield_proof (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = v.yieldUnrealized.toRat - loan.toExact.interestDue) :
    r.pool'.yieldUnrealized.toRat = v.yieldUnrealized.toRat - loan.toExact.interestDue := by
  obtain ⟨i, _, _, raw, _, hi, -, hadj, hpool, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  obtain ⟨_, _, _, _, yu', hs, -, -, hraw⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  have hiv := Loan.interestDue_toExact loan i hi
  have hin := RawLoan.interestDue_isNormalized loan i hi
  have hy : r.pool'.yieldUnrealized = yu' := by rw [show r.pool'.yieldUnrealized = r.pool'.toRawVault.yieldUnrealized
    from rfl, hpool, hraw]
  rw [hy]
  rw [← hiv] at hexact ⊢
  exact Number.operator_sub_exact_of_fits v.wf.yieldUnrealized_norm hin hs.yield hexact

/-- Defaulting an impaired loan -> LossUnrealized' = LossUnrealized − PrincipalOutstanding. -/
lemma Loan.manageDefault_loss_proof (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r))
    (himp : loan.isImpaired = true)
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = v.lossUnrealized.toRat - loan.principalOutstanding.toRat) :
    r.pool'.lossUnrealized.toRat = v.lossUnrealized.toRat - loan.principalOutstanding.toRat := by
  obtain ⟨i, -, hs⟩ := Loan.manageDefault_sums loan v r hok
  have hl := hs.loss
  simp only [Loan.defaultChange, himp, ↓reduceIte] at hl
  exact Number.operator_sub_exact_of_fits v.wf.lossUnrealized_norm loan.wf.principalOutstanding_norm hl hexact

/-- Proof body of `manageDefault_coverAvailable`. -/
lemma Loan.manageDefault_coverAvailable_proof (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hexact : ∃ w : Number, w.isNormalized ∧ w.toRat = loan.broker.coverAvailable.toRat - r.amountToPool.toRat) :
    r.loan'.broker.coverAvailable.toRat = loan.broker.coverAvailable.toRat - r.amountToPool.toRat := by
  obtain ⟨-, hc⟩ := default_broker loan v r hok
  obtain ⟨_, _, _, _, _, -, hdc, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  have hdn := Loan.defaultCover_isNormalized loan v _ hdc
  exact Number.operator_sub_exact_of_fits loan.broker.wf.coverAvailable_norm hdn hc hexact

/-- A default -> AssetsDeployed and DebtTotal each drop by PrincipalOutstanding. -/
lemma Loan.manageDefault_principal_proof (r : LoanWithAmounts Vault) (hok : (loan.manageDefault v).run = .ok (.ok r))
    (hdeployed : ∃ w : Number, w.isNormalized ∧
      w.toRat = v.assetsDeployed.toRat - loan.principalOutstanding.toRat)
    (hdebt : ∃ w : Number, w.isNormalized ∧
      w.toRat = loan.broker.debtTotal.toRat - loan.principalOutstanding.toRat) :
    v.assetsDeployed.toRat - r.pool'.assetsDeployed.toRat = loan.principalOutstanding.toRat ∧
      loan.broker.debtTotal.toRat - r.loan'.broker.debtTotal.toRat = loan.principalOutstanding.toRat := by
  obtain ⟨hd, -⟩ := default_broker loan v r hok
  obtain ⟨_, -, hs⟩ := Loan.manageDefault_sums loan v r hok
  have h1 := Number.operator_sub_exact_of_fits v.wf.assetsDeployed_norm loan.wf.principalOutstanding_norm
    hs.deployed hdeployed
  have h2 := Number.operator_sub_exact_of_fits loan.broker.wf.debtTotal_norm loan.wf.principalOutstanding_norm hd hdebt
  constructor <;> linarith

end XRPL.Model.Lending
