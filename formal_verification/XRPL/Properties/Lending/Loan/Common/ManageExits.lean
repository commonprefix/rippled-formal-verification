import XRPL.Properties.Lending.Loan.Common.ManageDefs

/-! # Proof bodies for the impair, unimpair and default exits

One proof per exit, in the order each action runs its checks. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The new AssetsAvailable of an update that moves no cash is the old one rounded to the asset, and
it is never negative. -/
private lemma cash_zero_nonneg (v : Vault) (c : PoolBalanceChange) (aa' ad' lu' ar' yu' : Number)
    (hc : c.cash = Number.zero) (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu') :
    STAmount.roundToNumericType v.numericType v.assetsAvailable .to_nearest = .ok aa' ∧ 0 ≤ aa'.signum := by
  obtain ⟨aa, h1, h2⟩ := hs.cash
  rw [hc] at h1
  rw [Number.eq_of_add_zero h1] at h2
  refine ⟨h2, Number.signum_nonneg_of_toRat aa' (STAmount.roundToNumericType_isNormalized _ _ _ _ _ h2) ?_⟩
  exact STAmount.roundToNumericType_nonneg _ _ _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg h2

/-- The new balances of an impair are never negative. -/
private lemma impair_sums_nonneg (loan : Loan) (v : Vault) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v { loss := loan.principalOutstanding } aa' ad' lu' ar' yu') :
    0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum := by
  have hd := Number.eq_of_add_zero hs.deployed
  have hy := Number.eq_of_add_zero hs.yield
  have hr := Number.eq_of_add_zero hs.reserved
  subst hd hy hr
  have hl := hs.loss
  have hln := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.lossUnrealized_norm
    loan.wf.principalOutstanding_norm hl
  refine ⟨(cash_zero_nonneg v _ _ _ _ _ _ rfl hs).2, ?_, ?_, ?_, ?_⟩
  · exact Number.signum_nonneg_of_toRat _ v.wf.assetsDeployed_norm v.exact.assetsDeployed_nonneg
  · exact Number.signum_nonneg_of_toRat _ hln (operator_add_nonneg _ _ _ v.wf.lossUnrealized_norm
      loan.wf.principalOutstanding_norm hl (add_nonneg v.exact.lossUnrealized_nonneg
        loan.exact.principalOutstanding_nonneg))
  · exact Number.signum_nonneg_of_toRat _ v.wf.yieldUnrealized_norm v.exact.yieldUnrealized_nonneg
  · exact Number.signum_nonneg_of_toRat _ v.wf.assetsReserved_norm v.exact.assetsReserved_nonneg

/-- A normalized value with a sign that is not negative is not below zero. -/
private lemma toRat_nonneg_of_signum (n : Number) (hn : n.isNormalized) (h : 0 ≤ n.signum) : 0 ≤ n.toRat := by
  by_contra hlt
  push Not at hlt
  rw [signum_eq n hn, if_neg (by linarith), if_pos hlt] at h
  omega

/-- An update that only moves LossUnrealized leaves a lawful vault once it succeeds. -/
private lemma loss_only_lawful (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (hc : c.cash = Number.zero) (hd : c.deployed = Number.zero) (hr : c.reserved = Number.zero)
    (hy : c.yield = Number.zero) (hl : c.loss.isNormalized)
    (hadj : (v.adjustBalances c).run = .ok (.ok raw)) :
    ∃ v', raw.to_lawful = .ok v' ∧ v'.toRawVault = raw := by
  obtain ⟨aa', ad', lu', ar', yu', hs, hnn, hle, rfl⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
  have hd' := hs.deployed
  have hy' := hs.yield
  have hr' := hs.reserved
  rw [hd] at hd'
  rw [hy] at hy'
  rw [hr] at hr'
  have hd'' := Number.eq_of_add_zero hd'
  have hy'' := Number.eq_of_add_zero hy'
  have hr'' := Number.eq_of_add_zero hr'
  subst hd'' hy'' hr''
  obtain ⟨hcash, -⟩ := cash_zero_nonneg v _ _ _ _ _ _ hc hs
  have han := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hcash
  have hln := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.lossUnrealized_norm hl hs.loss
  have hlu : lu'.toRat ≤ v.assetsDeployed.toRat :=
    (operator_lt_eq_false_iff _ _ v.wf.assetsDeployed_norm hln).mp hle
  refine Vault.balances_lawful v _ _ _ _ _ ⟨han, v.wf.assetsDeployed_norm, v.wf.assetsReserved_norm, hln,
    v.wf.yieldUnrealized_norm⟩ ⟨toRat_nonneg_of_signum _ han hnn.1, v.exact.assetsDeployed_nonneg,
    v.exact.assetsReserved_nonneg, toRat_nonneg_of_signum _ hln hnn.2.2.1, v.exact.yieldUnrealized_nonneg⟩
    hlu v.exact.assetsReserved_le v.valid.assetsDeployed_representable (Vault.round_cash_valid v _ hcash).1
    (Vault.round_cash_valid v _ hcash).2 ?_
  intro hst
  obtain ⟨h0, hd0⟩ := v.valid.empty_shares hst
  rw [h0, STAmount.roundToNumericType_zero_to_nearest] at hcash
  rw [← Except.ok.inj hcash, hd0, Number.toRat_zero]
  exact ⟨rfl, rfl⟩

/-- The new LossUnrealized of an unimpair never passes AssetsDeployed. -/
private lemma unimpair_loss_not_gt (loan : Loan) (v : Vault) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v { loss := loan.principalOutstanding.operator_neg } aa' ad' lu' ar' yu') :
    lu'.operator_gt ad' = false := by
  have hd := Number.eq_of_add_zero hs.deployed
  subst hd
  have hpn := Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm
  have hln := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.lossUnrealized_norm hpn hs.loss
  have hle : lu'.toRat ≤ v.lossUnrealized.toRat :=
    operator_add_le_of_le_normalized _ _ _ _ v.wf.lossUnrealized_norm hpn hs.loss v.wf.lossUnrealized_norm (by
      have : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
      rw [Number.toRat_neg]; linarith)
  unfold Number.operator_gt
  exact (operator_lt_eq_false_iff _ _ v.wf.assetsDeployed_norm hln).mpr (hle.trans v.exact.lossUnrealized_le)

variable (loan : Loan) (v : Vault) (now : UInt32)

/-- Proof body of the impair not-late exit of `Loan.manage_exits`. -/
lemma Loan.manageImpair_not_late_proof (hsoon : now ≤ loan.nextPaymentDueDate) :
    (loan.manageImpair v now).run = .ok (.error .tecTOO_SOON) := by
  have h : loan.isPaymentLate now = false := by
    unfold Loan.isPaymentLate; exact decide_eq_false (UInt32.not_lt.mpr hsoon)
  simp only [Loan.manageImpair]
  unfold_ter
  simp [h]

/-- Proof body of the impair limit exit of `Loan.manage_exits`. -/
lemma Loan.manageImpair_limit_exceeded_proof (aa' ad' lu' ar' yu' : Number)
    (hlate : loan.nextPaymentDueDate < now)
    (hs : Vault.AdjustSums v { loss := loan.principalOutstanding } aa' ad' lu' ar' yu')
    (hgt : lu'.operator_gt ad' = true) :
    (loan.manageImpair v now).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  rw [Loan.manageImpair_run loan v now hlate, Vault.poolAdjust_rejected v _ _
    (Vault.adjustBalances_limit_exceeded v _ _ _ _ _ _ hs (impair_sums_nonneg loan v _ _ _ _ _ hs) hgt)]

/-- Proof body of the impair success exit of `Loan.manage_exits`. -/
lemma Loan.manageImpair_success_proof (raw : RawVault)
    (hlate : loan.nextPaymentDueDate < now)
    (hadj : (v.adjustBalances { loss := loan.principalOutstanding }).run = .ok (.ok raw)) :
    ∃ v' loan', (loan.manageImpair v now).run = .ok (.ok { loan' := loan', pool' := v' }) ∧
      v'.toRawVault = raw ∧ loan'.toRawLoan = { loan.toRawLoan with isImpaired := true } := by
  obtain ⟨v', hv', hv'eq⟩ := loss_only_lawful v _ raw rfl rfl rfl rfl loan.wf.principalOutstanding_norm hadj
  obtain ⟨loan', hl, hleq⟩ := Loan.withImpaired_lawful loan true
  refine ⟨v', loan', ?_, hv'eq, hleq⟩
  rw [Loan.manageImpair_run loan v now hlate, Vault.poolAdjust_ok v _ raw v' hadj hv']
  rw [show (loan.withImpaired true).to_lawful = .ok loan' from hl]

/-- Proof body of the impair line of `manage_error_codes`. -/
lemma Loan.manageImpair_error_codes_proof (ter : TER) (hok : (loan.manageImpair v now).run = .ok (.error ter)) :
    ter = .tecTOO_SOON ∨ ter = .tecLIMIT_EXCEEDED := by
  by_cases hlate : loan.nextPaymentDueDate < now
  · rw [Loan.manageImpair_run loan v now hlate] at hok
    split at hok
    · exact absurd hok (by simp)
    · rename_i ter' hpool
      have hter : ter' = ter := by simpa using hok
      subst hter
      obtain ⟨aa', ad', lu', ar', yu', hs, h⟩ :=
        Vault.adjustBalances_rejected_parts v _ _ (Vault.poolAdjust_rejected_parts v _ _ hpool)
      rcases h with ⟨-, hneg⟩ | ⟨rfl, -⟩
      · have := impair_sums_nonneg loan v _ _ _ _ _ hs
        omega
      · exact Or.inr rfl
    · split at hok <;> simp at hok
  · rw [Loan.manageImpair_not_late_proof loan v now (by simpa using hlate)] at hok
    exact Or.inl (by simpa using hok.symm)

/-- Proof body of the unimpair bad-ledger exit of `Loan.manage_exits`. -/
lemma Loan.manageUnimpair_bad_ledger_proof (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v { loss := loan.principalOutstanding.operator_neg } aa' ad' lu' ar' yu')
    (hneg : lu'.signum < 0) :
    (loan.manageUnimpair v).run = .ok (.error .tefBAD_LEDGER) := by
  rw [Loan.manageUnimpair_run loan v, Vault.poolAdjust_rejected v _ _
    (Vault.adjustBalances_bad_ledger v _ _ _ _ _ _ hs (Or.inr (Or.inr (Or.inl hneg))))]

/-- Proof body of the unimpair success exit of `Loan.manage_exits`. -/
lemma Loan.manageUnimpair_success_proof (raw : RawVault)
    (hadj : (v.adjustBalances { loss := loan.principalOutstanding.operator_neg }).run = .ok (.ok raw)) :
    ∃ v' loan', (loan.manageUnimpair v).run = .ok (.ok { loan' := loan', pool' := v' }) ∧
      v'.toRawVault = raw ∧ loan'.toRawLoan = { loan.toRawLoan with isImpaired := false } := by
  obtain ⟨v', hv', hv'eq⟩ := loss_only_lawful v _ raw rfl rfl rfl rfl
    (Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm) hadj
  obtain ⟨loan', hl, hleq⟩ := Loan.withImpaired_lawful loan false
  refine ⟨v', loan', ?_, hv'eq, hleq⟩
  rw [Loan.manageUnimpair_run loan v, Vault.poolAdjust_ok v _ raw v' hadj hv']
  rw [show (loan.withImpaired false).to_lawful = .ok loan' from hl]

/-- Proof body of the unimpair line of `manage_error_codes`. -/
lemma Loan.manageUnimpair_error_codes_proof (ter : TER) (hok : (loan.manageUnimpair v).run = .ok (.error ter)) :
    ter = .tefBAD_LEDGER := by
  rw [Loan.manageUnimpair_run loan v] at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i ter' hpool
    have hter : ter' = ter := by simpa using hok
    subst hter
    obtain ⟨aa', ad', lu', ar', yu', hs, h⟩ :=
      Vault.adjustBalances_rejected_parts v _ _ (Vault.poolAdjust_rejected_parts v _ _ hpool)
    rcases h with ⟨rfl, -⟩ | ⟨-, hgt⟩
    · rfl
    · exact absurd hgt (by rw [unimpair_loss_not_gt loan v _ _ _ _ _ hs]; decide)
  · split at hok <;> simp at hok

/-- A default whose vault update is rejected is rejected with the same code. -/
private lemma default_rejected (interestDue dc : Number) (ter : TER)
    (hi : loan.interestDue = .ok interestDue) (hdc : loan.defaultCover v = .ok dc)
    (h : (v.adjustBalances (loan.defaultChange interestDue dc)).run = .ok (.error ter)) :
    (loan.manageDefault v).run = .ok (.error ter) := by
  rw [Loan.manageDefault_run loan v, hi]
  simp only
  rw [hdc]
  simp only
  rw [Vault.poolAdjust_rejected v _ _ h]

/-- Proof body of the impaired default bad-ledger exit of `Loan.manage_exits`. -/
lemma Loan.manageDefault_impaired_bad_ledger_proof (interestDue dc aa' ad' lu' ar' yu' : Number)
    (hi : loan.interestDue = .ok interestDue) (hdc : loan.defaultCover v = .ok dc)
    (himp : loan.isImpaired = true)
    (hs : Vault.AdjustSums v
      { cash := dc
        deployed := loan.principalOutstanding.operator_neg
        yield := interestDue.operator_neg
        loss := loan.principalOutstanding.operator_neg } aa' ad' lu' ar' yu')
    (hneg : lu'.signum < 0) :
    (loan.manageDefault v).run = .ok (.error .tefBAD_LEDGER) := by
  have hc : loan.defaultChange interestDue dc =
      { cash := dc
        deployed := loan.principalOutstanding.operator_neg
        yield := interestDue.operator_neg
        loss := loan.principalOutstanding.operator_neg } := by
    simp [Loan.defaultChange, himp]
  rw [← hc] at hs
  exact default_rejected loan v _ _ _ hi hdc
    (Vault.adjustBalances_bad_ledger v _ _ _ _ _ _ hs (Or.inr (Or.inr (Or.inl hneg))))

/-- Proof body of the default AssetsDeployed bad-ledger exit of `Loan.manage_exits`. -/
lemma Loan.manageDefault_deployed_bad_ledger_proof (interestDue dc aa' ad' lu' ar' yu' : Number)
    (hi : loan.interestDue = .ok interestDue) (hdc : loan.defaultCover v = .ok dc)
    (hs : Vault.AdjustSums v (loan.defaultChange interestDue dc) aa' ad' lu' ar' yu')
    (hneg : ad'.signum < 0) :
    (loan.manageDefault v).run = .ok (.error .tefBAD_LEDGER) :=
  default_rejected loan v _ _ _ hi hdc (Vault.adjustBalances_bad_ledger v _ _ _ _ _ _ hs (Or.inr (Or.inl hneg)))

/-- Proof body of the default YieldUnrealized bad-ledger exit of `Loan.manage_exits`. -/
lemma Loan.manageDefault_yield_bad_ledger_proof (interestDue dc aa' ad' lu' ar' yu' : Number)
    (hi : loan.interestDue = .ok interestDue) (hdc : loan.defaultCover v = .ok dc)
    (hs : Vault.AdjustSums v (loan.defaultChange interestDue dc) aa' ad' lu' ar' yu')
    (hneg : yu'.signum < 0) :
    (loan.manageDefault v).run = .ok (.error .tefBAD_LEDGER) :=
  default_rejected loan v _ _ _ hi hdc
    (Vault.adjustBalances_bad_ledger v _ _ _ _ _ _ hs (Or.inr (Or.inr (Or.inr (Or.inl hneg)))))

/-- Proof body of the default limit exit of `Loan.manage_exits`. -/
lemma Loan.manageDefault_limit_exceeded_proof (interestDue dc aa' ad' lu' ar' yu' : Number)
    (hi : loan.interestDue = .ok interestDue) (hdc : loan.defaultCover v = .ok dc)
    (himp : loan.isImpaired = false)
    (hs : Vault.AdjustSums v
      { cash := dc
        deployed := loan.principalOutstanding.operator_neg
        yield := interestDue.operator_neg } aa' ad' lu' ar' yu')
    (hnn : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum)
    (hgt : lu'.operator_gt ad' = true) :
    (loan.manageDefault v).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  have hc : loan.defaultChange interestDue dc =
      { cash := dc
        deployed := loan.principalOutstanding.operator_neg
        yield := interestDue.operator_neg } := by
    simp [Loan.defaultChange, himp]
  rw [← hc] at hs
  exact default_rejected loan v _ _ _ hi hdc (Vault.adjustBalances_limit_exceeded v _ _ _ _ _ _ hs hnn hgt)

/-- Proof body of the default success exit of `Loan.manage_exits`. -/
lemma Loan.manageDefault_success_proof (interestDue dc debtTotal' coverAvailable' : Number) (raw : RawVault)
    (v' : Vault) (broker' : LoanBroker)
    (hi : loan.interestDue = .ok interestDue) (hdc : loan.defaultCover v = .ok dc)
    (hadj : (v.adjustBalances (loan.defaultChange interestDue dc)).run = .ok (.ok raw))
    (hv' : raw.to_lawful = .ok v')
    (hdebt : loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok debtTotal')
    (hcover : loan.broker.coverAvailable.operator_sub dc .to_nearest = .ok coverAvailable')
    (hbroker : (loan.defaultedBroker debtTotal' coverAvailable').to_lawful = .ok broker') :
    ∃ loan', (loan.manageDefault v).run =
        .ok (.ok { loan' := loan', pool' := v', amountToPool := dc, amountToBroker := Number.zero }) ∧
      loan'.toRawLoan = loan.defaultedLoan broker' := by
  obtain ⟨loan', hl, hleq⟩ := Loan.defaultedLoan_lawful loan broker'
  refine ⟨loan', ?_, hleq⟩
  rw [Loan.manageDefault_run loan v, hi]
  simp only
  rw [hdc]
  simp only
  rw [Vault.poolAdjust_ok v _ raw v' hadj hv']
  simp only
  rw [hdebt]
  simp only
  rw [hcover]
  simp only
  rw [hbroker]
  simp only
  rw [hl]

/-- Proof body of the default line of `manage_error_codes`. -/
lemma Loan.manageDefault_error_codes_proof (ter : TER) (hok : (loan.manageDefault v).run = .ok (.error ter)) :
    ter = .tefBAD_LEDGER ∨ ter = .tecLIMIT_EXCEEDED := by
  rw [Loan.manageDefault_run loan v] at hok
  walk_ok
  obtain ⟨_, _, _, _, _, -, h⟩ :=
    Vault.adjustBalances_rejected_parts v _ _ (Vault.poolAdjust_rejected_parts v _ _ ‹_›)
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

end XRPL.Model.Lending
