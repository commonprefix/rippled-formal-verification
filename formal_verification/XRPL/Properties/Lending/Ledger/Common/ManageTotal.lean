import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Ledger.Common.ClosedLoans
import XRPL.Properties.Lending.Ledger.Common.LossInv
import XRPL.Properties.Lending.Ledger.Common.YieldGridInv
import XRPL.Properties.Lending.Loan.Common.DefaultTotal

/-! # Management actions on a reachable ledger

A stored loan has a stored broker of the vault's asset, so it takes the ledger's copy of its broker. The
asset stores AssetsAvailable exactly, and LossUnrealized is the sum of the impaired loans' principal. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A management action that passes its checks and succeeds on the stored loan writes its result. -/
private lemma LendingLedger.apply_manage_ok (l : LendingLedger) (hnd : l.vaultDeleted = false) (i : Nat) (e : LoanEntry)
    (b : LoanBroker) (loan : Loan) (action : LoanManageAction) (r : LoanWithPool Vault)
    (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b) (hw : e.loan.withBroker b = .ok loan)
    (hc : loan.canManage action l.now = .tesSUCCESS) (hr : (loan.manage action l.vault l.now).run = .ok (.ok r)) :
    (l.apply (.loanManage i action)).run = .ok (.ok (l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool'))) := by
  rw [LendingLedger.apply_of_preflight rfl]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan, he, hb, hw]
  unfold_ter
  simp only [ExceptT.run] at hr
  rw [hc, show TER.tesSUCCESS.isTesSuccess = true from rfl]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr]
  rfl

/-- The management checks read the loan only, never its broker. -/
private lemma Loan.canManage_withBroker {loan loan' : Loan} {b : LoanBroker} (hw : loan.withBroker b = .ok loan')
    (action : LoanManageAction) (now : UInt32) : loan'.canManage action now = loan.canManage action now := by
  have hraw := Loan.withBroker_eq hw
  unfold Loan.canManage
  rw [hraw]

/-- A stored loan takes the ledger's copy of its broker. -/
private lemma LendingLedger.Reachable.loan_withBroker {l : LendingLedger} (hr : l.Reachable) {i : Nat} {e : LoanEntry}
    (he : l.loan? i = some e) :
    ∃ b loan, l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
      loan.toRawLoan = { e.loan.toRawLoan with broker := b } := by
  obtain ⟨b, hb⟩ := hr.loanCountInv.broker_of_loan he
  have hs := hr.scaleInv
  obtain ⟨loan, hw⟩ := Loan.withBroker_ok e.loan b (by rw [hs.brokers _ b hb, hs.loanBroker i e he])
  exact ⟨b, loan, hb, hw, Loan.withBroker_eq hw⟩

/-- A slot adds its principal to exactly one of the sums for `p` and for not `p`. -/
private lemma principalIf_add_not (p : Loan → Bool) (o : Option LoanEntry) :
    LoanEntry.principalIf p o + LoanEntry.principalIf (fun x => !p x) o = LoanEntry.principalIf (fun _ => true) o := by
  cases o with
  | none => simp [LoanEntry.principalIf]
  | some e =>
    simp only [LoanEntry.principalIf]
    by_cases hp : p e.loan = true <;> simp [hp]

/-- A loan that `p` does not select fits next to the loans `p` selects. Their principal sum plus its
principal is at most the principal sum of all loans. -/
private lemma LendingLedger.principalSum_add_le_all (l : LendingLedger) (p : Loan → Bool) {i : Nat} {e : LoanEntry}
    (he : l.loan? i = some e) (hp : p e.loan = false) :
    l.principalSum p + e.loan.principalOutstanding.toRat ≤ l.principalSum (fun _ => true) := by
  have hsum : l.principalSum p + l.principalSum (fun x => !p x) = l.principalSum (fun _ => true) := by
    unfold LendingLedger.principalSum
    rw [← List.sum_map_add]
    congr 1
    exact List.map_congr_left fun o _ => principalIf_add_not p o
  have hle := LendingLedger.principalIf_le_sum l (fun x => !p x) i
  rw [he] at hle
  simp only [LoanEntry.principalIf, hp, Bool.not_false, ↓reduceIte] at hle
  linarith

/-- An impair that passes its checks succeeds while AssetsDeployed holds every loan's principal. The loan
is late and not impaired, and the impaired loans' principal plus its own fits in AssetsDeployed. -/
private lemma LendingLedger.impair_total_of_deployed (l : LendingLedger) (hr : l.Reachable)
    (hnd : l.vaultDeleted = false)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hdeployed : l.principalSum (fun _ => true) ≤ l.vault.assetsDeployed.toRat) (i : Nat) (e : LoanEntry)
    (he : l.loan? i = some e) (hc : e.loan.canManage .impair l.now = .tesSUCCESS)
    (hlate : e.loan.nextPaymentDueDate < l.now) :
    ∃ l', (l.apply (.loanManage i .impair)).run = .ok (.ok l') := by
  obtain ⟨b, loan, hb, hw, hraw⟩ := hr.loan_withBroker he
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding := (congrArg RawLoan.principalOutstanding hraw :)
  have hnpd : loan.nextPaymentDueDate = e.loan.nextPaymentDueDate := (congrArg RawLoan.nextPaymentDueDate hraw :)
  -- the loan is not impaired, as the check passed
  have himp : e.loan.isImpaired = false := by
    cases h : e.loan.isImpaired
    · rfl
    · rw [Loan.canManage_wrong_flag_proof e.loan .impair l.now (Or.inl ⟨h, rfl⟩)] at hc
      exact absurd hc (by decide)
  have hroom : l.vault.lossUnrealized.toRat + loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := by
    rw [hr.lossInv.sum, hpo]
    exact le_trans (LendingLedger.principalSum_add_le_all l (·.isImpaired) he himp) hdeployed
  obtain ⟨r, hok⟩ := Loan.manageImpair_ok_of_room loan l.vault l.now (hr.storesAvailable hmax)
    (by rw [hnpd]; exact hlate) hroom
  exact ⟨_, LendingLedger.apply_manage_ok l hnd i e b loan .impair r he hb hw
    (by rw [Loan.canManage_withBroker hw]; exact hc) hok⟩

/-- A default that succeeds on the loan runs as the management action. -/
private lemma Loan.manage_default_ok {loan : Loan} {v : Vault} {now : UInt32} {r : LoanWithAmounts Vault}
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    (loan.manage .default v now).run = .ok (.ok r.toLoanWithPool) := by
  simp only [Loan.manage]
  unfold_ter
  simp only [ExceptT.run] at h
  simp [h]

/-- A default that passes its checks succeeds on the base grid, when AssetsDeployed, DebtTotal and
YieldUnrealized hold what the loan takes out. -/
private lemma LendingLedger.default_total_of_grid (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (hasset : Vault.HoldsAsset l.vault) (i : Nat) (e : LoanEntry) (b : LoanBroker) (he : l.loan? i = some e)
    (hb : l.broker? e.brokerIndex = some b) (hc : e.loan.canManage .default l.now = .tesSUCCESS)
    (haa : Number.AtExponent l.vault.assetsAvailable.toRat l.vault.baseExponent (10 ^ 16))
    (hroom : l.vault.assetsAvailable.toRat + e.loan.principalOutstanding.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (had : Number.AtExponent l.vault.assetsDeployed.toRat l.vault.baseExponent (10 ^ 16))
    (hyu : Number.AtExponent l.vault.yieldUnrealized.toRat l.vault.baseExponent (10 ^ 16))
    (hdt : Number.AtExponent b.debtTotal.toRat l.vault.baseExponent (10 ^ 16))
    (hca : b.coverAvailable.toRat < 10 ^ 96)
    (hdeployed : l.principalSum (fun _ => true) ≤ l.vault.assetsDeployed.toRat)
    (hdebt : e.loan.principalOutstanding.toRat ≤ b.debtTotal.toRat)
    (hyield : e.loan.toExact.interestDue ≤ l.vault.yieldUnrealized.toRat) :
    ∃ l', (l.apply (.loanManage i .default)).run = .ok (.ok l') := by
  have hs := hr.scaleInv
  obtain ⟨loan, hw⟩ := Loan.withBroker_ok e.loan b (by rw [hs.brokers _ b hb, hs.loanBroker i e he])
  have hraw := Loan.withBroker_eq hw
  have hf : ∀ f : RawLoan → Prop, f { e.loan.toRawLoan with broker := b } → f loan.toRawLoan :=
    fun f h => by rw [hraw]; exact h
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding := hf (·.principalOutstanding = _) rfl
  have himp : loan.isImpaired = e.loan.isImpaired := hf (·.isImpaired = _) rfl
  have hbr : loan.broker = b := hf (·.broker = b) rfl
  have hls : loan.loanScale = e.loan.loanScale := hf (·.loanScale = _) rfl
  have hex : loan.toExact.interestDue = e.loan.toExact.interestDue := by
    show loan.toRawLoan.totalValueOutstanding.toRat - loan.toRawLoan.principalOutstanding.toRat -
      loan.toRawLoan.managementFeeOutstanding.toRat = _
    rw [hraw]; rfl
  -- the checks passed, so the loan is active
  have hpend : e.loan.isPending = false := by
    cases h : e.loan.isPending
    · rfl
    · rw [Loan.canManage_closed_proof e.loan .default l.now (Or.inl h)] at hc
      exact absurd hc (by decide)
  have hinv := hr.lossInv
  obtain ⟨n, hnv⟩ := hinv.grid
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨d, hd, hdv⟩ := had
  have hlu : Number.AtExponent l.vault.lossUnrealized.toRat l.vault.baseExponent (10 ^ 16) := by
    refine ⟨n, ?_, hnv⟩
    have h1 : (n : ℚ) * 10 ^ l.vault.baseExponent ≤ (d : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [← hnv, ← hdv]; exact l.vault.exact.lossUnrealized_le
    have := le_of_mul_le_mul_right h1 hp10
    have : n ≤ d := by exact_mod_cast this
    omega
  have hg : Loan.DefaultGrid loan l.vault :=
    { numericType := by rw [hbr, hs.brokers _ b hb]
      loanScale := by rw [hls]; exact hs.loanScale i e he
      assetsAvailable := haa
      room := by rw [hpo]; exact hroom
      assetsDeployed := ⟨d, hd, hdv⟩
      lossUnrealized := hlu
      yieldUnrealized := hyu
      debtTotal := by rw [hbr]; exact hdt
      coverAvailable := by rw [hbr]; exact hca }
  have hall : e.loan.principalOutstanding.toRat ≤ l.principalSum (fun _ => true) := by
    have := LendingLedger.principalIf_le_sum l (fun _ => true) i
    rw [he] at this
    simpa [LoanEntry.principalIf] using this
  have hdep' : (if loan.isImpaired then 0 else l.vault.lossUnrealized.toRat) + loan.principalOutstanding.toRat ≤
      l.vault.assetsDeployed.toRat := by
    rw [himp, hpo]
    cases h : e.loan.isImpaired
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hinv.sum]
      exact le_trans (LendingLedger.principalSum_add_le_all l (·.isImpaired) he h) hdeployed
    · simp only [↓reduceIte, zero_add]
      exact le_trans hall hdeployed
  have hres : l.vault.assetsReserved.toRat + loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := by
    rw [hpo, hinv.reserved.sum]
    exact le_trans (LendingLedger.principalSum_add_le_all l (·.isPending) he hpend) hdeployed
  have hloss : loan.isImpaired = true → loan.principalOutstanding.toRat ≤ l.vault.lossUnrealized.toRat := by
    intro h
    rw [himp] at h
    rw [hpo, hinv.sum]
    have := LendingLedger.principalIf_le_sum l (·.isImpaired) i
    rw [he] at this
    simpa [LoanEntry.principalIf, h] using this
  obtain ⟨r, hok⟩ := Loan.manageDefault_ok_of_grid loan l.vault hg hasset hdep' hres hloss
    (by rw [hbr, hpo]; exact hdebt) (by rw [hex]; exact hyield)
  exact ⟨_, LendingLedger.apply_manage_ok l hnd i e b loan .default _ he hb hw
    (by rw [Loan.canManage_withBroker hw]; exact hc) (Loan.manage_default_ok hok)⟩

/-- Proof body of the impair line of `Lending.loan_ops_total`. -/
lemma LendingLedger.impair_total_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (hmax : l.vault.numericType.isIntegral = true → l.vault.numericType.maxValue.toNat ≤ maxRep.toNat)
    (i : Nat) (e : LoanEntry) (he : l.loan? i = some e) (hc : e.loan.canManage .impair l.now = .tesSUCCESS)
    (hlate : e.loan.nextPaymentDueDate < l.now) :
    ∃ l', (l.apply (.loanManage i .impair)).run = .ok (.ok l') :=
  LendingLedger.impair_total_of_deployed l hr hnd hmax (le_of_eq hr.debtInv.deployed.symm) i e he hc hlate

/-- A default that passes its checks succeeds while the vault holds less than `10^16` base units. Beyond it
the cover can be negative, which the model pays and C++ rejects with tecINTERNAL. -/
private lemma LendingLedger.default_possible_of_cover (l : LendingLedger) (hr : l.Reachable)
    (hnd : l.vaultDeleted = false) (hasset : Vault.HoldsAsset l.vault) (i : Nat) (e : LoanEntry)
    (he : l.loan? i = some e) (hc : e.loan.canManage .default l.now = .tesSUCCESS)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (haa : ∃ n : ℕ, l.vault.assetsAvailable.toRat = (n : ℚ) * 10 ^ l.vault.baseExponent)
    (hyu : l.vault.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hyield : e.loan.toExact.interestDue ≤ l.vault.yieldUnrealized.toRat)
    (hca : ∀ b, l.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) :
    ∃ l', (l.apply (.loanManage i .default)).run = .ok (.ok l') := by
  obtain ⟨b, hb⟩ := hr.loanCountInv.broker_of_loan he
  have hdinv := hr.debtInv
  have hs := hr.scaleInv
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  have hunits : ∀ (x : ℚ) (n : ℕ), x = (n : ℚ) * 10 ^ l.vault.baseExponent →
      x < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent → Number.AtExponent x l.vault.baseExponent (10 ^ 16) := by
    intro x n hx hlt
    refine ⟨n, ?_, hx⟩
    rw [hx] at hlt
    exact_mod_cast lt_of_mul_lt_mul_right hlt hp10.le
  obtain ⟨nd, hnd'⟩ := hs.principalSum_grid (fun _ => true)
  obtain ⟨nt, hnt⟩ := hs.brokerPrincipal_grid e.brokerIndex
  have hdt := hdinv.debt e.brokerIndex b hb
  have hdtle : b.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
    rw [hdt, hdinv.deployed]; exact l.brokerPrincipal_le _
  have hpo : e.loan.principalOutstanding.toRat ≤ b.debtTotal.toRat := by
    have := l.principalOn_le_sum e.brokerIndex i
    rw [he] at this
    rw [hdt]; simpa [LoanEntry.principalOn] using this
  have hpoad : e.loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := le_trans hpo hdtle
  obtain ⟨ny, hny⟩ := hr.yieldGridInv.grid.nat l.vault.exact.yieldUnrealized_nonneg
  obtain ⟨na, hna⟩ := haa
  exact LendingLedger.default_total_of_grid l hr hnd hasset i e b he hb hc
    (hunits _ na hna (by linarith)) (by linarith)
    (hunits _ nd (by rw [hdinv.deployed, hnd']) (by linarith)) (hunits _ ny hny hyu)
    (hunits _ nt (by rw [hdt, hnt]) (by linarith)) (hca b hb) (le_of_eq hdinv.deployed.symm) hpo hyield

/-- A default passes its checks once the loan is active, not defaulted, not paid off, and past
NextPaymentDueDate + GracePeriod as the ledger adds the times. -/
private lemma Loan.canManage_default_ok (loan : Loan) (now : UInt32) (hp : loan.isPending = false)
    (hd : loan.isDefault = false) (hrem : loan.paymentRemaining ≠ 0)
    (hlate : loan.nextPaymentDueDate + loan.schedule.gracePeriod < now) :
    loan.canManage .default now = .tesSUCCESS := by
  unfold Loan.canManage
  simp [hp, hd, hrem, hlate]

/-- Proof body of the default line of `Lending.Reachable.loan_resolvable`. -/
lemma LendingLedger.default_possible_proof (l : LendingLedger) (hr : l.Reachable) (hnd : l.vaultDeleted = false)
    (hasset : Vault.HoldsAsset l.vault) (i : Nat) (e : LoanEntry) (he : l.loan? i = some e)
    (hp : e.loan.isPending = false) (hd : e.loan.isDefault = false) (hrem : e.loan.paymentRemaining ≠ 0)
    (hlate : e.loan.nextPaymentDueDate + e.loan.schedule.gracePeriod < l.now)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (haa : ∃ n : ℕ, l.vault.assetsAvailable.toRat = (n : ℚ) * 10 ^ l.vault.baseExponent)
    (hyu : l.vault.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hyield : e.loan.toExact.interestDue ≤ l.vault.yieldUnrealized.toRat)
    (hca : ∀ b, l.broker? e.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) :
    ∃ l', (l.apply (.loanManage i .default)).run = .ok (.ok l') :=
  LendingLedger.default_possible_of_cover l hr hnd hasset i e he
    (Loan.canManage_default_ok e.loan l.now hp hd hrem hlate) htotal haa hyu hyield hca

end XRPL.Model.Lending
