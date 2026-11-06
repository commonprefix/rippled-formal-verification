import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Lending.Ledger.Common.LoanReplay
import XRPL.Properties.Lending.Ledger.Common.LoanStarts
import XRPL.Properties.Lending.Ledger.Common.LoanTxResults
import XRPL.Properties.Lending.Loan.Common.AcceptProofs
import XRPL.Properties.Lending.Loan.Common.DeleteProofs
import XRPL.Properties.Lending.Loan.Common.Loss
import XRPL.Properties.Lending.Loan.Common.SetPhase
import XRPL.Properties.Lending.Loan.Common.SetUpdates

/-! # Proof bodies for LoanAccept and LoanDelete on a ledger

A successful LoanAccept or LoanDelete ran `Loan.accept` or `Loan.delete` on the stored loan read with its broker,
and a successful LoanSet ran `Loan.create` on the stored broker. Each proof below reaches those operations and
reuses the proof for the `Loan` operation. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private canFundLoan from XRPL.Model.Lending.Loan.LoanSet
open private Loan.canCreate_startDate Vault.phase_investment from XRPL.Properties.Lending.Ledger.Common.LoanStarts

/-- Proof body of `accept_releases`. -/
lemma LendingLedger.accept_releases_proof {l l' : LendingLedger} (hr : l.Reachable) {i : Nat}
    (h : (l.apply (.loanAccept i)).run = .ok (.ok l')) {loan loan' : Loan} (hat : l.LoanAt i loan)
    (hat' : l'.LoanAt i loan') {interestDue : Number} (hi : loan.interestDue = .ok interestDue) :
    l'.vault.assetsReserved.toRat = l.vault.assetsReserved.toRat - loan.principalOutstanding.toRat ∧
      l'.vault.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat + interestDue.toRat ∧
      { l'.vault.toRawVault with
          assetsReserved := l.vault.assetsReserved
          yieldUnrealized := l.vault.yieldUnrealized } = l.vault.toRawVault ∧
      loan'.broker = loan.broker := by
  obtain ⟨-, loan₀, r, -, hat₀, hc, hok, -, hv, hat₁, -, -⟩ := LendingLedger.loanAccept_ok h
  obtain rfl := hat.eq hat₀
  obtain rfl := hat'.eq hat₁
  have hf := hr.accept_fits hat hc hi hok
  rw [hv]
  exact Loan.accept_releases_proof loan l.vault interestDue r hi hok hr.availableStored hf.1 hf.2

/-- The loan a LoanSet adds sits on its broker at the end of the loan list. -/
private lemma LendingLedger.loan?_ofCreate {l l₁ : LendingLedger} {j : Nat} {r : LoanWithPool Vault}
    (hl₁ : l₁ = l.commitLoan (LoanEffect.ofCreate j l.loans.length r)) :
    l₁.loan? l.loans.length = some { brokerIndex := j, loan := r.loan' } := by
  subst hl₁
  rw [LendingLedger.loan?_commitLoan]
  simp [LoanEffect.ofCreate]

/-- A vault that lends for a schedule at close time `t` is in the same phase at the schedule's later StartDate. -/
private lemma LoanSchedule.FitsVault.phase_startDate {schedule : LoanSchedule} {v : Vault} {t : UInt32}
    (hfv : schedule.FitsVault v t) (ht : t < schedule.startDate) :
    v.phase schedule.startDate = v.phase t := by
  cases hs : v.schedule with
  | none => simp [XRPL.Model.SingleAssetVault.Vault.phase, hs]
  | some s =>
    rcases hfv with h0 | ⟨hinv, hred⟩
    · simp only [XRPL.Model.SingleAssetVault.Vault.phase, hs] at h0
      split at h0
      · cases h0
      · split at h0 <;> cases h0
    · have hsub := Vault.phase_investment hs hinv
      have hend := hred s hs
      rw [hinv]
      simp only [XRPL.Model.SingleAssetVault.Vault.phase, hs]
      have h1 : s.subscriptionDate < schedule.startDate := UInt32.lt_trans hsub ht
      have h2 : ¬ s.redemptionDate ≤ schedule.startDate := by
        rw [UInt32.le_iff_toNat_le]
        unfold loanRedemptionBuffer at hend
        omega
      simp [h1, h2]

/-- An active LoanSet at close time `t'` runs the checks a two-step LoanSet ran at an earlier `t`, when the vault is
in the same phase at both times. -/
private lemma Loan.canCreate_active_eq (broker : LoanBroker) (v : Vault) (p : Number) (fees : LoanFees)
    (schedule : LoanSchedule) (t t' : UInt32) (hph : v.phase t' = v.phase t) (ht : t < schedule.startDate) :
    Loan.canCreate broker v p fees schedule t' false = Loan.canCreate broker v p fees schedule t true := by
  have hf : canFundLoan v schedule t' broker.numericType = canFundLoan v schedule t broker.numericType := by
    unfold canFundLoan
    simp only [Vault.pool_phase, hph]
  have hexp : decide (t ≥ schedule.startDate) = false := by
    rw [decide_eq_false_iff_not, ge_iff_le, UInt32.le_iff_toNat_le]
    have := UInt32.lt_iff_toNat_lt.mp ht
    omega
  unfold Loan.canCreate
  rw [hf]
  simp only [Bool.false_and, Bool.true_and, hexp]

/-- A LoanSet whose checks pass and whose create succeeds adds the created loan to the ledger. -/
private lemma LendingLedger.apply_loanSet_of_create {l : LendingLedger} (hnd : l.vaultDeleted = false) {j : Nat}
    {principal : Number} {rates : LoanRates} {fees : LoanFees} {pi pt gp : Option UInt32} {sd : UInt32}
    {twoStep ao : Bool} {schedule : LoanSchedule} {broker : LoanBroker} {r : LoanWithPool Vault}
    (hs : LoanSchedule.build pi pt gp sd l.now twoStep = schedule)
    (hpre : (LendingTx.loanSet j principal rates fees pi pt gp sd twoStep ao).preflight l = .tesSUCCESS)
    (hsched : schedule.checkTimeAvailability = .ok .tesSUCCESS) (hb : l.broker? j = some broker)
    (hc : Loan.canCreate broker l.vault principal fees schedule l.now twoStep = .ok .tesSUCCESS)
    (hcr : (Loan.create broker l.vault principal rates fees schedule ao twoStep).run = .ok (.ok r)) :
    (l.apply (.loanSet j principal rates fees pi pt gp sd twoStep ao)).run =
      .ok (.ok (l.commitLoan (LoanEffect.ofCreate j l.loans.length r))) := by
  subst hs
  rw [LendingLedger.apply_of_preflight hpre]
  simp only [LendingLedger.applyChecked, hnd, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
    ↓reduceIte, LendingLedger.applyLoan]
  -- rewrite the checks to their result before reducing, so the kernel never unfolds them
  unfold LendingLedger.applyLoanSet
  rw [hsched]
  dsimp only
  rw [if_neg (by decide)]
  simp only [hb]
  rw [hc]
  unfold LendingLedger.loanSetChecked
  dsimp only
  rw [if_neg (by rw [show TER.tesSUCCESS.isTesSuccess = true from rfl]; decide)]
  rw [ExceptT.run_map, ExceptT.run_map, hcr]
  rfl

/-- Proof body of `createPending_accept`. -/
lemma LendingLedger.createPending_accept_proof {l l₁ l₂ lc : LendingLedger} (hr : l.Reachable) {j : Nat}
    {principal : Number} {rates : LoanRates} {fees : LoanFees}
    {paymentInterval paymentTotal gracePeriod : Option UInt32} {startDate : UInt32} {allowsOverpayment : Bool}
    (hset : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate true
      allowsOverpayment)).run = .ok (.ok l₁))
    (haccept : (l₁.apply (.loanAccept l.loans.length)).run = .ok (.ok l₂))
    (hclose : (l.apply (.close startDate)).run = .ok (.ok lc)) :
    ∃ lA, (lc.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate false
      allowsOverpayment)).run = .ok (.ok lA) ∧
      lA.vault = l₂.vault ∧ lA.brokers = l₂.brokers ∧ lA.loans = l₂.loans := by
  obtain ⟨broker, r, hb, hpre, hsched, hc, hcreate, hl₁, hv₁, hat₁, -, -⟩ := LendingLedger.loanSet_ok hset
  obtain ⟨e, loan, rA, he, hat, -, hacc, hl₂, -, -, -, -⟩ := LendingLedger.loanAccept_ok haccept
  obtain rfl := hat.eq hat₁
  obtain rfl := Option.some.inj (he.symm.trans (LendingLedger.loan?_ofCreate hl₁))
  have hnd := LendingLedger.apply_loan_live rfl hset
  set schedule := LoanSchedule.build paymentInterval paymentTotal gracePeriod startDate l.now true with hs
  have ht : l.now < startDate := Loan.canCreate_startDate broker l.vault principal fees schedule l.now true hc rfl

  -- the close moves the close time to StartDate
  have hlc : lc = { l with now := startDate } := by
    have h' : (Except.ok (Except.ok { l with now := max l.now startDate }) :
        Except Error (Except TER LendingLedger)) = .ok (.ok lc) := hclose
    simp only [Except.ok.injEq] at h'
    rw [← h']
    show { l with now := if l.now ≤ startDate then startDate else l.now } = _
    rw [if_pos (UInt32.le_of_lt ht)]
  subst hlc

  -- the active LoanSet at StartDate runs the same create on the same schedule, and its checks pass
  obtain ⟨hp, hpos⟩ := LendingTx.preflight_loanSet_principal l j principal rates fees paymentInterval paymentTotal
    gracePeriod startDate true allowsOverpayment (by rw [hpre]; rfl)
  have hst := Loan.canCreate_exact broker l.vault principal fees schedule l.now true hc principal List.mem_cons_self
  have hf := hr.create_fits hb hp hpos hst hcreate
  rw [hv₁] at hacc
  have hcr := Loan.createPending_accept_proof l.vault broker principal rates fees schedule allowsOverpayment r rA
    hp hpos.le hst hf.2.1 hcreate hacc
  have hph := LoanSchedule.FitsVault.phase_startDate
    (Loan.canCreate_fitsVault broker l.vault principal fees schedule l.now true hc) ht
  have hc' : Loan.canCreate broker l.vault principal fees schedule startDate false = .ok .tesSUCCESS := by
    rw [Loan.canCreate_active_eq broker l.vault principal fees schedule l.now startDate hph ht]
    exact hc
  have hpre' : (LendingTx.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate false
      allowsOverpayment).preflight { l with now := startDate } = .tesSUCCESS := by
    simp only [LendingTx.preflight] at hpre ⊢
    exact hpre
  refine ⟨_, LendingLedger.apply_loanSet_of_create (l := { l with now := startDate }) hnd rfl hpre' hsched hb hc' hcr,
    ?_, ?_, ?_⟩
  · rw [hl₂]; rfl
  · rw [hl₂, hl₁]
    simp [LendingLedger.commitLoan, LoanEffect.ofCreate, LoanEffect.ofLoan]
  · rw [hl₂, hl₁]
    simp [LendingLedger.commitLoan, LoanEffect.ofCreate, LoanEffect.ofLoan, storeSlot]

/-- Proof body of the vault part of `Lending.deleteActive_settled`. -/
lemma LendingLedger.deleteActive_keeps_vault_proof {l l' : LendingLedger} {i : Nat}
    (h : (l.apply (.loanDelete i)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan)
    (hp : loan.isPending = false) : l'.vault = l.vault := by
  obtain ⟨-, loan₀, r, -, hat₀, -, hok, -, hv, -⟩ := LendingLedger.loanDelete_ok h
  obtain rfl := hat.eq hat₀
  rw [hv, (Loan.delete_active_ok_inv loan l.vault r hp hok).2]

/-- Proof body of `createPending_deletePending_restores`. -/
lemma LendingLedger.createPending_deletePending_restores_proof {l l₁ l₂ : LendingLedger} (hr : l.Reachable)
    {j : Nat} {principal : Number} {rates : LoanRates} {fees : LoanFees}
    {paymentInterval paymentTotal gracePeriod : Option UInt32} {startDate : UInt32} {allowsOverpayment : Bool}
    (hset : (l.apply (.loanSet j principal rates fees paymentInterval paymentTotal gracePeriod startDate true
      allowsOverpayment)).run = .ok (.ok l₁))
    (hdelete : (l₁.apply (.loanDelete l.loans.length)).run = .ok (.ok l₂)) {broker broker' : LoanBroker}
    (hb : l.broker? j = some broker) (hb' : l₂.broker? j = some broker') :
    l₂.vault.assetsAvailable = l.vault.assetsAvailable ∧ l₂.vault.assetsReserved = l.vault.assetsReserved ∧
      broker'.debtTotal = broker.debtTotal ∧ broker'.loanCount = broker.loanCount := by
  obtain ⟨b, r, hb₀, hpre, -, hc, hcreate, hl₁, hv₁, hat₁, -, -⟩ := LendingLedger.loanSet_ok hset
  obtain rfl := Option.some.inj (hb.symm.trans hb₀)
  obtain ⟨e, loan, rD, he, hat, -, hdel, -, hv₂, -, -, hbr⟩ := LendingLedger.loanDelete_ok hdelete
  obtain rfl := hat.eq hat₁
  obtain rfl := Option.some.inj (he.symm.trans (LendingLedger.loan?_ofCreate hl₁))
  rw [hbr, if_pos rfl] at hb'
  obtain rfl := Option.some.inj hb'
  obtain ⟨hp, hpos⟩ := LendingTx.preflight_loanSet_principal l j principal rates fees paymentInterval paymentTotal
    gracePeriod startDate true allowsOverpayment (by rw [hpre]; rfl)
  have hst := Loan.canCreate_exact broker l.vault principal fees _ _ _ hc principal List.mem_cons_self
  have hf := hr.create_fits hb hp hpos hst hcreate
  rw [hv₁] at hdel
  rw [hv₂]
  exact Loan.createPending_deletePending_restores_proof l.vault broker principal rates fees _ allowsOverpayment r rD
    hp hpos.le hst hr.availableStored hf.1 hf.2.1 hf.2.2 hcreate hdel

/-- Proof body of `deletePending_principal`. -/
lemma LendingLedger.deletePending_principal_proof {l l' : LendingLedger} (hr : l.Reachable) {i : Nat}
    (h : (l.apply (.loanDelete i)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan) {e : LoanEntry}
    (he : l.loan? i = some e) {broker' : LoanBroker} (hb' : l'.broker? e.brokerIndex = some broker')
    (hp : loan.isPending = true)
    (haa : STAmount.Representable l.vault.numericType
      (l.vault.assetsAvailable.toRat + loan.principalOutstanding.toRat)) :
    l'.vault.assetsAvailable.toRat - l.vault.assetsAvailable.toRat = loan.principalOutstanding.toRat ∧
      l.vault.assetsReserved.toRat - l'.vault.assetsReserved.toRat = loan.principalOutstanding.toRat ∧
      l.vault.assetsDeployed.toRat - l'.vault.assetsDeployed.toRat = loan.principalOutstanding.toRat ∧
      loan.broker.debtTotal.toRat - broker'.debtTotal.toRat = loan.principalOutstanding.toRat := by
  obtain ⟨e₀, loan₀, r, he₀, hat₀, -, hok, -, hv, -, -, hbr⟩ := LendingLedger.loanDelete_ok h
  obtain rfl := hat.eq hat₀
  obtain rfl := Option.some.inj (he.symm.trans he₀)
  rw [hbr, if_pos rfl] at hb'
  obtain rfl := Option.some.inj hb'
  have hf := hr.deletePending_fits hat hp
  rw [hv]
  exact Loan.deletePending_principal_of_exact loan l.vault r hp hok hf.1 haa hf.2.1 hf.2.2.1 hf.2.2.2
    (hr.lastLoan_debt hat)

/-- Proof body of the last loan part of `Lending.deleteActive_settled`. -/
lemma LendingLedger.deleteActive_last_proof {l l' : LendingLedger} (hr : l.Reachable) {i : Nat}
    (h : (l.apply (.loanDelete i)).run = .ok (.ok l')) {loan : Loan} (hat : l.LoanAt i loan) {e : LoanEntry}
    (he : l.loan? i = some e) {broker' : LoanBroker} (hb' : l'.broker? e.brokerIndex = some broker')
    (hp : loan.isPending = false) (hlast : loan.broker.loanCount = 1) :
    loan.broker.debtTotal = Number.zero ∧ broker'.debtTotal = loan.broker.debtTotal := by
  obtain ⟨e₀, loan₀, r, he₀, hat₀, hc, hok, -, -, -, -, hbr⟩ := LendingLedger.loanDelete_ok h
  obtain rfl := hat.eq hat₀
  obtain rfl := Option.some.inj (he.symm.trans he₀)
  rw [hbr, if_pos rfl] at hb'
  obtain rfl := Option.some.inj hb'
  exact Loan.deleteActive_last_proof loan l.vault r hp (Loan.canDelete_active_paid loan hc hp) hlast
    (hr.lastLoan_debt hat hlast) hok

end XRPL.Model.Lending
