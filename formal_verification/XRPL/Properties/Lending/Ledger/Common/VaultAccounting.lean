import XRPL.Properties.Lending.Ledger.Common.VaultAccountingDefs
import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Lending.Loan.Common.AcceptDeleteLedger
import XRPL.Properties.Lending.Loan.Common.ManageLedger
import XRPL.Properties.Lending.Loan.Common.PayLedgerFunds
import XRPL.Properties.Lending.Loan.Common.SetLedger

/-! # The vault's balances over a sequence of transactions

AssetsDeployed, AssetsReserved, LossUnrealized and YieldUnrealized move by exactly what each transaction lends, pays,
accepts, deletes, defaults, impairs and books. AssetsTotal moves by exactly the assets that go in and out while the
vault is not coarsened, and AssetsAvailable is AssetsTotal less AssetsDeployed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A transaction reads the stored loan at `i` with its broker's current copy. -/
private lemma LendingLedger.LoanAt.loanRead {l : LendingLedger} {i : Nat} {loan : Loan} (h : l.LoanAt i loan) :
    l.loanRead i = some loan := by
  obtain ⟨e, b, he, hb, hw⟩ := h
  simp only [LendingLedger.loanRead, he, hb, hw]

/-- A transaction that is not a loan transaction keeps AssetsDeployed, AssetsReserved, LossUnrealized and
YieldUnrealized. -/
private lemma LendingLedger.apply_keepsLending {l l' : LendingLedger} {tx : LendingTx} (hl : ¬ tx.isLoan = true)
    (h : (l.apply tx).run = .ok (.ok l')) :
    l'.vault.assetsDeployed = l.vault.assetsDeployed ∧ l'.vault.assetsReserved = l.vault.assetsReserved ∧
      l'.vault.lossUnrealized = l.vault.lossUnrealized ∧ l'.vault.yieldUnrealized = l.vault.yieldUnrealized := by
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault]
    exact ⟨hk.assetsDeployed, hk.assetsReserved, hk.lossUnrealized, hk.yieldUnrealized⟩
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨rfl, rfl, rfl, rfl⟩
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- One successful transaction on a reachable ledger moves AssetsDeployed, AssetsReserved, LossUnrealized and
YieldUnrealized by exactly what it lends, pays, accepts, deletes, defaults, impairs and books. -/
private lemma LendingLedger.lending_step {l l' : LendingLedger} {tx : LendingTx} (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) :
    l'.vault.assetsDeployed.toRat = l.vault.assetsDeployed.toRat + l.lentOf tx - l.principalPaidOf tx -
        l.defaultedOf tx - l.deletedPendingOf tx ∧
      l'.vault.assetsReserved.toRat = l.vault.assetsReserved.toRat + l.lentPendingOf tx - l.acceptedOf tx -
        l.deletedPendingOf tx ∧
      l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat + l.impairedOf tx - l.unimpairedOf tx ∧
      l'.vault.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat + l.interestBookedOf tx -
        l.interestRemovedOf tx - l.interestDefaultedOf tx := by
  by_cases hl : tx.isLoan = true
  swap
  · obtain ⟨h1, h2, h3, h4⟩ := LendingLedger.apply_keepsLending hl h
    rw [h1, h2, h3, h4]
    cases tx <;> simp only [LendingTx.isLoan, not_true_eq_false] at hl <;>
      exact ⟨by show _ = _ + 0 - 0 - 0 - 0; ring, by show _ = _ + 0 - 0 - 0; ring, by show _ = _ + 0 - 0; ring,
        by show _ = _ + 0 - 0 - 0; ring⟩
  cases tx with
  | loanSet j principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨broker, r, hb, -, -, -, hcr, -, -, hat', -, -⟩ := LendingLedger.loanSet_ok h
    obtain ⟨-, hAD, -, hAR⟩ := LendingLedger.create_principal_proof hr hb h hat'
    change l'.vault.assetsDeployed.toRat - l.vault.assetsDeployed.toRat = principal.toRat at hAD
    change l'.vault.assetsReserved.toRat - l.vault.assetsReserved.toRat = _ at hAR
    have hLU : l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat :=
      (LendingLedger.create_assetsTotal_unchanged_proof hr h).2
    have hYU : l'.vault.yieldUnrealized.toRat =
        l.vault.yieldUnrealized.toRat + if twoStep then 0 else r.loan'.toExact.interestDue :=
      LendingLedger.create_yield_proof hr h hat'
    simp only [LendingLedger.lentOf, LendingLedger.principalPaidOf, LendingLedger.defaultedOf,
      LendingLedger.deletedPendingOf, LendingLedger.lentPendingOf, LendingLedger.acceptedOf,
      LendingLedger.impairedOf, LendingLedger.unimpairedOf, LendingLedger.interestBookedOf,
      LendingLedger.interestRemovedOf, LendingLedger.interestDefaultedOf, hb, hcr]
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    cases twoStep <;> simp only [Bool.false_eq_true, ↓reduceIte] at hYU ⊢ <;> linarith
  | loanAccept i =>
    obtain ⟨-, loan, r, -, hat, -, hok, -, hv, hat', -, -⟩ := LendingLedger.loanAccept_ok h
    obtain ⟨d, hi⟩ : ∃ d, loan.interestDue = .ok d := by
      have hok' := hok
      simp only [Loan.accept] at hok'
      unfold_ter at hok'
      walk_ok
      exact ⟨_, ‹_›⟩
    obtain ⟨hAR, hYU, -, -⟩ := LendingLedger.accept_releases_proof hr h hat hat' hi
    obtain ⟨hLU, hAD⟩ := Loan.accept_lossStep loan l.vault r hok
    rw [← hv] at hLU hAD
    simp only [LendingLedger.lentOf, LendingLedger.principalPaidOf, LendingLedger.defaultedOf,
      LendingLedger.deletedPendingOf, LendingLedger.lentPendingOf, LendingLedger.acceptedOf,
      LendingLedger.impairedOf, LendingLedger.unimpairedOf, LendingLedger.interestBookedOf,
      LendingLedger.interestRemovedOf, LendingLedger.interestDefaultedOf, hat.loanRead, hAD, hLU]
    rw [← Loan.interestDue_toExact loan d hi]
    exact ⟨by ring, by linarith, by ring, by linarith⟩
  | loanDelete i =>
    obtain ⟨e, loan, r, he, hat, -, hok, hl', hv, -, -, -⟩ := LendingLedger.loanDelete_ok h
    obtain ⟨e₀, he₀, -, hraw⟩ := hat.stored
    obtain rfl := Option.some.inj (he₀.symm.trans he)
    have hLU := (Loan.delete_lossStep loan l.vault r hok).1
    have hYU := Loan.delete_yield loan l.vault r hok
    rw [← hv] at hLU hYU
    simp only [LendingLedger.lentOf, LendingLedger.principalPaidOf, LendingLedger.defaultedOf,
      LendingLedger.deletedPendingOf, LendingLedger.lentPendingOf, LendingLedger.acceptedOf,
      LendingLedger.impairedOf, LendingLedger.unimpairedOf, LendingLedger.interestBookedOf,
      LendingLedger.interestRemovedOf, LendingLedger.interestDefaultedOf, hat.loanRead, hLU, hYU]
    cases hp : loan.isPending
    · -- a paid-off loan leaves the vault as it was
      have hvv := Loan.delete_active_vault loan l.vault r hp hok
      rw [hvv] at hv
      rw [hv]
      exact ⟨by simp, by simp, by ring, by ring⟩
    · -- a pending loan leaves AssetsDeployed and AssetsReserved, which are sums over the stored loans
      have hr' := hr.apply h
      have hPO : loan.principalOutstanding = e₀.loan.principalOutstanding :=
        (congrArg RawLoan.principalOutstanding hraw :)
      have hpe : e₀.loan.isPending = true := by rw [← (congrArg RawLoan.isPending hraw :)]; exact hp
      have hcD : l'.principalSum (fun _ => true) + LoanEntry.principalIf (fun _ => true) (l.loan? i) =
          l.principalSum (fun _ => true) + LoanEntry.principalIf (fun _ => true) none := by
        rw [hl']; exact l.principalSum_commitLoan _ _
      have hcR : l'.principalSum (·.isPending) + LoanEntry.principalIf (·.isPending) (l.loan? i) =
          l.principalSum (·.isPending) + LoanEntry.principalIf (·.isPending) none := by
        rw [hl']; exact l.principalSum_commitLoan _ _
      rw [he₀] at hcD hcR
      simp only [LoanEntry.principalIf, hpe, if_true, add_zero] at hcD hcR
      have hD := hr.debtInv.deployed
      have hD' := hr'.debtInv.deployed
      have hR := hr.reservedInv.sum
      have hR' := hr'.reservedInv.sum
      rw [hPO]
      exact ⟨by simp only [if_true]; linarith, by simp only [if_true]; linarith, by ring, by ring⟩
  | loanManage i action =>
    cases action with
    | impair =>
      obtain ⟨-, loan, r, -, hat, -, -, -, -, hat', -, -⟩ := LendingLedger.loanImpair_ok h
      obtain ⟨-, hLU, hraw⟩ := LendingLedger.manageImpair_loss_proof hr h hat hat'
      have hAD : l'.vault.assetsDeployed = l.vault.assetsDeployed :=
        (congrArg RawVault.assetsDeployed hraw :)
      have hAR : l'.vault.assetsReserved = l.vault.assetsReserved :=
        (congrArg RawVault.assetsReserved hraw :)
      have hYU : l'.vault.yieldUnrealized = l.vault.yieldUnrealized :=
        (congrArg RawVault.yieldUnrealized hraw :)
      simp only [LendingLedger.lentOf, LendingLedger.principalPaidOf, LendingLedger.defaultedOf,
        LendingLedger.deletedPendingOf, LendingLedger.lentPendingOf, LendingLedger.acceptedOf,
        LendingLedger.impairedOf, LendingLedger.unimpairedOf, LendingLedger.interestBookedOf,
        LendingLedger.interestRemovedOf, LendingLedger.interestDefaultedOf, hat.loanRead, hAD, hAR, hYU, hLU]
      exact ⟨by ring, by ring, by ring, by ring⟩
    | unimpair =>
      obtain ⟨-, loan, r, -, hat, -, -, -, -, hat', -, -⟩ := LendingLedger.loanUnimpair_ok h
      obtain ⟨-, hLU, hraw⟩ := LendingLedger.manageUnimpair_loss_proof hr h hat hat'
      have hAD : l'.vault.assetsDeployed = l.vault.assetsDeployed :=
        (congrArg RawVault.assetsDeployed hraw :)
      have hAR : l'.vault.assetsReserved = l.vault.assetsReserved :=
        (congrArg RawVault.assetsReserved hraw :)
      have hYU : l'.vault.yieldUnrealized = l.vault.yieldUnrealized :=
        (congrArg RawVault.yieldUnrealized hraw :)
      simp only [LendingLedger.lentOf, LendingLedger.principalPaidOf, LendingLedger.defaultedOf,
        LendingLedger.deletedPendingOf, LendingLedger.lentPendingOf, LendingLedger.acceptedOf,
        LendingLedger.impairedOf, LendingLedger.unimpairedOf, LendingLedger.interestBookedOf,
        LendingLedger.interestRemovedOf, LendingLedger.interestDefaultedOf, hat.loanRead, hAD, hAR, hYU, hLU]
      exact ⟨by ring, by ring, by ring, by ring⟩
    | default =>
      obtain ⟨-, loan, r, -, hat, -, hdef, -, hv, hat', -, -⟩ := LendingLedger.loanDefault_ok h
      obtain ⟨-, loan₂, r₂, -, hat₂, -, hm, -, hv₂, -, -, -⟩ := LendingLedger.loanManage_ok h
      obtain rfl := hat.eq hat₂
      have hAD := (LendingLedger.manageDefault_principal_proof hr h hat hat').1
      have hYU := LendingLedger.manageDefault_yield_proof hr h hat
      have hAR := (Loan.manage_debt loan .default l.vault l.now r₂ hm).2
      rw [← hv₂] at hAR
      have hLU : l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat -
          if loan.isImpaired then loan.principalOutstanding.toRat else 0 := by
        cases himp : loan.isImpaired
        · have h0 := (Loan.manageDefault_lossStep loan l.vault r hdef).1
          rw [himp, if_neg Bool.false_ne_true, Number.operator_add_zero_right, Except.ok.injEq] at h0
          rw [hv, ← h0]; simp
        · rw [LendingLedger.manageDefault_loss_proof hr h hat himp]; simp
      simp only [LendingLedger.lentOf, LendingLedger.principalPaidOf, LendingLedger.defaultedOf,
        LendingLedger.deletedPendingOf, LendingLedger.lentPendingOf, LendingLedger.acceptedOf,
        LendingLedger.impairedOf, LendingLedger.unimpairedOf, LendingLedger.interestBookedOf,
        LendingLedger.interestRemovedOf, LendingLedger.interestDefaultedOf, hat.loanRead, hAR, hYU, hLU]
      exact ⟨by linarith, by ring, by ring, by ring⟩
  | loanPay i pt amount =>
    obtain ⟨-, loan, r, -, hat, -, -, hok, -, hv, hat', -, -⟩ := LendingLedger.loanPay_ok h
    obtain ⟨p, hp⟩ := LendingLedger.loanPay_instalments h hat
    have hAD := (LendingLedger.payment_principal_proof l hr l' i pt amount h loan r.loan' hat hat' p hp).2.1
    have hYU : l'.vault.yieldUnrealized.toRat =
        l.vault.yieldUnrealized.toRat - (loan.toExact.interestDue - r.loan'.toExact.interestDue) :=
      LendingLedger.payment_yield_proof l hr l' i pt amount h loan r.loan' hat hat'
    have hAR := (Loan.pay_debt loan l.vault pt amount l.now r hok).2
    rw [← hv] at hAR
    have hLU : l'.vault.lossUnrealized.toRat = l.vault.lossUnrealized.toRat -
        if loan.isImpaired then loan.principalOutstanding.toRat else 0 := by
      cases himp : loan.isImpaired
      · rw [hv, (Loan.pay_lossStep loan l.vault pt amount l.now r hok).2.1 himp]; simp
      · rw [show l'.vault.lossUnrealized.toRat = _ from
          LendingLedger.payment_unimpairs_proof l hr l' i pt amount h loan hat himp]
        simp only [if_true]; rfl
    simp only [LendingLedger.lentOf, LendingLedger.principalPaidOf, LendingLedger.defaultedOf,
      LendingLedger.deletedPendingOf, LendingLedger.lentPendingOf, LendingLedger.acceptedOf,
      LendingLedger.impairedOf, LendingLedger.unimpairedOf, LendingLedger.interestBookedOf,
      LendingLedger.interestRemovedOf, LendingLedger.interestDefaultedOf, hat.loanRead, hp, hok, hAR, hYU, hLU]
    exact ⟨by linarith, by ring, by ring, by ring⟩
  | _ => simp only [LendingTx.isLoan, Bool.false_eq_true] at hl

/-- A payment on a reachable ledger whose vault is not coarsened before or after it sends the vault exactly the
principal and the interest it pays. -/
private lemma LendingLedger.amountToPool_step {l l' : LendingLedger} {tx : LendingTx} (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l')) (hnc : l.NotCoarsened) (hnc' : l'.NotCoarsened) :
    l.amountToPoolOf tx = l.principalPaidOf tx + l.interestPaidOf tx := by
  cases tx with
  | loanPay i pt amount =>
    obtain ⟨-, loan, r, -, hat, -, -, hok, -⟩ := LendingLedger.loanPay_ok h
    obtain ⟨p, hp⟩ := LendingLedger.loanPay_instalments h hat
    have hT : l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat = l.vault.assetsAvailable.toRat +
        l.vault.assetsDeployed.toRat + ((0 : ℚ) - 0 - 0 + l.paidInterest i pt amount - 0) :=
      LendingLedger.flow_step l l' _ hr h hnc (fun _ => hnc')
    have hD := (LendingLedger.lending_step hr h).1
    have hAD0 : 0 ≤ l'.vault.assetsDeployed.toRat := l'.vault.exact.assetsDeployed_nonneg
    unfold LendingLedger.NotCoarsened at hnc'
    rw [LendingLedger.apply_baseExponent h] at hnc'
    simp only [LendingLedger.amountToPoolOf, LendingLedger.principalPaidOf, LendingLedger.interestPaidOf,
      LendingLedger.paidInterest, LendingLedger.lentOf, LendingLedger.defaultedOf, LendingLedger.deletedPendingOf,
      hat.loanRead, hp, hok] at hT hD ⊢
    -- the vault after the payment holds AssetsAvailable + principalPaid + interestPaid, below `10^16` base units
    have hAA := LendingLedger.payment_vault_amountToPool_proof l hr l' i pt amount h loan hat p hp r hok
      (by linarith)
    linarith
  | _ => simp [LendingLedger.amountToPoolOf, LendingLedger.principalPaidOf, LendingLedger.interestPaidOf]

/-- A sequence of successful transactions is a run that collects some interest beyond the schedule. -/
private lemma LendingLedger.Reaches.reachableFromIn {start l : LendingLedger} {txs : List LendingTx}
    (h : LendingLedger.Reaches start txs l) : ∃ x, start.ReachableFromIn txs l x := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | step tx _ hok ih =>
    obtain ⟨x, hx⟩ := ih
    exact ⟨_, .step tx hx hok⟩

/-- The sum of one kind of flow along a sequence is that kind of the sequence's flows. -/
private lemma LendingLedger.runSum_flow (π : AssetFlows → ℚ) (h0 : π 0 = 0) (hadd : ∀ a b, π (a + b) = π a + π b)
    (l : LendingLedger) (txs : List LendingTx) :
    l.runSum (fun l₀ tx => π (l₀.flowOf tx)) txs = π (l.flows txs) := by
  induction txs generalizing l with
  | nil => exact h0.symm
  | cons tx txs ih =>
    simp only [LendingLedger.runSum, LendingLedger.flows, hadd]
    cases (l.apply tx).run with
    | error _ => rw [h0]
    | ok r =>
      cases r with
      | error _ => rw [h0]
      | ok l' => dsimp only; rw [ih]

/-- On every successful step the AssetsTotal a default writes off is PrincipalOutstanding less the cover it moves
to the vault. -/
private lemma LendingLedger.defaultLosses_step {l l' : LendingLedger} {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) :
    (l.flowOf tx).defaultLosses = l.defaultedOf tx - l.defaultCoveredOf tx := by
  cases tx with
  | loanManage i action =>
    cases action with
    | default =>
      obtain ⟨-, loan, r, -, hat, -, hdef, -⟩ := LendingLedger.loanDefault_ok h
      obtain ⟨_, _, _, _, _, -, hdc, -⟩ := Loan.manageDefault_ok_parts loan l.vault r hdef
      simp only [LendingLedger.flowOf, LendingLedger.defaultLoss, LendingLedger.defaultedOf,
        LendingLedger.defaultCoveredOf, hat.loanRead, hdc, hdef]
    | _ => exact (sub_zero 0).symm
  | _ => exact (sub_zero 0).symm

/-- Along a sequence of successful transactions, the flows that make up AssetsTotal are the sums of this file. -/
lemma LendingLedger.Reaches.flows_eq {start l : LendingLedger} {txs : List LendingTx}
    (hrun : LendingLedger.Reaches start txs l) :
    (start.flows txs).deposits = start.deposits txs ∧ (start.flows txs).withdrawals = start.withdrawals txs ∧
      (start.flows txs).clawbacks = start.clawbacks txs ∧ (start.flows txs).interestPaid = start.interestPaid txs ∧
      (start.flows txs).defaultLosses = start.defaulted txs - start.defaultCovered txs := by
  have hflow : ∀ (π : AssetFlows → ℚ) (f : LendingLedger → LendingTx → ℚ), π 0 = 0 →
      (∀ a b, π (a + b) = π a + π b) → (∀ l₀ tx, f l₀ tx = π (l₀.flowOf tx)) →
      π (start.flows txs) = start.runSum f txs := fun π f h0 hadd hf => by
    rw [← LendingLedger.runSum_flow π h0 hadd]
    exact congrArg (start.runSum · txs) (funext fun l₀ => funext fun tx => (hf l₀ tx).symm)
  have hof : ∀ (l₀ : LendingLedger) (tx : LendingTx),
      l₀.depositsOf tx = (l₀.flowOf tx).deposits ∧ l₀.withdrawalsOf tx = (l₀.flowOf tx).withdrawals ∧
        l₀.clawbacksOf tx = (l₀.flowOf tx).clawbacks ∧ l₀.interestPaidOf tx = (l₀.flowOf tx).interestPaid :=
    fun l₀ tx => by
      cases tx with
      | loanManage _ a => cases a <;> exact ⟨rfl, rfl, rfl, rfl⟩
      | _ => exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨hflow _ _ rfl (fun _ _ => rfl) (fun l₀ tx => (hof l₀ tx).1),
    hflow _ _ rfl (fun _ _ => rfl) (fun l₀ tx => (hof l₀ tx).2.1),
    hflow _ _ rfl (fun _ _ => rfl) (fun l₀ tx => (hof l₀ tx).2.2.1),
    hflow _ _ rfl (fun _ _ => rfl) (fun l₀ tx => (hof l₀ tx).2.2.2), ?_⟩
  rw [← LendingLedger.runSum_flow AssetFlows.defaultLosses rfl (fun _ _ => rfl)]
  unfold LendingLedger.defaulted LendingLedger.defaultCovered
  rw [← LendingLedger.runSum_sub]
  exact LendingLedger.runSum_congr hrun fun _ _ _ _ _ _ hok => LendingLedger.defaultLosses_step hok

/-- Over any sequence of transactions from a reachable ledger, the vault's balances move by exactly the flows.
AssetsTotal and AssetsAvailable need the vault not coarsened on every ledger of the sequence. -/
lemma LendingLedger.vault_accounting_proof {start l : LendingLedger} {txs : List LendingTx} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) :
    (start.NotCoarsenedAlong txs →
      l.vault.toRawVault.toExact.assetsTotal = start.vault.toRawVault.toExact.assetsTotal + start.deposits txs -
        start.withdrawals txs - start.clawbacks txs + start.interestPaid txs - start.defaulted txs +
        start.defaultCovered txs) ∧
    (start.NotCoarsenedAlong txs →
      l.vault.assetsAvailable.toRat = start.vault.assetsAvailable.toRat + start.deposits txs - start.withdrawals txs -
        start.clawbacks txs - start.lent txs + start.amountToPool txs + start.defaultCovered txs +
        start.deletedPending txs) ∧
    l.vault.assetsDeployed.toRat = start.vault.assetsDeployed.toRat + start.lent txs - start.principalPaid txs -
      start.defaulted txs - start.deletedPending txs ∧
    l.vault.assetsReserved.toRat = start.vault.assetsReserved.toRat + start.lentPending txs - start.accepted txs -
      start.deletedPending txs ∧
    l.vault.lossUnrealized.toRat = start.vault.lossUnrealized.toRat + start.impaired txs - start.unimpaired txs ∧
    l.vault.yieldUnrealized.toRat = start.vault.yieldUnrealized.toRat + start.interestBooked txs -
      start.interestRemoved txs - start.interestDefaulted txs := by
  have hall : ∀ (pre : List LendingTx) (l₁ : LendingLedger) (tx : LendingTx) (l₂ : LendingLedger),
      pre ++ [tx] <+: txs → LendingLedger.Reaches start pre l₁ → (l₁.apply tx).run = .ok (.ok l₂) → True :=
    fun _ _ _ _ _ _ _ => trivial
  have hAD := LendingLedger.Reaches.runSum_eq (F := fun l₀ => l₀.vault.assetsDeployed.toRat)
    (d := fun l₀ tx => l₀.lentOf tx - l₀.principalPaidOf tx - l₀.defaultedOf tx - l₀.deletedPendingOf tx)
    (fun _ _ _ hr₁ hok _ => by beta_reduce; rw [(LendingLedger.lending_step hr₁ hok).1]; ring) hr hrun hall
  have hAR := LendingLedger.Reaches.runSum_eq (F := fun l₀ => l₀.vault.assetsReserved.toRat)
    (d := fun l₀ tx => l₀.lentPendingOf tx - l₀.acceptedOf tx - l₀.deletedPendingOf tx)
    (fun _ _ _ hr₁ hok _ => by beta_reduce; rw [(LendingLedger.lending_step hr₁ hok).2.1]; ring) hr hrun hall
  have hLU := LendingLedger.Reaches.runSum_eq (F := fun l₀ => l₀.vault.lossUnrealized.toRat)
    (d := fun l₀ tx => l₀.impairedOf tx - l₀.unimpairedOf tx)
    (fun _ _ _ hr₁ hok _ => by beta_reduce; rw [(LendingLedger.lending_step hr₁ hok).2.2.1]; ring) hr hrun hall
  have hYU := LendingLedger.Reaches.runSum_eq (F := fun l₀ => l₀.vault.yieldUnrealized.toRat)
    (d := fun l₀ tx => l₀.interestBookedOf tx - l₀.interestRemovedOf tx - l₀.interestDefaultedOf tx)
    (fun _ _ _ hr₁ hok _ => by beta_reduce; rw [(LendingLedger.lending_step hr₁ hok).2.2.2]; ring) hr hrun hall
  beta_reduce at hAD hAR hLU hYU
  rw [LendingLedger.runSum_sub, LendingLedger.runSum_sub, LendingLedger.runSum_sub] at hAD
  rw [LendingLedger.runSum_sub, LendingLedger.runSum_sub] at hAR hYU
  rw [LendingLedger.runSum_sub] at hLU
  have hADl : l.vault.assetsDeployed.toRat = start.vault.assetsDeployed.toRat + start.lent txs -
      start.principalPaid txs - start.defaulted txs - start.deletedPending txs := by
    rw [hAD]; unfold LendingLedger.lent LendingLedger.principalPaid LendingLedger.defaulted
      LendingLedger.deletedPending; ring
  -- AssetsTotal is the sum of the flows over a run on which the vault is never coarsened
  have hAT : start.NotCoarsenedAlong txs →
      l.vault.toRawVault.toExact.assetsTotal = start.vault.toRawVault.toExact.assetsTotal + start.deposits txs -
        start.withdrawals txs - start.clawbacks txs + start.interestPaid txs - start.defaulted txs +
        start.defaultCovered txs := by
    intro hnc
    obtain ⟨x, hx⟩ := hrun.reachableFromIn
    have hT := LendingLedger.assetsTotal_eq_proof start l txs x hr hx
      (fun pre l₁ _ hp h₁ => hnc pre l₁ hp h₁.reaches)
    obtain ⟨hdep, hpay, hclaw, hint, hdl⟩ := hrun.flows_eq
    rw [hT, hdep, hpay, hclaw, hint, hdl]
    ring
  -- on such a run each payment sends the vault exactly the principal and the interest it pays
  have hpool : start.NotCoarsenedAlong txs →
      start.amountToPool txs = start.principalPaid txs + start.interestPaid txs := fun hnc => by
    unfold LendingLedger.amountToPool LendingLedger.principalPaid LendingLedger.interestPaid
    rw [← LendingLedger.runSum_add]
    exact LendingLedger.runSum_congr hrun fun pre l₁ tx l₂ hp h₁ hok =>
      LendingLedger.amountToPool_step (h₁.reachable hr) hok (hnc pre l₁ ((List.prefix_append pre [tx]).trans hp) h₁)
        (hnc (pre ++ [tx]) l₂ hp (.step tx h₁ hok))
  refine ⟨hAT, fun hnc => ?_, hADl, ?_, ?_, ?_⟩
  · -- AssetsAvailable is AssetsTotal less AssetsDeployed
    have h1 := hAT hnc
    have h2 := hpool hnc
    change l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat =
      start.vault.assetsAvailable.toRat + start.vault.assetsDeployed.toRat + _ - _ - _ + _ - _ + _ at h1
    linarith
  · rw [hAR]; unfold LendingLedger.lentPending LendingLedger.accepted LendingLedger.deletedPending; ring
  · rw [hLU]; unfold LendingLedger.impaired LendingLedger.unimpaired; ring
  · rw [hYU]; unfold LendingLedger.interestBooked LendingLedger.interestRemoved LendingLedger.interestDefaulted; ring

end XRPL.Model.Lending
