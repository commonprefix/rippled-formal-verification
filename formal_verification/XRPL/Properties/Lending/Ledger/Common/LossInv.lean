import XRPL.Properties.Lending.Ledger.Common.ReservedInv
import XRPL.Properties.Lending.Loan.Common.Loss

/-! # LossUnrealized on a reachable ledger

LossUnrealized is the sum of PrincipalOutstanding over the impaired loans. Impair adds the loan's principal,
and unimpair, a default or a payment takes it off. A delete keeps both sides, as the loan adds nothing. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- What every reachable ledger keeps about LossUnrealized: it is the sum of PrincipalOutstanding over the
impaired loans, AssetsDeployed and each principal stay within `10^16` base units, no pending loan is impaired. -/
structure LendingLedger.LossInv (l : LendingLedger) : Prop where
  reserved : l.ReservedInv
  deployed : l.vault.assetsDeployed.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent
  principal : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e →
    e.loan.principalOutstanding.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent
  active : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e → e.loan.isPending = true →
    e.loan.isImpaired = false
  sum : l.vault.lossUnrealized.toRat = l.principalSum (·.isImpaired)

/-- LossUnrealized is a whole number of base units. -/
lemma LendingLedger.LossInv.grid {l : LendingLedger} (hinv : l.LossInv) :
    ∃ n : ℕ, l.vault.lossUnrealized.toRat = (n : ℚ) * 10 ^ l.vault.baseExponent := by
  rw [hinv.sum]; exact hinv.reserved.scale.principalSum_grid _

/-- LossUnrealized is at most `10^16` base units. -/
lemma LendingLedger.LossInv.bound {l : LendingLedger} (hinv : l.LossInv) :
    l.vault.lossUnrealized.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent :=
  le_trans l.vault.exact.lossUnrealized_le hinv.deployed

/-- A loan effect keeps the invariant when it moves LossUnrealized by what its slot held before and after,
keeps AssetsDeployed inside the bound and writes a loan inside the bound that is not pending and impaired. -/
lemma LendingLedger.LossInv.commitLoan {l : LendingLedger} (hinv : l.LossInv) {u : LoanEffect}
    (hres : (l.commitLoan u).ReservedInv) (hs : Vault.KeepsSettings l.vault u.vault)
    (hsum : u.vault.lossUnrealized.toRat + LoanEntry.principalIf (·.isImpaired) (l.loan? u.loanIndex) =
      l.vault.lossUnrealized.toRat + LoanEntry.principalIf (·.isImpaired) u.loan)
    (hdep : u.vault.assetsDeployed.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hloan : ∀ e', u.loan = some e' →
      e'.loan.principalOutstanding.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
        (e'.loan.isPending = true → e'.loan.isImpaired = false)) :
    (l.commitLoan u).LossInv := by
  have hv : (l.commitLoan u).vault = u.vault := rfl
  have hc := l.principalSum_commitLoan u (·.isImpaired)
  refine ⟨hres, by rw [hv, hs.baseExponent_eq]; exact hdep, fun j e he => ?_, fun j e he hp => ?_, ?_⟩
  · rw [hv, hs.baseExponent_eq]
    rw [LendingLedger.loan?_commitLoan] at he
    by_cases hj : j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
    · rw [if_pos hj] at he; exact (hloan e he).1
    · rw [if_neg hj] at he; exact hinv.principal j e he
  · rw [LendingLedger.loan?_commitLoan] at he
    by_cases hj : j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
    · rw [if_pos hj] at he; exact (hloan e he).2 hp
    · rw [if_neg hj] at he; exact hinv.active j e he hp
  · rw [hv]
    have := hinv.sum
    linarith

/-- An operation on a stored loan keeps the invariant when it moves LossUnrealized by the loan's impaired principal
before and after, grows neither AssetsDeployed nor PrincipalOutstanding, and writes a loan that is not pending. -/
lemma LendingLedger.LossInv.ofLoan {l : LendingLedger} (hinv : l.LossInv) {i : Nat} {e : LoanEntry}
    {loan' : Loan} {v' : Vault} (he : l.loan? i = some e)
    (hres : (l.commitLoan (LoanEffect.ofLoan i e loan' v')).ReservedInv) (hs : Vault.KeepsSettings l.vault v')
    (hsum : v'.lossUnrealized.toRat + LoanEntry.principalIf (·.isImpaired) (some e) =
      l.vault.lossUnrealized.toRat + LoanEntry.principalIf (·.isImpaired) (some { e with loan := loan' }))
    (hdep : v'.assetsDeployed.toRat ≤ l.vault.assetsDeployed.toRat)
    (hpo : loan'.principalOutstanding.toRat ≤ e.loan.principalOutstanding.toRat)
    (hp' : loan'.isPending = false) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).LossInv := by
  refine hinv.commitLoan hres hs ?_ (by show v'.assetsDeployed.toRat ≤ _; linarith [hinv.deployed])
    fun e' he' => ?_
  · show v'.lossUnrealized.toRat + LoanEntry.principalIf (·.isImpaired) (l.loan? i) = _
    rw [he]; exact hsum
  · simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
    subst he'
    exact ⟨le_trans hpo (hinv.principal i e he), fun h => by rw [hp'] at h; cases h⟩

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.LossInv.loan_step {l : LendingLedger} (hinv : l.LossInv) {tx : LendingTx}
    (hpre : (tx.preflight l).isTesSuccess = true) {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (l.commitLoan u).LossInv := by
  have hs := l.applyLoan_keepsSettings tx u hu
  have hres := hinv.reserved.loan_step hpre hu
  have hbase := Vault.baseExponent_scale_range l.vault
  have hb10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hlt : l.vault.lossUnrealized.toRat < 2 ^ 63 * 10 ^ l.vault.baseExponent :=
    lt_of_le_of_lt hinv.bound (mul_lt_mul_of_pos_right (by norm_num) hb10)
  have hslot : ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.isImpaired = true →
      e.loan.principalOutstanding.toRat ≤ l.vault.lossUnrealized.toRat := fun i e he hi => by
    have := l.principalIf_le_sum (·.isImpaired) i
    rw [he] at this
    simp only [LoanEntry.principalIf, hi, if_true] at this
    rw [hinv.sum]; exact this
  have hsub : ∀ (i : Nat) (e : LoanEntry) (d : Number), l.loan? i = some e → e.loan.isImpaired = true →
      l.vault.lossUnrealized.operator_add e.loan.principalOutstanding.operator_neg .to_nearest = .ok d →
      d.toRat = l.vault.lossUnrealized.toRat - e.loan.principalOutstanding.toRat := fun i e d he hi hok =>
    Number.operator_add_neg_toRat_of_grid _ _ d _ l.vault.wf.lossUnrealized_norm e.loan.wf.principalOutstanding_norm
      hinv.grid (hinv.reserved.scale.principal_grid he) (hslot i e he hi) hlt hsb hok
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
    have hnt := hinv.reserved.scale.brokers i broker hb
    obtain ⟨-, -, hPO, -, himp⟩ := Loan.create_reserved broker l.vault principal rates fees _ ao twoStep r hpn
      hpos hst hnt hinv.reserved.grid hcr
    obtain ⟨hLU, hAD, hpb⟩ := Loan.create_lossStep broker l.vault principal rates fees _ ao twoStep r hpn hpos hst hcr
    have hnone : l.loan? l.loans.length = none := by
      unfold LendingLedger.loan?; rw [List.getElem?_eq_none (le_refl _)]; rfl
    refine hinv.commitLoan hres hs ?_ hAD fun e' he' => ?_
    · show r.pool'.lossUnrealized.toRat + LoanEntry.principalIf (·.isImpaired) (l.loan? l.loans.length) =
        l.vault.lossUnrealized.toRat + LoanEntry.principalIf (·.isImpaired) (some { brokerIndex := i, loan := r.loan' })
      rw [hnone, hLU]
      simp [LoanEntry.principalIf, himp]
    · simp only [LoanEffect.ofCreate, Option.some.injEq] at he'
      subst he'
      exact ⟨by rw [hPO]; exact hpb, fun _ => himp⟩
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    have hraw := Loan.withBroker_eq hw
    have hep : e.loan.isPending = true := by
      rw [← (congrArg RawLoan.isPending hraw :)]; exact Loan.canAccept_pending loan l.vault l.now hc
    have hei : e.loan.isImpaired = false := hinv.active i e he hep
    obtain ⟨-, hp', hPO', hI'⟩ := Loan.accept_reserved loan l.vault r hr
    obtain ⟨hLU, hAD⟩ := Loan.accept_lossStep loan l.vault r hr
    have hI'' : r.loan'.isImpaired = false := by rw [hI', (congrArg RawLoan.isImpaired hraw :)]; exact hei
    refine hinv.ofLoan he hres hs ?_ (by rw [hAD]) (by rw [hPO', (congrArg RawLoan.principalOutstanding hraw :)]) hp'
    rw [hLU]
    simp [LoanEntry.principalIf, hei, hI'']
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, hu'⟩ := l.applyLoan_delete_inv u i hu
    have hv : u.vault = r.pool' := by rw [hu']
    have hi : u.loanIndex = i := by rw [hu']
    have hlo : u.loan = none := by rw [hu']
    have hraw := Loan.withBroker_eq hw
    obtain ⟨hLU, hAD⟩ := Loan.delete_lossStep loan l.vault r hr
    -- the deleted loan adds nothing to the sum: a pending loan is not impaired, an active one owes nothing
    have hold : LoanEntry.principalIf (·.isImpaired) (some e) = 0 := by
      cases hp : loan.isPending
      · have hpr := Loan.canDelete_active_paid loan hc hp
        rw [(congrArg RawLoan.paymentRemaining hraw :)] at hpr
        have hz := (e.loan.valid.paid_zeroed hpr).2.1
        simp only [LoanEntry.principalIf]
        split
        · rw [show e.loan.principalOutstanding = e.loan.toRawLoan.principalOutstanding from rfl, hz,
            Number.toRat_zero]
        · rfl
      · have hep : e.loan.isPending = true := by rw [← (congrArg RawLoan.isPending hraw :)]; exact hp
        simp [LoanEntry.principalIf, hinv.active i e he hep]
    refine hinv.commitLoan hres hs ?_ ?_ fun e' he' => by rw [hlo] at he'; cases he'
    · rw [hv, hi, hlo, he, hold, hLU]
      simp [LoanEntry.principalIf]
    · rw [hv]; linarith [hinv.deployed]
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    have hraw := Loan.withBroker_eq hw
    have hePO : loan.principalOutstanding = e.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have heI : loan.isImpaired = e.loan.isImpaired := (congrArg RawLoan.isImpaired hraw :)
    have hnp := Loan.canManage_not_pending loan action l.now hc
    have hp' : r.loan'.isPending = false := by rw [Loan.manage_isPending loan action _ _ r hr]; exact hnp
    have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    cases action with
    | impair =>
      have hni := Loan.canManage_impair_not_impaired loan l.now hc
      obtain ⟨hLU, hAD, hI', hPO'⟩ := Loan.manageImpair_lossStep loan l.vault l.now r hr
      -- the principal joins LossUnrealized exactly, both are within `10^16` base units
      obtain ⟨n, hn⟩ := hinv.grid
      obtain ⟨m, hm⟩ := hinv.reserved.scale.principal_grid he
      have hn16 : n ≤ 10 ^ 16 := by
        have : (n : ℚ) * 10 ^ l.vault.baseExponent ≤ (10 ^ 16 : ℕ) * 10 ^ l.vault.baseExponent := by
          push_cast; rw [← hn]; exact hinv.bound
        exact_mod_cast le_of_mul_le_mul_right this hb10
      have hm16 : m ≤ 10 ^ 16 := by
        have : (m : ℚ) * 10 ^ l.vault.baseExponent ≤ (10 ^ 16 : ℕ) * 10 ^ l.vault.baseExponent := by
          push_cast; rw [← hm]; exact hinv.principal i e he
        exact_mod_cast le_of_mul_le_mul_right this hb10
      have hval := Number.operator_add_toRat_of_grid _ _ _ n m _ l.vault.wf.lossUnrealized_norm
        loan.wf.principalOutstanding_norm (by rw [hn]; norm_cast) (by rw [hePO, hm]; norm_cast)
        ⟨by omega, by omega⟩ hsb hLU
      refine hinv.ofLoan he hres hs ?_ (by rw [hAD]) (by rw [hPO', hePO]) hp'
      have hei : e.loan.isImpaired = false := by rw [← heI]; exact hni
      simp only [LoanEntry.principalIf, hei, hI', if_true, Bool.false_eq_true, if_false, add_zero]
      rw [hval, hn, hPO', hePO, hm]; push_cast; ring
    | unimpair =>
      have hii := Loan.canManage_unimpair_impaired loan l.now hc
      obtain ⟨hLU, hAD, hI', hPO'⟩ := Loan.manageUnimpair_lossStep loan l.vault r hr
      have hei : e.loan.isImpaired = true := by rw [← heI]; exact hii
      have hval := hsub i e _ he hei (by rw [← hePO]; exact hLU)
      refine hinv.ofLoan he hres hs ?_ (by rw [hAD]) (by rw [hPO', hePO]) hp'
      simp only [LoanEntry.principalIf, hei, hI', if_true, Bool.false_eq_true, if_false, add_zero]
      rw [hval]; ring
    | default =>
      simp only [Loan.manage] at hr
      unfold_ter at hr
      walk_ok
      rename_i rd hd
      obtain ⟨hLU, hAD, hPO', hI'⟩ := Loan.manageDefault_lossStep loan l.vault rd hd
      have hp'' : rd.loan'.isPending = false := by rw [Loan.manageDefault_isPending loan _ rd hd]; exact hnp
      refine hinv.ofLoan he hres hs ?_ hAD (by rw [hPO', Number.toRat_zero, ← hePO]; exact hp0) hp''
      -- the defaulted loan owes nothing, and an impaired one releases its principal
      have hnew : LoanEntry.principalIf (·.isImpaired) (some { e with loan := rd.loan' }) = 0 := by
        simp only [LoanEntry.principalIf]
        split
        · rw [hPO', Number.toRat_zero]
        · rfl
      rw [hnew]
      cases hi : loan.isImpaired
      · have hei : e.loan.isImpaired = false := by rw [← heI]; exact hi
        rw [hi, if_neg Bool.false_ne_true, Number.operator_add_zero_right, Except.ok.injEq] at hLU
        simp only [LoanEntry.principalIf, hei, Bool.false_eq_true, if_false, add_zero]
        rw [← hLU]
      · have hei : e.loan.isImpaired = true := by rw [← heI]; exact hi
        rw [hi, if_pos rfl] at hLU
        have hval := hsub i e _ he hei (by rw [← hePO]; exact hLU)
        simp only [LoanEntry.principalIf, hei, if_true, add_zero]
        rw [hval]; ring
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    have hraw := Loan.withBroker_eq hw
    have hePO : loan.principalOutstanding = e.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have heI : loan.isImpaired = e.loan.isImpaired := (congrArg RawLoan.isImpaired hraw :)
    have hp' : r.loan'.isPending = false := by
      rw [Loan.pay_isPending loan _ _ _ _ r hr]; exact Loan.canPay_not_pending loan paymentType hc
    obtain ⟨himpd, hnot, hAD⟩ := Loan.pay_lossStep loan l.vault paymentType amount l.now r hr
    have hI' := Loan.pay_isImpaired loan l.vault paymentType amount l.now r hr
    have hPO' := (Loan.pay_outstanding_le loan l.vault paymentType amount l.now r hr).1
    refine hinv.ofLoan he hres hs ?_ hAD (by rw [← hePO]; exact hPO') hp'
    cases hi : loan.isImpaired
    · have hei : e.loan.isImpaired = false := by rw [← heI]; exact hi
      simp only [LoanEntry.principalIf, hei, hI', Bool.false_eq_true, if_false, add_zero]
      rw [hnot hi]
    · have hei : e.loan.isImpaired = true := by rw [← heI]; exact hi
      have hval := hsub i e _ he hei (by rw [← hePO]; exact himpd hi)
      simp only [LoanEntry.principalIf, hei, hI', if_true, Bool.false_eq_true, if_false, add_zero]
      rw [hval]; ring
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.LossInv.step {l l' : LendingLedger} (hinv : l.LossInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.LossInv := by
  have hpre := (LendingLedger.apply_checked h).1
  have hres := hinv.reserved.step h
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hrest : (l.commitVault u).loans = l.loans ∧ (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hbe : u.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hk.numericType, hk.scale]
    have hl : ∀ j, (l.commitVault u).loan? j = l.loan? j := fun j => by
      unfold LendingLedger.loan?; rw [hrest.1]
    refine ⟨hres, ?_, fun j e he => ?_, fun j e he hp => ?_, ?_⟩
    · rw [hrest.2, hk.assetsDeployed, hbe]; exact hinv.deployed
    · rw [hl] at he; rw [hrest.2, hbe]; exact hinv.principal j e he
    · rw [hl] at he; exact hinv.active j e he hp
    · rw [hrest.2, hk.lossUnrealized, LendingLedger.principalSum_of_loans hrest.1]; exact hinv.sum
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact ⟨hres, hinv.deployed, hinv.principal, hinv.active, hinv.sum⟩
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    exact hinv.loan_step hpre hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hv hb hl
  · -- vaultDelete only sets the deleted flag
    simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    exact ⟨hres, hinv.deployed, hinv.principal, hinv.active, hinv.sum⟩
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hres, hinv.deployed, hinv.principal, hinv.active, hinv.sum⟩

/-- A genesis ledger has lost and lent nothing and has no loans. -/
lemma LendingLedger.Genesis.lossInv {g : LendingLedger} (hg : g.Genesis) : g.LossInv := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  have hlu : g.vault.lossUnrealized = Number.zero := (congrArg RawVault.lossUnrealized hraw :)
  have had : g.vault.assetsDeployed = Number.zero := (congrArg RawVault.assetsDeployed hraw :)
  have hnone : ∀ j, g.loan? j = none := fun j => by unfold LendingLedger.loan?; rw [hg.no_loans]; rfl
  refine ⟨hg.reservedInv, ?_, fun j e he => (by rw [hnone] at he; cases he),
    fun j e he _ => (by rw [hnone] at he; cases he), ?_⟩
  · rw [had, Number.toRat_zero]; positivity
  · rw [hlu, Number.toRat_zero]; unfold LendingLedger.principalSum; rw [hg.no_loans]; rfl

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.lossInv {l : LendingLedger} (hr : l.Reachable) : l.LossInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.lossInv) (fun _ _ _ hi ha => hi.step ha) hr

/-- Proof body of the LossUnrealized line of `Lending.Reachable.ledger_sums`. -/
lemma LendingLedger.loss_impaired_proof (l : LendingLedger) (hr : l.Reachable) :
    l.vault.lossUnrealized.toRat = l.principalSum (·.isImpaired) :=
  hr.lossInv.sum

end XRPL.Model.Lending
