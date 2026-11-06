import XRPL.Properties.Lending.Ledger.Common.AccountingDefs
import XRPL.Properties.Lending.Ledger.Common.RedemptionDebt
import XRPL.Properties.Lending.Loan.Common.Reserved

/-! # AssetsReserved on a reachable ledger

AssetsReserved is the sum of PrincipalOutstanding over the pending loans. A pending LoanSet adds its
principal, an accept or a pending delete takes it out, and every other transaction keeps both sides. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- Taking a whole number of base units, at most the balance, out of a balance below `2^63` base units is
exact. -/
lemma Number.operator_add_neg_toRat_of_grid (x y d : Number) (s : Int) (hx : x.isNormalized)
    (hy : y.isNormalized) (hxg : ∃ a : ℕ, x.toRat = (a : ℚ) * 10 ^ s) (hyg : ∃ c : ℕ, y.toRat = (c : ℚ) * 10 ^ s)
    (hle : y.toRat ≤ x.toRat) (hlt : x.toRat < 2 ^ 63 * 10 ^ s) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hok : x.operator_add y.operator_neg .to_nearest = .ok d) : d.toRat = x.toRat - y.toRat := by
  obtain ⟨a, ha⟩ := hxg
  obtain ⟨c, hc⟩ := hyg
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hca : c ≤ a := by
    have : (c : ℚ) * 10 ^ s ≤ (a : ℚ) * 10 ^ s := by rw [← ha, ← hc]; exact hle
    exact_mod_cast le_of_mul_le_mul_right this hp
  have ha63 : a < 2 ^ 63 := by
    have : (a : ℚ) * 10 ^ s < (2 ^ 63 : ℕ) * 10 ^ s := by push_cast; rw [← ha]; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  have h := Number.operator_add_toRat_of_grid _ _ d a (-(c : ℤ)) s hx (Number.operator_neg_isNormalized _ hy)
    (by rw [ha]; norm_cast) (by rw [Number.toRat_neg, hc]; push_cast; ring) ⟨by omega, by omega⟩ hs hok
  rw [h, ha, hc]; push_cast; ring

/-- A management action keeps the pending flag. -/
lemma Loan.manage_isPending (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (r : LoanWithPool Vault) (h : (loan.manage action v now).run = .ok (.ok r)) :
    r.loan'.isPending = loan.isPending := by
  cases action with
  | impair => exact Loan.manageImpair_isPending loan v now r h
  | unimpair => exact Loan.manageUnimpair_isPending loan v r h
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok
    exact Loan.manageDefault_isPending loan v _ ‹_›

/-- What every reachable ledger keeps about AssetsReserved: it is the sum of PrincipalOutstanding over the
pending loans, at most `10^16` base units, and the asset stores each pending loan's principal exactly. -/
structure LendingLedger.ReservedInv (l : LendingLedger) : Prop where
  scale : l.ScaleInv
  bound : l.vault.assetsReserved.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent
  exact : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e → e.loan.isPending = true →
    STAmount.Representable l.vault.numericType e.loan.principalOutstanding.toRat
  sum : l.vault.assetsReserved.toRat = l.principalSum (·.isPending)

/-- AssetsReserved is a whole number of base units. -/
lemma LendingLedger.ReservedInv.grid {l : LendingLedger} (hinv : l.ReservedInv) :
    ∃ n : ℕ, l.vault.assetsReserved.toRat = (n : ℚ) * 10 ^ l.vault.baseExponent := by
  rw [hinv.sum]; exact hinv.scale.principalSum_grid _

/-- A loan effect keeps the invariant when it moves AssetsReserved by what its slot held before and
after, stays inside the bound and writes a pending loan only with an exact principal. -/
lemma LendingLedger.ReservedInv.commitLoan {l : LendingLedger} (hinv : l.ReservedInv) {u : LoanEffect}
    (hscale : (l.commitLoan u).ScaleInv) (hs : Vault.KeepsSettings l.vault u.vault)
    (hsum : u.vault.assetsReserved.toRat + LoanEntry.principalIf (·.isPending) (l.loan? u.loanIndex) =
      l.vault.assetsReserved.toRat + LoanEntry.principalIf (·.isPending) u.loan)
    (hbound : u.vault.assetsReserved.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hexact : ∀ e', u.loan = some e' → e'.loan.isPending = true →
      STAmount.Representable l.vault.numericType e'.loan.principalOutstanding.toRat) :
    (l.commitLoan u).ReservedInv := by
  have hv : (l.commitLoan u).vault = u.vault := rfl
  have hc := l.principalSum_commitLoan u (·.isPending)
  refine ⟨hscale, by rw [hv, hs.baseExponent_eq]; exact hbound, fun j e he hp => ?_, ?_⟩
  · rw [hv, hs.numericType]
    rw [LendingLedger.loan?_commitLoan] at he
    by_cases hj : j = (if u.loanIndex < l.loans.length then u.loanIndex else l.loans.length)
    · rw [if_pos hj] at he; exact hexact e he hp
    · rw [if_neg hj] at he; exact hinv.exact j e he hp
  · rw [hv]
    have := hinv.sum
    linarith

/-- A loan operation that leaves its loan active, on an active loan, keeps AssetsReserved and the sum. -/
private lemma LendingLedger.ReservedInv.ofActive {l : LendingLedger} (hinv : l.ReservedInv) {i : Nat} {e : LoanEntry}
    {broker : LoanBroker} {loan loan' : Loan} {v' : Vault} (he : l.loan? i = some e)
    (hw : e.loan.withBroker broker = .ok loan)
    (hscale : (l.commitLoan (LoanEffect.ofLoan i e loan' v')).ScaleInv) (hs : Vault.KeepsSettings l.vault v')
    (hp : loan.isPending = false) (hp' : loan'.isPending = false) (har : v'.assetsReserved = l.vault.assetsReserved) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).ReservedInv := by
  have hep : e.loan.isPending = false := by rw [← (congrArg RawLoan.isPending (Loan.withBroker_eq hw) :)]; exact hp
  refine hinv.commitLoan hscale hs ?_ (by show v'.assetsReserved.toRat ≤ _; rw [har]; exact hinv.bound)
    fun e' he' hpe => ?_
  · show v'.assetsReserved.toRat + LoanEntry.principalIf (·.isPending) (l.loan? i) =
      l.vault.assetsReserved.toRat + LoanEntry.principalIf (·.isPending) (some { e with loan := loan' })
    rw [he, har]
    simp [LoanEntry.principalIf, hep, hp']
  · simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
    subst he'
    rw [hp'] at hpe; cases hpe

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.ReservedInv.loan_step {l : LendingLedger} (hinv : l.ReservedInv) {tx : LendingTx}
    (hpre : (tx.preflight l).isTesSuccess = true) {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (l.commitLoan u).ReservedInv := by
  have hs := l.applyLoan_keepsSettings tx u hu
  have hscale := hinv.scale.loan_step hpre hu
  have hbase := Vault.baseExponent_scale_range l.vault
  have hb10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hlt : l.vault.assetsReserved.toRat < 2 ^ 63 * 10 ^ l.vault.baseExponent :=
    lt_of_le_of_lt hinv.bound (mul_lt_mul_of_pos_right (by norm_num) hb10)
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
    have hnt := hinv.scale.brokers i broker hb
    obtain ⟨hAR, hfit, hPO, hpend, -⟩ := Loan.create_reserved broker l.vault principal rates fees _ ao twoStep r hpn
      hpos hst hnt hinv.grid hcr
    have hnone : l.loan? l.loans.length = none := by
      unfold LendingLedger.loan?; rw [List.getElem?_eq_none (le_refl _)]; rfl
    refine hinv.commitLoan hscale hs ?_ ?_ fun e' he' hpe => ?_
    · show r.pool'.assetsReserved.toRat + LoanEntry.principalIf (·.isPending) (l.loan? l.loans.length) =
        l.vault.assetsReserved.toRat + LoanEntry.principalIf (·.isPending) (some { brokerIndex := i, loan := r.loan' })
      rw [hnone, hAR]
      simp only [LoanEntry.principalIf, hpend, hPO, add_zero]
    · show r.pool'.assetsReserved.toRat ≤ _
      rw [hAR]
      have hp0 : 0 ≤ principal.toRat := hpos.le
      split <;> linarith [hinv.bound]
    · simp only [LoanEffect.ofCreate, Option.some.injEq] at he'
      subst he'
      rw [hPO, ← hnt]
      exact (STAmount.isRounded_eq_false_iff _ principal hpn hpos.le).mp hst
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    have hraw := Loan.withBroker_eq hw
    have hp := Loan.canAccept_pending loan l.vault l.now hc
    obtain ⟨hAR, hp', -, -⟩ := Loan.accept_reserved loan l.vault r hr
    have hep : e.loan.isPending = true := by rw [← (congrArg RawLoan.isPending hraw :)]; exact hp
    have hePO : loan.principalOutstanding = e.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have hc := l.principalSum_commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') (·.isPending)
    have hold : LoanEntry.principalIf (·.isPending) (l.loan? i) = e.loan.principalOutstanding.toRat := by
      rw [he]; simp [LoanEntry.principalIf, hep]
    have hnew : LoanEntry.principalIf (·.isPending) (some { e with loan := r.loan' }) = 0 := by
      simp [LoanEntry.principalIf, hp']
    have hle : loan.principalOutstanding.toRat ≤ l.vault.assetsReserved.toRat := by
      have := (l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool')).principalSum_nonneg (·.isPending)
      change _ + LoanEntry.principalIf (·.isPending) (l.loan? i) = _ + LoanEntry.principalIf (·.isPending)
        (some { e with loan := r.loan' }) at hc
      rw [hold, hnew] at hc
      rw [hePO, hinv.sum]; linarith
    have hval := Number.operator_add_neg_toRat_of_grid _ _ _ _ l.vault.wf.assetsReserved_norm
      loan.wf.principalOutstanding_norm hinv.grid (by rw [hePO]; exact hinv.scale.principal_grid he) hle hlt hsb hAR
    have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    refine hinv.commitLoan hscale hs ?_ ?_ fun e' he' hpe => ?_
    · show r.pool'.assetsReserved.toRat + LoanEntry.principalIf (·.isPending) (l.loan? i) =
        l.vault.assetsReserved.toRat + LoanEntry.principalIf (·.isPending) (some { e with loan := r.loan' })
      rw [hold, hnew, hval, hePO]; ring
    · show r.pool'.assetsReserved.toRat ≤ _
      rw [hval]; linarith [hinv.bound]
    · simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
      subst he'
      rw [hp'] at hpe; cases hpe
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, hu'⟩ := l.applyLoan_delete_inv u i hu
    have hv : u.vault = r.pool' := by rw [hu']
    have hi : u.loanIndex = i := by rw [hu']
    have hlo : u.loan = none := by rw [hu']
    have hraw := Loan.withBroker_eq hw
    have hlb : loan.broker = broker := (congrArg RawLoan.broker hraw :)
    have hePO : loan.principalOutstanding = e.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have hpe : loan.isPending = e.loan.isPending := (congrArg RawLoan.isPending hraw :)
    have hc := l.principalSum_commitLoan u (·.isPending)
    rw [hi, hlo, he] at hc
    refine hinv.commitLoan hscale hs ?_ ?_ fun e' he' => by rw [hlo] at he'; cases he'
    · rw [hv, hi, hlo, he]
      cases hp : loan.isPending
      · rw [Loan.delete_active_vault loan l.vault r hp hr]
        simp [LoanEntry.principalIf, ← hpe, hp]
      · obtain ⟨principal', hround, hAR⟩ := Loan.delete_pending_reserved loan l.vault r hp hr
        have hep : e.loan.isPending = true := by rw [← hpe]; exact hp
        -- the asset stores the principal, so the rounding keeps it
        have hrep : STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false := by
          rw [STAmount.isRounded_eq_false_iff _ _ loan.wf.principalOutstanding_norm
            ((loan.exact.principalOutstanding_nonneg : 0 ≤ loan.principalOutstanding.toRat)),
            hlb, hinv.scale.brokers _ broker hb, hePO]
          exact hinv.exact i e he hep
        have hp' := STAmount.roundToNumericType_of_isRounded_false _ _ _ loan.wf.principalOutstanding_norm hrep hround
        have hle : principal'.toRat ≤ l.vault.assetsReserved.toRat := by
          have := (l.commitLoan u).principalSum_nonneg (·.isPending)
          simp only [LoanEntry.principalIf, hep, if_true, add_zero] at hc
          rw [hp', hePO, hinv.sum]; linarith
        have hval := Number.operator_add_neg_toRat_of_grid _ _ _ _ l.vault.wf.assetsReserved_norm
          (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround) hinv.grid
          (by rw [hp', hePO]; exact hinv.scale.principal_grid he) hle hlt hsb hAR
        simp only [LoanEntry.principalIf, hep, if_true, add_zero]
        rw [hval, hp', hePO]; ring
    · rw [hv]
      have := (Loan.delete_debt loan l.vault r hr).2
      linarith [hinv.bound]
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    exact hinv.ofActive he hw hscale hs (Loan.canManage_not_pending loan action l.now hc)
      (by rw [Loan.manage_isPending loan action _ _ r hr]; exact Loan.canManage_not_pending loan action l.now hc)
      (Loan.manage_debt loan action l.vault l.now r hr).2
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    exact hinv.ofActive he hw hscale hs (Loan.canPay_not_pending loan paymentType hc)
      (by rw [Loan.pay_isPending loan _ _ _ _ r hr]; exact Loan.canPay_not_pending loan paymentType hc)
      (Loan.pay_debt loan l.vault paymentType amount l.now r hr).2
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.ReservedInv.step {l l' : LendingLedger} (hinv : l.ReservedInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.ReservedInv := by
  have hpre := (LendingLedger.apply_checked h).1
  have hscale := hinv.scale.step h
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hrest : (l.commitVault u).loans = l.loans ∧ (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    have hbe : u.vault.baseExponent = l.vault.baseExponent := by
      unfold XRPL.Model.SingleAssetVault.Vault.baseExponent; rw [hk.numericType, hk.scale]
    have hl : ∀ j, (l.commitVault u).loan? j = l.loan? j := fun j => by
      unfold LendingLedger.loan?; rw [hrest.1]
    refine ⟨hscale, ?_, fun j e he hp => ?_, ?_⟩ <;> rw [hrest.2]
    · rw [hk.assetsReserved, hbe]; exact hinv.bound
    · rw [hl] at he; rw [hk.numericType]; exact hinv.exact j e he hp
    · rw [hk.assetsReserved, LendingLedger.principalSum_of_loans hrest.1]; exact hinv.sum
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    exact ⟨hscale, hinv.bound, hinv.exact, hinv.sum⟩
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
    exact ⟨hscale, hinv.bound, hinv.exact, hinv.sum⟩
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hscale, hinv.bound, hinv.exact, hinv.sum⟩

/-- A genesis ledger reserves nothing and has no loans. -/
lemma LendingLedger.Genesis.reservedInv {g : LendingLedger} (hg : g.Genesis) : g.ReservedInv := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  have har : g.vault.assetsReserved = Number.zero := (congrArg RawVault.assetsReserved hraw :)
  have hnone : ∀ j, g.loan? j = none := fun j => by unfold LendingLedger.loan?; rw [hg.no_loans]; rfl
  refine ⟨hg.scaleInv, ?_, fun j e he _ => (by rw [hnone] at he; cases he), ?_⟩
  · rw [har, Number.toRat_zero]; positivity
  · rw [har, Number.toRat_zero]; unfold LendingLedger.principalSum; rw [hg.no_loans]; rfl

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.reservedInv {l : LendingLedger} (hr : l.Reachable) : l.ReservedInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.reservedInv) (fun _ _ _ hi ha => hi.step ha) hr

/-- Proof body of the AssetsReserved line of `Lending.Reachable.ledger_sums`. -/
lemma LendingLedger.reserved_pending_proof (l : LendingLedger) (hr : l.Reachable) :
    l.vault.assetsReserved.toRat = l.principalSum (·.isPending) :=
  hr.reservedInv.sum

end XRPL.Model.Lending
