import XRPL.Properties.Lending.Ledger.Common.LossInv
import XRPL.Properties.Lending.Loan.Common.Debt

/-! # DebtTotal and AssetsDeployed on a reachable ledger

A broker's DebtTotal is the sum of PrincipalOutstanding over its loans, and AssetsDeployed the sum over all
loans. Every loan transaction moves the loan's principal and the two balances by the same whole units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- PrincipalOutstanding of a slot's loan when it is on broker `j`, else zero. -/
def LoanEntry.principalOn (j : Nat) : Option LoanEntry → ℚ
  | some e => if e.brokerIndex = j then e.loan.principalOutstanding.toRat else 0
  | none => 0

/-- Σ PrincipalOutstanding of the stored loans on broker `j`. -/
def LendingLedger.brokerPrincipal (l : LendingLedger) (j : Nat) : ℚ :=
  (l.loans.map (LoanEntry.principalOn j)).sum

/-- Rewriting one slot changes a sum of slots by what the slot held before and after. -/
lemma List.sum_map_storeSlot {α : Type} (f : Option α → ℚ) (hf : f none = 0) (xs : List (Option α)) (i : Nat)
    (x : Option α) : ((storeSlot xs i x).map f).sum + f (xs[i]?).join = (xs.map f).sum + f x := by
  unfold storeSlot
  split
  · rename_i hi
    rw [List.map_set, List.getElem?_eq_getElem hi, Option.join_some]
    have := List.sum_set_add (xs.map f) i (f x) (by simpa using hi)
    simpa using this
  · rename_i hi
    rw [List.getElem?_eq_none (by omega), List.map_append, List.sum_append]
    simp [hf]

/-- A loan effect changes a broker's sum by its slot. -/
private lemma LendingLedger.brokerPrincipal_commitLoan (l : LendingLedger) (u : LoanEffect) (j : Nat) :
    (l.commitLoan u).brokerPrincipal j + LoanEntry.principalOn j (l.loan? u.loanIndex) =
      l.brokerPrincipal j + LoanEntry.principalOn j u.loan :=
  List.sum_map_storeSlot (LoanEntry.principalOn j) rfl l.loans u.loanIndex u.loan

/-- A slot adds at least zero to a broker's sum. -/
lemma LoanEntry.principalOn_nonneg (j : Nat) (o : Option LoanEntry) : 0 ≤ LoanEntry.principalOn j o := by
  cases o with
  | none => exact le_refl _
  | some e =>
    simp only [LoanEntry.principalOn]
    split
    · exact (e.loan.exact.principalOutstanding_nonneg : 0 ≤ e.loan.principalOutstanding.toRat)
    · exact le_refl _

/-- A broker's sum is at least zero. -/
private lemma LendingLedger.brokerPrincipal_nonneg (l : LendingLedger) (j : Nat) : 0 ≤ l.brokerPrincipal j :=
  List.sum_nonneg fun _ hx => by
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
    exact LoanEntry.principalOn_nonneg j o

/-- A broker's sum is at most the sum over all loans. -/
lemma LendingLedger.brokerPrincipal_le (l : LendingLedger) (j : Nat) :
    l.brokerPrincipal j ≤ l.principalSum (fun _ => true) := by
  unfold LendingLedger.brokerPrincipal LendingLedger.principalSum
  apply List.sum_le_sum
  intro o _
  cases o with
  | none => exact le_refl _
  | some e =>
    simp only [LoanEntry.principalOn, LoanEntry.principalIf, if_true]
    split
    · exact le_refl _
    · exact (e.loan.exact.principalOutstanding_nonneg : 0 ≤ e.loan.principalOutstanding.toRat)

/-- One slot adds at most a broker's whole sum. -/
lemma LendingLedger.principalOn_le_sum (l : LendingLedger) (j i : Nat) :
    LoanEntry.principalOn j (l.loan? i) ≤ l.brokerPrincipal j := by
  have hnn : ∀ x ∈ l.loans.map (LoanEntry.principalOn j), 0 ≤ x := fun _ hx => by
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
    exact LoanEntry.principalOn_nonneg j o
  unfold LendingLedger.loan?
  cases h : l.loans[i]? with
  | none => exact List.sum_nonneg hnn
  | some o => exact List.single_le_sum hnn _ (List.mem_map_of_mem (List.mem_of_getElem? h))

/-- A broker with no stored loans has an empty sum. -/
private lemma LendingLedger.brokerPrincipal_eq_zero (l : LendingLedger) (j : Nat) (h : l.loansOf j = 0) :
    l.brokerPrincipal j = 0 := by
  unfold LendingLedger.loansOf at h
  unfold LendingLedger.brokerPrincipal
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
  cases o with
  | none => rfl
  | some e =>
    have hne : ¬ e.brokerIndex = j := by
      intro hj
      have := (List.countP_pos_iff (p := fun o : Option LoanEntry => o.any (·.brokerIndex == j))).mpr
        ⟨some e, ho, by simp only [Option.any_some, hj, beq_self_eq_true]⟩
      omega
    simp [LoanEntry.principalOn, hne]

/-- A broker's sum is a whole number of base units. -/
lemma LendingLedger.ScaleInv.brokerPrincipal_grid {l : LendingLedger} (hinv : l.ScaleInv) (j : Nat) :
    ∃ n : ℕ, l.brokerPrincipal j = (n : ℚ) * 10 ^ l.vault.baseExponent := by
  have hslot : ∀ o ∈ l.loans, ∃ m : ℕ, LoanEntry.principalOn j o = (m : ℚ) * 10 ^ l.vault.baseExponent := by
    intro o ho
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
    cases o with
    | none => exact ⟨0, by simp [LoanEntry.principalOn]⟩
    | some e =>
      have he : l.loan? i = some e := by unfold LendingLedger.loan?; rw [hi]; rfl
      obtain ⟨m, hm⟩ := hinv.principal_grid he
      simp only [LoanEntry.principalOn]
      split
      · exact ⟨m, hm⟩
      · exact ⟨0, by simp⟩
  unfold LendingLedger.brokerPrincipal
  generalize l.loans = xs at hslot
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons o os ih =>
    obtain ⟨m, hm⟩ := hslot o List.mem_cons_self
    obtain ⟨n, hn⟩ := ih fun o' ho' => hslot o' (List.mem_cons_of_mem _ ho')
    exact ⟨m + n, by rw [List.map_cons, List.sum_cons, hm, hn]; push_cast; ring⟩

/-- A whole number of units, at least zero, is a natural number of units. -/
lemma Number.OnGrid.nat {s : Int} {x : Number} (hx : Number.OnGrid s x) (h0 : 0 ≤ x.toRat) :
    ∃ a : ℕ, x.toRat = (a : ℚ) * 10 ^ s := by
  obtain ⟨-, k, hk⟩ := hx
  have hp : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have hk0 : 0 ≤ k := by
    have : (0 : ℚ) ≤ (k : ℚ) * 10 ^ s := hk ▸ h0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  refine ⟨k.toNat, ?_⟩
  rw [hk, show ((k.toNat : ℕ) : ℚ) = (k : ℚ) by exact_mod_cast Int.toNat_of_nonneg hk0]

/-- A natural number of units is on the grid. -/
lemma Number.OnGrid.of_nat {s : Int} {x : Number} (hx : x.isNormalized) (a : ℕ) (h : x.toRat = (a : ℚ) * 10 ^ s) :
    Number.OnGrid s x := ⟨hx, a, by rw [h]; push_cast; rfl⟩

/-- What every reachable ledger keeps about DebtTotal and AssetsDeployed: each stored broker's DebtTotal is
the sum over its loans and AssetsDeployed the sum over all loans, beside the loss and count invariants. -/
structure LendingLedger.DebtInv (l : LendingLedger) : Prop where
  loss : l.LossInv
  count : l.LoanCountInv
  deployed : l.vault.assetsDeployed.toRat = l.principalSum (fun _ => true)
  debt : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.debtTotal.toRat = l.brokerPrincipal j

/-- A loan effect keeps the invariant when it moves its broker's DebtTotal and AssetsDeployed by what its slot
held before and after, and keeps the slot on the same broker. -/
lemma LendingLedger.DebtInv.commitLoan {l : LendingLedger} (hinv : l.DebtInv) {u : LoanEffect}
    {b : LoanBroker} (hb : l.broker? u.brokerIndex = some b)
    (hloss : (l.commitLoan u).LossInv) (hcount : (l.commitLoan u).LoanCountInv)
    (hold : ∀ e, l.loan? u.loanIndex = some e → e.brokerIndex = u.brokerIndex)
    (hnew : ∀ e, u.loan = some e → e.brokerIndex = u.brokerIndex)
    (hdebt : u.broker.debtTotal.toRat + LoanEntry.principalOn u.brokerIndex (l.loan? u.loanIndex) =
      b.debtTotal.toRat + LoanEntry.principalOn u.brokerIndex u.loan)
    (hAD : u.vault.assetsDeployed.toRat + LoanEntry.principalIf (fun _ => true) (l.loan? u.loanIndex) =
      l.vault.assetsDeployed.toRat + LoanEntry.principalIf (fun _ => true) u.loan) :
    (l.commitLoan u).DebtInv := by
  refine ⟨hloss, hcount, ?_, fun j b' hb' => ?_⟩
  · have hc := l.principalSum_commitLoan u (fun _ => true)
    show u.vault.assetsDeployed.toRat = _
    have := hinv.deployed
    linarith
  · have hc := l.brokerPrincipal_commitLoan u j
    rw [LendingLedger.broker?_commitLoan l u b hb] at hb'
    split at hb'
    · subst_vars
      cases hb'
      have := hinv.debt _ b hb
      linarith
    · rename_i hj
      have h1 : LoanEntry.principalOn j (l.loan? u.loanIndex) = 0 := by
        cases ho : l.loan? u.loanIndex with
        | none => rfl
        | some e =>
          simp only [LoanEntry.principalOn, hold e ho]
          rw [if_neg (Ne.symm hj)]
      have h2 : LoanEntry.principalOn j u.loan = 0 := by
        cases hn : u.loan with
        | none => rfl
        | some e =>
          simp only [LoanEntry.principalOn, hnew e hn]
          rw [if_neg (Ne.symm hj)]
      rw [h1, h2] at hc
      rw [hinv.debt j b' hb']
      linarith

/-- An operation on a stored loan keeps the invariant when it moves DebtTotal and AssetsDeployed by the change
in the loan's PrincipalOutstanding. -/
lemma LendingLedger.DebtInv.ofLoan {l : LendingLedger} (hinv : l.DebtInv) {i : Nat} {e : LoanEntry}
    {broker : LoanBroker} {loan loan' : Loan} {v' : Vault} (he : l.loan? i = some e)
    (hb : l.broker? e.brokerIndex = some broker) (hw : e.loan.withBroker broker = .ok loan)
    (hloss : (l.commitLoan (LoanEffect.ofLoan i e loan' v')).LossInv)
    (hcount : (l.commitLoan (LoanEffect.ofLoan i e loan' v')).LoanCountInv)
    (hdebt : loan'.broker.debtTotal.toRat + loan.principalOutstanding.toRat =
      broker.debtTotal.toRat + loan'.principalOutstanding.toRat)
    (hAD : v'.assetsDeployed.toRat + loan.principalOutstanding.toRat =
      l.vault.assetsDeployed.toRat + loan'.principalOutstanding.toRat) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).DebtInv := by
  have hePO : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding (Loan.withBroker_eq hw) :)
  refine hinv.commitLoan hb hloss hcount (fun e' he' => ?_) (fun e' he' => ?_) ?_ ?_
  · rw [show (LoanEffect.ofLoan i e loan' v').loanIndex = i from rfl, he] at he'
    cases he'; rfl
  · simp only [LoanEffect.ofLoan, Option.some.injEq] at he'
    subst he'; rfl
  · show loan'.broker.debtTotal.toRat + LoanEntry.principalOn e.brokerIndex (l.loan? i) =
      broker.debtTotal.toRat + LoanEntry.principalOn e.brokerIndex (some { e with loan := loan' })
    rw [he]
    simp only [LoanEntry.principalOn, if_true]
    rw [← hePO]; exact hdebt
  · show v'.assetsDeployed.toRat + LoanEntry.principalIf (fun _ => true) (l.loan? i) =
      l.vault.assetsDeployed.toRat + LoanEntry.principalIf (fun _ => true) (some { e with loan := loan' })
    rw [he]
    simp only [LoanEntry.principalIf, if_true]
    rw [← hePO]; exact hAD

/-- A loan transaction keeps the invariant. -/
lemma LendingLedger.DebtInv.loan_step {l : LendingLedger} (hinv : l.DebtInv) {tx : LendingTx}
    (hpre : (tx.preflight l).isTesSuccess = true) {u : LoanEffect} (hu : (l.applyLoan tx).run = .ok (.ok u)) :
    (l.commitLoan u).DebtInv := by
  have hloss := hinv.loss.loan_step hpre hu
  have hcount := hinv.count.loan_step hpre hu
  have hscale := hinv.loss.reserved.scale
  have hbase := Vault.baseExponent_scale_range l.vault
  have hb10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have h63 : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent < 2 ^ 63 * 10 ^ l.vault.baseExponent :=
    mul_lt_mul_of_pos_right (by norm_num) hb10
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  have hADg : Number.OnGrid l.vault.baseExponent l.vault.assetsDeployed := by
    obtain ⟨n, hn⟩ := hscale.principalSum_grid (fun _ => true)
    exact Number.OnGrid.of_nat l.vault.wf.assetsDeployed_norm n (by rw [hinv.deployed]; exact hn)
  have hADlt : l.vault.assetsDeployed.toRat < 2 ^ 63 * 10 ^ l.vault.baseExponent :=
    lt_of_le_of_lt hinv.loss.deployed h63
  have hDT : ∀ (j : Nat) (br : LoanBroker), l.broker? j = some br →
      Number.OnGrid l.vault.baseExponent br.debtTotal ∧ 0 ≤ br.debtTotal.toRat ∧
        br.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := fun j br hbr => by
    obtain ⟨n, hn⟩ := hscale.brokerPrincipal_grid j
    have hd := hinv.debt j br hbr
    refine ⟨Number.OnGrid.of_nat br.wf.debtTotal_norm n (by rw [hd]; exact hn),
      by rw [hd]; exact l.brokerPrincipal_nonneg j, ?_⟩
    rw [hd, hinv.deployed]; exact l.brokerPrincipal_le j
  have hDTlt : ∀ (j : Nat) (br : LoanBroker), l.broker? j = some br →
      br.debtTotal.toRat < 2 ^ 63 * 10 ^ l.vault.baseExponent := fun j br hbr =>
    lt_of_le_of_lt (hDT j br hbr).2.2 hADlt
  have hPO : ∀ (i : Nat) (e : LoanEntry) (br : LoanBroker), l.loan? i = some e →
      l.broker? e.brokerIndex = some br →
      Number.OnGrid l.vault.baseExponent e.loan.principalOutstanding ∧
        0 ≤ e.loan.principalOutstanding.toRat ∧ e.loan.principalOutstanding.toRat ≤ br.debtTotal.toRat ∧
        e.loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat := fun i e br he hbr => by
    obtain ⟨m, hm⟩ := hscale.principal_grid he
    refine ⟨Number.OnGrid.of_nat e.loan.wf.principalOutstanding_norm m hm,
      (e.loan.exact.principalOutstanding_nonneg : 0 ≤ e.loan.principalOutstanding.toRat),
      ?_, ?_⟩
    · have := l.principalOn_le_sum e.brokerIndex i
      rw [he] at this
      simp only [LoanEntry.principalOn, if_true] at this
      rw [hinv.debt _ br hbr]; exact this
    · have := l.principalIf_le_sum (fun _ => true) i
      rw [he] at this
      simp only [LoanEntry.principalIf, if_true] at this
      rw [hinv.deployed]; exact this
  cases tx with
  | loanSet i principal rates fees pi pt gp sd twoStep ao =>
    obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
    simp only [LendingLedger.applyLoan] at hu
    obtain ⟨broker, r, hb, hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
    have hst := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
    have hnt := hscale.brokers i broker hb
    obtain ⟨-, -, hPOr, -, -⟩ := Loan.create_reserved broker l.vault principal rates fees _ ao twoStep r hpn
      hpos hst hnt hinv.loss.reserved.grid hcr
    obtain ⟨hzone, hfunds⟩ := Loan.create_inside_open_zone broker l.vault principal rates fees _ ao twoStep r hpn
      hpos hst hcr
    obtain ⟨hdt, hadd⟩ := Loan.create_debtStep broker l.vault principal rates fees _ ao twoStep r hcr
    have hls := Loan.create_loanScale_proof broker l.vault principal rates fees _ ao twoStep r hpn hpos hst hnt hcr
    have hpg : Number.OnGrid l.vault.baseExponent principal := by
      obtain ⟨⟨-, k, hk⟩, -⟩ := Loan.principal_onGrid r.loan'
      rw [hls, hPOr] at hk
      exact ⟨hpn, k, hk⟩
    have hlim : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
      have h2 : (10 : ℚ) ^ (l.vault.baseExponent - 1) = 10 ^ l.vault.baseExponent / 10 := by
        rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
      rw [h2] at hzone
      push_cast at hzone
      nlinarith
    obtain ⟨hDTg, hDT0, hDTle⟩ := hDT i broker hb
    have hnone : l.loan? l.loans.length = none := by
      unfold LendingLedger.loan?; rw [List.getElem?_eq_none (le_refl _)]; rfl
    have hold : ∀ e, l.loan? (LoanEffect.ofCreate i l.loans.length r).loanIndex = some e →
        e.brokerIndex = (LoanEffect.ofCreate i l.loans.length r).brokerIndex := by
      intro e he
      rw [show (LoanEffect.ofCreate i l.loans.length r).loanIndex = l.loans.length from rfl, hnone] at he
      cases he
    refine hinv.commitLoan hb hloss hcount hold (fun e he => ?_) ?_ ?_
    · simp only [LoanEffect.ofCreate, Option.some.injEq] at he
      subst he; rfl
    · show r.loan'.broker.debtTotal.toRat + LoanEntry.principalOn i (l.loan? l.loans.length) =
        broker.debtTotal.toRat + LoanEntry.principalOn i (some { brokerIndex := i, loan := r.loan' })
      rw [hnone]
      simp only [LoanEntry.principalOn, if_true, add_zero]
      rw [Number.OnGrid.add_exact hDTg hpg hDT0 hpos.le (by linarith [l.vault.exact.assetsAvailable_nonneg])
        hsb hdt, hPOr]
    · show r.pool'.assetsDeployed.toRat + LoanEntry.principalIf (fun _ => true) (l.loan? l.loans.length) =
        l.vault.assetsDeployed.toRat +
          LoanEntry.principalIf (fun _ => true) (some { brokerIndex := i, loan := r.loan' })
      rw [hnone]
      simp only [LoanEntry.principalIf, if_true, add_zero]
      rw [Number.OnGrid.add_exact hADg hpg hAD0 hpos.le (by linarith [l.vault.exact.assetsAvailable_nonneg])
        hsb hadd, hPOr]
  | loanAccept i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_accept_inv u i hu
    have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    obtain ⟨-, -, hPO', -⟩ := Loan.accept_reserved loan l.vault r hr
    refine hinv.ofLoan he hb hw hloss hcount ?_ ?_
    · rw [Loan.accept_broker loan _ r hr, hlb, hPO']
    · rw [(Loan.accept_lossStep loan l.vault r hr).2, hPO']
  | loanManage i action =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_manage_inv u i action hu
    have hraw := Loan.withBroker_eq hw
    have hlb : loan.broker = broker := (congrArg RawLoan.broker hraw :)
    have hePO : loan.principalOutstanding = e.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    obtain ⟨hPg, hP0, hPDT, hPAD⟩ := hPO i e broker he hb
    rw [← hePO] at hPg hP0 hPDT hPAD
    obtain ⟨hDTg, -, -⟩ := hDT _ broker hb
    cases action with
    | impair =>
      obtain ⟨-, hAD', -, hPO'⟩ := Loan.manageImpair_lossStep loan l.vault l.now r hr
      refine hinv.ofLoan he hb hw hloss hcount ?_ ?_
      · rw [(Loan.manageImpair_debt loan l.vault l.now r hr).1, hlb, hPO']
      · rw [hAD', hPO']
    | unimpair =>
      obtain ⟨-, hAD', -, hPO'⟩ := Loan.manageUnimpair_lossStep loan l.vault r hr
      refine hinv.ofLoan he hb hw hloss hcount ?_ ?_
      · rw [(Loan.manageUnimpair_debt loan l.vault r hr).1, hlb, hPO']
      · rw [hAD', hPO']
    | default =>
      simp only [Loan.manage] at hr
      unfold_ter at hr
      walk_ok
      rename_i rd hd
      obtain ⟨hdt, hadd, hPO'⟩ := Loan.manageDefault_debtStep loan l.vault rd hd
      rw [hlb] at hdt
      refine hinv.ofLoan he hb hw hloss hcount ?_ ?_
      · rw [Number.OnGrid.sub_exact hDTg hPg hP0 hPDT (hDTlt _ broker hb) hsb hdt, hPO', Number.toRat_zero]
        ring
      · rw [Number.operator_add_neg_toRat_of_grid _ _ _ _ l.vault.wf.assetsDeployed_norm
          loan.wf.principalOutstanding_norm (hADg.nat hAD0) (hPg.nat hP0) hPAD hADlt hsb hadd, hPO',
          Number.toRat_zero]
        ring
  | loanPay i paymentType amount =>
    obtain ⟨e, broker, loan, r, he, hb, hw, -, hr, rfl⟩ := l.applyLoan_pay_inv u i paymentType amount hu
    have hraw := Loan.withBroker_eq hw
    have hlb : loan.broker = broker := (congrArg RawLoan.broker hraw :)
    have hePO : loan.principalOutstanding = e.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    have hls : loan.loanScale = l.vault.baseExponent := by
      rw [show loan.loanScale = e.loan.loanScale from (congrArg RawLoan.loanScale hraw :)]
      exact hscale.loanScale i e he
    obtain ⟨hPg, hP0, hPDT, hPAD⟩ := hPO i e broker he hb
    rw [← hePO] at hPg hP0 hPDT hPAD
    obtain ⟨hDTg, -, -⟩ := hDT _ broker hb
    obtain ⟨paid, hpg, hp0, hpe, hdt, hadd⟩ := Loan.pay_principal loan l.vault paymentType amount l.now r
      (by rw [hls]; omega) hr
    rw [hls] at hpg
    have hpo0 : 0 ≤ r.loan'.principalOutstanding.toRat := r.loan'.exact.principalOutstanding_nonneg
    have hle : paid.toRat ≤ loan.principalOutstanding.toRat := by linarith
    rw [hlb] at hdt
    refine hinv.ofLoan he hb hw hloss hcount ?_ ?_
    · rw [Number.OnGrid.sub_exact hDTg hpg hp0 (by linarith) (hDTlt _ broker hb) hsb hdt]
      linarith
    · rw [Number.operator_add_neg_toRat_of_grid _ _ _ _ l.vault.wf.assetsDeployed_norm hpg.1 (hADg.nat hAD0)
        (hpg.nat hp0) (by linarith) hADlt hsb hadd]
      linarith
  | loanDelete i =>
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hr, hu'⟩ := l.applyLoan_delete_inv u i hu
    have hv : u.vault = r.pool' := by rw [hu']
    have hbi : u.brokerIndex = e.brokerIndex := by rw [hu']
    have hbr : u.broker = r.broker' := by rw [hu']
    have hi : u.loanIndex = i := by rw [hu']
    have hlo : u.loan = none := by rw [hu']
    have hraw := Loan.withBroker_eq hw
    have hlb : loan.broker = broker := (congrArg RawLoan.broker hraw :)
    have hePO : loan.principalOutstanding = e.loan.principalOutstanding :=
      (congrArg RawLoan.principalOutstanding hraw :)
    obtain ⟨hPg, hP0, hPDT, hPAD⟩ := hPO i e broker he hb
    rw [← hePO] at hPg hP0 hPDT hPAD
    obtain ⟨hDTg, hDT0, -⟩ := hDT _ broker hb
    have hc' := l.brokerPrincipal_commitLoan u e.brokerIndex
    rw [hi, hlo, he] at hc'
    simp only [LoanEntry.principalOn, if_true, add_zero] at hc'
    have hlast : broker.loanCount - 1 == 0 → (l.commitLoan u).brokerPrincipal e.brokerIndex = 0 := by
      intro h0
      apply LendingLedger.brokerPrincipal_eq_zero
      have hb' : (l.commitLoan u).broker? e.brokerIndex = some u.broker := by
        rw [LendingLedger.broker?_commitLoan l u broker (by rw [hbi]; exact hb), if_pos hbi.symm]
      have := hcount.counted _ _ hb'
      rw [hbr, Loan.delete_loanCount loan _ r hr, hlb] at this
      rw [← this, show broker.loanCount - 1 = 0 from beq_iff_eq.mp h0]; rfl
    obtain ⟨hpend, hact⟩ := Loan.delete_debtStep loan l.vault r hr
    rw [hlb] at hpend hact
    refine hinv.commitLoan (b := broker) (by rw [hbi]; exact hb) hloss hcount
      (fun e' he' => by rw [hi, he] at he'; cases he'; exact hbi.symm) (fun e' he' => by rw [hlo] at he'; cases he')
      ?_ ?_
    · rw [hbr, hbi, hi, hlo, he]
      simp only [LoanEntry.principalOn, if_true, add_zero]
      cases hp : loan.isPending
      · obtain ⟨-, hd⟩ := hact hp
        rw [hd]
        split
        · rename_i h0
          have := hlast h0
          rw [Number.toRat_zero, hinv.debt _ broker hb]
          linarith
        · -- an active loan that can be deleted owes nothing
          have hpr := Loan.canDelete_active_paid loan hc hp
          have hz := (loan.valid.paid_zeroed hpr).2.1
          rw [← hePO, show loan.principalOutstanding = loan.toRawLoan.principalOutstanding from rfl, hz,
            Number.toRat_zero, add_zero]
      · obtain ⟨-, d, hd, hdt⟩ := hpend hp
        rw [hdt]
        split
        · rename_i h0
          have := hlast h0
          rw [Number.toRat_zero, hinv.debt _ broker hb]
          linarith
        · rw [Number.OnGrid.sub_exact hDTg hPg hP0 hPDT (hDTlt _ broker hb) hsb hd, hePO]
          ring
    · rw [hv, hi, hlo, he]
      simp only [LoanEntry.principalIf, if_true, add_zero]
      cases hp : loan.isPending
      · rw [(hact hp).1]
        have hpr := Loan.canDelete_active_paid loan hc hp
        have hz := (loan.valid.paid_zeroed hpr).2.1
        rw [← hePO, show loan.principalOutstanding = loan.toRawLoan.principalOutstanding from rfl, hz,
          Number.toRat_zero, add_zero]
      · rw [Number.operator_add_neg_toRat_of_grid _ _ _ _ l.vault.wf.assetsDeployed_norm
          loan.wf.principalOutstanding_norm (hADg.nat hAD0) (hPg.nat hP0) hPAD hADlt hsb (hpend hp).1, hePO]
        ring
  | _ => simp only [LendingLedger.applyLoan] at hu; cases hu

/-- A broker transaction keeps DebtTotal equal to the sum over the broker's loans. -/
private lemma LendingLedger.DebtInv.broker_debt {l : LendingLedger} (hinv : l.DebtInv) {tx : LendingTx}
    {u : BrokerEffect} (hu : (l.applyBroker tx).run = .ok (.ok u)) (j : Nat) (b' : LoanBroker)
    (hb' : (l.commitBroker u).broker? j = some b') : b'.debtTotal.toRat = (l.commitBroker u).brokerPrincipal j := by
  have hsum : (l.commitBroker u).brokerPrincipal j = l.brokerPrincipal j := rfl
  have hnone : ∀ k, l.brokers.length ≤ k → l.broker? k = none := fun k hk => by
    unfold LendingLedger.broker?; rw [List.getElem?_eq_none hk]; rfl
  rw [hsum]
  rw [LendingLedger.broker?_commitBroker] at hb'
  by_cases hj : j = (if u.index < l.brokers.length then u.index else l.brokers.length)
  · rw [if_pos hj] at hb'
    rcases LendingLedger.applyBroker_cases l tx u hu with ⟨hi, b, hb, h0, -⟩ | ⟨b, b2, hb, hb2, hd, -⟩ |
      ⟨b, hb, hb2, -⟩
    · -- a new broker has no debt and no loans
      rw [hb] at hb'; cases hb'
      rw [hi, if_neg (lt_irrefl _)] at hj
      rw [h0, Number.toRat_zero, hj,
        l.brokerPrincipal_eq_zero _ (hinv.count.orphans _ (hnone _ le_rfl))]
    · rw [hb2] at hb'; cases hb'
      rw [if_pos (LendingLedger.broker?_lt hb)] at hj
      rw [hd, hj]; exact hinv.debt _ b hb
    · rw [hb2] at hb'; cases hb'
  · rw [if_neg hj] at hb'; exact hinv.debt j b' hb'

/-- Every transaction keeps the invariant. -/
lemma LendingLedger.DebtInv.step {l l' : LendingLedger} (hinv : l.DebtInv) {tx : LendingTx}
    (h : (l.apply tx).run = .ok (.ok l')) : l'.DebtInv := by
  have hpre := (LendingLedger.apply_checked h).1
  have hloss := hinv.loss.step h
  have hcount := hinv.count.step h
  by_cases hv : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hv h
    have hk := l.applyVault_keepsLending tx u hu
    have hrest : (l.commitVault u).loans = l.loans ∧ (l.commitVault u).brokers = l.brokers ∧
        (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    refine ⟨hloss, hcount, ?_, fun j b hb => ?_⟩
    · rw [hrest.2.2, hk.assetsDeployed, LendingLedger.principalSum_of_loans hrest.1]; exact hinv.deployed
    · have hb0 : l.broker? j = some b := by unfold LendingLedger.broker? at hb ⊢; rw [hrest.2.1] at hb; exact hb
      rw [hinv.debt j b hb0]
      unfold LendingLedger.brokerPrincipal; rw [hrest.1]
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker hb h
    exact ⟨hloss, hcount, hinv.deployed, hinv.broker_debt hu⟩
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
    exact ⟨hloss, hcount, hinv.deployed, hinv.debt⟩
  · -- close only moves the close time
    simp only [LendingLedger.applyChecked] at hc
    cases hc
    exact ⟨hloss, hcount, hinv.deployed, hinv.debt⟩

/-- A genesis ledger has lent nothing and has no brokers or loans. -/
lemma LendingLedger.Genesis.debtInv {g : LendingLedger} (hg : g.Genesis) : g.DebtInv := by
  obtain ⟨scale, m, s, eer, ocb, nt, -, hcreate⟩ := hg.created
  unfold Vault.create at hcreate
  have hraw := (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hcreate).1
  have had : g.vault.assetsDeployed = Number.zero := (congrArg RawVault.assetsDeployed hraw :)
  refine ⟨hg.lossInv, hg.loanCountInv, ?_, fun j b hb => ?_⟩
  · rw [had, Number.toRat_zero]; unfold LendingLedger.principalSum; rw [hg.no_loans]; rfl
  · unfold LendingLedger.broker? at hb; rw [hg.no_brokers] at hb; cases hb

/-- Every reachable ledger satisfies the invariant. -/
lemma LendingLedger.Reachable.debtInv {l : LendingLedger} (hr : l.Reachable) : l.DebtInv :=
  LendingLedger.Reachable.invariant (fun _ hg => hg.debtInv) (fun _ _ _ hi ha => hi.step ha) hr

/-- Σ DebtTotal of the stored brokers. -/
def LendingLedger.debtSum (l : LendingLedger) : ℚ :=
  ∑ j ∈ Finset.range l.brokers.length, ((l.broker? j).map (·.debtTotal.toRat)).getD 0

/-- Summing the broker sums over the brokers swaps with summing over the loans. -/
private lemma brokerSums_swap (n : Nat) (xs : List (Option LoanEntry)) :
    ∑ j ∈ Finset.range n, (xs.map (LoanEntry.principalOn j)).sum =
      (xs.map (fun o => ∑ j ∈ Finset.range n, LoanEntry.principalOn j o)).sum := by
  induction xs with
  | nil => simp
  | cons o os ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

/-- Proof body of the DebtTotal line of `Lending.Reachable.ledger_sums`. -/
lemma LendingLedger.debt_principal_proof (l : LendingLedger) (hr : l.Reachable) (j : Nat) (b : LoanBroker)
    (hb : l.broker? j = some b) : b.debtTotal.toRat = l.brokerPrincipal j :=
  hr.debtInv.debt j b hb

/-- Proof body of the AssetsDeployed line of `Lending.Reachable.ledger_sums`. -/
lemma LendingLedger.assets_lent_proof (l : LendingLedger) (hr : l.Reachable) :
    l.vault.assetsDeployed.toRat = l.debtSum := by
  have hinv := hr.debtInv
  have hslot : ∀ j, ((l.broker? j).map (·.debtTotal.toRat)).getD 0 = l.brokerPrincipal j := by
    intro j
    cases hb : l.broker? j with
    | none => rw [l.brokerPrincipal_eq_zero j (hinv.count.orphans j hb)]; rfl
    | some b => exact hinv.debt j b hb
  unfold LendingLedger.debtSum
  simp only [hslot]
  unfold LendingLedger.brokerPrincipal
  rw [brokerSums_swap, hinv.deployed]
  unfold LendingLedger.principalSum
  congr 1
  apply List.map_congr_left
  intro o ho
  cases o with
  | none => simp [LoanEntry.principalOn, LoanEntry.principalIf]
  | some e =>
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
    have hlt : e.brokerIndex < l.brokers.length := by
      by_contra hge
      push Not at hge
      have hnone : l.broker? e.brokerIndex = none := by
        unfold LendingLedger.broker?; rw [List.getElem?_eq_none hge]; rfl
      have h0 := hinv.count.orphans _ hnone
      unfold LendingLedger.loansOf at h0
      have := (List.countP_pos_iff (p := fun o : Option LoanEntry => o.any (·.brokerIndex == e.brokerIndex))).mpr
        ⟨some e, ho, by simp only [Option.any_some, beq_self_eq_true]⟩
      omega
    simp only [LoanEntry.principalOn, LoanEntry.principalIf, if_true]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hlt)]

/-- Proof body of `Lending.Reachable.loss_reserved_deployed`. -/
lemma LendingLedger.loss_reserved_deployed_proof (l : LendingLedger) (hr : l.Reachable) :
    l.vault.lossUnrealized.toRat + l.vault.assetsReserved.toRat ≤ l.vault.assetsDeployed.toRat := by
  have hinv := hr.debtInv
  rw [hinv.loss.sum, hinv.loss.reserved.sum, hinv.deployed]
  unfold LendingLedger.principalSum
  rw [← List.sum_map_add]
  apply List.sum_le_sum
  intro o ho
  cases o with
  | none => simp [LoanEntry.principalIf]
  | some e =>
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
    have he : l.loan? i = some e := by unfold LendingLedger.loan?; rw [hi]; rfl
    have hp0 : 0 ≤ e.loan.principalOutstanding.toRat := e.loan.exact.principalOutstanding_nonneg
    simp only [LoanEntry.principalIf, if_true]
    -- a pending loan is never impaired, so a loan counts at most once
    by_cases hp : e.loan.isPending = true
    · have hi := hinv.loss.active i e he hp
      simp only [hi, hp, Bool.false_eq_true, if_false, if_true, zero_add, le_refl]
    · rw [if_neg hp, add_zero]
      split <;> linarith

end XRPL.Model.Lending
