import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Ledger.Common.ScaleInv
import XRPL.Properties.Lending.Loan.Common.OrderCreates

/-! # Proof body for the order of two LoanSets on a ledger

Each LoanSet creates its loan on the ledger's copy of its broker and writes the vault and that broker. The
second LoanSet reads the broker the first one wrote only when both use the same broker. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A successful LoanSet passed its preflight and preclaim, created the loan on the stored broker and wrote
the result. -/
private lemma loanSet_step (l l' : LendingLedger) (i : Nat) (p : Number) (ra : LoanRates) (fa : LoanFees)
    (pi pt gp : Option UInt32) (sd : UInt32) (ts ao : Bool)
    (h : (l.apply (.loanSet i p ra fa pi pt gp sd ts ao)).run = .ok (.ok l')) :
    ∃ broker r, l.broker? i = some broker ∧ p.isNormalized ∧ 0 < p.toRat ∧
      STAmount.isRounded broker.numericType p = false ∧
      (Loan.create broker l.vault p ra fa (LoanSchedule.build pi pt gp sd l.now ts) ao ts).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofCreate i l.loans.length r) := by
  obtain ⟨hpre, -⟩ := LendingLedger.apply_checked h
  obtain ⟨hp, hpos⟩ := LendingTx.preflight_loanSet_principal l i p ra fa pi pt gp sd ts ao hpre
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨broker, r, hb, hc, hr, rfl⟩ :=
    l.applyLoanSet_inv u i p ra fa (LoanSchedule.build pi pt gp sd l.now ts) ts ao hu
  exact ⟨broker, r, hb, hp, hpos,
    Loan.canCreate_exact broker l.vault p fa _ _ _ hc p List.mem_cons_self, hr, rfl⟩

variable (l lA lB lAB lBA : LendingLedger) (i j : Nat) (bA bB : LoanBroker) (pa pb : Number)
  (ra rb : LoanRates) (fa fb : LoanFees) (pia pta gpa pib ptb gpb : Option UInt32) (sda sdb : UInt32)
  (tsa aoa tsb aob : Bool)

/-- Two LoanSets on the base grid give the same vault and brokers in either order. When both use one broker, its
DebtTotal must stay below `10^16` base units after either loan. -/
lemma LendingLedger.creates_comm_of_fits (hr : l.Reachable)
    (hbA : l.broker? i = some bA) (hbB : l.broker? j = some bB)
    (hgA : Loan.CreateGrid bA l.vault) (hgB : Loan.CreateGrid bB l.vault)
    (hdebt : i = j → bA.debtTotal.toRat + pa.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
      bA.debtTotal.toRat + pb.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hA : (l.apply (.loanSet i pa ra fa pia pta gpa sda tsa aoa)).run = .ok (.ok lA))
    (hAB : (lA.apply (.loanSet j pb rb fb pib ptb gpb sdb tsb aob)).run = .ok (.ok lAB))
    (hB : (l.apply (.loanSet j pb rb fb pib ptb gpb sdb tsb aob)).run = .ok (.ok lB))
    (hBA : (lB.apply (.loanSet i pa ra fa pia pta gpa sda tsa aoa)).run = .ok (.ok lBA)) :
    lAB.vault = lBA.vault ∧ lAB.brokers = lBA.brokers := by
  have hscale := hr.scaleInv
  obtain ⟨b₁, rA, hb₁, hpa, hposa, hsta, hcA, rfl⟩ := loanSet_step _ _ _ _ _ _ _ _ _ _ _ _ hA
  obtain ⟨b₂, rB, hb₂, hpb, hposb, hstb, hcB, rfl⟩ := loanSet_step _ _ _ _ _ _ _ _ _ _ _ _ hB
  rw [hbA] at hb₁
  rw [hbB] at hb₂
  cases hb₁
  cases hb₂
  obtain ⟨c₂, rAB, hc₂, -, -, -, hcAB, rfl⟩ := loanSet_step _ _ _ _ _ _ _ _ _ _ _ _ hAB
  obtain ⟨c₁, rBA, hc₁, -, -, -, hcBA, rfl⟩ := loanSet_step _ _ _ _ _ _ _ _ _ _ _ _ hBA
  rw [LendingLedger.broker?_commitLoan l _ bA hbA j] at hc₂
  rw [LendingLedger.broker?_commitLoan l _ bB hbB i] at hc₁
  dsimp only [LoanEffect.ofCreate] at hc₂ hc₁
  have hntA := hscale.brokers i bA hbA
  have hntB := hscale.brokers j bB hbB
  by_cases hij : i = j
  · -- one broker: the second LoanSet reads the broker the first one wrote
    subst hij
    rw [hbA] at hbB
    cases hbB
    obtain ⟨hdA, hdB⟩ := hdebt rfl
    rw [if_pos rfl] at hc₂ hc₁
    cases hc₂
    cases hc₁
    obtain ⟨hv, hb⟩ := Loan.creates_comm_same_proof l.vault bA pa pb ra rb fa fb _ _ aoa aob tsa tsb rA rAB rB rBA
      hpa hposa hsta hpb hposb hstb hntA hgA hdA hdB hcA hcAB hcB hcBA
    refine ⟨hv, ?_⟩
    show ((l.brokers.set i (some rA.loan'.broker)).set i (some rAB.loan'.broker)) =
      ((l.brokers.set i (some rB.loan'.broker)).set i (some rBA.loan'.broker))
    rw [List.set_set, List.set_set, hb]
  · -- two brokers: each LoanSet reads its own broker as stored
    rw [if_neg (Ne.symm hij)] at hc₂
    rw [if_neg hij] at hc₁
    rw [hbB] at hc₂
    rw [hbA] at hc₁
    cases hc₂
    cases hc₁
    obtain ⟨hv, hb₁, hb₂⟩ := Loan.creates_comm_other_proof l.vault bA bB pa pb ra rb fa fb _ _ aoa aob tsa tsb rA
      rAB rB rBA hpa hposa hsta hpb hposb hstb hntA hntB hgA hgB hcA hcAB hcB hcBA
    refine ⟨hv, ?_⟩
    show ((l.brokers.set i (some rA.loan'.broker)).set j (some rAB.loan'.broker)) =
      ((l.brokers.set j (some rB.loan'.broker)).set i (some rBA.loan'.broker))
    rw [hb₁, hb₂, List.set_comm _ _ hij]


/-- Proof body of `Lending.creates_comm`. -/
lemma LendingLedger.creates_comm_proof (hr : l.Reachable)
    (hA : (l.apply (.loanSet i pa ra fa pia pta gpa sda tsa aoa)).run = .ok (.ok lA))
    (hAB : (lA.apply (.loanSet j pb rb fb pib ptb gpb sdb tsb aob)).run = .ok (.ok lAB))
    (hB : (l.apply (.loanSet j pb rb fb pib ptb gpb sdb tsb aob)).run = .ok (.ok lB))
    (hBA : (lB.apply (.loanSet i pa ra fa pia pta gpa sda tsa aoa)).run = .ok (.ok lBA)) :
    lAB.vault = lBA.vault ∧ lAB.brokers = lBA.brokers := by
  -- each first LoanSet passed the Open-limit check on the reachable ledger
  obtain ⟨b₁, r₁, hb₁, hpa, hposa, hsta, hc₁, -⟩ := loanSet_step _ _ _ _ _ _ _ _ _ _ _ _ hA
  obtain ⟨b₂, r₂, hb₂, hpb, hposb, hstb, hc₂, -⟩ := loanSet_step _ _ _ _ _ _ _ _ _ _ _ _ hB
  refine LendingLedger.creates_comm_of_fits l lA lB lAB lBA i j b₁ b₂ pa pb ra rb fa fb pia pta gpa pib ptb gpb sda
    sdb tsa aoa tsb aob hr hb₁ hb₂ (hr.createGrid hb₁ hpa hposa hsta hc₁) (hr.createGrid hb₂ hpb hposb hstb hc₂)
    (fun hij => ?_) hA hAB hB hBA
  subst hij
  rw [hb₁] at hb₂
  cases hb₂
  exact ⟨hr.create_debt_room hb₁ hpa hposa hsta hc₁, hr.create_debt_room hb₁ hpb hposb hstb hc₂⟩

end XRPL.Model.Lending
