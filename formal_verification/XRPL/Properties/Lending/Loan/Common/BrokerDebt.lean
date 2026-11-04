import XRPL.Properties.Lending.Loan.Common.DeleteExits
import XRPL.Properties.Lending.Loan.Common.ManageProofs
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Totality
import XRPL.Properties.Vault.Proofs.Support.VaultBalances

/-! # What loan operations do to DebtTotal and AssetsReserved

Impair, unimpair, default and delete never raise DebtTotal or AssetsReserved. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- Taking an amount of at least zero off a balance never raises it. -/
lemma Number.operator_sub_le_self {x y d : Number} (hx : x.isNormalized) (hy : y.isNormalized)
    (hy0 : 0 ≤ y.toRat) (hok : x.operator_sub y .to_nearest = .ok d) : d.toRat ≤ x.toRat :=
  operator_sub_le_of_le_normalized x y d x hx hy hok hx (by linarith)

/-- Adding a change of at most zero never raises a balance. -/
lemma Number.operator_add_le_self {x y d : Number} (hx : x.isNormalized) (hy : y.isNormalized)
    (hy0 : y.toRat ≤ 0) (hok : x.operator_add y .to_nearest = .ok d) : d.toRat ≤ x.toRat :=
  operator_add_le_of_le_normalized x y d x hx hy hok hx (by linarith)

/-- A vault update without a reserved change keeps AssetsReserved. -/
lemma Vault.poolAdjust_reserved_zero (v v' : Vault) (c : PoolBalanceChange) (hc : c.reserved = Number.zero)
    (h : AssetPool.adjustBalances v c = .ok (.ok v')) : v'.assetsReserved = v.assetsReserved := by
  have hr := (Vault.poolAdjust_adjustSums v c v' h).reserved
  rw [hc, Number.operator_add_zero_right] at hr
  exact (Except.ok.inj hr).symm

/-- Changing the impairment keeps the broker and AssetsReserved. -/
private lemma Loan.changeImpairment_debt (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) :
    r.loan'.broker = loan.broker ∧ r.pool'.assetsReserved = v.assetsReserved := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    exact ⟨(congrArg RawLoan.broker (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1 :),
      Vault.poolAdjust_reserved_zero _ _ _ rfl ‹_›⟩

/-- Impair keeps the broker and AssetsReserved. -/
lemma Loan.manageImpair_debt (loan : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (loan.manageImpair v now).run = .ok (.ok r)) :
    r.loan'.broker = loan.broker ∧ r.pool'.assetsReserved = v.assetsReserved := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_debt loan v true r ‹_›

/-- Unimpair keeps the broker and AssetsReserved. -/
lemma Loan.manageUnimpair_debt (loan : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (loan.manageUnimpair v).run = .ok (.ok r)) :
    r.loan'.broker = loan.broker ∧ r.pool'.assetsReserved = v.assetsReserved :=
  Loan.changeImpairment_debt loan v false r h

/-- A default never raises DebtTotal and keeps AssetsReserved. -/
lemma Loan.manageDefault_debt (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (h : (loan.manageDefault v).run = .ok (.ok r)) :
    r.loan'.broker.debtTotal.toRat ≤ loan.broker.debtTotal.toRat ∧ r.pool'.assetsReserved = v.assetsReserved := by
  obtain ⟨_, d, c, raw, b, -, -, hadj, hraw, hdebt, -, hb, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r h
  have hbr : r.loan'.broker = b := by
    rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]; rfl
  have hd' : b.debtTotal = d := by
    rw [show b.debtTotal = b.toRawLoanBroker.debtTotal from rfl, hb]; rfl
  refine ⟨?_, ?_⟩
  · rw [hbr, hd']
    exact Number.operator_sub_le_self loan.broker.wf.debtTotal_norm loan.wf.principalOutstanding_norm
      ((loan.exact.principalOutstanding_nonneg : 0 ≤ loan.principalOutstanding.toRat)) hdebt
  · obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
    have hr := hs.reserved
    rw [show (loan.defaultChange _ r.amountToPool).reserved = Number.zero from rfl,
      Number.operator_add_zero_right] at hr
    rw [show r.pool'.assetsReserved = r.pool'.toRawVault.assetsReserved from rfl, hraw, heq]
    exact (Except.ok.inj hr).symm

/-- Releasing a loan sets DebtTotal to the given value, or to zero with the last loan. -/
private lemma LoanBroker.releaseLoan_debt (lb lb' : LoanBroker) (d : Number) (h : lb.releaseLoan d = .ok lb') :
    lb'.debtTotal = d ∨ lb'.debtTotal = Number.zero := by
  unfold LoanBroker.releaseLoan at h
  have hraw := (congrArg RawLoanBroker.debtTotal (RawLoanBroker.to_lawful_ok h).1 :)
  dsimp only at hraw
  rw [show lb'.debtTotal = lb'.toRawLoanBroker.debtTotal from rfl, hraw]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- A delete never raises DebtTotal or AssetsReserved. -/
lemma Loan.delete_debt (loan : Loan) (v : Vault) (r : LoanBrokerWithPool Vault)
    (h : (loan.delete v).run = .ok (.ok r)) :
    r.broker'.debtTotal.toRat ≤ loan.broker.debtTotal.toRat ∧
      r.pool'.assetsReserved.toRat ≤ v.assetsReserved.toRat := by
  have hd0 : 0 ≤ loan.broker.debtTotal.toRat := loan.broker.exact.debtTotal_nonneg
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  by_cases hp : loan.isPending = true
  · obtain ⟨principal', raw, d, hround, hadj, hv', hdebt, hrel⟩ := Loan.delete_pending_ok_inv loan v r hp h
    refine ⟨?_, ?_⟩
    · rcases LoanBroker.releaseLoan_debt _ _ _ hrel with hb | hb <;> rw [hb]
      · exact Number.operator_sub_le_self loan.broker.wf.debtTotal_norm loan.wf.principalOutstanding_norm hp0 hdebt
      · rw [Number.toRat_zero]; exact hd0
    · have hpn := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
      have hp0' := STAmount.roundToNumericType_nonneg _ _ _ loan.wf.principalOutstanding_norm hp0 hround
      obtain ⟨_, _, _, _, _, hs, -, -, heq⟩ := Vault.adjustBalances_ok_parts v _ raw hadj
      have hr := hs.reserved
      rw [show (loan.deleteChange principal').reserved = principal'.operator_neg from rfl] at hr
      rw [show r.pool'.assetsReserved = r.pool'.toRawVault.assetsReserved from rfl,
        (XRPL.Model.SingleAssetVault.RawVault.to_lawful_ok hv').1, heq]
      exact Number.operator_add_le_self v.wf.assetsReserved_norm (Number.operator_neg_isNormalized _ hpn)
        (by rw [Number.toRat_neg]; linarith) hr
  · simp only [Loan.delete, Bool.not_eq_true] at h hp
    rw [hp] at h
    unfold_ter at h
    walk_ok
    refine ⟨?_, le_refl _⟩
    rcases LoanBroker.releaseLoan_debt _ _ _ ‹Loan.deleteActive _ = Except.ok _› with hb | hb <;> rw [hb]
    rw [Number.toRat_zero]; exact hd0

end XRPL.Model.Lending
