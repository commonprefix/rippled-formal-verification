import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Properties.Lending.Common.PoolBalances
import XRPL.Properties.Lending.Loan.LoanValid
import XRPL.Properties.Lending.LoanBroker.LoanBrokerValid
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Protocol.STAmount.Common.Representable
import XRPL.Properties.Vault.Proofs.Support.CashGrid

/-! # LoanManage steps read in plain terms

The cover a default pays, the balance change each action makes to the vault, and the loan and
broker a default writes. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.changeImpairment defaultCoveredAmount from XRPL.Model.Lending.Loan.LoanManage

/-- The cover a default pays the vault: the liquidation amount capped by PrincipalOutstanding and CoverAvailable,
rounded towards zero to the asset, then floored so AssetsAvailable + cover lands on its own grid. -/
def Loan.defaultCover (loan : Loan) (v : Vault) : Except Error Number := do
  let broker := loan.broker
  let minimumCover ← tenthBipsOfValue broker.debtTotal broker.coverRateMinimum .upward
  let liquidationAmount ← tenthBipsOfValue minimumCover broker.coverRateLiquidation .upward
  let cappedAmount := Number.min (Number.min liquidationAmount loan.principalOutstanding) broker.coverAvailable
  let coveredAmount ← STAmount.roundToNumericType broker.numericType cappedAmount .towards_zero
  let defaultCovered ← sumRoundAndSubtract v.assetsAvailable coveredAmount v.baseExponent broker.numericType
    .downward
  defaultCovered.toNumber .to_nearest

/-- The steps of a cover computation that succeeds. -/
lemma Loan.defaultCover_parts (loan : Loan) (v : Vault) (dc : Number) (h : loan.defaultCover v = .ok dc) :
    ∃ minimumCover liquidationAmount coveredAmount : Number, ∃ st : STAmount,
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      STAmount.roundToNumericType loan.broker.numericType
        (Number.min (Number.min liquidationAmount loan.principalOutstanding) loan.broker.coverAvailable)
        .towards_zero = .ok coveredAmount ∧
      sumRoundAndSubtract v.assetsAvailable coveredAmount v.baseExponent loan.broker.numericType .downward =
        .ok st ∧
      st.toNumber .to_nearest = .ok dc := by
  unfold Loan.defaultCover at h
  obtain ⟨mc, hmc, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨liq, hliq, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨c, hc, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨st, hst, h⟩ := bind_ok_peel _ _ _ h
  exact ⟨mc, liq, c, st, hmc, hliq, hc, hst, h⟩

/-- The cover a default pays is a normalized `Number`. -/
lemma Loan.defaultCover_isNormalized (loan : Loan) (v : Vault) (dc : Number) (h : loan.defaultCover v = .ok dc) :
    dc.isNormalized := by
  obtain ⟨_, _, _, st, -, -, -, -, h⟩ := Loan.defaultCover_parts loan v dc h
  exact STAmount.toNumber_isNormalized st _ dc h

/-- The model's cover computation is `Loan.defaultCover`. -/
private lemma Loan.defaultCoveredAmount_eq (loan : Loan) (v : Vault) :
    defaultCoveredAmount loan.broker v loan.principalOutstanding = loan.defaultCover v := rfl

/-- The balance change a default makes to the vault: the cover joins AssetsAvailable, the principal
leaves AssetsDeployed, the interest leaves YieldUnrealized, an impaired loan releases its loss. -/
def Loan.defaultChange (loan : Loan) (interestDue defaultCovered : Number) : PoolBalanceChange :=
  { cash := defaultCovered
    deployed := loan.principalOutstanding.operator_neg
    yield := interestDue.operator_neg
    loss := if loan.isImpaired then loan.principalOutstanding.operator_neg else Number.zero }

/-- The broker a default writes: the principal leaves DebtTotal, the cover leaves CoverAvailable. -/
def Loan.defaultedBroker (loan : Loan) (debtTotal' coverAvailable' : Number) : RawLoanBroker :=
  { loan.broker.toRawLoanBroker with debtTotal := debtTotal', coverAvailable := coverAvailable' }

/-- The loan a default writes: marked defaulted, on the new broker, with nothing outstanding. -/
def Loan.defaultedLoan (loan : Loan) (broker' : LoanBroker) : RawLoan :=
  { loan.toRawLoan with
    broker := broker'
    isDefault := true
    totalValueOutstanding := Number.zero
    principalOutstanding := Number.zero
    managementFeeOutstanding := Number.zero
    paymentRemaining := 0
    nextPaymentDueDate := 0 }

/-- The loan an impair or unimpair writes: only the impaired flag changes. -/
def Loan.withImpaired (loan : Loan) (impaired : Bool) : RawLoan :=
  { loan.toRawLoan with isImpaired := impaired }

/-- The loan an impair or unimpair writes is lawful: the impaired flag is not part of the invariant. -/
lemma Loan.withImpaired_lawful (loan : Loan) (b : Bool) :
    ∃ loan', ({ loan.toRawLoan with isImpaired := b } : RawLoan).to_lawful = .ok loan' ∧
      loan'.toRawLoan = { loan.toRawLoan with isImpaired := b } := by
  obtain ⟨rl, wf, valid⟩ := loan
  refine RawLoan.to_lawful_ok_of ?_ ?_
  · cases wf; constructor <;> assumption
  · cases valid; constructor <;> assumption

/-- An impair or unimpair keeps the loan's amounts, so it keeps interestDue. -/
lemma Loan.changeImpairment_interestDue (loan : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment loan v b).run = .ok (.ok r)) :
    r.loan'.toExact.interestDue = loan.toExact.interestDue := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hr := (RawLoan.to_lawful_ok ‹RawLoan.to_lawful _ = Except.ok _›).1
    exact Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hr :)
      (congrArg RawLoan.principalOutstanding hr :) (congrArg RawLoan.managementFeeOutstanding hr :)

/-- A vault with new balances is lawful when they are normalized and not negative, the loss and the reserve fit in
AssetsDeployed, the asset stores both assets fields, AssetsAvailable is on the grid, and no shares means no assets. -/
lemma Vault.balances_lawful (v : Vault) (aa' ad' ar' lu' yu' : Number)
    (hn : aa'.isNormalized ∧ ad'.isNormalized ∧ ar'.isNormalized ∧ lu'.isNormalized ∧ yu'.isNormalized)
    (hnn : 0 ≤ aa'.toRat ∧ 0 ≤ ad'.toRat ∧ 0 ≤ ar'.toRat ∧ 0 ≤ lu'.toRat ∧ 0 ≤ yu'.toRat)
    (hlu : lu'.toRat ≤ ad'.toRat) (har : ar'.toRat ≤ ad'.toRat)
    (hrep : STAmount.isRounded v.numericType ad' = false)
    (haar : STAmount.isRounded v.numericType aa' = false)
    (haag : ∃ k : ℤ, aa'.toRat = k * 10 ^ v.baseExponent)
    (hempty : v.sharesTotal = Number.zero → aa'.toRat = 0 ∧ ad'.toRat = 0) :
    ∃ v', ({ v.toRawVault with
        assetsAvailable := aa'
        assetsDeployed := ad'
        assetsReserved := ar'
        lossUnrealized := lu'
        yieldUnrealized := yu' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with
        assetsAvailable := aa'
        assetsDeployed := ad'
        assetsReserved := ar'
        lossUnrealized := lu'
        yieldUnrealized := yu' } := by
  obtain ⟨han, hdn, hrn, hln, hyn⟩ := hn
  obtain ⟨ha, hd, hr, hl, hy⟩ := hnn
  have hz : ∀ n : Number, n.isNormalized → 0 ≤ n.toRat → Number.zero.operator_le n = true := fun n hn h =>
    (operator_le_iff _ _ Number.zero_isNormalized hn).mpr (by rw [Number.toRat_zero]; exact h)
  have hwf := v.wf
  have hvalid := v.valid
  refine RawVault.to_lawful_ok_of ?_ ?_
  · exact { hwf with
      assetsAvailable_norm := han
      assetsDeployed_norm := hdn
      assetsReserved_norm := hrn
      lossUnrealized_norm := hln
      yieldUnrealized_norm := hyn }
  · refine { hvalid with
      assetsAvailable_nonneg := hz _ han ha
      assetsDeployed_nonneg := hz _ hdn hd
      assetsReserved_nonneg := hz _ hrn hr
      lossUnrealized_nonneg := hz _ hln hl
      yieldUnrealized_nonneg := hz _ hyn hy
      empty_shares := fun h => ⟨(Number.toRat_eq_zero_iff_eq_zero han).mp (hempty h).1,
        (Number.toRat_eq_zero_iff_eq_zero hdn).mp (hempty h).2⟩
      lossUnrealized_le := (operator_le_iff _ _ hln hdn).mpr hlu
      assetsDeployed_representable := hrep
      assetsReserved_le := (operator_le_iff _ _ hrn hdn).mpr har
      assetsAvailable_representable := haar
      assetsAvailable_onGrid := Vault.onGrid_clause v aa' han ha haag }

/-- The loan a default writes is lawful: nothing is outstanding and no payment remains. The new broker holds the same
asset, so the origination fee stays on the LoanScale grid. -/
lemma Loan.defaultedLoan_lawful (loan : Loan) (broker' : LoanBroker)
    (hnt : broker'.numericType = loan.broker.numericType) :
    ∃ loan', (loan.defaultedLoan broker').to_lawful = .ok loan' ∧ loan'.toRawLoan = loan.defaultedLoan broker' := by
  have hwf := loan.wf
  have he := loan.exact
  have hz : (0 : ℚ) = Number.zero.toRat := Number.toRat_zero.symm
  have hat : Number.AtExponent Number.zero.toRat loan.loanScale broker'.numericType.mantissaBound :=
    ⟨0, NumericType.mantissaBound_pos _, by rw [Number.toRat_zero]; simp⟩
  have hat' : Number.zero.isAtExponent loan.loanScale broker'.numericType = true :=
    (Number.isAtExponent_iff _ _ _ Number.zero_isNormalized (le_of_eq hz)).mpr hat
  have hwf' : (loan.defaultedLoan broker').WF := { hwf with
    principalOutstanding_norm := Number.zero_isNormalized
    totalValueOutstanding_norm := Number.zero_isNormalized
    managementFeeOutstanding_norm := Number.zero_isNormalized
    totalValueOutstanding_atExponent := hat'
    principalOutstanding_atExponent := hat'
    managementFeeOutstanding_atExponent := hat'
    originationFee_atExponent := by
      show loan.fees.originationFee.isAtExponent loan.loanScale broker'.numericType = true
      rw [hnt]; exact hwf.originationFee_atExponent }
  have hex : (loan.defaultedLoan broker').toExact.Valid := { he with
    paid_zeroed := fun _ => ⟨Number.toRat_zero, Number.toRat_zero, Number.toRat_zero⟩
    unpaid_nonzero := fun h => absurd rfl h
    principalOutstanding_nonneg := le_of_eq hz
    totalValueOutstanding_nonneg := le_of_eq hz
    managementFeeOutstanding_nonneg := le_of_eq hz
    paid_no_due_date := fun _ => rfl
    interest_nonneg := by
      show (0 : ℚ) ≤ Number.zero.toRat - Number.zero.toRat - Number.zero.toRat
      rw [Number.toRat_zero]; simp
    paymentRemaining_le_total := UInt32.zero_le
    dueDate_schedule := fun h => absurd rfl h }
  exact RawLoan.to_lawful_ok_of hwf' ((RawLoan.valid_iff_exact _ hwf').mpr hex)

/-- A normalized value that is not below zero has a sign that is not negative. -/
lemma Number.signum_nonneg_of_toRat (n : Number) (hn : n.isNormalized) (h : 0 ≤ n.toRat) : 0 ≤ n.signum := by
  rw [signum_eq n hn]
  split_ifs <;> first | omega | linarith

/-- Adding the canonical zero leaves a balance as it is. -/
lemma Number.eq_of_add_zero {x y : Number} (h : x.operator_add Number.zero .to_nearest = .ok y) : y = x := by
  rw [Number.operator_add_zero_right] at h; exact (Except.ok.inj h).symm

/-- Impair once the loan is late: the vault update, then the re-check of the flagged loan. -/
lemma Loan.manageImpair_run (loan : Loan) (v : Vault) (now : UInt32) (hlate : loan.nextPaymentDueDate < now) :
    (loan.manageImpair v now).run =
      (match AssetPool.adjustBalances v { loss := loan.principalOutstanding } with
       | .error e => .error e
       | .ok (.error ter) => .ok (.error ter)
       | .ok (.ok v') =>
         match (loan.withImpaired true).to_lawful with
         | .error e => .error e
         | .ok loan' => .ok (.ok { loan' := loan', pool' := v' })) := by
  have h : loan.isPaymentLate now = true := by unfold Loan.isPaymentLate; exact decide_eq_true hlate
  simp only [Loan.manageImpair, Loan.changeImpairment, Loan.withImpaired]
  unfold_ter
  simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases AssetPool.adjustBalances v { loss := loan.principalOutstanding } with e | ter | v'
  · rfl
  · rfl
  · simp only
    rcases ({ loan.toRawLoan with isImpaired := true } : RawLoan).to_lawful with e | l <;> rfl

/-- Unimpair: the vault update, then the re-check of the cleared loan. -/
lemma Loan.manageUnimpair_run (loan : Loan) (v : Vault) :
    (loan.manageUnimpair v).run =
      (match AssetPool.adjustBalances v { loss := loan.principalOutstanding.operator_neg } with
       | .error e => .error e
       | .ok (.error ter) => .ok (.error ter)
       | .ok (.ok v') =>
         match (loan.withImpaired false).to_lawful with
         | .error e => .error e
         | .ok loan' => .ok (.ok { loan' := loan', pool' := v' })) := by
  simp only [Loan.manageUnimpair, Loan.changeImpairment, Loan.withImpaired]
  unfold_ter
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases AssetPool.adjustBalances v { loss := loan.principalOutstanding.operator_neg } with e | ter | v'
  · rfl
  · rfl
  · simp only
    rcases ({ loan.toRawLoan with isImpaired := false } : RawLoan).to_lawful with e | l <;> rfl

/-- Default: the interest and the cover, the vault update, then the broker and the re-checks. -/
lemma Loan.manageDefault_run (loan : Loan) (v : Vault) :
    (loan.manageDefault v).run =
      match loan.interestDue with
      | .error e => .error e
      | .ok interestDue =>
        match loan.defaultCover v with
        | .error e => .error e
        | .ok dc =>
          match AssetPool.adjustBalances v (loan.defaultChange interestDue dc) with
          | .error e => .error e
          | .ok (.error ter) => .ok (.error ter)
          | .ok (.ok v') =>
            match loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest with
            | .error e => .error e
            | .ok debtTotal' =>
              match loan.broker.coverAvailable.operator_sub dc .to_nearest with
              | .error e => .error e
              | .ok coverAvailable' =>
                match (loan.defaultedBroker debtTotal' coverAvailable').to_lawful with
                | .error e => .error e
                | .ok broker' =>
                  match (loan.defaultedLoan broker').to_lawful with
                  | .error e => .error e
                  | .ok loan' =>
                    .ok (.ok { loan' := loan', pool' := v', amountToPool := dc, amountToBroker := Number.zero }) := by
  simp only [Loan.manageDefault, ← Loan.defaultCoveredAmount_eq, Loan.defaultChange, Loan.defaultedBroker,
    Loan.defaultedLoan]
  unfold_ter
  rcases loan.interestDue with e | i
  · rfl
  simp only
  rcases defaultCoveredAmount loan.broker v loan.principalOutstanding with e | dc
  · rfl
  simp only
  rcases AssetPool.adjustBalances v _ with e | ter | v'
  · rfl
  · rfl
  simp only
  rcases loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest with e | d
  · rfl
  simp only
  rcases loan.broker.coverAvailable.operator_sub dc .to_nearest with e | c
  · rfl
  simp only
  rcases RawLoanBroker.to_lawful _ with e | b
  · rfl
  simp only
  rcases RawLoan.to_lawful _ with e | l <;> rfl

/-- A rejected vault update left a new balance negative (tefBAD_LEDGER) or LossUnrealized above
AssetsDeployed (tecLIMIT_EXCEEDED). -/
lemma Vault.adjustBalances_rejected_parts (v : Vault) (c : PoolBalanceChange) (ter : TER)
    (h : (v.adjustBalances c).run = .ok (.error ter)) :
    ∃ aa' ad' lu' ar' yu', Vault.AdjustSums v c aa' ad' lu' ar' yu' ∧
      ((ter = .tefBAD_LEDGER ∧
          (aa'.signum < 0 ∨ ad'.signum < 0 ∨ lu'.signum < 0 ∨ yu'.signum < 0 ∨ ar'.signum < 0)) ∨
        (ter = .tecLIMIT_EXCEEDED ∧ lu'.operator_gt ad' = true)) := by
  simp only [XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  · refine ⟨_, _, _, _, _, ⟨⟨_, ‹_›, ‹_›⟩, ‹_›, ‹_›, ‹_›, ‹_›⟩, Or.inl ⟨rfl, ?_⟩⟩
    have hc := ‹(_ || _) = true›
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    tauto
  · exact ⟨_, _, _, _, _, ⟨⟨_, ‹_›, ‹_›⟩, ‹_›, ‹_›, ‹_›, ‹_›⟩, Or.inr ⟨rfl, ‹_›⟩⟩

end XRPL.Model.Lending
