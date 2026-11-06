import XRPL.Properties.Lending.Ledger.Common.StuckLoan
import XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness
import XRPL.Properties.Lending.Ledger.Common.IsolationDefs

/-! # Reachable payments that pass their checks and fail

Each run breaks exactly one condition of the payment line of `loan_ops_total`: the coarsened vault of loan C (the
dust guard), the negative interest part of a tiny-rate instalment, and an instalment that is only management fee (the
C++ test LoanPayFeeOnlyInstalment). Each run is checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

open private niGenesis niTxs niGenesis_genesis from XRPL.Properties.Lending.Ledger.Common.NegativeInterestWitness

/-- A closed-ended IOU vault at Scale 0, subscription until 1000, redemption 14 years of 365 days later. -/
private def foSchedule : VaultSchedule := ⟨1000, 1000 + 14 * 31536000⟩

/-- The new vault VaultCreate makes for `foSchedule`. -/
private def foRawVault : RawVault := { cwRawVault with scale := 0, schedule := some foSchedule }

private def foVault : Vault := ⟨foRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def foGenesis : LendingLedger := { vault := foVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma foGenesis_genesis : foGenesis.Genesis where
  created := ⟨some 0, none, foSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨foVault.wf, foVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- An InterestRate of 45.5% and no other rate. -/
private def foRates : LoanRates :=
  { interestRate := 45500, lateInterestRate := 0, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- The regular payment of 1 at 100 seconds before the due date of instalment `k`. -/
private def foPay (k : UInt32) : List LendingTx :=
  [.close (1001 + k * 31536000 - 100), .loanPay 0 .regular ⟨false, 1000000000000000000, -18⟩]

/-- The run of the C++ test LoanPayFeeOnlyInstalment: a deposit of `10^12`, a broker with a 10% management fee, a
loan of 2 in twelve yearly instalments, and instalments 1 to 8 of 1 each. -/
private def foTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-3)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, some 10000, none, none⟩,
   .loanSet 0 ⟨false, 2000000000000000000, -18⟩ foRates cwFees (some 31536000) (some 12) (some 60) 0 false false] ++
  foPay 1 ++ foPay 2 ++ foPay 3 ++ foPay 4 ++ foPay 5 ++ foPay 6 ++ foPay 7 ++ foPay 8

/-- After `txs` the payment of loan `j` of exactly its amount due passes the payment checks, its interest part,
credit and the vault's size meet the conditions asked for, and it is rejected with `ter`. -/
private def payCheck (g : LendingLedger) (txs : List LendingTx) (j : Nat) (pt : LoanPaymentType)
    (late imp total parts credit : Bool) (ter : TER) : Bool :=
  match g.run txs with
  | .ok l =>
    match l.loan? j with
    | some e =>
      match l.broker? e.brokerIndex with
      | some b =>
        match e.loan.withBroker b with
        | .ok loan =>
          match loan.paymentComponents pt l.now with
          | .ok pc =>
            match pc.totalDue with
            | .ok td =>
              !l.vaultDeleted && decide (b.coverAvailable.toRat < 10 ^ 96) &&
                decide (loan.canPay pt = .tesSUCCESS) && decide (loan.isPaymentLate l.now = late) &&
                decide ((LendingTx.loanPay j pt td).preflight l = .tesSUCCESS) &&
                decide (e.loan.isImpaired = imp) && decide (l.vault.numericType = .fractional) &&
                (!total || decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
                  10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)) &&
                (match (loan.payInstalments l.vault pt td l.now).run with
                  | .ok (.ok p) =>
                    decide (loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 89) &&
                      (!parts || decide (0 ≤ p.amounts.interestPaid.toRat)) &&
                      (!credit || decide (0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨
                        p.loan.paymentRemaining = 0))
                  | _ => true) &&
                (match (l.apply (.loanPay j pt td)).run with
                  | .ok (.error t) => decide (t = ter)
                  | _ => false)
            | .error _ => false
          | .error _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

/-- A run whose check passes gives a reachable ledger with that rejected payment. -/
private lemma LendingLedger.payCheck_sound {g : LendingLedger} (hg : g.Genesis) {txs : List LendingTx} {j : Nat}
    {pt : LoanPaymentType} {late imp total parts credit : Bool} {ter : TER}
    (h : payCheck g txs j pt late imp total parts credit ter = true) :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? j = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
        b.coverAvailable.toRat < 10 ^ 96 ∧ loan.canPay pt = .tesSUCCESS ∧ loan.isPaymentLate l.now = late ∧
        loan.paymentComponents pt l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (LendingTx.loanPay j pt td).preflight l = .tesSUCCESS ∧ l.CreditFits j pt td ∧ l.FeeFits j pt td ∧
        e.loan.isImpaired = imp ∧ (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) ∧
        (total = true → l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
          10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) ∧
        (parts = true → ∀ p, (loan.payInstalments l.vault pt td l.now).run = .ok (.ok p) →
          0 ≤ p.amounts.interestPaid.toRat) ∧
        (credit = true → ∀ p, (loan.payInstalments l.vault pt td l.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        (l.apply (.loanPay j pt td)).run = .ok (.error ter) := by
  unfold payCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i b hb
  split at h
  case h_2 => cases h
  rename_i loan hw
  split at h
  case h_2 => cases h
  rename_i pc hpc
  split at h
  case h_2 => cases h
  rename_i td htd
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hnd, hca⟩, hc⟩, hlate⟩, hpre⟩, himp⟩, hfrac⟩, htot⟩, hinst⟩, hres⟩ := h
  have hlb : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, Loan.withBroker_eq hw]
  have hq : ∀ p, (loan.payInstalments l.vault pt td l.now).run = .ok (.ok p) →
      loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 89 ∧
      (parts = true → 0 ≤ p.amounts.interestPaid.toRat) ∧
      (credit = true → 0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨
        p.loan.paymentRemaining = 0) := by
    intro p hp
    rw [hp] at hinst
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hinst
    obtain ⟨⟨hfee, hpa⟩, hcr⟩ := hinst
    refine ⟨hfee, fun h1 => ?_, fun h1 => ?_⟩
    · rcases hpa with h0 | h0
      · rw [h1] at h0; cases h0
      · exact h0
    · rcases hcr with h0 | h0
      · rw [h1] at h0; cases h0
      · exact h0
  have hat : ∀ loan', l.LoanAt j loan' → loan' = loan := by
    intro loan' ⟨e', b', he', hb', hw'⟩
    rw [he] at he'
    obtain rfl := Option.some.inj he'
    rw [hb] at hb'
    obtain rfl := Option.some.inj hb'
    rw [hw] at hw'
    exact (Except.ok.inj hw').symm
  have hfit : l.CreditFits j pt td := by
    intro loan' p _ _ hint
    rw [hfrac] at hint
    cases hint
  have hfeeF : l.FeeFits j pt td := by
    intro loan' p hat' hp
    obtain rfl := hat loan' hat'
    exact Or.inl ⟨hfrac, (hq p hp).1⟩
  refine ⟨l, LendingLedger.Reachable.of_run hg hl, by simpa using hnd, e, b, loan, pc, td, he, hb, hw, hca, hc,
    hlate, hpc, htd, hpre, hfit, hfeeF, himp, fun hn => absurd (hn.symm.trans hfrac) (by decide), fun h1 => ?_,
    fun h1 p hp => (hq p hp).2.1 h1,
    fun h1 p hp => (hq p hp).2.2 h1, ?_⟩
  · simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at htot
    rcases htot with h0 | h0
    · rw [h1] at h0; cases h0
    · exact h0
  · split at hres
    · rename_i t ht
      obtain rfl := of_decide_eq_true hres
      exact ht
    · cases hres

private lemma payCheck_coarsened :
    payCheck cwGenesis cwCoarsenedTxs 2 .late true false false true true .tecPRECISION_LOSS = true := by
  native_decide

private lemma payCheck_negative_interest :
    payCheck niGenesis niTxs 0 .regular false false true false true .tecLIMIT_EXCEEDED = true := by
  native_decide

private lemma payCheck_fee_only :
    payCheck foGenesis (foTxs ++ [.close (1001 + 9 * 31536000 - 100)]) 0 .regular false false true true false
      .tecPRECISION_LOSS = true := by
  native_decide

/-- A late payment that passes its checks can fail on a coarsened vault. Loan C is late and not impaired, and its
late payment of exactly totalDue rounds to no credit. -/
lemma LendingLedger.payment_total_witness :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 2 = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
        b.coverAvailable.toRat < 10 ^ 96 ∧ loan.canPay .late = .tesSUCCESS ∧ loan.isPaymentLate l.now = true ∧
        loan.paymentComponents .late l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (LendingTx.loanPay 2 .late td).preflight l = .tesSUCCESS ∧ l.CreditFits 2 .late td ∧
        l.FeeFits 2 .late td ∧ e.loan.isImpaired = false ∧
        (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) ∧
        (∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) → 0 ≤ p.amounts.interestPaid.toRat) ∧
        (∀ p, (loan.payInstalments l.vault .late td l.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        (l.apply (.loanPay 2 .late td)).run = .ok (.error .tecPRECISION_LOSS) := by
  obtain ⟨l, hr, hnd, e, b, loan, pc, td, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hx, -, hp, hc, hres⟩ :=
    LendingLedger.payCheck_sound cwGenesis_genesis payCheck_coarsened
  exact ⟨l, hr, hnd, e, b, loan, pc, td, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hx, hp rfl, hc rfl, hres⟩

/-- A regular payment that passes its checks fails on a negative interest part. The third instalment of a loan
at a tiny rate takes more principal than its amount, so paying exactly its amount due is rejected. -/
lemma LendingLedger.payment_total_negative_interest_witness :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 0 = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
        b.coverAvailable.toRat < 10 ^ 96 ∧ loan.canPay .regular = .tesSUCCESS ∧
        loan.isPaymentLate l.now = false ∧ loan.paymentComponents .regular l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (LendingTx.loanPay 0 .regular td).preflight l = .tesSUCCESS ∧ l.CreditFits 0 .regular td ∧
        l.FeeFits 0 .regular td ∧ e.loan.isImpaired = false ∧
        (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) ∧
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
        (∀ p, (loan.payInstalments l.vault .regular td l.now).run = .ok (.ok p) →
          0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat ∨ p.loan.paymentRemaining = 0) ∧
        (l.apply (.loanPay 0 .regular td)).run = .ok (.error .tecLIMIT_EXCEEDED) := by
  obtain ⟨l, hr, hnd, e, b, loan, pc, td, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hx, ht, -, hc, hres⟩ :=
    LendingLedger.payCheck_sound niGenesis_genesis payCheck_negative_interest
  exact ⟨l, hr, hnd, e, b, loan, pc, td, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hx, ht rfl, hc rfl, hres⟩

/-- A regular payment that passes its checks fails on an instalment that is only management fee. Instalment 9
of a loan of 2 at 45.5% sends its whole amount to the broker, so AssetsAvailable does not move. -/
lemma LendingLedger.payment_total_fee_only_witness :
    ∃ l : LendingLedger, l.Reachable ∧ l.vaultDeleted = false ∧
      ∃ (e : LoanEntry) (b : LoanBroker) (loan : Loan) (pc : PaymentComponents) (td : Number),
        l.loan? 0 = some e ∧ l.broker? e.brokerIndex = some b ∧ e.loan.withBroker b = .ok loan ∧
        b.coverAvailable.toRat < 10 ^ 96 ∧ loan.canPay .regular = .tesSUCCESS ∧
        loan.isPaymentLate l.now = false ∧ loan.paymentComponents .regular l.now = .ok pc ∧ pc.totalDue = .ok td ∧
        (LendingTx.loanPay 0 .regular td).preflight l = .tesSUCCESS ∧ l.CreditFits 0 .regular td ∧
        l.FeeFits 0 .regular td ∧ e.loan.isImpaired = false ∧
        (l.vault.numericType = .native → loan.totalValueOutstanding.toRat < 6 * 10 ^ 14) ∧
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
        (∀ p, (loan.payInstalments l.vault .regular td l.now).run = .ok (.ok p) →
          0 ≤ p.amounts.interestPaid.toRat) ∧
        (l.apply (.loanPay 0 .regular td)).run = .ok (.error .tecPRECISION_LOSS) := by
  obtain ⟨l, hr, hnd, e, b, loan, pc, td, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hx, ht, hp, -, hres⟩ :=
    LendingLedger.payCheck_sound foGenesis_genesis payCheck_fee_only
  exact ⟨l, hr, hnd, e, b, loan, pc, td, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hx, ht rfl, hp rfl, hres⟩

end XRPL.Model.Lending
