import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Ledger.Common.PaymentsCommute
import XRPL.Properties.Lending.Ledger.Common.PaymentsCommuteWitness
import XRPL.Properties.Lending.Ledger.Common.DefaultOrder
import XRPL.Properties.Lending.Ledger.Common.DefaultOrderWitness
import XRPL.Properties.Lending.Ledger.Common.Isolation
import XRPL.Properties.Lending.Ledger.Common.IsolationWitness
import XRPL.Properties.Lending.Ledger.Common.BrokerSubsequence
import XRPL.Properties.Lending.Ledger.Common.BrokerSubsequenceReplay
import XRPL.Properties.Lending.Ledger.Common.BrokerSubsequenceWitness
import XRPL.Properties.Lending.Ledger.Common.CoverWithdrawDefault
import XRPL.Properties.Lending.Ledger.Common.LoanSubsequence
import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceReplay
import XRPL.Properties.Lending.Ledger.Common.LoanSubsequenceWitness
import XRPL.Properties.Lending.Ledger.Common.OrderCreates
import XRPL.Properties.Lending.Loan.Common.OrderDefaults
import XRPL.Properties.Lending.Loan.Common.Twin

/-! # Order of transactions

A default's cover depends on the broker's DebtTotal at the time of the default, and all loans share one Open limit
of `9·10^15` base units. Loans created with the same terms are charged the same for every instalment. Other
transactions never change a loan: its own transactions alone leave the same fields, and a broker's and its loans'
transactions alone leave the same broker, up to how a coarsened vault rounds a default's cover. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Lending.Loan.doPayment from XRPL.Model.Lending.Loan.LoanPay

/-- Payments on two loans -> the same vault and DebtTotal in either order. Every other broker field is the same too,
and each loan differs only in its copy of the broker. CoverAvailable can differ, by design. -/
theorem Lending.payments_comm (l la lb lab lba : LendingLedger) (hr : l.Reachable) (i j : Nat) (hij : i ≠ j)
    (pt pt' : LoanPaymentType) (a a' : Number)
    (ha : (l.apply (.loanPay i pt a)).run = .ok (.ok la)) (hab : (la.apply (.loanPay j pt' a')).run = .ok (.ok lab))
    (hb : (l.apply (.loanPay j pt' a')).run = .ok (.ok lb)) (hba : (lb.apply (.loanPay i pt a)).run = .ok (.ok lba))
    -- the payments are at base scale: AssetsAvailable' stays below `10^16` base units (FV_M4_25)
    (htotal : lab.vault.assetsAvailable.toRat < 10 ^ 16 * (10 : ℚ) ^ lab.vault.baseExponent) :
    lab.vault = lba.vault ∧
      (∀ k, lab.broker? k = lba.broker? k ∨ ∃ b b', lab.broker? k = some b ∧ lba.broker? k = some b' ∧
        b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable }) ∧
      (∀ k, lab.loan? k = lba.loan? k ∨ ∃ e e', lab.loan? k = some e ∧ lba.loan? k = some e' ∧
        e'.brokerIndex = e.brokerIndex ∧ e'.loan.toRawLoan = { e.loan.toRawLoan with broker := e'.loan.broker }) :=
  LendingLedger.payments_comm_proof l la lb lab lba hr i j hij pt pt' a a' ha hab hb hba htotal

/-- Witness: a run where the two orders leave different vaults. Loan A's late payment takes AssetsAvailable past
`10^16` base units, and loan D's instalment of 1.9 then credits 1, while paid first it leaves one unit more. -/
theorem Lending.payments_comm_attained :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat) (pt pt' : LoanPaymentType) (a a' : Number),
      l.Reachable ∧ i ≠ j ∧
      (l.apply (.loanPay i pt a)).run = .ok (.ok la) ∧ (la.apply (.loanPay j pt' a')).run = .ok (.ok lab) ∧
      (l.apply (.loanPay j pt' a')).run = .ok (.ok lb) ∧ (lb.apply (.loanPay i pt a)).run = .ok (.ok lba) ∧
      lab.vault ≠ lba.vault :=
  LendingLedger.payments_comm_coarsened_witness

/-- Two defaults -> the same vault and brokers in either order. Every loan reads the same too, only the broker copy
stored with a defaulted loan differs. -/
theorem Lending.defaults_comm (l la lb lab lba : LendingLedger) (hr : l.Reachable) (i j : Nat)
    (ha : (l.apply (.loanManage i .default)).run = .ok (.ok la))
    (hab : (la.apply (.loanManage j .default)).run = .ok (.ok lab))
    (hb : (l.apply (.loanManage j .default)).run = .ok (.ok lb))
    (hba : (lb.apply (.loanManage i .default)).run = .ok (.ok lba))
    -- the liquidation amount caps none of the four defaults (Question FV_M4_18)
    (hliq : l.DefaultUncapped i ∧ la.DefaultUncapped j ∧ l.DefaultUncapped j ∧ lb.DefaultUncapped i)
    -- the vault is not coarsened (Bug FV_M4_28)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    -- CoverAvailable is below 2^63 base units, so a Number takes each cover off it exactly
    (hcover : ∀ loan, l.LoanAt i loan →
      loan.broker.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) :
    lab.vault = lba.vault ∧ lab.brokers = lba.brokers ∧ ∀ k loan, lab.LoanAt k loan ↔ lba.LoanAt k loan :=
  LendingLedger.defaults_comm_proof l la lb lab lba hr i j ha hab hb hba hliq htotal hcover

/-- Witness: a run where the liquidation amount caps the defaults and the two orders give a different vault. Loans
of 800 and 150 on a broker with DebtTotal 950: the larger first gets 935 of cover, the other order only 870. -/
theorem Lending.defaults_comm_attained :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat), l.Reachable ∧
      (l.apply (.loanManage i .default)).run = .ok (.ok la) ∧
      (la.apply (.loanManage j .default)).run = .ok (.ok lab) ∧
      (l.apply (.loanManage j .default)).run = .ok (.ok lb) ∧
      (lb.apply (.loanManage i .default)).run = .ok (.ok lba) ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
      (∀ loan, l.LoanAt i loan → loan.broker.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) ∧
      lab.vault ≠ lba.vault :=
  LendingLedger.defaults_comm_liquidation_witness

/-- Witness: a run on a coarsened vault where the two orders give a different vault. AssetsAvailable is
999999999999999.9, and each cover is floored at the scale of AssetsAvailable'. -/
theorem Lending.defaults_comm_coarsened_attained :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat), l.Reachable ∧
      (l.apply (.loanManage i .default)).run = .ok (.ok la) ∧
      (la.apply (.loanManage j .default)).run = .ok (.ok lab) ∧
      (l.apply (.loanManage j .default)).run = .ok (.ok lb) ∧
      (lb.apply (.loanManage i .default)).run = .ok (.ok lba) ∧
      (l.DefaultUncapped i ∧ la.DefaultUncapped j ∧ l.DefaultUncapped j ∧ lb.DefaultUncapped i) ∧
      (∀ loan, l.LoanAt i loan → loan.broker.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) ∧
      lab.vault ≠ lba.vault :=
  LendingLedger.defaults_comm_coarsened_witness

/-- Witness: a run where the two orders give a different broker. The cover of 1000000000001 on a vault at Scale 10 is
about 10^22 base units, above 2^63, and a Number rounds each cover taken off it to whole millionths. -/
theorem Lending.defaults_comm_cover_attained :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat), l.Reachable ∧
      (l.apply (.loanManage i .default)).run = .ok (.ok la) ∧
      (la.apply (.loanManage j .default)).run = .ok (.ok lab) ∧
      (l.apply (.loanManage j .default)).run = .ok (.ok lb) ∧
      (lb.apply (.loanManage i .default)).run = .ok (.ok lba) ∧
      (l.DefaultUncapped i ∧ la.DefaultUncapped j ∧ l.DefaultUncapped j ∧ lb.DefaultUncapped i) ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
      lab.brokers ≠ lba.brokers :=
  LendingLedger.defaults_comm_cover_witness

/-- Transaction on one loan, or on one broker or its loans -> every loan transaction on another loan of the same broker,
or on another broker's loan, that would have succeeded still succeeds. -/
theorem Lending.isolation (l la lb : LendingLedger) (hr : l.Reachable) (j : Nat) (e' : LoanEntry) (tx tx' : LendingTx)
    (he' : l.loan? j = some e') (htx' : tx'.loanIndex? = some j)
    (ha : (l.apply tx).run = .ok (.ok la)) (hb : (l.apply tx').run = .ok (.ok lb)) :
    -- the first is a LoanSet or a transaction on another loan of the same broker, at the same close time
    (l.loanTxBroker? tx = some e'.brokerIndex → tx.loanIndex? ≠ some j →
      -- a LoanAccept of loan `j` still fits its interest in the Open limit (Question FV_M4_33)
      (∀ x, tx' = .loanAccept j → e'.loan.interestDue = .ok x → la.vault.exceedsOpenLimit x = .ok false) →
      -- the first transaction leaves the vault not coarsened (the dust guard, FV_M4_21)
      la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent →
      -- the broker holds its cover as an amount of the asset, a balance the model does not track
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) →
      -- a payment's credit fits the XRP or MPT supply, and its fee fits beside the cover, which the model does not
      -- track
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) →
      (∀ pt amount, tx' = .loanPay j pt amount → la.FeeFits j pt amount) →
      ∃ lab, (la.apply tx').run = .ok (.ok lab)) ∧
    -- the first is a broker transaction, a LoanSet or a transaction on a loan of broker `k`
    (∀ k : Nat, l.txBroker? tx = some k → k ≠ e'.brokerIndex →
      -- a LoanAccept of loan `j` still fits its interest in the Open limit (Question FV_M4_33)
      (∀ x, tx' = .loanAccept j → e'.loan.interestDue = .ok x → la.vault.exceedsOpenLimit x = .ok false) →
      -- the first transaction leaves the vault not coarsened (the dust guard, FV_M4_21)
      la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent →
      -- the broker holds its cover as an amount of the asset, a balance the model does not track
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) →
      -- a payment's credit fits the XRP or MPT supply, which the model does not track
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) →
      ∃ lab, (la.apply tx').run = .ok (.ok lab)) :=
  ⟨fun hon hj hopen htotal hca hcredit hfee => LendingLedger.payment_isolation_proof l la lb hr j e' tx tx' he' hon hj
      htx' ha hb hopen htotal hca hcredit hfee,
    fun k hon hkj hopen htotal hca hcredit => LendingLedger.broker_isolation_proof l la lb hr j k e' tx tx' he' hon hkj
      htx' ha hb hopen htotal hca hcredit⟩

/-- Witness: a run where accepting another loan is then rejected. Two pending loans on one broker each fit the
Open limit, and once one is accepted and books its interest the other one exceeds it. -/
theorem Lending.isolation_loan_attained :
    ∃ (l la lb : LendingLedger) (j : Nat) (e' : LoanEntry) (tx tx' : LendingTx),
      l.Reachable ∧ l.loan? j = some e' ∧ l.loanTxBroker? tx = some e'.brokerIndex ∧ tx.loanIndex? ≠ some j ∧
      tx'.loanIndex? = some j ∧ (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.FeeFits j pt amount) ∧
      (la.apply tx').run = .ok (.error .tecLIMIT_EXCEEDED) :=
  LendingLedger.payment_isolation_open_witness

/-- Witness: a run where a payment on another loan is then rejected. A late payment of 7000000000000000 on loan A
coarsens the vault, and a payment of 0.1 on loan C of the same broker rounds to no credit. -/
theorem Lending.isolation_loan_coarsened_attained :
    ∃ (l la lb : LendingLedger) (j : Nat) (e' : LoanEntry) (tx tx' : LendingTx),
      l.Reachable ∧ l.loan? j = some e' ∧ l.loanTxBroker? tx = some e'.brokerIndex ∧ tx.loanIndex? ≠ some j ∧
      tx'.loanIndex? = some j ∧ (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      (∀ x, tx' = .loanAccept j → e'.loan.interestDue = .ok x → la.vault.exceedsOpenLimit x = .ok false) ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.FeeFits j pt amount) ∧
      (la.apply tx').run = .ok (.error .tecPRECISION_LOSS) :=
  LendingLedger.payment_isolation_coarsened_witness

/-- Witness: a run where accepting another broker's loan is then rejected. Two pending loans on two brokers each
fit the Open limit, and once one is accepted and books its interest the other one exceeds it. -/
theorem Lending.isolation_broker_attained :
    ∃ (l la lb : LendingLedger) (j k : Nat) (e' : LoanEntry) (tx tx' : LendingTx),
      l.Reachable ∧ l.loan? j = some e' ∧ l.txBroker? tx = some k ∧ k ≠ e'.brokerIndex ∧
      tx'.loanIndex? = some j ∧ (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (la.apply tx').run = .ok (.error .tecLIMIT_EXCEEDED) :=
  LendingLedger.broker_isolation_open_witness

/-- Witness: a run where a payment on another broker's loan is then rejected. A late payment of 7000000000000000
on loan A of one broker coarsens the vault, and a payment of 0.1 on loan C of another broker rounds to no credit. -/
theorem Lending.isolation_broker_coarsened_attained :
    ∃ (l la lb : LendingLedger) (j k : Nat) (e' : LoanEntry) (tx tx' : LendingTx),
      l.Reachable ∧ l.loan? j = some e' ∧ l.txBroker? tx = some k ∧ k ≠ e'.brokerIndex ∧
      tx'.loanIndex? = some j ∧ (l.apply tx).run = .ok (.ok la) ∧ (l.apply tx').run = .ok (.ok lb) ∧
      (∀ x, tx' = .loanAccept j → e'.loan.interestDue = .ok x → la.vault.exceedsOpenLimit x = .ok false) ∧
      (∀ b, la.broker? e'.brokerIndex = some b → b.coverAvailable.toRat < 10 ^ 96) ∧
      (∀ pt amount, tx' = .loanPay j pt amount → la.CreditFits j pt amount) ∧
      (la.apply tx').run = .ok (.error .tecPRECISION_LOSS) :=
  LendingLedger.broker_isolation_coarsened_witness

/-- A sequence and its subsequence of one loan's transactions, each at the same time -> once the loan is active,
every later transaction on it succeeds and the loan's fields end with the same values in both. -/
theorem Lending.Reachable.loan_subsequence (start l : LendingLedger) (txs : List LendingTx) (i : Nat)
    (hr : start.Reachable) (hrun : LendingLedger.Reaches start txs l) :
    -- every later transaction on the loan succeeds once it is active in both: the vault without the other
    -- transactions is not coarsened, and the balances the model does not track fit
    (∀ (pre post : List LendingTx) (m : LendingLedger) (loan : Loan), txs = pre ++ post →
      LendingLedger.Reaches start (start.loanSubsequence i pre) m → m.LoanAt (start.aloneIndex i) loan →
      loan.isPending = false → start.NotCoarsenedAlong (start.loanSubsequence i txs) →
      start.UntrackedFitsAlong (start.aloneIndex i) (start.loanSubsequence i txs) →
      ∃ m', LendingLedger.Reaches start (start.loanSubsequence i txs) m') ∧
    -- the loan's fields end with the same values in both
    ∀ (m : LendingLedger) (loan loan' : Loan), LendingLedger.Reaches start (start.loanSubsequence i txs) m →
      l.LoanAt i loan → m.LoanAt (start.aloneIndex i) loan' →
      loan'.toRawLoan = { loan.toRawLoan with broker := loan'.toRawLoan.broker } :=
  ⟨LendingLedger.loan_subsequence_success_of_replay LendingLedger.loanTx_replay_twin hr hrun,
    fun _ _ _ hsub hat hat' => LendingLedger.loan_subsequence_fields_proof hr hrun hsub hat hat'⟩

/-- Witness: a subsequence where a payment fails. A VaultWithdraw un-coarsens the vault so loan C's late payment of
0.1 passes. Without it AssetsAvailable 1874246907153726 sits on the grid of 1 and the payment fails. -/
theorem Lending.Reachable.loan_subsequence_attained :
    ∃ (start l : LendingLedger) (txs : List LendingTx) (i : Nat) (pre post : List LendingTx) (m : LendingLedger)
      (loan : Loan),
      start.Reachable ∧ LendingLedger.Reaches start txs l ∧ txs = pre ++ post ∧
      LendingLedger.Reaches start (start.loanSubsequence i pre) m ∧ m.LoanAt (start.aloneIndex i) loan ∧
      loan.isPending = false ∧ start.UntrackedFitsAlong (start.aloneIndex i) (start.loanSubsequence i txs) ∧
      ¬ ∃ m', LendingLedger.Reaches start (start.loanSubsequence i txs) m' :=
  LendingLedger.loan_subsequence_witness

/-- A sequence and its subsequence of one broker's and its loans' transactions, each at the same time -> when the
broker and its loans are created and accepted, the rest succeeds and the broker's fields end the same in both. -/
theorem Lending.Reachable.broker_subsequence (start l : LendingLedger) (txs : List LendingTx) (k : Nat)
    (hr : start.Reachable) (hrun : LendingLedger.Reaches start txs l) :
    -- every other transaction on the broker or its loans succeeds: the vault is not coarsened in either sequence,
    -- and the balances the model does not track fit
    (start.OpeningsSucceedAlong (start.brokerSubsequence k txs) → start.NotCoarsenedAlong txs →
      start.NotCoarsenedAlong (start.brokerSubsequence k txs) →
      start.BrokerUntrackedFitsAlong (start.aloneBrokerIndex k) (start.brokerSubsequence k txs) →
      ∃ m, LendingLedger.Reaches start (start.brokerSubsequence k txs) m) ∧
    -- the broker's fields end with the same values in both, CoverAvailable while the vault is not coarsened
    ∀ (m : LendingLedger) (b b' : LoanBroker), LendingLedger.Reaches start (start.brokerSubsequence k txs) m →
      l.broker? k = some b → m.broker? (start.aloneBrokerIndex k) = some b' →
      b'.toRawLoanBroker = { b.toRawLoanBroker with coverAvailable := b'.coverAvailable } ∧
      (start.NotCoarsenedAlong txs → start.NotCoarsenedAlong (start.brokerSubsequence k txs) →
        b'.coverAvailable.toRat = b.coverAvailable.toRat) :=
  ⟨LendingLedger.broker_subsequence_success_of_replay LendingLedger.loanTx_replay_twin_at
      LendingLedger.brokerTx_replay_same hr hrun,
    fun _ _ _ hsub hb hb' =>
      LendingLedger.broker_subsequence_fields_proof LendingLedger.brokerTx_result_same hr hrun hsub hb hb'⟩

/-- Witness: a subsequence where a payment fails. A VaultWithdraw un-coarsens the vault so a late payment of 0.1 on
a loan of broker 0 passes. Without it AssetsAvailable 1874246907153726 sits on the grid of 1 and the payment fails. -/
theorem Lending.Reachable.broker_subsequence_attained :
    ∃ (start l : LendingLedger) (txs : List LendingTx) (k : Nat),
      start.Reachable ∧ LendingLedger.Reaches start txs l ∧
      start.OpeningsSucceedAlong (start.brokerSubsequence k txs) ∧
      start.BrokerUntrackedFitsAlong (start.aloneBrokerIndex k) (start.brokerSubsequence k txs) ∧
      ¬ ∃ m, LendingLedger.Reaches start (start.brokerSubsequence k txs) m :=
  LendingLedger.broker_subsequence_witness

/-- Witness: a sequence where CoverAvailable differs. A default of 15 with 1.5 of cover moves only 1 after a late
payment on another broker's loan coarsens the vault, and 1.5 without it, so the cover ends at 1 and at 0.5. -/
theorem Lending.Reachable.broker_subsequence_cover_attained :
    ∃ (start l : LendingLedger) (txs : List LendingTx) (k : Nat) (m : LendingLedger) (b b' : LoanBroker),
      start.Reachable ∧ LendingLedger.Reaches start txs l ∧
      LendingLedger.Reaches start (start.brokerSubsequence k txs) m ∧ l.broker? k = some b ∧
      m.broker? (start.aloneBrokerIndex k) = some b' ∧ b'.coverAvailable.toRat ≠ b.coverAvailable.toRat :=
  LendingLedger.broker_subsequence_cover_witness

/-- Two loans with the same fields, but on different brokers and vaults with the same ManagementFeeRate, asset type and
base scale -> the same totalDue for every instalment at the same time. -/
theorem Lending.same_terms_same_payments (b b' : LoanBroker) (v v' : Vault) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    (r r' : LoanWithDisbursement Vault) (hnt : b'.numericType = b.numericType)
    (hm : b'.managementFeeRate = b.managementFeeRate) (hbe : v'.baseExponent = v.baseExponent)
    (h : (Loan.create b v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (h' : (Loan.create b' v' principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r')) :
    Loan.Twin r.loan' r'.loan' ∧
      (∀ l l' : Loan, Loan.Twin l l' → ∀ (pt : LoanPaymentType) (now : UInt32),
        l'.paymentComponents pt now = l.paymentComponents pt now) ∧
      -- `doPayment` is the loan's update for one instalment, so paying the same instalments keeps the two loans alike
      ∀ (l l' n n' : Loan) (pc : PaymentComponents), Loan.Twin l l' → Lending.Loan.doPayment l pc = .ok n →
        Lending.Loan.doPayment l' pc = .ok n' → Loan.Twin n n' :=
  ⟨Loan.create_twin b b' v v' principal rates fees schedule allowsOverpayment pending r r' hnt hm hbe h h',
    fun _ _ ht pt now => Loan.paymentComponents_twin ht pt now,
    fun _ _ _ _ pc ht hn hn' => Loan.doPayment_twin ht pc hn hn'⟩

/-- Two new loans -> the same vault and brokers in either order. -/
theorem Lending.creates_comm (l lA lB lAB lBA : LendingLedger) (i j : Nat) (pa pb : Number) (ra rb : LoanRates)
    (fa fb : LoanFees) (pia pta gpa pib ptb gpb : Option UInt32) (sda sdb : UInt32) (tsa aoa tsb aob : Bool)
    (hr : l.Reachable)
    (hA : (l.apply (.loanSet i pa ra fa pia pta gpa sda tsa aoa)).run = .ok (.ok lA))
    (hAB : (lA.apply (.loanSet j pb rb fb pib ptb gpb sdb tsb aob)).run = .ok (.ok lAB))
    (hB : (l.apply (.loanSet j pb rb fb pib ptb gpb sdb tsb aob)).run = .ok (.ok lB))
    (hBA : (lB.apply (.loanSet i pa ra fa pia pta gpa sda tsa aoa)).run = .ok (.ok lBA)) :
    lAB.vault = lBA.vault ∧ lAB.brokers = lBA.brokers :=
  LendingLedger.creates_comm_proof l lA lB lAB lBA i j pa pb ra rb fa fb pia pta gpa pib ptb gpb sda sdb tsa aoa
    tsb aob hr hA hAB hB hBA

/-- Impair then default -> the same vault and broker as a direct default. -/
theorem Lending.impair_default_same (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (r₁ : LoanWithPool Vault) (r₂ r : LoanWithAmounts Vault)
    (himp : loan.isImpaired = false) -- LoanManage preclaim
    (h₁ : (loan.manageImpair l.vault l.now).run = .ok (.ok r₁))
    (h₂ : (r₁.loan'.manageDefault r₁.pool').run = .ok (.ok r₂))
    (h : (loan.manageDefault l.vault).run = .ok (.ok r)) :
    r₂.pool' = r.pool' ∧ r₂.loan'.broker = r.loan'.broker :=
  Loan.impair_default_same_proof loan l.vault l.now r₁ r₂ r himp h₁ h₂ h hr.availableStored (hr.impair_fits hat)

/-- LoanBrokerCoverWithdraw then default -> the same vault as a direct default. -/
theorem Lending.coverWithdraw_default_same (l la lab lb : LendingLedger) (hr : l.Reachable) (k i : Nat)
    (amount : STAmount) (ha : (l.apply (.loanBrokerCoverWithdraw k amount)).run = .ok (.ok la))
    (hab : (la.apply (.loanManage i .default)).run = .ok (.ok lab))
    (hb : (l.apply (.loanManage i .default)).run = .ok (.ok lb)) :
    lab.vault = lb.vault :=
  LendingLedger.coverWithdraw_default_same_proof l la lab lb hr k i amount ha hab hb

end XRPL.Model
