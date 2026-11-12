import XRPL.Properties.Lending.Ledger.Common.ShareValueRunDefs
import XRPL.Properties.Lending.Ledger.Common.PayoffWitness
import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Vault.Proofs.MaxValueFits

/-! # Sequences that lower shareValue

Two one-transaction sequences for the sequence row on shareValue. In the first a VaultWithdraw of a holder that is
not the only one pays a price rounded to nearest above the worth of the share. In the second a payment on a coarsened
vault is credited below what it pays. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule WithdrawAmount)

/-- The only step of a one-transaction sequence is its transaction, run on the first ledger. -/
private lemma single_step {pre : List LendingTx} {t tx : LendingTx} (h : pre ++ [t] <+: [tx]) :
    pre = [] ∧ t = tx := by
  obtain ⟨suffix, hs⟩ := h
  have hlen := congrArg List.length hs
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hpre : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hpre
  simp only [List.nil_append, List.cons_append, List.cons.injEq] at hs
  exact ⟨rfl, hs.1⟩

/-- A one-transaction sequence passes through its first ledger and its last ledger only. -/
private lemma LendingLedger.Reaches.single_cases {start l' l : LendingLedger} {tx : LendingTx}
    {pre : List LendingTx} (hok : (start.apply tx).run = .ok (.ok l')) (hp : pre <+: [tx])
    (hr : LendingLedger.Reaches start pre l) : l = start ∨ l = l' := by
  obtain ⟨suffix, hs⟩ := hp
  cases pre with
  | nil => exact Or.inl hr.nil_inv
  | cons t ts =>
    simp only [List.cons_append, List.cons.injEq] at hs
    obtain ⟨rfl, hts⟩ := hs
    obtain rfl : ts = [] := (List.append_eq_nil_iff.mp hts).1
    obtain ⟨l₁, h₁, hr₁⟩ := hr.cons_inv
    rw [hok] at h₁
    obtain rfl := Except.ok.inj (Except.ok.inj h₁)
    exact Or.inr hr₁.nil_inv

/-- For a one-transaction sequence the conditions on the transaction and on SharesTotal are facts about its
transaction, its first ledger and its last ledger. -/
private lemma LendingLedger.along_single {start l' : LendingLedger} {tx : LendingTx}
    (hok : (start.apply tx).run = .ok (.ok l')) (hkeep : start.lowersShareValue tx = false)
    (hS : start.vault.sharesTotal ≠ Number.zero) (hS' : l'.vault.sharesTotal ≠ Number.zero)
    (hfit : start.vault.sharesTotal.toRat + start.sharesCreatedOf tx ≤ 2 ^ 63 - 1) :
    start.KeepsShareValueAlong [tx] ∧ start.SharesLeftAlong [tx] ∧ start.SharesFitAlong [tx] := by
  refine ⟨fun pre l t hp hr => ?_, fun pre l hp hr => ?_, fun pre l t hp hr => ?_⟩
  · obtain ⟨rfl, rfl⟩ := single_step hp
    obtain rfl := hr.nil_inv
    exact hkeep
  · rcases hr.single_cases hok hp with rfl | rfl <;> assumption
  · obtain ⟨rfl, rfl⟩ := single_step hp
    obtain rfl := hr.nil_inv
    exact hfit

/-- A one-transaction sequence is not coarsened along the way when its first and last ledgers are not. -/
private lemma LendingLedger.notCoarsenedAlong_single {start l' : LendingLedger} {tx : LendingTx}
    (hok : (start.apply tx).run = .ok (.ok l')) (hnc : start.NotCoarsened) (hnc' : l'.NotCoarsened) :
    start.NotCoarsenedAlong [tx] := by
  intro pre l hp hr
  rcases hr.single_cases hok hp with rfl | rfl <;> assumption

/-- A one-transaction sequence moves whole worth along the way when its transaction does on the first ledger. -/
private lemma LendingLedger.wholeWorthAlong_single {start : LendingLedger} {tx : LendingTx}
    (hwhole : start.movesWholeWorth tx) : start.WholeWorthAlong [tx] := by
  intro pre l t hp hr
  obtain ⟨rfl, rfl⟩ := single_step hp
  obtain rfl := hr.nil_inv
  exact hwhole

/-- Subscription until 1000, redemption 30 days later. -/
private def ndSchedule : VaultSchedule := ⟨1000, 1000 + 30 * 86400⟩

/-- The new MPT vault VaultCreate makes for `ndSchedule`. -/
private def ndRawVault : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := NumericType.int64, scale := 0, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some ndSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

private def ndVault : Vault := ⟨ndRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def ndGenesis : LendingLedger := { vault := ndVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma ndGenesis_genesis : ndGenesis.Genesis where
  created := ⟨none, none, ndSchedule, none, false, NumericType.int64, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨ndVault.wf, ndVault.valid⟩⟩
  holds_asset := Or.inr (Or.inr rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- One unit of the MPT, and also one share. -/
private def ndUnit : STAmount := STAmount.unchecked .int64 1 0 false

/-- Holders 0 and 1 deposit 1 unit each for 1 share each, then a donation of 1 unit. The vault holds 3 units for 2
shares. -/
private def ndTxs : List LendingTx :=
  [.vaultDeposit 0 ndUnit false, .vaultDeposit 1 ndUnit false, .vaultDeposit 0 ndUnit true]

/-- Holder 0 redeems its share. -/
private def ndWithdraw : LendingTx := .vaultWithdraw 0 (.vaultShares ndUnit)

/-- The withdrawal succeeds on a vault that is not coarsened, leaves shares, and lowers shareValue. Holder 0 is not
the only holder. -/
private def ndCheck : Bool :=
  match ndGenesis.run ndTxs with
  | .ok l =>
    match (l.apply ndWithdraw).run with
    | .ok (.ok l') =>
      decide (l'.vault.toRawVault.shareValue < l.vault.toRawVault.shareValue) && !l.isSoleShareholder 0 &&
        decide (l.vault.sharesTotal ≠ Number.zero) && decide (l'.vault.sharesTotal ≠ Number.zero) &&
        decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
          10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) &&
        decide (l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat <
          10 ^ 16 * (10 : ℚ) ^ l'.vault.baseExponent)
    | _ => false
  | .error _ => false

private lemma ndCheck_true : ndCheck = true := by native_decide

/-- A sequence that meets every condition of the sequence row except the whole worth of the shares, and lowers
shareValue. One share of 2, worth `1.5`, is redeemed for `2`, and shareValue falls from `1.5` to `1`. -/
lemma LendingLedger.no_dilution_withdraw_witness :
    ∃ (start l : LendingLedger) (txs : List LendingTx), start.Reachable ∧ LendingLedger.Reaches start txs l ∧
      start.KeepsShareValueAlong txs ∧ start.SharesLeftAlong txs ∧ start.NotCoarsenedAlong txs ∧
      start.SharesFitAlong txs ∧ l.vault.toRawVault.shareValue < start.vault.toRawVault.shareValue := by
  have h := ndCheck_true
  unfold ndCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  split at h
  case h_2 => cases h
  rename_i l' hl'
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hlt, hsole⟩, hS⟩, hS'⟩, hnc⟩, hnc'⟩ := h
  obtain ⟨hk, hs, hf⟩ := LendingLedger.along_single hl' hsole hS hS' (by
    show l.vault.sharesTotal.toRat + (0 : ℚ) ≤ 2 ^ 63 - 1
    linarith [Vault.sharesTotal_le_maxRep l.vault])
  exact ⟨l, l', [ndWithdraw], LendingLedger.Reachable.of_run ndGenesis_genesis hl, .single hl', hk, hs,
    LendingLedger.notCoarsenedAlong_single hl' hnc hnc', hf, hlt⟩

/-- A sequence that meets every condition of the sequence row except a vault that is not coarsened, and lowers
shareValue. On a coarsened vault an instalment of `1.5` without interest is credited as `1`. -/
lemma LendingLedger.no_dilution_coarsened_witness :
    ∃ (start l : LendingLedger) (txs : List LendingTx), start.Reachable ∧ LendingLedger.Reaches start txs l ∧
      start.KeepsShareValueAlong txs ∧ start.SharesLeftAlong txs ∧ start.SharesFitAlong txs ∧
      start.WholeWorthAlong txs ∧ l.vault.toRawVault.shareValue < start.vault.toRawVault.shareValue := by
  obtain ⟨l, l', i, paymentType, amount, -, -, hr, hok, -, -, hlt⟩ :=
    LendingLedger.payment_share_value_falls_reachable
  have hST : l'.vault.sharesTotal = l.vault.sharesTotal :=
    (LendingLedger.loan_ops_scope_proof l l' _ rfl hok).2.2.2.1
  -- shareValue is at least zero, so a ledger it falls from has shares
  have hS : l.vault.sharesTotal ≠ Number.zero := by
    intro h0
    have hzero : l.vault.toRawVault.shareValue = 0 := by
      unfold RawVault.shareValue
      rw [RawVault.WF.toExact_sharesTotal _ l.vault.wf, h0, Number.toRat_zero, div_zero]
    have hnonneg : 0 ≤ l'.vault.toRawVault.shareValue := Vault.perShareValue_nonneg l'.vault
    linarith
  obtain ⟨hk, hs, hf⟩ := LendingLedger.along_single hok rfl hS (by rw [hST]; exact hS) (by
    show l.vault.sharesTotal.toRat + (0 : ℚ) ≤ 2 ^ 63 - 1
    linarith [Vault.sharesTotal_le_maxRep l.vault])
  exact ⟨l, l', [.loanPay i paymentType amount], hr, .single hok, hk, hs, hf,
    LendingLedger.wholeWorthAlong_single trivial, hlt⟩

end XRPL.Model.Lending
