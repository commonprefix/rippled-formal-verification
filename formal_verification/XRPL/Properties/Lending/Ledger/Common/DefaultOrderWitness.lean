import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Ledger.Common.DefaultOrderDefs
import XRPL.Properties.Lending.Ledger.Common.ManageReachable

/-! # Witnesses for the order of two defaults

Reachable runs where two defaults give a different vault or broker in the two orders, each breaking one hypothesis
of `defaults_comm`: a liquidation amount that caps a default, a coarsened vault, and a CoverAvailable above `2^63`
base units. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule)

/-- The default of loan `i` on `l` reads a liquidation amount of at least min(PrincipalOutstanding,
CoverAvailable). -/
private def uncappedCheck (l : LendingLedger) (i : Nat) : Bool :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b =>
      match e.loan.withBroker b with
      | .ok loan =>
        match tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward with
        | .ok mc =>
          match tenthBipsOfValue mc loan.broker.coverRateLiquidation .upward with
          | .ok liq => decide (min loan.principalOutstanding.toRat loan.broker.coverAvailable.toRat ≤ liq.toRat)
          | .error _ => false
        | .error _ => false
      | .error _ => false
    | none => false
  | none => false

private lemma uncapped_of_check {l : LendingLedger} {i : Nat} (h : uncappedCheck l i = true) :
    l.DefaultUncapped i := by
  intro loan mc liq hat hmc hliq
  obtain ⟨e, b, he, hb, hw⟩ := hat
  simp only [uncappedCheck, he, hb, hw, hmc, hliq] at h
  exact of_decide_eq_true h

/-- The broker of loan `i` on `l` holds a CoverAvailable below `2^63` base units. -/
private def coverCheck (l : LendingLedger) (i : Nat) : Bool :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b => decide (b.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent)
    | none => false
  | none => false

private lemma cover_of_check {l : LendingLedger} {i : Nat} (h : coverCheck l i = true) :
    ∀ loan, l.LoanAt i loan → loan.broker.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent := by
  intro loan hat
  obtain ⟨e, he, hb, -⟩ := hat.stored
  simp only [coverCheck, he, hb] at h
  exact of_decide_eq_true h

/-- The defaults of loans `i` and `j` on `l` in both orders, and a check `p` of the four ledgers they produce. -/
private def bothOrders (l : LendingLedger) (i j : Nat)
    (p : LendingLedger → LendingLedger → LendingLedger → LendingLedger → Bool) : Bool :=
  match (l.apply (.loanManage i .default)).run, (l.apply (.loanManage j .default)).run with
  | .ok (.ok la), .ok (.ok lb) =>
    match (la.apply (.loanManage j .default)).run, (lb.apply (.loanManage i .default)).run with
    | .ok (.ok lab), .ok (.ok lba) => p la lb lab lba
    | _, _ => false
  | _, _ => false

private lemma bothOrders_true {l : LendingLedger} {i j : Nat}
    {p : LendingLedger → LendingLedger → LendingLedger → LendingLedger → Bool} (h : bothOrders l i j p = true) :
    ∃ la lb lab lba, (l.apply (.loanManage i .default)).run = .ok (.ok la) ∧
      (la.apply (.loanManage j .default)).run = .ok (.ok lab) ∧
      (l.apply (.loanManage j .default)).run = .ok (.ok lb) ∧
      (lb.apply (.loanManage i .default)).run = .ok (.ok lba) ∧ p la lb lab lba = true := by
  unfold bothOrders at h
  split at h
  · rename_i la lb ha hb
    split at h
    · rename_i lab lba hab hba
      exact ⟨la, lb, lab, lba, ha, hab, hb, hba, h⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- A closed-ended IOU vault at Scale 0, subscription until 1000, redemption 900 days later. -/
private def dlSchedule : VaultSchedule := ⟨1000, 1000 + 900 * 86400⟩

private def dlRawVault : RawVault := { cwRawVault with scale := 0, schedule := some dlSchedule }

private def dlVault : Vault := ⟨dlRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def dlGenesis : LendingLedger := { vault := dlVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma dlGenesis_genesis : dlGenesis.Genesis where
  created := ⟨some 0, none, dlSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨dlVault.wf, dlVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- A deposit of 10000, a broker at 100% minimum cover and 90% liquidation with 2000 of cover, loans of 800 and
150, then a close past both grace periods. -/
private def dlTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 1000000000000000 (-11)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, some 100000, some 90000⟩,
   .loanBrokerCoverDeposit 0 (cwAmount 2000000000000000 (-12)),
   .loanSet 0 ⟨false, 8000000000000000000, -16⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 1500000000000000000, -16⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .close 100000]

/-- The defaults of loans 800 and 150 in both orders: the vault is not coarsened, the cover is 2000, and the vault
ends with AssetsAvailable 9985 in one order and 9920 in the other. -/
private def dlCheck : Bool :=
  match dlGenesis.run dlTxs with
  | .ok l => bothOrders l 0 1 fun _ _ lab lba =>
      decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) && coverCheck l 0 &&
      decide (lab.vault.assetsAvailable.toRat ≠ lba.vault.assetsAvailable.toRat)
  | .error _ => false

private lemma dlCheck_true : dlCheck = true := by native_decide

/-- Two defaults capped by their liquidation amount. Loans of 800 and 150 on a broker with DebtTotal 950, 2000
of cover and a 90% liquidation rate: the larger first gets 800 + 135 = 935 of cover, the other order 150 + 720. -/
lemma LendingLedger.defaults_comm_liquidation_witness :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat), l.Reachable ∧
      (l.apply (.loanManage i .default)).run = .ok (.ok la) ∧
      (la.apply (.loanManage j .default)).run = .ok (.ok lab) ∧
      (l.apply (.loanManage j .default)).run = .ok (.ok lb) ∧
      (lb.apply (.loanManage i .default)).run = .ok (.ok lba) ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
      (∀ loan, l.LoanAt i loan → loan.broker.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) ∧
      lab.vault ≠ lba.vault := by
  have h := dlCheck_true
  unfold dlCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  obtain ⟨la, lb, lab, lba, ha, hab, hb, hba, hp⟩ := bothOrders_true h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨htotal, hcov⟩, hne⟩ := hp
  exact ⟨l, la, lb, lab, lba, 0, 1, LendingLedger.Reachable.of_run dlGenesis_genesis hl, ha, hab, hb, hba,
    htotal, cover_of_check hcov, fun hv => hne (by rw [hv])⟩

/-- The run of `CoarsenedVault.lean` with both brokers at 100% minimum cover and 100% liquidation: broker 0 holds
800000000000000 of cover and broker 1 holds 1. AssetsAvailable ends at `999999999999999.9`. -/
private def dcTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8999990000000000 (-1)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, some 100000, some 100000⟩,
   .loanBrokerCreate ⟨none, none, some 100000, some 100000⟩,
   .loanBrokerCoverDeposit 1 (cwAmount 1000000000000000 (-15)),
   .loanBrokerCoverDeposit 0 (cwAmount 8000000000000000 (-1)),
   .loanSet 0 ⟨false, 7000000000000000000, -4⟩ (cwRates 100000) cwFees (some 86400) (some 5) (some 60) 0 false false,
   .loanSet 1 ⟨false, 1000000000000000000, -18⟩ (cwRates 0) cwFees (some 86400) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 2000000000000000000, -18⟩ (cwRates 0) cwFees (some 86400) (some 20) (some 60) 0 false false,
   .close 69207461,
   .loanPay 0 .late ⟨false, 7000000000000000000, -3⟩,
   .close (1000 + 900 * 86400 + 1),
   .vaultWithdraw 0 (.vaultAssets (cwAmount 8742469071537271 (-1)))] ++
  List.replicate 8 (.loanPay 2 .late ⟨false, 1000000000000000000, -19⟩)

/-- The defaults of loans B and C in both orders: no liquidation amount caps them, the covers are small, and the
vault ends with AssetsAvailable `10^15 + 1` in one order and `10^15 + 2` in the other. -/
private def dcCheck : Bool :=
  match cwGenesis.run dcTxs with
  | .ok l => bothOrders l 1 2 fun la lb lab lba =>
      uncappedCheck l 1 && uncappedCheck la 2 && uncappedCheck l 2 && uncappedCheck lb 1 && coverCheck l 1 &&
      decide (lab.vault.assetsAvailable.toRat ≠ lba.vault.assetsAvailable.toRat)
  | .error _ => false

private lemma dcCheck_true : dcCheck = true := by native_decide

/-- Two defaults on a reachable coarsened vault. AssetsAvailable is `999999999999999.9`. Loan B first pays 0.1
of its cover of 1, then loan C pays 1 of 1.2. Loan C first pays 1.1, then loan B pays its full 1. -/
lemma LendingLedger.defaults_comm_coarsened_witness :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat), l.Reachable ∧
      (l.apply (.loanManage i .default)).run = .ok (.ok la) ∧
      (la.apply (.loanManage j .default)).run = .ok (.ok lab) ∧
      (l.apply (.loanManage j .default)).run = .ok (.ok lb) ∧
      (lb.apply (.loanManage i .default)).run = .ok (.ok lba) ∧
      (l.DefaultUncapped i ∧ la.DefaultUncapped j ∧ l.DefaultUncapped j ∧ lb.DefaultUncapped i) ∧
      (∀ loan, l.LoanAt i loan → loan.broker.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) ∧
      lab.vault ≠ lba.vault := by
  have h := dcCheck_true
  unfold dcCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  obtain ⟨la, lb, lab, lba, ha, hab, hb, hba, hp⟩ := bothOrders_true h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hcov⟩, hne⟩ := hp
  exact ⟨l, la, lb, lab, lba, 1, 2, LendingLedger.Reachable.of_run cwGenesis_genesis hl, ha, hab, hb, hba,
    ⟨uncapped_of_check h1, uncapped_of_check h2, uncapped_of_check h3, uncapped_of_check h4⟩, cover_of_check hcov,
    fun hv => hne (by rw [hv])⟩

/-- A closed-ended IOU vault at Scale 10, subscription until 1000, redemption 900 days later. -/
private def dvSchedule : VaultSchedule := ⟨1000, 1000 + 900 * 86400⟩

private def dvRawVault : RawVault := { cwRawVault with scale := 10, schedule := some dvSchedule }

private def dvVault : Vault := ⟨dvRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def dvGenesis : LendingLedger := { vault := dvVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma dvGenesis_genesis : dvGenesis.Genesis where
  created := ⟨some 10, none, dvSchedule, none, false, .fractional, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨dvVault.wf, dvVault.valid⟩⟩
  holds_asset := Or.inl rfl
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- No fees but the given LoanServiceFee. -/
private def dvFees (service : Number) : LoanFees := { cwFees with serviceFee := service }

/-- A broker at 10% minimum cover and 100% liquidation lends loans A and B. Defaulting A leaves a cover of 1, so
B's first instalment adds its fee of `10^12` to the cover. Then loans C of `0.0000005` and D of `0.000001`. -/
private def dvTxs : List LendingTx :=
  [.vaultDeposit 0 (cwAmount 8000000000000000 (-10)) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, some 10000, some 100000⟩,
   .loanBrokerCoverDeposit 0 (cwAmount 1000100000000000 (-11)),
   .loanSet 0 ⟨false, 9000000000000000000, -14⟩ (cwRates 0) cwFees (some 60) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 1000000000000000000, -14⟩ (cwRates 0) (dvFees ⟨false, 1000000000000000000, -6⟩)
     (some 86400) (some 2) (some 60) 0 false false,
   .close 1300,
   .loanManage 0 .default,
   .loanPay 1 .regular ⟨false, 1000000005000000000, -6⟩,
   .loanSet 0 ⟨false, 5000000000000000000, -25⟩ (cwRates 0) cwFees (some 60) (some 1) (some 60) 0 false false,
   .loanSet 0 ⟨false, 1000000000000000000, -24⟩ (cwRates 0) cwFees (some 60) (some 1) (some 60) 0 false false,
   .close 1500]

/-- The defaults of loans C and D in both orders: no liquidation amount caps them, the vault is not coarsened, and
the broker ends with CoverAvailable `1000000000000.999999` in one order and `1000000000000.999998` in the other. -/
private def dvCheck : Bool :=
  match dvGenesis.run dvTxs with
  | .ok l => bothOrders l 2 3 fun la lb lab lba =>
      uncappedCheck l 2 && uncappedCheck la 3 && uncappedCheck l 3 && uncappedCheck lb 2 &&
      decide (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) &&
      match lab.broker? 0, lba.broker? 0 with
      | some b, some b' => decide (b.coverAvailable.toRat ≠ b'.coverAvailable.toRat)
      | _, _ => false
  | .error _ => false

private lemma dvCheck_true : dvCheck = true := by native_decide

/-- Two defaults on a broker with a cover of `1000000000001`, where a `Number` keeps whole millionths. C then D
leaves `1000000000000.999999`, D then C leaves `.999998`: the half millionth of C rounds to even both times. -/
lemma LendingLedger.defaults_comm_cover_witness :
    ∃ (l la lb lab lba : LendingLedger) (i j : Nat), l.Reachable ∧
      (l.apply (.loanManage i .default)).run = .ok (.ok la) ∧
      (la.apply (.loanManage j .default)).run = .ok (.ok lab) ∧
      (l.apply (.loanManage j .default)).run = .ok (.ok lb) ∧
      (lb.apply (.loanManage i .default)).run = .ok (.ok lba) ∧
      (l.DefaultUncapped i ∧ la.DefaultUncapped j ∧ l.DefaultUncapped j ∧ lb.DefaultUncapped i) ∧
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent ∧
      lab.brokers ≠ lba.brokers := by
  have h := dvCheck_true
  unfold dvCheck at h
  split at h
  case h_2 => cases h
  rename_i l hl
  obtain ⟨la, lb, lab, lba, ha, hab, hb, hba, hp⟩ := bothOrders_true h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, htotal⟩, hne⟩ := hp
  refine ⟨l, la, lb, lab, lba, 2, 3, LendingLedger.Reachable.of_run dvGenesis_genesis hl, ha, hab, hb, hba,
    ⟨uncapped_of_check h1, uncapped_of_check h2, uncapped_of_check h3, uncapped_of_check h4⟩, htotal, ?_⟩
  intro hbr
  have hk : lab.broker? 0 = lba.broker? 0 := by unfold LendingLedger.broker?; rw [hbr]
  rw [hk] at hne
  split at hne
  · rename_i b b' hb hb'
    rw [hb] at hb'
    cases hb'
    exact of_decide_eq_true hne rfl
  · exact absurd hne (by decide)

end XRPL.Model.Lending
