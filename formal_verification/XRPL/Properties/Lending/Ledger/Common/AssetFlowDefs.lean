import XRPL.Properties.Lending.Ledger.Common.ReachableFromIn
import XRPL.Properties.Lending.Loan.Common.ManageDefs

/-! # The assets each transaction moves in or out of AssetsTotal

`l.flowOf tx` reads the amounts off the operation `tx` runs on `l`: the assets a VaultDeposit adds, the payout of
a VaultWithdraw after its early-exit fee, the assets a VaultClawback recovers, the interest a LoanPay pays and the
PrincipalOutstanding − defaultCovered a default writes off. `start.flows txs` adds them up along a run. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault WithdrawAmount)

/-- What transactions move in or out of AssetsTotal, by kind. -/
@[ext] structure AssetFlows where
  deposits : ℚ
  withdrawals : ℚ
  clawbacks : ℚ
  interestPaid : ℚ
  defaultLosses : ℚ

namespace AssetFlows

instance : Zero AssetFlows := ⟨⟨0, 0, 0, 0, 0⟩⟩

instance : Add AssetFlows :=
  ⟨fun a b => ⟨a.deposits + b.deposits, a.withdrawals + b.withdrawals, a.clawbacks + b.clawbacks,
    a.interestPaid + b.interestPaid, a.defaultLosses + b.defaultLosses⟩⟩

@[simp] lemma add_deposits (a b : AssetFlows) : (a + b).deposits = a.deposits + b.deposits := rfl
@[simp] lemma add_withdrawals (a b : AssetFlows) : (a + b).withdrawals = a.withdrawals + b.withdrawals := rfl
@[simp] lemma add_clawbacks (a b : AssetFlows) : (a + b).clawbacks = a.clawbacks + b.clawbacks := rfl
@[simp] lemma add_interestPaid (a b : AssetFlows) : (a + b).interestPaid = a.interestPaid + b.interestPaid := rfl
@[simp] lemma add_defaultLosses (a b : AssetFlows) : (a + b).defaultLosses = a.defaultLosses + b.defaultLosses := rfl
@[simp] lemma zero_deposits : (0 : AssetFlows).deposits = 0 := rfl
@[simp] lemma zero_withdrawals : (0 : AssetFlows).withdrawals = 0 := rfl
@[simp] lemma zero_clawbacks : (0 : AssetFlows).clawbacks = 0 := rfl
@[simp] lemma zero_interestPaid : (0 : AssetFlows).interestPaid = 0 := rfl
@[simp] lemma zero_defaultLosses : (0 : AssetFlows).defaultLosses = 0 := rfl

/-- The change of AssetsTotal the flows add up to. -/
def net (f : AssetFlows) : ℚ := f.deposits - f.withdrawals - f.clawbacks + f.interestPaid - f.defaultLosses

lemma net_zero : (0 : AssetFlows).net = 0 := by
  show (0 : ℚ) - 0 - 0 + 0 - 0 = 0; ring

lemma net_add (a b : AssetFlows) : (a + b).net = a.net + b.net := by
  show (a.deposits + b.deposits) - (a.withdrawals + b.withdrawals) - (a.clawbacks + b.clawbacks) +
    (a.interestPaid + b.interestPaid) - (a.defaultLosses + b.defaultLosses) = _
  unfold net; ring

lemma zero_add' (a : AssetFlows) : 0 + a = a := by ext <;> simp

lemma add_zero' (a : AssetFlows) : a + 0 = a := by ext <;> simp

lemma add_assoc' (a b c : AssetFlows) : a + b + c = a + (b + c) := by ext <;> simp [add_assoc]

end AssetFlows

/-- The assets a VaultDeposit adds to the vault. -/
def LendingLedger.depositedAssets (l : LendingLedger) (amount : STAmount) (isDonation : Bool) : ℚ :=
  if hpos : 0 < amount.toRat then
    match (l.vault.deposit amount isDonation l.now hpos).run with
    | .ok (.ok r) => r.assets.toRat
    | _ => 0
  else 0

/-- The assets a VaultWithdraw pays the holder, after the early-exit fee. -/
def LendingLedger.withdrawalPayout (l : LendingLedger) (h : Nat) (amount : WithdrawAmount) : ℚ :=
  if hpos : 0 < amount.amount.toRat then
    match (l.vault.withdraw amount (l.isSoleShareholder h) l.now hpos (some (l.sharesOf h))).run with
    | .ok (.ok r) => r.assets.toRat
    | _ => 0
  else 0

/-- The assets a VaultClawback recovers from the holder. -/
def LendingLedger.clawedAssets (l : LendingLedger) (h : Nat) (assets : STAmount) : ℚ :=
  if hnn : 0 ≤ assets.toRat then
    match STAmount.ofNumber .int64 (l.sharesOf h) .to_nearest with
    | .ok holderShares =>
      match (l.vault.clawback assets holderShares (l.isSoleShareholder h) hnn).run with
      | .ok (.ok r) => r.assets.toRat
      | _ => 0
    | .error _ => 0
  else 0

/-- The loan stored at `i`, read with its broker's current copy, as every loan transaction reads it. -/
def LendingLedger.loanRead (l : LendingLedger) (i : Nat) : Option Loan :=
  match l.loan? i with
  | some e =>
    match l.broker? e.brokerIndex with
    | some b =>
      match e.loan.withBroker b with
      | .ok loan => some loan
      | .error _ => none
    | none => none
  | none => none

/-- The interest a LoanPay pays the vault. -/
def LendingLedger.paidInterest (l : LendingLedger) (i : Nat) (pt : LoanPaymentType) (amount : Number) : ℚ :=
  match l.loanRead i with
  | some loan =>
    match (loan.payInstalments l.vault pt amount l.now).run with
    | .ok (.ok p) => p.amounts.interestPaid.toRat
    | _ => 0
  | none => 0

/-- What a default writes off AssetsTotal: PrincipalOutstanding − defaultCovered. -/
def LendingLedger.defaultLoss (l : LendingLedger) (i : Nat) : ℚ :=
  match l.loanRead i with
  | some loan =>
    match loan.defaultCover l.vault with
    | .ok dc => loan.principalOutstanding.toRat - dc.toRat
    | .error _ => 0
  | none => 0

/-- The assets a transaction moves in or out of AssetsTotal, read off the operation it runs on `l`. -/
def LendingLedger.flowOf (l : LendingLedger) : LendingTx → AssetFlows
  | .vaultDeposit _ amount isDonation => ⟨l.depositedAssets amount isDonation, 0, 0, 0, 0⟩
  | .vaultWithdraw h amount => ⟨0, l.withdrawalPayout h amount, 0, 0, 0⟩
  | .vaultClawback h assets => ⟨0, 0, l.clawedAssets h assets, 0, 0⟩
  | .loanPay i pt amount => ⟨0, 0, 0, l.paidInterest i pt amount, 0⟩
  | .loanManage i .default => ⟨0, 0, 0, 0, l.defaultLoss i⟩
  | _ => 0

/-- The flows of the transactions `txs` applied in order from `l`. Once one fails, the ones after it add nothing. -/
def LendingLedger.flows (l : LendingLedger) : List LendingTx → AssetFlows
  | [] => 0
  | tx :: txs =>
    l.flowOf tx +
      match (l.apply tx).run with
      | .ok (.ok l') => l'.flows txs
      | _ => 0

/-- A run of no transactions stays where it started. -/
lemma LendingLedger.Reaches.nil_inv {start l : LendingLedger} (h : LendingLedger.Reaches start [] l) : l = start := by
  have : ∀ ts l', LendingLedger.Reaches start ts l' → ts = [] → l' = start := by
    intro ts l' h'
    induction h' with
    | refl => intro; rfl
    | step tx _ _ _ => intro h''; simp at h''
  exact this [] l h rfl

/-- A run that starts with a transaction applied it first. -/
lemma LendingLedger.Reaches.cons_inv {start l : LendingLedger} {tx : LendingTx} {txs : List LendingTx}
    (h : LendingLedger.Reaches start (tx :: txs) l) :
    ∃ l₁, (start.apply tx).run = .ok (.ok l₁) ∧ LendingLedger.Reaches l₁ txs l := by
  generalize hts : tx :: txs = ts at h
  induction h generalizing tx txs with
  | refl => cases hts
  | @step txs₀ l₀ l₁ tx₀ hprev hok ih =>
    cases txs₀ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hts
      obtain ⟨rfl, rfl⟩ := hts
      obtain rfl := hprev.nil_inv
      exact ⟨l₁, hok, .refl⟩
    | cons t ts =>
      simp only [List.cons_append, List.cons.injEq] at hts
      obtain ⟨rfl, rfl⟩ := hts
      obtain ⟨l₂, h₂, hr₂⟩ := ih rfl
      exact ⟨l₂, h₂, .step tx₀ hr₂ hok⟩

/-- A run's flows grow by each step's flow. -/
lemma LendingLedger.flows_snoc {start l l' : LendingLedger} {txs : List LendingTx} {tx : LendingTx}
    (h : LendingLedger.Reaches start txs l) (hok : (l.apply tx).run = .ok (.ok l')) :
    start.flows (txs ++ [tx]) = start.flows txs + l.flowOf tx := by
  induction txs generalizing start with
  | nil =>
    obtain rfl := h.nil_inv
    simp only [List.nil_append, LendingLedger.flows, hok]
    rw [AssetFlows.zero_add', AssetFlows.add_zero']
  | cons t ts ih =>
    obtain ⟨l₁, h₁, hr₁⟩ := LendingLedger.Reaches.cons_inv h
    simp only [List.cons_append, LendingLedger.flows, h₁]
    rw [ih hr₁, AssetFlows.add_assoc']

end XRPL.Model.Lending
