import XRPL.Properties.Lending.Ledger.Common.ReachableProofs
import XRPL.Properties.Lending.Loan.Common.ShareValue

/-! # Winding a vault down

After RedemptionDate a vault winds down with defaults, LoanDelete, LoanBrokerDelete and VaultWithdraw. None of them
is a VaultDeposit, so a wind-down that ends in VaultDelete deletes the vault without a donation. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A transaction that winds a vault down: a default, a LoanDelete, a LoanBrokerDelete, or a VaultWithdraw of any
amount. A VaultDeposit, donation or not, and a VaultClawback, the issuer's action, are not among them. -/
def LendingTx.isWindDown : LendingTx → Bool
  | .loanManage _ .default | .loanDelete _ | .loanBrokerDelete _ | .vaultWithdraw _ _ => true
  | _ => false

/-- A wind-down transaction that redeems whole holdings on `l`: a default, a LoanDelete, a LoanBrokerDelete, or a
VaultWithdraw of every share the holder owns. -/
def LendingLedger.WholeWindDownTx (l : LendingLedger) : LendingTx → Prop
  | .loanManage _ .default | .loanDelete _ | .loanBrokerDelete _ => True
  | .vaultWithdraw h (.vaultShares shares) => shares.toRat = (l.sharesOf h).toRat
  | _ => False

/-- `l.WindsDownWhole txs l'`: the wind-down transactions `txs`, each redeeming whole holdings, take `l` to `l'`, each
one succeeding. -/
inductive LendingLedger.WindsDownWhole (start : LendingLedger) : List LendingTx → LendingLedger → Prop where
  | refl : start.WindsDownWhole [] start
  | step {txs : List LendingTx} {l l' : LendingLedger} (tx : LendingTx) :
      start.WindsDownWhole txs l → l.WholeWindDownTx tx → (l.apply tx).run = .ok (.ok l') →
        start.WindsDownWhole (txs ++ [tx]) l'

/-- No holder is left owning shares worth less than one unit at the scale of AssetsAvailable: a holder that owns some
but not all shares, worth something, owns at least that unit. -/
def LendingLedger.NoDust (l : LendingLedger) : Prop :=
  ∀ h, 0 < (l.sharesOf h).toRat → (l.sharesOf h).toRat < l.vault.sharesTotal.toRat →
    0 < (l.sharesOf h).toRat * l.vault.shareValue →
    ∀ E, numberExponent l.vault.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok E →
      (10 : ℚ) ^ E ≤ (l.sharesOf h).toRat * l.vault.shareValue

/-- One wind-down transaction winds the ledger down. -/
lemma LendingLedger.WindsDownWhole.single {l l' : LendingLedger} {tx : LendingTx} (hw : l.WholeWindDownTx tx)
    (h : (l.apply tx).run = .ok (.ok l')) : l.WindsDownWhole [tx] l' := by
  simpa using LendingLedger.WindsDownWhole.step tx .refl hw h

/-- Two wind-downs in a row wind the ledger down to where the second one ends. -/
lemma LendingLedger.WindsDownWhole.trans {start l l' : LendingLedger} {txs txs' : List LendingTx}
    (h₁ : start.WindsDownWhole txs l) (h₂ : l.WindsDownWhole txs' l') : start.WindsDownWhole (txs ++ txs') l' := by
  induction h₂ with
  | refl => simpa using h₁
  | step tx _ hw ha ih => rw [← List.append_assoc]; exact .step tx ih hw ha

/-- A wind-down is a run of successful transactions. -/
lemma LendingLedger.WindsDownWhole.reaches {start l : LendingLedger} {txs : List LendingTx}
    (h : start.WindsDownWhole txs l) : LendingLedger.Reaches start txs l := by
  induction h with
  | refl => exact .refl
  | step tx _ _ ha ih => exact .step tx ih ha

/-- A wind-down from a reachable ledger ends in a reachable ledger. -/
lemma LendingLedger.WindsDownWhole.reachable {start l : LendingLedger} {txs : List LendingTx}
    (hr : start.Reachable) (h : start.WindsDownWhole txs l) : l.Reachable := by
  obtain ⟨g, txs₀, hg, hreach, -⟩ := hr
  exact ⟨g, txs₀ ++ txs, hg, hreach.trans h.reaches, fun _ _ => trivial⟩


/-- A transaction that redeems whole holdings is a wind-down transaction. -/
lemma LendingLedger.WholeWindDownTx.isWindDown {l : LendingLedger} {tx : LendingTx} (h : l.WholeWindDownTx tx) :
    tx.isWindDown = true := by
  cases tx with
  | loanManage i a => cases a <;> first | rfl | exact h.elim
  | loanDelete i => rfl
  | loanBrokerDelete j => rfl
  | vaultWithdraw h' amount => rfl
  | _ => exact h.elim

/-- A wind-down by whole redemptions runs wind-down transactions only. -/
lemma LendingLedger.WindsDownWhole.isWindDown {start l : LendingLedger} {txs : List LendingTx}
    (h : start.WindsDownWhole txs l) : ∀ tx ∈ txs, tx.isWindDown = true := by
  induction h with
  | refl => intro tx htx; cases htx
  | step tx _ hw _ ih =>
    intro tx' htx
    rcases List.mem_append.mp htx with h' | h'
    · exact ih tx' h'
    · rw [List.mem_singleton.mp h']
      exact hw.isWindDown

end XRPL.Model.Lending
