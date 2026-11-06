import XRPL.Properties.Lending.Ledger.Common.LoanRuns
import XRPL.Properties.Lending.Loan.Common.RegularPayoffSplit

/-! # A loan paid off by regular payments on the ledger

A run of ledger transactions in which only regular LoanPays pay the loan at `i`. Any other transaction may come in
between, other loans and brokers, vault transactions, close, and LoanAccept, impair or unimpair of that loan, but
no other payment type and no default of it. Read at slot `i` it is a regular payoff run of the loan,
`Loan.RegularPayoff`, so the sums of the loan-level theorems carry over. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A run from `start` in which only regular payments pay the loan at `i`, each one satisfying `fits` on the ledger
before it. `cost`, `toVault` and `toBroker` sum what those payments charge, credit the vault and pay the broker. -/
inductive LendingLedger.RegularPayoff (i : Nat) (fits : LendingLedger → Loan → UnsettledPayment Vault → Prop)
    (start : LendingLedger) : LendingLedger → ℚ → ℚ → ℚ → Prop where
  | refl : LendingLedger.RegularPayoff i fits start start 0 0 0
  | pay {l l' : LendingLedger} {cost toVault toBroker : ℚ} (amount : Number) (loan : Loan)
      (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault) :
      LendingLedger.RegularPayoff i fits start l cost toVault toBroker → l.LoanAt i loan →
      (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p) → fits l loan p →
      (loan.regularPayment l.vault amount l.now).run = .ok (.ok r) →
      (l.apply (.loanPay i .regular amount)).run = .ok (.ok l') →
      LendingLedger.RegularPayoff i fits start l' (cost + p.totalPaid.toRat) (toVault + r.amountToPool.toRat)
        (toBroker + r.amountToBroker.toRat)
  | other {l l' : LendingLedger} {cost toVault toBroker : ℚ} (tx : LendingTx) :
      LendingLedger.RegularPayoff i fits start l cost toVault toBroker →
      (∀ paymentType amount, tx ≠ .loanPay i paymentType amount) → tx ≠ .loanManage i .default →
      (l.apply tx).run = .ok (.ok l') → LendingLedger.RegularPayoff i fits start l' cost toVault toBroker

/-- The payment does not coarsen the vault: AssetsAvailable plus the principal and the interest it pays stays below
`10^16` base units. -/
def LendingLedger.PaysVaultUncoarsened (l : LendingLedger) (_loan : Loan) (p : UnsettledPayment Vault) : Prop :=
  l.vault.assetsAvailable.toRat + (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) <
    10 ^ 16 * 10 ^ l.vault.baseExponent

/-- The payment does not coarsen the broker's cover: below its minimum cover the broker takes the fee into a
CoverAvailable that stays below `10^16` base units. -/
def LendingLedger.PaysCoverUncoarsened (l : LendingLedger) (loan : Loan) (p : UnsettledPayment Vault) : Prop :=
  loan.broker.hasMinimumCover l.vault.baseExponent = .ok false →
    loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent

/-- A regular payoff run on a reachable ledger is a regular payoff run of the loan at `i`, from the loan at `i` at
its start, when each payment that `fits` on the ledger fits the loan-level `fitsLoan`. -/
lemma LendingLedger.RegularPayoff.toLoan {i : Nat} {fits : LendingLedger → Loan → UnsettledPayment Vault → Prop}
    {fitsLoan : Loan → Vault → UInt32 → UnsettledPayment Vault → Prop}
    (hfits : ∀ (l : LendingLedger) (loan : Loan) (p : UnsettledPayment Vault), l.Reachable → l.LoanAt i loan →
      fits l loan p → fitsLoan loan l.vault l.now p)
    {start l : LendingLedger} {cost toVault toBroker : ℚ} (hr : start.Reachable)
    (hrun : start.RegularPayoff i fits l cost toVault toBroker) {loan₀ : Loan} {t₀ : UInt32}
    (hat₀ : start.LoanAt i loan₀) (ht₀ : t₀ ≤ start.now) :
    l.Reachable ∧ i < l.loans.length ∧ ∀ loan, l.LoanAt i loan →
      ∃ t, t ≤ l.now ∧ Loan.RegularPayoff fitsLoan loan₀ t₀ loan t cost toVault toBroker := by
  induction hrun with
  | refl =>
    have hlt : i < start.loans.length := by
      obtain ⟨e, _, he, -⟩ := hat₀
      exact LendingLedger.loan?_lt he
    refine ⟨hr, hlt, fun loan hat => ⟨t₀, ht₀, ?_⟩⟩
    obtain rfl := hat₀.eq hat
    exact .refl
  | @pay l₁ l₂ cost toVault toBroker amount loan p r _ hat hp hfit hreg h ih =>
    obtain ⟨hrl, hil, hl⟩ := ih
    obtain ⟨_, x, r', -, hx, -, hc, hpay, -, -, hy, hnow, -⟩ := LendingLedger.loanPay_ok h
    obtain rfl := hat.eq hx
    have hrr : r' = r := Except.ok.inj (Except.ok.inj (hpay.symm.trans hreg))
    subst hrr
    refine ⟨hrl.apply h, (LendingLedger.apply_loanSlot h hil).1, fun y hy' => ?_⟩
    obtain rfl := hy'.eq hy
    obtain ⟨t, ht, hrp⟩ := hl loan hat
    exact ⟨l₁.now, UInt32.le_iff_toNat_le.mpr (by rw [hnow]),
      .pay loan t l₁.now l₁.vault amount p r' cost toVault toBroker hrp ht hc hp (hfits l₁ loan p hrl hat hfit) hreg⟩
  | @other l₁ l₂ cost toVault toBroker tx _ hnp hnd h ih =>
    obtain ⟨hrl, hil, hl⟩ := ih
    refine ⟨hrl.apply h, (LendingLedger.apply_loanSlot h hil).1, fun y hy => ?_⟩
    obtain ⟨x, hx, hcase⟩ := LendingLedger.loanAt_apply hrl h hil hy
    obtain ⟨t, ht, hrp⟩ := hl x hx
    have hnow := LendingLedger.apply_now_le h
    rcases hcase with ⟨b, hnt, hw⟩ | rfl | ⟨action, rfl⟩ | ⟨paymentType, amount, rfl⟩
    · refine ⟨t, ?_, .refresh x y t b _ _ _ hrp hnt hw⟩
      rw [UInt32.le_iff_toNat_le] at ht hnow ⊢
      omega
    · obtain ⟨_, x', r, -, hx', hc, hok, -, -, hy', -⟩ := LendingLedger.loanAccept_ok h
      obtain rfl := hx.eq hx'
      obtain rfl := hy.eq hy'
      exact ⟨l₁.now, hnow, .accept x t l₁.now l₁.vault r _ _ _ hrp ht hc hok⟩
    · cases action with
      | impair =>
        obtain ⟨_, x', r, -, hx', hc, hok, -, -, hy', -⟩ := LendingLedger.loanImpair_ok h
        obtain rfl := hx.eq hx'
        obtain rfl := hy.eq hy'
        exact ⟨l₁.now, hnow, .impair x t l₁.now l₁.vault r _ _ _ hrp ht hc hok⟩
      | unimpair =>
        obtain ⟨_, x', r, -, hx', hc, hok, -, -, hy', -⟩ := LendingLedger.loanUnimpair_ok h
        obtain rfl := hx.eq hx'
        obtain rfl := hy.eq hy'
        exact ⟨l₁.now, hnow, .unimpair x t l₁.now l₁.vault r _ _ _ hrp ht hc hok⟩
      | default => exact absurd rfl hnd
    · exact absurd rfl (hnp paymentType amount)

/-- Proof body of the cost line of `Lending.Reachable.regularPayoff`. -/
lemma LendingLedger.regularPayoff_cost_proof (l l' : LendingLedger) (i : Nat) (loan loan' : Loan)
    (cost toVault toBroker : ℚ) (hr : l.Reachable) (hat : l.LoanAt i loan)
    (hrun : l.RegularPayoff i (fun _ _ _ => True) l' cost toVault toBroker) (hat' : l'.LoanAt i loan')
    (hpaid : loan'.paymentRemaining = 0)
    (hfit : loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat <
      10 ^ 16 * 10 ^ loan.loanScale) :
    cost = loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat := by
  obtain ⟨t₀, ht₀, hs⟩ := hr.loanAt_reachable hat
  obtain ⟨-, -, hl⟩ := hrun.toLoan (fitsLoan := fun _ _ _ _ => True) (fun _ _ _ _ _ _ => trivial) hr hat ht₀
  obtain ⟨t, -, hrp⟩ := hl loan' hat'
  exact Loan.Reachable.regularPayoff_cost_proof loan loan' t₀ t cost toVault toBroker hs hrp hpaid hfit

/-- Proof body of the vault line of `Lending.Reachable.regularPayoff`. -/
lemma LendingLedger.regularPayoff_vault_proof (l l' : LendingLedger) (i : Nat) (loan loan' : Loan)
    (cost toVault toBroker : ℚ) (hr : l.Reachable) (hat : l.LoanAt i loan)
    (hrun : l.RegularPayoff i LendingLedger.PaysVaultUncoarsened l' cost toVault toBroker) (hat' : l'.LoanAt i loan')
    (hpaid : loan'.paymentRemaining = 0) :
    toVault = loan.totalValueOutstanding.toRat - loan.managementFeeOutstanding.toRat := by
  obtain ⟨-, -, hl⟩ := hrun.toLoan (fitsLoan := Loan.PaysVaultUncoarsened)
    (fun lk x _ hrk hx hfit => ⟨⟨lk, i, hrk, hx, rfl, rfl⟩, hfit⟩) hr hat (UInt32.le_iff_toNat_le.mpr (le_refl _))
  obtain ⟨t, -, hrp⟩ := hl loan' hat'
  exact Loan.Reachable.regularPayoff_vault_proof loan loan' l.now t cost toVault toBroker hrp hpaid

/-- Proof body of the broker line of `Lending.Reachable.regularPayoff`. -/
lemma LendingLedger.regularPayoff_broker_proof (l l' : LendingLedger) (i : Nat) (loan loan' : Loan)
    (cost toVault toBroker : ℚ) (hr : l.Reachable) (hat : l.LoanAt i loan)
    (hrun : l.RegularPayoff i LendingLedger.PaysCoverUncoarsened l' cost toVault toBroker) (hat' : l'.LoanAt i loan')
    (hpaid : loan'.paymentRemaining = 0)
    (hfit : loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat <
      10 ^ 16 * 10 ^ loan.loanScale) :
    toBroker = loan.managementFeeOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat := by
  obtain ⟨t₀, ht₀, hs⟩ := hr.loanAt_reachable hat
  obtain ⟨-, -, hl⟩ := hrun.toLoan (fitsLoan := Loan.PaysCoverUncoarsened)
    (fun lk x _ hrk hx hfit => ⟨⟨lk, i, hrk, hx, rfl, rfl⟩, hfit⟩) hr hat ht₀
  obtain ⟨t, -, hrp⟩ := hl loan' hat'
  exact Loan.Reachable.regularPayoff_broker_proof loan loan' t₀ t cost toVault toBroker hs hrp hpaid hfit

end XRPL.Model.Lending
