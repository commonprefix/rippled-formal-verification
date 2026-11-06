import XRPL.Properties.Lending.Ledger.Common.DefaultCredit
import XRPL.Properties.Lending.Ledger.Common.VaultOutflow
import XRPL.Properties.Lending.Loan.Common.ManageProofs
import XRPL.Properties.Lending.Loan.Common.PayYield

/-! # Regular payments, defaults, withdrawals and clawbacks never raise AssetsTotal + YieldUnrealized

A regular payment moves its interest from YieldUnrealized to AssetsTotal. A default takes the loan's principal and
interest off and credits at most the principal, and a withdrawal or clawback only pays out. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.pay_units from XRPL.Properties.Lending.Loan.Common.PayReachable

/-- A regular payment on a reachable ledger never raises AssetsTotal + YieldUnrealized. AssetsAvailable gains
at most the principal and interest paid, AssetsDeployed loses the principal and YieldUnrealized the interest. -/
private lemma Loan.regularPayment_capacity (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (amount : Number) (r : LoanWithAmounts Vault)
    (hc : loan.canPay .regular = .tesSUCCESS) (hok : (loan.pay l.vault .regular amount l.now).run = .ok (.ok r)) :
    r.pool'.toRawVault.toExact.assetsTotal + r.pool'.yieldUnrealized.toRat ≤
      l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat := by
  obtain ⟨payment, hpay, hs⟩ := Loan.pay_ok loan l.vault .regular amount l.now r hok
  obtain ⟨pp, ip, hpp, hip⟩ := Loan.pay_units loan amount .regular r hr hat payment hpay hok
  have hrange := LendingLedger.Reachable.loanScale_range hr hat
  have hint := Loan.regularPayment_interest loan l.vault amount l.now payment hrange hpay
  have hset := Loan.settle_interestDue payment r hs
  obtain ⟨hP, hAD, -⟩ := Loan.payment_principal_proof loan amount .regular r l hr i hat payment hpay hok
  have hyield := Loan.payment_yield_proof loan amount .regular r l hr i hat hok (hr.pay_yield_lt hat hok)
  -- principal plus interest paid is at most what the loan owed, below `2^63` base units
  obtain ⟨t, hle, hrl⟩ := hr.loanAt_reachable hat
  have hi0' := Loan.Reachable.interestDue_nonneg (hrl.pay hle .regular l.vault amount r hc hok)
  have hP0' : 0 ≤ r.loan'.principalOutstanding.toRat := r.loan'.exact.principalOutstanding_nonneg
  obtain ⟨-, -, -, hTb, -, hM0, -⟩ := Loan.outstanding_grid loan
  have hls := (hr.loanAt_scale hat).1
  rw [hls] at hTb
  have hiD : loan.toExact.interestDue =
      loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat - loan.managementFeeOutstanding.toRat := rfl
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hlt : ((pp + ip : ℕ) : ℤ) < 2 ^ 63 := by
    have : (((pp + ip : ℕ) : ℤ) : ℚ) * 10 ^ l.vault.baseExponent < ((2 ^ 63 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
      push_cast
      rw [add_mul, ← hpp, ← hip, hint, ← hset]
      linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((pp + ip : ℕ) : ℤ) l.vault.baseExponent
    ⟨by omega, hlt⟩ hsb
  have hup := Loan.payment_vault_upper_bound_proof loan amount .regular r l hr i hat payment hpay hok
    ⟨w, hw, by rw [hwv, hpp, hip]; push_cast; ring⟩
  have hy : r.pool'.yieldUnrealized.toRat =
      l.vault.yieldUnrealized.toRat - (loan.toExact.interestDue - r.loan'.toExact.interestDue) := hyield
  show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat + r.pool'.yieldUnrealized.toRat ≤
    l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat
  linarith

/-- A default on a reachable ledger never raises AssetsTotal + YieldUnrealized. It credits a cover of at most
the principal it takes off AssetsDeployed, and takes the loan's interest of at least zero off YieldUnrealized. -/
private lemma Loan.manageDefault_capacity (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (r : LoanWithAmounts Vault) (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hsupply : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63) :
    r.pool'.toRawVault.toExact.assetsTotal + r.pool'.yieldUnrealized.toRat ≤
      l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat := by
  obtain ⟨hAT, -⟩ := LendingLedger.manageDefault_vault_exact_proof l hr i loan hat r hok hsupply
  have hyield := Loan.manageDefault_yield_proof loan l.vault r hok (hr.yield_fits hat hr.yield_lt)
  obtain ⟨_, _, _, _, _, -, hdc, -⟩ := Loan.manageDefault_ok_parts loan l.vault r hok
  obtain ⟨mc, liq, -, -, hmc, hliq, -⟩ := Loan.defaultCover_parts loan l.vault _ hdc
  have hdcle := Loan.defaultCover_le loan l.vault _ mc liq hdc hmc hliq
  have hdcpo : r.amountToPool.toRat ≤ loan.principalOutstanding.toRat :=
    le_trans hdcle (le_trans (min_le_left _ _) (min_le_right _ _))
  obtain ⟨t, -, hrl⟩ := hr.loanAt_reachable hat
  have hi0 := Loan.Reachable.interestDue_nonneg hrl
  have hAT' : r.pool'.toRawVault.toExact.assetsTotal =
      l.vault.toRawVault.toExact.assetsTotal - (loan.principalOutstanding.toRat - r.amountToPool.toRat) := hAT
  rw [hAT', hyield]
  linarith

/-- Proof body of `Lending.capacity_monotone`. -/
lemma LendingLedger.capacity_monotone_proof (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (htx : (∃ i amount, tx = .loanPay i .regular amount) ∨ tx.isOutflow = true)
    (h : (l.apply tx).run = .ok (.ok l'))
    (hsupply : l.vault.numericType = NumericType.int64 → ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
      l.vault.assetsAvailable.toRat + b.coverAvailable.toRat < 2 ^ 63) :
    l'.vault.toRawVault.toExact.assetsTotal + l'.vault.yieldUnrealized.toRat ≤
      l.vault.toRawVault.toExact.assetsTotal + l.vault.yieldUnrealized.toRat := by
  rcases htx with ⟨i, amount, rfl⟩ | hout
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
    obtain ⟨e, broker, loan, r, he, hb, hw, hc, hrr, rfl⟩ := l.applyLoan_pay_inv u i .regular amount hu
    exact Loan.regularPayment_capacity l hr i loan ⟨e, broker, he, hb, hw⟩ amount r hc hrr
  · cases tx with
    | loanManage i action =>
      cases action with
      | default =>
        obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
        obtain ⟨e, broker, loan, r, he, hb, hw, -, hrr, rfl⟩ := l.applyLoan_manage_inv u i .default hu
        have hlb : loan.broker = broker := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
        simp only [Loan.manage] at hrr
        unfold_ter at hrr
        walk_ok
        rename_i rd hd
        exact Loan.manageDefault_capacity l hr i loan ⟨e, broker, he, hb, hw⟩ rd hd
          (fun hnt => by rw [hlb]; exact hsupply hnt _ broker hb)
      | _ => simp [LendingTx.isOutflow] at hout
    | vaultWithdraw holder amount =>
      obtain ⟨-, hle, hAD⟩ := LendingLedger.lent_out_protected_proof l l' _ hr hr.holdsAsset.maxValue_le
        (Or.inl ⟨holder, amount, rfl⟩) h
      obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
      have hvault : (l.commitVault u).vault = u.vault := by
        unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
      have hYU := (l.applyVault_keepsLending _ u hu).yieldUnrealized
      rw [hvault] at hle hAD ⊢
      show u.vault.assetsAvailable.toRat + u.vault.assetsDeployed.toRat + u.vault.yieldUnrealized.toRat ≤
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat
      rw [hAD, hYU]
      linarith
    | vaultClawback holder assets =>
      obtain ⟨-, hle, hAD⟩ := LendingLedger.lent_out_protected_proof l l' _ hr hr.holdsAsset.maxValue_le
        (Or.inr ⟨holder, assets, rfl⟩) h
      obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault rfl h
      have hvault : (l.commitVault u).vault = u.vault := by
        unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
      have hYU := (l.applyVault_keepsLending _ u hu).yieldUnrealized
      rw [hvault] at hle hAD ⊢
      show u.vault.assetsAvailable.toRat + u.vault.assetsDeployed.toRat + u.vault.yieldUnrealized.toRat ≤
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.vault.yieldUnrealized.toRat
      rw [hAD, hYU]
      linarith
    | _ => simp [LendingTx.isOutflow] at hout

end XRPL.Model.Lending
