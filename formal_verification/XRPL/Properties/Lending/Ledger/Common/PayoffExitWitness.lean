import XRPL.Properties.Lending.Ledger.Common.CoarsenedVault
import XRPL.Properties.Lending.Ledger.Common.Exits
import XRPL.Properties.Protocol.STAmount.Mul.Common.Integral

/-! # An MPT vault whose sole holder can't withdraw every share

A closed-ended MPT vault lends almost all its cash for one day at a 100% late rate, and the loan is paid 136 years
late, which grows AssetsAvailable to about `1.23·10^18` units. The 19-digit price of all the shares then rounds one
unit above the cash, and the final VaultWithdraw fails with tecINSUFFICIENT_FUNDS. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultSchedule WithdrawAmount)

/-- Subscription until 1000, redemption 900 days later. -/
private def mpSchedule : VaultSchedule := ⟨1000, 1000 + 900 * 86400⟩

/-- The new MPT vault VaultCreate makes for `mpSchedule`. -/
private def mpRawVault : RawVault :=
  { assetsAvailable := Number.zero, assetsDeployed := Number.zero, assetsReserved := Number.zero,
    assetsMaximum := none, numericType := NumericType.int64, scale := 0, sharesTotal := Number.zero,
    lossUnrealized := Number.zero, yieldUnrealized := Number.zero, schedule := some mpSchedule,
    earlyExitFeeRate := none, ownerCanBlockDeposit := false, depositBlocked := false }

private def mpVault : Vault := ⟨mpRawVault, by native_decide, by native_decide⟩

/-- The ledger right after VaultCreate. -/
private def mpGenesis : LendingLedger := { vault := mpVault, shares := [], brokers := [], loans := [], now := 0 }

private lemma mpGenesis_genesis : mpGenesis.Genesis where
  created := ⟨none, none, mpSchedule, none, false, NumericType.int64, by native_decide, by
    unfold Vault.create RawVault.to_lawful
    exact dif_pos ⟨mpVault.wf, mpVault.valid⟩⟩
  holds_asset := Or.inr (Or.inr rfl)
  no_holders := rfl
  no_brokers := rfl
  no_loans := rfl
  not_deleted := rfl

/-- No interest, a late rate of 100%. -/
private def mpRates : LoanRates :=
  { interestRate := 0, lateInterestRate := 100000, closeInterestRate := 0, overpaymentInterestRate := 0,
    overpaymentFee := 0 }

/-- A deposit of `8999998218225000` units, a broker without cover, a one-day loan of `8999998218223805` units, a
close at 4294966740, near the end of the 32-bit clock, and the late payment of `1234707329474129226` units. -/
private def mpTxs : List LendingTx :=
  [.vaultDeposit 0 (STAmount.unchecked .int64 8999998218225000 0 false) false,
   .close 1001,
   .loanBrokerCreate ⟨none, none, none, none⟩,
   .loanSet 0 ⟨false, 8999998218223805000, -3⟩ mpRates cwFees (some 86400) (some 1) (some 60) 0 false false,
   .close 4294966740,
   .loanPay 0 .late ⟨false, 1234707329474129226, 0⟩]

/-- Every loan stored on the ledger is paid off. -/
private def LendingLedger.loansPaid (l : LendingLedger) : Bool :=
  l.loans.all fun o => match o with
    | some e => e.loan.paymentRemaining == 0
    | none => true

private lemma LendingLedger.loansPaid_spec {l : LendingLedger} (h : l.loansPaid = true) :
    ∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.paymentRemaining = 0 := by
  intro i e he
  unfold LendingLedger.loan? at he
  cases hi : l.loans[i]? with
  | none => rw [hi] at he; cases he
  | some o =>
    rw [hi] at he
    cases o with
    | none => cases he
    | some e' =>
      cases he
      have := List.all_eq_true.mp h _ (List.mem_of_getElem? hi)
      simpa using this

/-- In the redemption phase, with every loan paid off and holder 0 owning every share, the withdrawal of every
share is rejected. The shares name a canonical int64 amount, the one form the preflight accepts. -/
private def mpCheck : Bool :=
  match mpGenesis.run mpTxs with
  | .ok l =>
    !l.vaultDeleted && l.vault.phase l.now == .redemption && l.loansPaid && l.isSoleShareholder 0 &&
      l.vault.numericType == NumericType.int64 &&
      match STAmount.ofNumber .int64 (l.sharesOf 0) .to_nearest with
      | .ok S =>
        decide (S.toRat = (l.sharesOf 0).toRat) && isCanonicalAmount S .int64 && isPositiveAmount S &&
          match (l.apply (.vaultWithdraw 0 (.vaultShares S))).run with
          | .ok (.error .tecINSUFFICIENT_FUNDS) => true
          | _ => false
      | .error _ => false
  | .error _ => false

private lemma mpCheck_true : mpCheck = true := by native_decide

/-- Two int64 amounts the preflight accepts with the same value are the same amount. -/
private lemma STAmount.eq_of_int64_canonical {a b : STAmount} (ha : isCanonicalAmount a .int64 = true)
    (hpa : isPositiveAmount a = true) (hb : isCanonicalAmount b .int64 = true) (hpb : isPositiveAmount b = true)
    (hv : a.toRat = b.toRat) : a = b := by
  simp only [isCanonicalAmount, Bool.and_eq_true, beq_iff_eq, show NumericType.int64.isIntegral = true from rfl,
    if_true, decide_eq_true_eq] at ha hb
  simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hpa hpb
  rw [STAmount.toRat_of_nonneg_offset_zero a hpa.1 ha.2.1, STAmount.toRat_of_nonneg_offset_zero b hpb.1 hb.2.1]
    at hv
  have hm : a.mValue = b.mValue := UInt64.toNat_inj.mp (by exact_mod_cast hv)
  cases a; cases b
  simp_all

/-- A reachable MPT vault in redemption, with every loan closed, can refuse its sole holder the withdrawal of
every share. The cash of about `1.23·10^18` units prices all the shares one unit above itself. -/
lemma LendingLedger.payoff_exit_mpt_witness :
    ∃ (l : LendingLedger) (h : Nat), l.Reachable ∧ l.vaultDeleted = false ∧ l.vault.phase l.now = .redemption ∧
      (∀ (i : Nat) (e : LoanEntry), l.loan? i = some e → e.loan.paymentRemaining = 0) ∧
      l.isSoleShareholder h = true ∧ l.vault.numericType = NumericType.int64 ∧
      ∀ (shares : STAmount) (l' : LendingLedger), shares.toRat = (l.sharesOf h).toRat →
        (l.apply (.vaultWithdraw h (.vaultShares shares))).run ≠ .ok (.ok l') := by
  have hc := mpCheck_true
  unfold mpCheck at hc
  split at hc
  case h_2 => cases hc
  rename_i l hl
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hnd, hph⟩, hpaid⟩, hsole⟩, hnt⟩, hc⟩ := hc
  split at hc
  case h_2 => cases hc
  rename_i S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hSv, hSc⟩, hSp⟩, hw⟩ := hc
  have hrej : (l.apply (.vaultWithdraw 0 (.vaultShares S))).run = .ok (.error .tecINSUFFICIENT_FUNDS) := by
    split at hw
    · rename_i h'; exact h'
    · cases hw
  refine ⟨l, 0, LendingLedger.Reachable.of_run mpGenesis_genesis hl, hnd, hph, l.loansPaid_spec hpaid, hsole, hnt,
    fun shares l' hv hok => ?_⟩
  by_cases hpre : (isCanonicalAmount shares .int64 && isPositiveAmount shares) = true
  · rw [Bool.and_eq_true] at hpre
    have heq := STAmount.eq_of_int64_canonical hpre.1 hpre.2 hSc hSp (by rw [hv, hSv])
    rw [heq, hrej] at hok
    cases hok
  · have hp : (LendingTx.vaultWithdraw 0 (.vaultShares shares)).preflight l = .temBAD_AMOUNT := by
      simp only [LendingTx.preflight]
      rw [if_neg hpre]
    unfold LendingLedger.apply at hok
    rw [hp] at hok
    cases hok

end XRPL.Model.Lending
