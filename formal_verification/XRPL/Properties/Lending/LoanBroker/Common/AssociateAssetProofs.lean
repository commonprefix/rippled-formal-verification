import XRPL.Properties.Lending.LoanBroker.Common.DepositAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawAccuracy
import XRPL.Properties.Lending.LoanBroker.Common.ClawbackAccuracy
import XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality

/-! # Proof bodies for the XRP and MPT `associateAsset` theorems

On an XRP or MPT broker every cover operation moves `coverAvailable` by a whole
number. A whole `coverAvailable` within the type's bounds is stored exactly, so
`associateAsset` leaves it alone. `AssociateAsset.lean` states the theorems and
delegates here. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

variable {α : Type} [AssetPool α]

/-- A whole `coverAvailable` within an XRP or MPT type's bounds is on the asset
grid. -/
private lemma LoanBroker.coverAvailable_integral_not_rounded (lb : LoanBroker)
    (hnt : lb.numericType.isIntegral = true) (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hden : lb.toExact.coverAvailable.den = 1) (hcap : lb.toExact.coverAvailable < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded lb.numericType lb.coverAvailable = false :=
  STAmount.isRounded_integral_eq_false _ _ hnt hmaxoff lb.wf.coverAvailable_norm
    lb.exact.coverAvailable_nonneg hden (Rat.le_pred_of_lt hden hcap) hmax

/-- **Proof body of `coverDeposit_associateAsset_integral`.** -/
lemma LoanBroker.coverDeposit_associateAsset_integral_proof (lb : LoanBroker)
    (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverDeposit amount = .ok (.ok res))
    (hnt : lb.numericType.isIntegral = true) (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable + amount.toRat < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable + amount.toRat ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false := by
  have hnt' := (LoanBroker.coverDeposit_fixed_fields lb amount res hok).numericType
  have hup := LoanBroker.coverDeposit_credit_integral_proof lb amount res hok hint hsz hcint hbound
  have hval : res.loanBroker'.toExact.coverAvailable =
      lb.toExact.coverAvailable + amount.toRat := by linarith
  have hden : res.loanBroker'.toExact.coverAvailable.den = 1 := by
    rw [hval]
    exact Rat.den_one_add _ _ hcint (STAmount.IntegralCanonical.den_eq_one _ hint)
  exact LoanBroker.coverAvailable_integral_not_rounded res.loanBroker' (by rw [hnt']; exact hnt)
    (by rw [hnt']; exact hmaxoff) hden (by rw [hval]; exact hbound) (by rw [hval, hnt']; exact hmax)

/-- **Proof body of `coverWithdraw_associateAsset_integral`.** -/
lemma LoanBroker.coverWithdraw_associateAsset_integral_proof (lb : LoanBroker)
    (amount : STAmount) (res : LoanBrokerCoverResult)
    (hok : lb.coverWithdraw amount = .ok (.ok res))
    (hnt : lb.numericType.isIntegral = true) (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hint : amount.IntegralCanonical) (hsz : amount.mValue.toNat ≤ 2 ^ 63 - 1)
    (hnn : 0 ≤ amount.toRat) (hcint : lb.toExact.coverAvailable.den = 1)
    (hbound : lb.toExact.coverAvailable < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false := by
  have hnt' := (LoanBroker.coverWithdraw_fixed_fields lb amount res hok).numericType
  have hdown :=
    LoanBroker.coverWithdraw_debit_integral_proof lb amount res hok hint hsz hnn hcint hbound
  have hval : res.loanBroker'.toExact.coverAvailable =
      lb.toExact.coverAvailable - amount.toRat := by linarith
  have hden : res.loanBroker'.toExact.coverAvailable.den = 1 := by
    rw [hval]
    exact Rat.den_one_sub _ _ hcint (STAmount.IntegralCanonical.den_eq_one _ hint)
  exact LoanBroker.coverAvailable_integral_not_rounded res.loanBroker' (by rw [hnt']; exact hnt)
    (by rw [hnt']; exact hmaxoff) hden (by rw [hval]; linarith) (by rw [hval, hnt']; linarith)

/-- **Proof body of `coverClawback_associateAsset_integral`.** -/
lemma LoanBroker.coverClawback_associateAsset_integral_proof (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) (res : LoanBrokerCoverResult)
    (hcan : lb.canCoverClawback pool amount = .ok .tesSUCCESS)
    (hok : lb.coverClawback pool amount = .ok (.ok res))
    (hreq : ∀ a ∈ amount, a.isZero = false → a.ExactCanonical ∧ 0 ≤ a.toRat)
    (hnt : lb.numericType.isIntegral = true) (hmaxoff : (0 : Int) ≤ lb.numericType.maxOffset)
    (hcint : lb.toExact.coverAvailable.den = 1) (hbound : lb.toExact.coverAvailable < 2 ^ 63)
    (hmax : lb.toExact.coverAvailable ≤ lb.numericType.maxValue.toNat) :
    STAmount.isRounded res.loanBroker'.numericType res.loanBroker'.coverAvailable = false := by
  have hnt' := (LoanBroker.coverClawback_fixed_fields lb pool amount res hok).numericType
  obtain ⟨hint, _, hnn⟩ :=
    LoanBroker.coverClawback_amount_integral lb pool amount res hcan hok hreq hnt
  have hdown := LoanBroker.coverClawback_debit_integral_proof lb pool amount res hcan hok hreq hnt
    hcint hbound
  have hval : res.loanBroker'.toExact.coverAvailable =
      lb.toExact.coverAvailable - res.amount'.toRat := by linarith
  have hden : res.loanBroker'.toExact.coverAvailable.den = 1 := by
    rw [hval]
    exact Rat.den_one_sub _ _ hcint (STAmount.IntegralCanonical.den_eq_one _ hint)
  exact LoanBroker.coverAvailable_integral_not_rounded res.loanBroker' (by rw [hnt']; exact hnt)
    (by rw [hnt']; exact hmaxoff) hden (by rw [hval]; linarith) (by rw [hval, hnt']; linarith)

end XRPL.Model.Lending
