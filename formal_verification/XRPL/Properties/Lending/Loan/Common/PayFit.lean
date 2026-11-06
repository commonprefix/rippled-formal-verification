import XRPL.Properties.Lending.Loan.Common.PaySize
import XRPL.Properties.Lending.Loan.Common.PayReachable
import XRPL.Properties.Lending.Loan.Common.PayReachableWitness

/-! # What a payment adds fits a `Number`

On a reachable ledger a loan is at the base scale and pays principal and interest of whole base units, together
at most `300·(10^16 + 1)` of them, so their sum is a `Number`. The payment's vault bounds need no size hypothesis.
Its fee and the broker's cover are whole base units too, so their sum is a `Number` below `2^63` base units. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.pay_units LendingLedger.LoanAt.parts from XRPL.Properties.Lending.Loan.Common.PayReachable

variable (loan : Loan) (amount : Number) (paymentType : LoanPaymentType) (r : LoanWithAmounts Vault)

/-- On a reachable ledger the principal and interest a payment pays sum to a `Number`. -/
lemma Loan.payment_sum_fits (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r)) :
    ∃ w : Number, w.isNormalized ∧
      w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat := by
  obtain ⟨pp, ip, hpp, hip⟩ := Loan.pay_units loan amount paymentType r hr hat payment hpay hok
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  have hls := (hr.loanAt_scale hat).1
  have hrange := LendingLedger.Reachable.loanScale_range hr hat
  have hsum := hreach.pay_sum_le hrange.2 l.vault paymentType amount l.now payment hpay
  rw [hls, hpp, hip] at hsum
  have hu : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hlt : pp + ip < 2 ^ 63 := by
    have : ((pp + ip : ℕ) : ℚ) * 10 ^ l.vault.baseExponent ≤
        ((300 * (10 ^ 16 + 1) : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by push_cast; linarith
    have := le_of_mul_le_mul_right this hu
    have : pp + ip ≤ 300 * (10 ^ 16 + 1) := by exact_mod_cast this
    omega
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((pp + ip : ℕ) : ℤ) l.vault.baseExponent
    (by constructor <;> omega) (by unfold minExponent maxExponent; omega)
  exact ⟨w, hw, by rw [hwv, hpp, hip]; push_cast; ring⟩

/-- Proof body of `payment_vault_upper_bound`, on any reachable ledger. -/
lemma Loan.payment_vault_upper_bound_reachable_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r)) :
    (r.pool'.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤ 0 :=
  Loan.payment_vault_upper_bound_proof loan amount paymentType r l hr i hat payment hpay hok
    (Loan.payment_sum_fits loan amount paymentType r l hr i hat payment hpay hok)

/-- Proof body of the upper line of `Lending.payment_fees`. -/
lemma Loan.payment_fees_upper_bound_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault) (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok false)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (hfit : loan.broker.numericType.isIntegral = true → loan.broker.coverAvailable.toRat +
      payment.amounts.feePaid.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) :
    (r.loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat) - payment.amounts.feePaid.toRat ≤ 0 := by
  have hfee0 := (Loan.pay_parts_nonneg loan amount paymentType r l.vault l.now payment hpay hok).2.2
  refine Loan.payment_fees_upper_bound_of_fits loan l.vault amount l.now paymentType r payment hcover hpay hok hfee0
    fun hint => ?_
  -- the cover and the fee are whole base units, so their sum below `2^63` units is a `Number`
  obtain ⟨e, b, -, hb, hlb, -⟩ := LendingLedger.LoanAt.parts hat
  subst hlb
  obtain ⟨c, hc⟩ := (hr.cover_onGrid hb).nat loan.broker.exact.coverAvailable_nonneg
  obtain ⟨t, -, hreach⟩ := hr.loanAt_reachable hat
  obtain ⟨gs, gl, -⟩ := Loan.Reachable.fees_onGrid hreach
  have gfee := Loan.payInstalments_fee_onGrid loan l.vault paymentType amount l.now payment
    (hr.loanScale_range hat) gs gl hpay
  rw [(hr.loanAt_scale hat).1] at gfee
  obtain ⟨f, hf⟩ := gfee.nat hfee0
  have hu : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hlt : c + f < 2 ^ 63 := by
    have h := hfit hint
    rw [hc, hf, ← add_mul] at h
    exact_mod_cast lt_of_mul_lt_mul_right h hu.le
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((c + f : ℕ) : ℤ) l.vault.baseExponent
    (by constructor <;> omega) (by unfold minExponent maxExponent; omega)
  exact ⟨w, hw, by rw [hwv, hc, hf]; push_cast; ring⟩

end XRPL.Model.Lending
