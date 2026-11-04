import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.LoanSteps
import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Lending.Loan.Common.PaidAmounts
import XRPL.Properties.Lending.Loan.Common.PayBounds

/-! # Payments that keep AssetsAvailable plus the payment below `10^16` base units

On a reachable ledger a payment pays principal and interest in whole base units. While AssetsAvailable plus that
payment stays below `10^16` base units, the vault credits it on the base grid, so neither AssetsTotal nor the share
value falls. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The loan read at `i` is the only one: the slot and its broker fix it. -/
lemma LendingLedger.LoanAt.unique {l : LendingLedger} {i : Nat} {loan loan' : Loan} (h : l.LoanAt i loan)
    {e : LoanEntry} {b : LoanBroker} (he : l.loan? i = some e) (hb : l.broker? e.brokerIndex = some b)
    (hw : e.loan.withBroker b = .ok loan') : loan' = loan := by
  obtain ⟨e₂, b₂, he₂, hb₂, hw₂⟩ := h
  rw [he] at he₂
  obtain rfl := Option.some.inj he₂
  rw [hb] at hb₂
  obtain rfl := Option.some.inj hb₂
  rw [hw] at hw₂
  exact Except.ok.inj hw₂

/-- A balance of whole base units and another strictly less than one base unit above it is at most the first. -/
private lemma units_le_of_lt {x y : ℚ} {m n : ℕ} {b : Int} (hx : x = (m : ℚ) * 10 ^ b) (hy : y = (n : ℚ) * 10 ^ b)
    (h : x - y < 10 ^ b) : x ≤ y := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  rw [hx, hy, ← sub_mul] at h
  have h1 : (m : ℚ) - n < 1 := by
    have := lt_of_mul_lt_mul_right (by linarith : ((m : ℚ) - n) * 10 ^ b < 1 * 10 ^ b) hp.le
    exact this
  have h2 : m ≤ n := by
    have : (m : ℤ) - n < 1 := by exact_mod_cast h1
    omega
  rw [hx, hy]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hp.le

/-- A payment that keeps AssetsAvailable below `10^16` base units loses less than a base unit of AssetsTotal.
The vault credits principal and interest on the base grid and takes the principal off AssetsDeployed. -/
lemma LendingLedger.pay_total_lt (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan) (paymentType : LoanPaymentType) (amount : Number) (payment : UnsettledPayment Vault)
    (r : LoanWithAmounts Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    l.vault.toExact.assetsTotal - r.pool'.toExact.assetsTotal < 10 ^ l.vault.baseExponent := by
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  obtain ⟨hls, hnt⟩ := hr.loanAt_scale hat

  obtain ⟨g1, g2⟩ := Loan.payInstalments_onGrid loan l.vault paymentType amount l.now payment
    (by rw [hls]; omega) hpay
  rw [hls] at g1 g2
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault paymentType amount l.now r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨_, _, _, _, _, _, _, hsums, -⟩ := UnsettledPayment.settle_ok payment r hs
  have hparts := hsums.parts
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hparts
  have hpp0 := (Number.signum_nonneg_iff_toRat g1.1).mp hparts.1.1
  have hip0 := (Number.signum_nonneg_iff_toRat g2.1).mp hparts.1.2
  obtain ⟨pp, hpp⟩ := g1.nat hpp0
  obtain ⟨ip, hip⟩ := g2.nat hip0
  obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨d, hd, hdv⟩ := hr.deployed_units

  have hsumv : payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat =
      ((pp + ip : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by rw [hpp, hip]; push_cast; ring
  have hall : a + (pp + ip) < 10 ^ 16 := by
    rw [ha, hsumv, ← add_mul] at htotal
    have : ((a + (pp + ip) : ℕ) : ℚ) < 10 ^ 16 := by
      push_cast; exact lt_of_mul_lt_mul_right (by push_cast at htotal; linarith) hp10.le
    exact_mod_cast this
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((pp + ip : ℕ) : ℤ) l.vault.baseExponent
    (by constructor <;> omega) (by unfold minExponent maxExponent; omega)
  have hsum : ∃ w : Number, w.isNormalized ∧ 0 ≤ w.toRat ∧
      w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat :=
    ⟨w, hw, by rw [hwv]; positivity, by rw [hwv, hsumv]; push_cast; ring⟩
  obtain ⟨w', hw', hw'v⟩ := Number.exists_normalized_int_mul_pow ((d : ℤ) - pp) l.vault.baseExponent
    (by constructor <;> omega) (by unfold minExponent maxExponent; omega)
  have hdeployed : ∃ w : Number, w.isNormalized ∧
      w.toRat = l.vault.assetsDeployed.toRat - payment.amounts.principalPaid.toRat :=
    ⟨w', hw', by rw [hw'v, hdv, hpp]; push_cast; ring⟩
  have hroom : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤
        (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent := by
    have h1 : ((a + (pp + ip) : ℕ) : ℚ) + 1 ≤ 10 ^ 16 := by
      have : a + (pp + ip) + 1 ≤ 10 ^ 16 := by omega
      exact_mod_cast this
    have hpow : (10 : ℚ) ^ (16 + l.vault.baseExponent) = 10 ^ 16 * 10 ^ l.vault.baseExponent := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    rw [hpow, ha, hsumv, ← add_mul]
    have := mul_le_mul_of_nonneg_right h1 hp10.le
    push_cast at this ⊢
    linarith
  obtain ⟨hlt, -⟩ := Loan.payment_assetsTotal_lower_bound_at_base loan l.vault amount l.now paymentType r payment a hnt
    hr.availableStored hpay hok hsum hdeployed ha hroom
  linarith

/-- A successful LoanPay: the loan read at `i` paid on the ledger's vault, and its slot and the vault rewritten
with the vault settings kept. -/
lemma LendingLedger.loanPay_parts {l l' : LendingLedger} {i : Nat} {paymentType : LoanPaymentType} {amount : Number}
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) :
    ∃ (e : LoanEntry) (loan : Loan) (r : LoanWithAmounts Vault), l.loan? i = some e ∧ l.LoanAt i loan ∧
      e.loan.withBroker loan.broker = .ok loan ∧ (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') ∧ Vault.KeepsSettings l.vault r.pool' := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  have hks := LendingLedger.applyLoan_keepsSettings l _ u hu
  obtain ⟨e, broker, loan, r, he, hb, hw, -, hok, rfl⟩ := LendingLedger.applyLoan_pay_inv l u i paymentType amount hu
  have hbr : loan.broker = broker := by
    rw [show loan.broker = loan.toRawLoan.broker from rfl, Loan.withBroker_eq hw]
  exact ⟨e, loan, r, he, ⟨e, broker, he, hb, hw⟩, by rw [hbr]; exact hw, hok, rfl, hks⟩

/-- A payment that keeps AssetsAvailable plus its credit below `10^16` base units never lowers AssetsTotal. Both
totals are whole base units, and the payment loses less than one of them. -/
lemma LendingLedger.pay_assetsTotal_le {l l' : LendingLedger} (hr : l.Reachable) {i : Nat}
    {paymentType : LoanPaymentType} {amount : Number} (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l'))
    (loan : Loan) (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    l.vault.toExact.assetsTotal ≤ l'.vault.toExact.assetsTotal := by
  have hr' := hr.apply h
  obtain ⟨e, loan', r, he, hat', -, hok, rfl, hks⟩ := LendingLedger.loanPay_parts h
  obtain ⟨e₂, b₂, he₂, hb₂, hw₂⟩ := hat'
  obtain rfl := hat.unique he₂ hb₂ hw₂
  have hlt := LendingLedger.pay_total_lt l hr i loan' hat paymentType amount payment r hpay hok htotal
  have hbe := hks.baseExponent_eq
  obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨d, -, hd⟩ := hr.deployed_units
  obtain ⟨a', ha'⟩ := hr'.assetsAvailable_units hr'.holdsAsset
  obtain ⟨d', -, hd'⟩ := hr'.deployed_units
  change r.pool'.assetsAvailable.toRat = (a' : ℚ) * 10 ^ r.pool'.baseExponent at ha'
  change r.pool'.assetsDeployed.toRat = (d' : ℚ) * 10 ^ r.pool'.baseExponent at hd'
  rw [hbe] at ha' hd'
  exact units_le_of_lt (m := a + d) (n := a' + d')
    (by show l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat = _; rw [ha, hd]; push_cast; ring)
    (by show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat = _; rw [ha', hd']; push_cast; ring) hlt

/-- Proof body of the shareValue' ≥ shareValue part of `Lending.payment_share_value`. -/
lemma LendingLedger.payment_share_value_proof (l : LendingLedger) (hr : l.Reachable) (l' : LendingLedger) (i : Nat)
    (paymentType : LoanPaymentType) (amount : Number)
    (h : (l.apply (.loanPay i paymentType amount)).run = .ok (.ok l')) (loan : Loan) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    l.vault.toRawVault.shareValue ≤ l'.vault.toRawVault.shareValue := by
  have hge := LendingLedger.pay_assetsTotal_le hr h loan hat payment hpay htotal
  obtain ⟨e, loan', r, he, hat', -, hok, rfl, hks⟩ := LendingLedger.loanPay_parts h
  obtain ⟨e₂, b₂, he₂, hb₂, hw₂⟩ := hat'
  obtain rfl := hat.unique he₂ hb₂ hw₂
  change l.vault.toExact.assetsTotal ≤ r.pool'.toExact.assetsTotal at hge

  -- LossUnrealized does not rise: the payment releases the loss of an impaired loan
  obtain ⟨himp, hnimp, -⟩ := Loan.pay_lossStep loan' l.vault paymentType amount l.now r hok
  have hlu : r.pool'.lossUnrealized.toRat ≤ l.vault.lossUnrealized.toRat := by
    cases hi : loan'.isImpaired
    · rw [hnimp hi]
    · obtain ⟨w, hw, hwv⟩ := hr.unimpair_fits hat
      have hsub := Number.operator_add_exact_of_fits l.vault.wf.lossUnrealized_norm
        (Number.operator_neg_isNormalized _ loan'.wf.principalOutstanding_norm) (himp hi)
        ⟨w, hw, by rw [hwv, Number.toRat_neg]; ring⟩
      have hpo0 : 0 ≤ loan'.principalOutstanding.toRat := loan'.exact.principalOutstanding_nonneg
      rw [hsub, Number.toRat_neg]
      linarith

  -- SharesTotal is unchanged, so the share value does not fall
  have hS : r.pool'.toExact.sharesTotal = l.vault.toExact.sharesTotal := by
    show r.pool'.sharesTotal.toRat.num.toNat = l.vault.sharesTotal.toRat.num.toNat
    rw [hks.sharesTotal]
  show l.vault.toRawVault.withdrawNav / (l.vault.toExact.sharesTotal : ℚ) ≤
    r.pool'.toRawVault.withdrawNav / (r.pool'.toExact.sharesTotal : ℚ)
  rw [hS]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  show l.vault.toExact.assetsTotal - l.vault.lossUnrealized.toRat ≤
    r.pool'.toExact.assetsTotal - r.pool'.lossUnrealized.toRat
  linarith

end XRPL.Model.Lending
