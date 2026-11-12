import XRPL.Properties.Lending.Loan.Common.RegularInterest
import XRPL.Properties.Lending.Loan.Common.PayBounds
import XRPL.Properties.Lending.Loan.Common.PayValues
import XRPL.Properties.Lending.Loan.Common.YieldValue
import XRPL.Properties.Lending.Ledger.Common.IntegralCoverInv

/-! # Payments on a reachable ledger

On a reachable ledger the vault balances are whole base units and the loan's scale is the vault's base scale.
These are the proof bodies of the LoanPay theorems stated over a reachable ledger. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

variable (loan : Loan) (amount : Number) (paymentType : LoanPaymentType) (r : LoanWithAmounts Vault)

/-- The loan at `i` reads its broker's ledger copy, and the stored PrincipalOutstanding. -/
private lemma LendingLedger.LoanAt.parts {l : LendingLedger} {i : Nat} {loan : Loan} (hat : l.LoanAt i loan) :
    ∃ e b, l.loan? i = some e ∧ l.broker? e.brokerIndex = some b ∧ loan.broker = b ∧
      loan.principalOutstanding = e.loan.principalOutstanding := by
  obtain ⟨e, b, he, hb, hw⟩ := hat
  have hraw := Loan.withBroker_eq hw
  exact ⟨e, b, he, hb, (congrArg RawLoan.broker hraw :), (congrArg RawLoan.principalOutstanding hraw :)⟩

/-- The loan at `i` of a reachable ledger owes at most `10^16` base units of principal. -/
private lemma LendingLedger.Reachable.loanAt_principal {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) :
    loan.principalOutstanding.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
  obtain ⟨e, b, he, -, -, hpo⟩ := hat.parts
  rw [hpo]
  exact hr.lossInv.principal i e he

/-- A payment that passes moves principal, interest and fee of at least zero. -/
lemma Loan.pay_parts_nonneg (v : Vault) (now : UInt32) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments v paymentType amount now).run = .ok (.ok payment))
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    0 ≤ payment.amounts.principalPaid.toRat ∧ 0 ≤ payment.amounts.interestPaid.toRat ∧
      0 ≤ payment.amounts.feePaid.toRat := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v paymentType amount now r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨_, _, _, _, _, _, _, hsums, -⟩ := UnsettledPayment.settle_ok payment r hs
  have hparts := hsums.parts
  obtain ⟨h1, h2, h3⟩ := Loan.payInstalments_norm loan v amount now paymentType payment hpay
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hparts
  exact ⟨(Number.signum_nonneg_iff_toRat h1).mp hparts.1.1, (Number.signum_nonneg_iff_toRat h2).mp hparts.1.2,
    (Number.signum_nonneg_iff_toRat h3).mp hparts.2⟩

/-- On a reachable ledger a payment pays principal and interest in whole base units of at least zero. -/
private lemma Loan.pay_units {l : LendingLedger} (hr : l.Reachable) {i : Nat} (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r)) :
    ∃ pp ip : ℕ, payment.amounts.principalPaid.toRat = (pp : ℚ) * 10 ^ l.vault.baseExponent ∧
      payment.amounts.interestPaid.toRat = (ip : ℚ) * 10 ^ l.vault.baseExponent := by
  obtain ⟨g1, g2⟩ := Loan.payInstalments_onGrid loan l.vault paymentType amount l.now payment
    (hr.loanScale_range hat) hpay
  obtain ⟨h1, h2, -⟩ := Loan.pay_parts_nonneg loan amount paymentType r l.vault l.now payment hpay hok
  rw [(hr.loanAt_scale hat).1] at g1 g2
  obtain ⟨pp, hpp⟩ := g1.nat h1
  obtain ⟨ip, hip⟩ := g2.nat h2
  exact ⟨pp, ip, hpp, hip⟩

/-- Paying an impaired loan -> LossUnrealized' = LossUnrealized − PrincipalOutstanding. -/
lemma Loan.payment_unimpairs_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (himp : loan.isImpaired = true) (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r)) :
    r.pool'.toExact.lossUnrealized = l.vault.toExact.lossUnrealized - loan.toExact.principalOutstanding := by
  have hsum := Loan.payment_unimpairs_sum loan l.vault amount l.now paymentType r himp hok
  obtain ⟨n, hn⟩ := hr.lossInv.grid
  have hnb := hr.lossInv.bound
  obtain ⟨hpg, -⟩ := Loan.principal_onGrid loan
  rw [(hr.loanAt_scale hat).1] at hpg
  obtain ⟨j, hj⟩ := hpg.nat loan.exact.principalOutstanding_nonneg
  have hjb := hr.loanAt_principal hat
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hn16 : n ≤ 10 ^ 16 := by
    have : (n : ℚ) * 10 ^ l.vault.baseExponent ≤ ((10 ^ 16 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [← hn]; push_cast; exact hnb
    exact_mod_cast le_of_mul_le_mul_right this hp
  have hj16 : j ≤ 10 ^ 16 := by
    have : (j : ℚ) * 10 ^ l.vault.baseExponent ≤ ((10 ^ 16 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [← hj]; push_cast; exact hjb
    exact_mod_cast le_of_mul_le_mul_right this hp
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hv := Number.operator_add_toRat_of_grid _ _ _ n (-(j : ℤ)) l.vault.baseExponent l.vault.wf.lossUnrealized_norm
    (Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm) (by rw [hn]; push_cast; ring)
    (by rw [Number.toRat_neg, hj]; push_cast; ring) (by constructor <;> omega)
    (by unfold minExponent maxExponent; omega) hsum
  show r.pool'.lossUnrealized.toRat = l.vault.lossUnrealized.toRat - loan.principalOutstanding.toRat
  rw [hv, hn, hj]
  push_cast
  ring

/-- A payment -> PrincipalOutstanding, AssetsDeployed and DebtTotal each drop by principalPaid. -/
lemma Loan.payment_principal_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r)) :
    loan.principalOutstanding.toRat - r.loan'.principalOutstanding.toRat = payment.amounts.principalPaid.toRat ∧
      l.vault.assetsDeployed.toRat - r.pool'.assetsDeployed.toRat = payment.amounts.principalPaid.toRat ∧
      loan.broker.debtTotal.toRat - r.loan'.broker.debtTotal.toRat = payment.amounts.principalPaid.toRat := by
  have hrange := hr.loanScale_range hat
  have hls := (hr.loanAt_scale hat).1
  obtain ⟨paid, hpg, hp0, hpe, hdt, had⟩ := Loan.pay_principal loan l.vault paymentType amount l.now r hrange hok
  obtain ⟨-, -, hpe'⟩ := Loan.payInstalments_paidOn loan l.vault paymentType amount l.now payment hrange hpay
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault paymentType amount l.now r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨_, _, _, _, _, _, broker', -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok payment r hs
  have hpo : r.loan'.principalOutstanding = payment.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding (RawLoan.to_lawful_ok hloan).1 :)
  have hpaid : paid.toRat = payment.amounts.principalPaid.toRat := by
    have : payment.amounts.principalPaid.toRat + r.loan'.principalOutstanding.toRat =
        loan.principalOutstanding.toRat := by rw [hpo]; exact hpe'
    linarith
  rw [hls] at hpg
  obtain ⟨k, hk⟩ := hpg.nat hp0
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hs : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hk16 : k ≤ 10 ^ 16 := by
    have : (k : ℚ) * 10 ^ l.vault.baseExponent ≤ ((10 ^ 16 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [← hk]; push_cast
      have := hr.loanAt_principal hat
      have : 0 ≤ r.loan'.principalOutstanding.toRat := r.loan'.exact.principalOutstanding_nonneg
      linarith
    exact_mod_cast le_of_mul_le_mul_right this hp
  -- AssetsDeployed and DebtTotal are whole base units within `10^16` of them
  obtain ⟨nd, hnd⟩ := hr.scaleInv.principalSum_grid (fun _ => true)
  have had0 : l.vault.assetsDeployed.toRat = (nd : ℚ) * 10 ^ l.vault.baseExponent := by
    rw [hr.debtInv.deployed, hnd]
  have hnd16 : nd ≤ 10 ^ 16 := by
    have : (nd : ℚ) * 10 ^ l.vault.baseExponent ≤ ((10 ^ 16 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [← had0]; push_cast; exact hr.lossInv.deployed
    exact_mod_cast le_of_mul_le_mul_right this hp
  obtain ⟨e, b, -, hb, hlb, -⟩ := hat.parts
  obtain ⟨nb, hnb⟩ := hr.scaleInv.brokerPrincipal_grid e.brokerIndex
  have hdt0 : loan.broker.debtTotal.toRat = (nb : ℚ) * 10 ^ l.vault.baseExponent := by
    rw [hlb, hr.debtInv.debt _ b hb, hnb]
  have hnb16 : nb ≤ 10 ^ 16 := by
    have : (nb : ℚ) * 10 ^ l.vault.baseExponent ≤ ((10 ^ 16 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [← hnb]; push_cast
      exact le_trans (l.brokerPrincipal_le e.brokerIndex) (by rw [← hr.debtInv.deployed]; exact hr.lossInv.deployed)
    exact_mod_cast le_of_mul_le_mul_right this hp
  have hvd := Number.operator_add_toRat_of_grid _ _ _ nd (-(k : ℤ)) l.vault.baseExponent
    l.vault.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hpg.1) (by rw [had0]; push_cast; ring)
    (by rw [Number.toRat_neg, hk]; push_cast; ring) (by constructor <;> omega) hs had
  have hvt := Number.operator_sub_toRat_of_grid _ _ _ nb k l.vault.baseExponent loan.broker.wf.debtTotal_norm hpg.1
    (by rw [hdt0]; push_cast; ring) (by rw [hk]; push_cast; ring) (by constructor <;> omega) hs hdt
  refine ⟨by rw [hpo]; linarith, ?_, ?_⟩
  · rw [hvd, had0, ← hpaid, hk]; push_cast; ring
  · rw [hvt, hdt0, ← hpaid, hk]; push_cast; ring

/-- The sum of whole base units below `10^16` of them is a `Number`. -/
private lemma LendingLedger.sum_number {l : LendingLedger} (x y : ℚ) (a b : ℕ)
    (ha : x = (a : ℚ) * 10 ^ l.vault.baseExponent) (hb : y = (b : ℚ) * 10 ^ l.vault.baseExponent)
    (hlt : x + y < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∃ w : Number, w.isNormalized ∧ 0 ≤ w.toRat ∧ w.toRat = x + y := by
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hab : a + b < 10 ^ 16 := by
    have : ((a + b : ℕ) : ℚ) * 10 ^ l.vault.baseExponent < ((10 ^ 16 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by
      push_cast; rw [add_mul, ← ha, ← hb]; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((a + b : ℕ) : ℤ) l.vault.baseExponent
    (by constructor <;> omega) (by unfold minExponent maxExponent; omega)
  refine ⟨w, hw, by rw [hwv]; positivity, ?_⟩
  rw [hwv, ha, hb]; push_cast; ring

/-- Below `10^16` base units, the room the base-grid lemmas need: a sum of whole base units is at most one unit
under `10^(16 + b)`. -/
private lemma LendingLedger.room_of_lt {l : LendingLedger} (x y : ℚ) (a b : ℕ)
    (ha : x = (a : ℚ) * 10 ^ l.vault.baseExponent) (hb : y = (b : ℚ) * 10 ^ l.vault.baseExponent)
    (hlt : x + y < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    x + y ≤ (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent := by
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hab : a + b + 1 ≤ 10 ^ 16 := by
    have : ((a + b : ℕ) : ℚ) * 10 ^ l.vault.baseExponent < ((10 ^ 16 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by
      push_cast; rw [add_mul, ← ha, ← hb]; exact hlt
    have := lt_of_mul_lt_mul_right this hp.le
    exact_mod_cast this
  have h1 : ((a + b + 1 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent ≤ ((10 ^ 16 : ℕ) : ℚ) * 10 ^ l.vault.baseExponent :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hp.le
  rw [open_line_eq, ha, hb]
  push_cast at h1 ⊢
  linarith

/-- Proof body of the first line of `Lending.payment_vault`, given that principalPaid + interestPaid is a `Number`. -/
lemma Loan.payment_vault_upper_bound_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (hsum : ∃ w : Number, w.isNormalized ∧
      w.toRat = payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) :
    (r.pool'.assetsAvailable.toRat - l.vault.assetsAvailable.toRat) -
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) ≤ 0 := by
  obtain ⟨h1, h2, -⟩ := Loan.pay_parts_nonneg loan amount paymentType r l.vault l.now payment hpay hok
  obtain ⟨w, hw, hwv⟩ := hsum
  exact Loan.payment_vault_upper_bound_of_fits loan l.vault amount l.now paymentType r payment
    (hr.loanAt_scale hat).2 (hr.storesAvailable hr.holdsAsset.maxValue_le) hpay hok ⟨w, hw, by rw [hwv]; linarith, hwv⟩

/-- The cover of a stored loan's broker is whole base units. -/
private lemma LendingLedger.Reachable.loan_cover_units {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) : ∃ c : ℕ, loan.broker.coverAvailable.toRat = (c : ℚ) * 10 ^ l.vault.baseExponent := by
  obtain ⟨e, b, -, hb, hlb, -⟩ := hat.parts
  rw [hlb]
  cases hnt : l.vault.numericType.isIntegral
  · have hfr := NumericType.eq_fractional_of_not_integral (by simpa using hnt)
    exact (hr.coverGridInv.cover hfr _ b hb).nat b.exact.coverAvailable_nonneg
  · exact (hr.integralCover hnt _ b hb).nat b.exact.coverAvailable_nonneg

/-- Proof body of `payment_fees_lower_bound`. -/
lemma Loan.payment_fees_lower_bound_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault) (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok false)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (hroom : loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat ≤
      (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent) :
    ∀ e, numberExponent r.loan'.broker.coverAvailable l.vault.baseExponent loan.broker.numericType = .ok e →
      loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat - r.loan'.broker.coverAvailable.toRat <
        10 ^ e := by
  obtain ⟨c, hc⟩ := hr.loan_cover_units hat
  obtain ⟨h1, h2, -⟩ := Loan.payment_fees_lower_bound_at_base loan l.vault amount l.now paymentType r payment c
    (hr.loanAt_scale hat).2 hcover hpay hok (Loan.pay_parts_nonneg loan amount paymentType r l.vault l.now payment
      hpay hok).2.2 hc hroom
  intro e he
  rw [h2 e he]
  exact h1

/-- Proof body of the amountToBroker line of `payment_fees`. Below the minimum cover, a cover that is not coarsened
gains exactly what the payment sends the broker. -/
lemma Loan.payment_cover_amountToBroker_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (hcover : loan.broker.hasMinimumCover l.vault.baseExponent = .ok false)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (hroom : loan.broker.coverAvailable.toRat + payment.amounts.feePaid.toRat ≤
      (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent) :
    r.loan'.broker.coverAvailable.toRat - loan.broker.coverAvailable.toRat = r.amountToBroker.toRat := by
  obtain ⟨c, hc⟩ := hr.loan_cover_units hat
  obtain ⟨-, -, h⟩ := Loan.payment_fees_lower_bound_at_base loan l.vault amount l.now paymentType r payment c
    (hr.loanAt_scale hat).2 hcover hpay hok (Loan.pay_parts_nonneg loan amount paymentType r l.vault l.now payment
      hpay hok).2.2 hc hroom
  linarith

/-- A lawful loan's interestDue in LoanScale units: at least minus one, at least zero for an XRP or MPT loan, and
below the asset's mantissa bound. -/
private lemma Loan.interest_units (l : Loan) (i : Number) (h : l.interestDue = .ok i) :
    ∃ k : ℤ, i.toRat = (k : ℚ) * 10 ^ l.loanScale ∧ l.toExact.interestDue = (k : ℚ) * 10 ^ l.loanScale ∧
      -1 ≤ k ∧ k < l.toExact.numericType.mantissaBound ∧ (l.broker.numericType.isIntegral = true → 0 ≤ k) := by
  obtain ⟨t, p, m, ht, -, -, -, -, -, hu, hge, -⟩ := Loan.state_units l
    { valueOutstanding := l.totalValueOutstanding, principalOutstanding := l.principalOutstanding,
      interestDue := i, managementFeeDue := l.managementFeeOutstanding } (by
        unfold RawLoan.interestDue at h
        unfold Loan.state LoanState.build
        simp only [bind, Except.bind] at h ⊢
        split at h
        · cases h
        · rw [h]; rfl)
  have hex : l.toExact.interestDue = i.toRat := (Loan.interestDue_toExact l i h).symm
  have hpos : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
  refine ⟨(t : ℤ) - p - m, hu.val, by rw [hex]; exact hu.val, hge, by omega, fun _ => ?_⟩
  have h0 : 0 ≤ l.toExact.interestDue := l.exact.interest_nonneg
  rw [hex, hu.val] at h0
  have : (0 : ℚ) ≤ (((t : ℤ) - p - m : ℤ) : ℚ) := nonneg_of_mul_nonneg_left h0 hpos
  exact_mod_cast this

/-- A payment adds to YieldUnrealized the change in the loan's interestDue, a whole number of base units below
`2^63` of them. -/
private lemma Loan.pay_yieldDelta (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r)) :
    ∃ yd : Number, yd.isNormalized ∧
      l.vault.yieldUnrealized.operator_add yd .to_nearest = .ok r.pool'.yieldUnrealized ∧
      ∃ k : ℤ, yd.toRat = (k : ℚ) * 10 ^ l.vault.baseExponent ∧ -2 ^ 63 < k ∧ k < 2 ^ 63 ∧
        yd.toRat = r.loan'.toExact.interestDue - loan.toExact.interestDue := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan l.vault paymentType amount l.now r hok
  obtain ⟨-, hu, hst, hsi, -⟩ := Loan.payInstalments_ok loan l.vault paymentType amount l.now p hp
  obtain ⟨_, yd, _, _, _, raw, _, hsums, hadj, hv', -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hpool := Vault.poolAdjust_ok _ _ raw r.pool' hadj hv'
  obtain ⟨i', hi', hyd⟩ := hsums.yield
  have hls : p.loan.loanScale = loan.loanScale := hst.loanScale
  have hb : loan.loanScale = l.vault.baseExponent := (hr.loanAt_scale hat).1
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hraw := (RawLoan.to_lawful_ok hloan).1
  have hrl : r.loan'.toExact.interestDue = p.loan.toExact.interestDue :=
    Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hraw :)
      (congrArg RawLoan.principalOutstanding hraw :) (congrArg RawLoan.managementFeeOutstanding hraw :)
  have hYU : p.pool.yieldUnrealized = l.vault.yieldUnrealized := by
    cases himp : loan.isImpaired
    · rw [Loan.unimpairIfImpaired_not loan l.vault himp] at hu
      simp only [Except.ok.injEq, LoanWithPool.mk.injEq] at hu
      rw [← hu.2]
    · rw [Loan.unimpairIfImpaired_impaired loan l.vault himp] at hu
      split at hu
      · cases hu
      · cases hu
      · rename_i v1 hadj1
        obtain rfl : v1 = p.pool := by injection hu with hu; injection hu with hu; injection hu
        exact Vault.poolAdjust_yield_zero l.vault _ _ rfl hadj1
  have hy := (Vault.poolAdjust_adjustSums _ _ _ hpool).yield
  rw [hYU] at hy

  -- both interests in base units, and their change is exact
  obtain ⟨a, ha, hae, ha1, haB, haI⟩ := Loan.interest_units p.loan i' hi'
  obtain ⟨c, hc, hce, hc1, hcB, hcI⟩ := Loan.interest_units loan _ hsi
  rw [hls, hb] at ha hae
  rw [hb] at hc hce
  have hint : p.loan.broker.numericType = loan.broker.numericType :=
    (congrArg (fun b : LoanBroker => b.numericType) hst.broker :)
  have hnt : p.loan.toExact.numericType = loan.toExact.numericType := hint
  have hB := NumericType.mantissaBound_le loan.toExact.numericType
  have hac : -2 ^ 63 < a - c ∧ a - c < 2 ^ 63 := by
    cases hi : loan.broker.numericType.isIntegral
    · have hfr : loan.toExact.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
      rw [hnt, hfr] at haB
      rw [hfr] at hcB
      simp only [NumericType.mantissaBound] at haB hcB
      constructor <;> push_cast at haB hcB ⊢ <;> omega
    · have h1 := haI (by rw [hint]; exact hi)
      have h2 := hcI hi
      rw [hnt] at haB
      have : (loan.toExact.numericType.mantissaBound : ℤ) ≤ 2 ^ 63 := by exact_mod_cast hB
      constructor <;> omega
  have hg1 := Loan.interestDue_onGrid p.loan i' hi'
  have hg2 := Loan.interestDue_onGrid loan _ hsi
  have hydv := Number.operator_sub_toRat_of_grid i' p.scheduledInterest yd a c l.vault.baseExponent hg1.1 hg2.1 ha hc
    hac hsb hyd
  have hydn := operator_sub_isNormalized_to_nearest_sz _ _ _ hg1.1 hg2.1 hyd
  refine ⟨yd, hydn, hy, a - c, by rw [hydv], hac.1, hac.2, ?_⟩
  rw [hydv, hrl, hae, hce]
  push_cast
  ring

/-- A payment -> YieldUnrealized' = YieldUnrealized − (interestDue − interestDue'). -/
lemma Loan.payment_yield_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (hyu : r.pool'.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    r.pool'.toExact.yieldUnrealized =
      l.vault.toExact.yieldUnrealized - (loan.toExact.interestDue - r.loan'.toExact.interestDue) := by
  obtain ⟨yd, hydn, hy, k, hydv, hk1, hk2, hyde⟩ := Loan.pay_yieldDelta loan amount paymentType r l hr i hat hok
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hsb : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega

  -- YieldUnrealized is whole base units, and the new one stays below `2^62` of them, so the sum is exact
  obtain ⟨hYn, ky, hky⟩ := hr.yieldGridInv.grid
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hky0 : 0 ≤ ky := by
    have h0 : (0 : ℚ) ≤ l.vault.yieldUnrealized.toRat := l.vault.exact.yieldUnrealized_nonneg
    rw [hky] at h0
    exact_mod_cast nonneg_of_mul_nonneg_left h0 hp
  have hlt : ky + k < 2 ^ 62 := by
    by_contra hge
    push Not at hge
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (2 ^ 62) l.vault.baseExponent (by norm_num) hsb
    have hR := operator_add_rounded_to_nearest _ _ _ hYn hydn hy
    have hle := Number.roundsToRepresentable_ge _ _ hR w hw (by
      rw [hwv, hky, hydv, ← add_mul]
      apply mul_le_mul_of_nonneg_right _ hp.le
      have h62 : ((2 ^ 62 : ℤ) : ℚ) ≤ ((ky + k : ℤ) : ℚ) := by exact_mod_cast hge
      push_cast at h62 ⊢
      linarith)
    rw [hwv] at hle
    have : (10 : ℚ) ^ 16 * 10 ^ l.vault.baseExponent ≤ ((2 ^ 62 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent :=
      mul_le_mul_of_nonneg_right (by norm_num) hp.le
    change r.pool'.yieldUnrealized.toRat < _ at hyu
    linarith
  have hv := Number.operator_add_toRat_of_grid _ _ _ ky k l.vault.baseExponent hYn hydn hky (by rw [hydv])
    (by constructor <;> omega) hsb hy
  show r.pool'.yieldUnrealized.toRat =
    l.vault.yieldUnrealized.toRat - (loan.toExact.interestDue - r.loan'.toExact.interestDue)
  rw [hv, hky]
  rw [hydv] at hyde
  push_cast
  linarith

/-- Proof body of the YieldUnrealized line of `regularPayment_yield`. -/
lemma Loan.regularPayment_yieldUnrealized_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (hat : l.LoanAt i loan) (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hok : (loan.regularPayment l.vault amount l.now).run = .ok (.ok r))
    (hyu : l.vault.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    l.vault.toExact.yieldUnrealized - r.pool'.toExact.yieldUnrealized = payment.amounts.interestPaid.toRat := by
  have hok' : (loan.pay l.vault .regular amount l.now).run = .ok (.ok r) := hok
  have hint := Loan.regularPayment_interest loan l.vault amount l.now payment (hr.loanScale_range hat) hpay
  -- the paid loan keeps the outstanding amounts of the instalments
  obtain ⟨p, hp', hs⟩ := Loan.pay_ok loan l.vault .regular amount l.now r hok'
  rw [hpay] at hp'
  obtain rfl := Except.ok.inj (Except.ok.inj hp')
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok payment r hs
  have hraw := (RawLoan.to_lawful_ok hloan).1
  have hrl : r.loan'.toExact.interestDue = payment.loan.toExact.interestDue :=
    Loan.toExact_interestDue_congr (congrArg RawLoan.totalValueOutstanding hraw :)
      (congrArg RawLoan.principalOutstanding hraw :) (congrArg RawLoan.managementFeeOutstanding hraw :)

  -- the payment takes its interest off YieldUnrealized, so YieldUnrealized' is at most YieldUnrealized
  have hyu' : r.pool'.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
    obtain ⟨yd, hydn, hy, -, -, -, -, hyde⟩ := Loan.pay_yieldDelta loan amount .regular r l hr i hat hok'
    obtain ⟨-, hip0, -⟩ := Loan.pay_parts_nonneg loan amount .regular r l.vault l.now payment hpay hok'
    have hyd0 : yd.toRat ≤ 0 := by rw [hyde, hrl]; linarith
    have hR := operator_add_rounded_to_nearest _ _ _ l.vault.wf.yieldUnrealized_norm hydn hy
    have := Number.roundsToRepresentable_le _ _ hR l.vault.yieldUnrealized l.vault.wf.yieldUnrealized_norm
      (by linarith)
    linarith
  have hyield := Loan.payment_yield_proof loan amount .regular r l hr i hat hok' hyu'
  rw [hyield, hrl, hint]
  ring

/-- Proof body of `regularPayment_yield`. -/
lemma Loan.regularPayment_yield_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok payment))
    (hok : (loan.regularPayment l.vault amount l.now).run = .ok (.ok r))
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hyu : l.vault.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    r.pool'.toExact.assetsTotal - l.vault.toExact.assetsTotal = payment.amounts.interestPaid.toRat ∧
      l.vault.toExact.yieldUnrealized - r.pool'.toExact.yieldUnrealized = payment.amounts.interestPaid.toRat := by
  have hok' : (loan.pay l.vault .regular amount l.now).run = .ok (.ok r) := hok
  obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨pp, ip, hpp, hip⟩ := Loan.pay_units loan amount .regular r hr hat payment hpay hok'
  have hsumv : payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat =
      ((pp + ip : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by rw [hpp, hip]; push_cast; ring
  have hsum := LendingLedger.sum_number (l := l) _ _ pp ip hpp hip (by
    have := l.vault.exact.assetsAvailable_nonneg
    change 0 ≤ l.vault.assetsAvailable.toRat at this
    linarith)
  have hroom := LendingLedger.room_of_lt (l := l) _ _ a (pp + ip) ha hsumv htotal
  obtain ⟨hAA, -⟩ := Loan.payment_vault_at_base loan l.vault amount l.now .regular r payment a (hr.loanAt_scale hat).2
    (hr.storesAvailable hr.holdsAsset.maxValue_le) hpay hok' hsum ha hroom
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hfloor : (⌊(payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) /
      10 ^ l.vault.baseExponent⌋ : ℚ) = ((pp + ip : ℕ) : ℚ) := by
    rw [hsumv, mul_div_cancel_right₀ _ hp.ne']
    exact_mod_cast Int.floor_natCast (pp + ip)
  rw [hfloor] at hAA
  have hdep := (Loan.payment_principal_proof loan amount .regular r l hr i hat payment hpay hok').2.1
  refine ⟨?_, Loan.regularPayment_yieldUnrealized_proof loan amount r l hr i hat payment hpay hok hyu⟩
  show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat -
    (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat) = _
  rw [hAA, ← hsumv]
  linarith

/-- Proof body of the amountToPool line of `Lending.payment_vault`. A vault that is not coarsened gains exactly
what the payment sends it. -/
lemma Loan.payment_vault_amountToPool_proof (l : LendingLedger) (hr : l.Reachable) (i : Nat) (hat : l.LoanAt i loan)
    (payment : UnsettledPayment Vault)
    (hpay : (loan.payInstalments l.vault paymentType amount l.now).run = .ok (.ok payment))
    (hok : (loan.pay l.vault paymentType amount l.now).run = .ok (.ok r))
    (htotal : l.vault.assetsAvailable.toRat +
      (payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat) <
        10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    r.pool'.assetsAvailable.toRat - l.vault.assetsAvailable.toRat = r.amountToPool.toRat := by
  obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨pp, ip, hpp, hip⟩ := Loan.pay_units loan amount paymentType r hr hat payment hpay hok
  have hsumv : payment.amounts.principalPaid.toRat + payment.amounts.interestPaid.toRat =
      ((pp + ip : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by rw [hpp, hip]; push_cast; ring
  have hsum := LendingLedger.sum_number (l := l) _ _ pp ip hpp hip (by
    have := l.vault.exact.assetsAvailable_nonneg
    change 0 ≤ l.vault.assetsAvailable.toRat at this
    linarith)
  have hroom := LendingLedger.room_of_lt (l := l) _ _ a (pp + ip) ha hsumv htotal
  obtain ⟨-, -, h⟩ := Loan.payment_vault_at_base loan l.vault amount l.now paymentType r payment a
    (hr.loanAt_scale hat).2 (hr.storesAvailable hr.holdsAsset.maxValue_le) hpay hok hsum ha hroom
  linarith

end XRPL.Model.Lending
