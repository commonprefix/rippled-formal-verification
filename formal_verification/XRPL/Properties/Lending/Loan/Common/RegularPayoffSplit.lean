import XRPL.Properties.Lending.Loan.Common.RegularPayoffRun
import XRPL.Properties.Lending.Loan.Common.PayReachable
import XRPL.Properties.Lending.Ledger.Common.BaseGrid

/-! # What the vault and the broker receive from a regular payoff

Without coarsening a payment credits the vault exactly its principal and interest, and the broker its fee. A regular
payoff pays the vault TotalValueOutstanding − ManagementFeeOutstanding at create, the broker the rest plus the fees. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private Loan.pay_vault_sums Loan.unimpair_pool vault_credit_at_base credit_at_base Loan.pay_cover_sums
  from XRPL.Properties.Lending.Loan.Common.PayBounds

/-- The payment is made at the close time of a reachable ledger, on its vault, on the loan the ledger stores. -/
def Loan.PaysOnLedger (loan : Loan) (v : Vault) (now : UInt32) (_p : UnsettledPayment Vault) : Prop :=
  ∃ (l : LendingLedger) (i : Nat), l.Reachable ∧ l.LoanAt i loan ∧ l.vault = v ∧ l.now = now

/-- A payment on a reachable ledger that does not coarsen the vault: AssetsAvailable plus the principal and the
interest it pays stays below `10^16` base units. -/
def Loan.PaysVaultUncoarsened (loan : Loan) (v : Vault) (now : UInt32) (p : UnsettledPayment Vault) : Prop :=
  loan.PaysOnLedger v now p ∧
    v.assetsAvailable.toRat + (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) <
      10 ^ 16 * 10 ^ v.baseExponent

/-- A payment on a reachable ledger that does not coarsen the broker's cover: below its minimum cover the broker
takes the fee into a CoverAvailable that stays below `10^16` base units. -/
def Loan.PaysCoverUncoarsened (loan : Loan) (v : Vault) (now : UInt32) (p : UnsettledPayment Vault) : Prop :=
  loan.PaysOnLedger v now p ∧ (loan.broker.hasMinimumCover v.baseExponent = .ok false →
    loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 16 * 10 ^ v.baseExponent)

/-- Whole base units below `10^16` of them leave a base unit of room. -/
private lemma room_of_units (b : Int) (x : ℚ) (k : ℕ) (hx : x = (k : ℚ) * 10 ^ b) (hlt : x < 10 ^ 16 * 10 ^ b) :
    x ≤ (10 : ℚ) ^ (16 + b) - 10 ^ b := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hk : k < 10 ^ 16 := by
    have : (k : ℚ) * 10 ^ b < ((10 ^ 16 : ℕ) : ℚ) * 10 ^ b := by rw [← hx]; push_cast; exact hlt
    exact_mod_cast lt_of_mul_lt_mul_right this hp.le
  have hk' : (k : ℚ) + 1 ≤ 10 ^ 16 := by
    have : k + 1 ≤ 10 ^ 16 := by omega
    exact_mod_cast this
  rw [zpow_add₀ (by norm_num), hx]
  have : (10 : ℚ) ^ (16 : ℤ) = 10 ^ 16 := by norm_num
  rw [this]
  nlinarith

/-- A payment on a reachable ledger that does not coarsen the vault credits it exactly the principal and the
interest it pays. -/
lemma Loan.pay_amountToPool_exact (loan : Loan) (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (hat : l.LoanAt i loan) (pt : LoanPaymentType) (amount : Number) (p : UnsettledPayment Vault)
    (r : LoanWithAmounts Vault) (hpay : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p))
    (hok : (loan.pay l.vault pt amount l.now).run = .ok (.ok r))
    (hfit : l.vault.assetsAvailable.toRat + (p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) <
      10 ^ 16 * 10 ^ l.vault.baseExponent) :
    r.amountToPool.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat := by
  have hls := (hr.loanAt_scale hat).1
  have hnt := (hr.loanAt_scale hat).2
  have hAA := hr.storesAvailable hr.holdsAsset.maxValue_le
  obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds l.vault
  have hrange : -81 ≤ loan.loanScale ∧ loan.loanScale ≤ 0 := by omega
  obtain ⟨p', tp, credit, toPool, aa, hp, hu, htp, hcredit, hto, hamt, haa, hA', -, hb⟩ :=
    Loan.pay_vault_sums loan l.vault amount l.now pt r hok
  rw [hpay] at hp
  obtain rfl := Except.ok.inj (Except.ok.inj hp)
  obtain ⟨h1, h2, -⟩ := Loan.pay_parts_nonneg loan amount pt r l.vault l.now p hpay hok
  obtain ⟨g1, g2⟩ := Loan.payInstalments_onGrid loan l.vault pt amount l.now p hrange hpay
  rw [hls] at g1 g2
  have hs : minExponent + 18 ≤ l.vault.baseExponent ∧ l.vault.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
  have htpv := Number.OnGrid.add_exact g1 g2 h1 h2 (by nlinarith) hs htp
  have gtp := Number.OnGrid.add g1 g2 hs htp
  obtain ⟨k, hk⟩ := gtp.nat (by rw [htpv]; linarith)
  obtain ⟨hAv, -, hnt1, hbe, -⟩ := Loan.unimpair_pool loan l.vault p.pool hu hAA
  rw [hb, hnt, ← hnt1, hbe] at hcredit
  have hAv' : p.pool.assetsAvailable.toRat = (a : ℚ) * 10 ^ l.vault.baseExponent := by rw [hAv, ha]
  have hroom : p.pool.assetsAvailable.toRat + tp.toRat ≤ (10 : ℚ) ^ (16 + l.vault.baseExponent) -
      10 ^ l.vault.baseExponent := by
    refine room_of_units _ _ (a + k) (by rw [hAv', hk]; push_cast; ring) ?_
    rw [hAv, htpv]; exact hfit
  obtain ⟨htov, -⟩ := vault_credit_at_base _ _ _ _ _ _ _ _ a (by rw [hnt1]; exact hbint) ⟨hblo, hbhi⟩
    p.pool.wf.assetsAvailable_norm hAv' gtp.1 (by rw [htpv]; linarith) hroom hcredit hto haa hA'
  -- the floor of whole base units is the sum
  rw [hamt, htov, hk, mul_div_assoc, div_self hp10.ne', mul_one, Int.floor_natCast, ← htpv, hk]
  push_cast
  ring

/-- A payment on a reachable ledger that does not coarsen the broker's cover pays the broker exactly the fee.
Above its minimum cover the broker's owner takes the fee, below it the cover takes it whole. -/
lemma Loan.pay_amountToBroker_exact (loan : Loan) (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (hat : l.LoanAt i loan) (pt : LoanPaymentType) (amount : Number) (p : UnsettledPayment Vault)
    (r : LoanWithAmounts Vault) (hpay : (loan.payInstalments l.vault pt amount l.now).run = .ok (.ok p))
    (hok : (loan.pay l.vault pt amount l.now).run = .ok (.ok r))
    (gfee : Number.OnGrid l.vault.baseExponent p.amounts.feePaid)
    (hfit : loan.broker.hasMinimumCover l.vault.baseExponent = .ok false →
      loan.broker.coverAvailable.toRat + p.amounts.feePaid.toRat < 10 ^ 16 * 10 ^ l.vault.baseExponent) :
    r.amountToBroker.toRat = p.amounts.feePaid.toRat := by
  obtain ⟨p', hp', hs⟩ := Loan.pay_ok loan l.vault pt amount l.now r hok
  rw [hpay] at hp'
  obtain rfl := Except.ok.inj (Except.ok.inj hp')
  obtain ⟨-, hu, hst, -, -⟩ := Loan.payInstalments_ok loan l.vault pt amount l.now p hpay
  obtain ⟨_, _, toBroker, _, _, _, _, hsums, -, -, -, -, -, hto⟩ := UnsettledPayment.settle_ok p r hs
  have hbe := Loan.unimpairIfImpaired_baseExponent loan l.vault p.pool _ hu
  have hb : p.loan.broker = loan.broker := hst.broker
  rcases hsums.fee with ⟨-, hfb, -⟩ | ⟨hc, -⟩
  · rw [hto, hfb]
  -- below the minimum cover: the fee floored to whole base units is the fee
  rw [hb, hbe] at hc
  obtain ⟨p'', fc, tb, hp'', hfc, htb, htob, -⟩ := Loan.pay_cover_sums loan l.vault amount l.now pt r hc hok
  rw [hpay] at hp''
  obtain rfl := Except.ok.inj (Except.ok.inj hp'')
  have hfee0 := (Loan.pay_parts_nonneg loan amount pt r l.vault l.now p hpay hok).2.2
  obtain ⟨-, -, hfn⟩ := Loan.payInstalments_norm loan l.vault amount l.now pt p hpay
  have hC := loan.broker.wf.coverAvailable_norm
  have hC0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
  obtain ⟨hblo, hbhi, hbint⟩ := Vault.baseExponent_bounds l.vault
  have hnt := (hr.loanAt_scale hat).2
  have hint : loan.broker.numericType.isIntegral = true → l.vault.baseExponent = 0 := by rw [hnt]; exact hbint
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨c, hcv⟩ : ∃ c : ℕ, loan.broker.coverAvailable.toRat = (c : ℚ) * 10 ^ l.vault.baseExponent := by
    obtain ⟨e, b, -, hb', hw⟩ := hat
    have hlb : loan.broker = b := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
    rw [hlb]
    cases hnti : l.vault.numericType.isIntegral
    · have hfr := NumericType.eq_fractional_of_not_integral (by simpa using hnti)
      exact (hr.coverGridInv.cover hfr _ b hb').nat b.exact.coverAvailable_nonneg
    · exact (hr.integralCover hnti _ b hb').nat b.exact.coverAvailable_nonneg
  obtain ⟨k, hk⟩ := gfee.nat hfee0
  have hroom := room_of_units _ _ (c + k) (by rw [hcv, hk]; push_cast; ring) (hfit hc)
  obtain ⟨-, htn⟩ := sumRoundAndSubtract_downward_le _ _ _ _ fc hC hC0 hfn hfee0 ⟨by omega, by omega⟩ hfc
  obtain ⟨htv, -⟩ := htn tb htb
  have hfcv := credit_at_base _ _ _ _ fc c hint ⟨hblo, hbhi⟩ hC hcv hfn hfee0 hroom hfc
  rw [htob, htv, hfcv, hk, mul_div_assoc, div_self hp10.ne', mul_one, Int.floor_natCast]
  push_cast
  ring

/-- A regular payment on a reachable ledger pays as principal and interest the value it takes off the loan, less
the management fee it takes off. -/
private lemma Loan.regularPayment_vault_part (loan : Loan) (l : LendingLedger) (hr : l.Reachable) (i : Nat)
    (hat : l.LoanAt i loan) (amount : Number) (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault)
    (hpay : (loan.payInstalments l.vault .regular amount l.now).run = .ok (.ok p))
    (hok : (loan.pay l.vault .regular amount l.now).run = .ok (.ok r)) :
    p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat =
      (loan.totalValueOutstanding.toRat - r.loan'.totalValueOutstanding.toRat) -
        (loan.managementFeeOutstanding.toRat - r.loan'.managementFeeOutstanding.toRat) := by
  have hls := (hr.loanAt_scale hat).1
  obtain ⟨hblo, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hpp := (Loan.payment_principal_proof loan amount .regular r l hr i hat p hpay hok).1
  have hip := Loan.regularPayment_interest loan l.vault amount l.now p (by omega) hpay
  obtain ⟨p', hp', hs⟩ := Loan.pay_ok loan l.vault .regular amount l.now r hok
  rw [hpay] at hp'
  obtain rfl := Except.ok.inj (Except.ok.inj hp')
  have hid := Loan.settle_interestDue p r hs
  have e1 : loan.toExact.interestDue = loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := rfl
  have e2 : r.loan'.toExact.interestDue = r.loan'.totalValueOutstanding.toRat -
      r.loan'.principalOutstanding.toRat - r.loan'.managementFeeOutstanding.toRat := rfl
  rw [← hid] at hip
  linarith

/-- What a regular payoff run whose payments don't coarsen the vault credited it so far. -/
private lemma Loan.RegularPayoff.vault_eq {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    {cost toVault toBroker : ℚ}
    (h : Loan.RegularPayoff Loan.PaysVaultUncoarsened start t₀ loan t cost toVault toBroker) :
    toVault = (start.totalValueOutstanding.toRat - loan.totalValueOutstanding.toRat) -
      (start.managementFeeOutstanding.toRat - loan.managementFeeOutstanding.toRat) := by
  induction h with
  | refl => ring
  | refresh l l' _ b _ _ _ _ _ hl ih =>
    have hk := Loan.KeepsAmounts.of_raw (l := l) hl rfl rfl rfl
    rw [hk.totalValueOutstanding, hk.managementFeeOutstanding]; exact ih
  | accept l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.accept_keepsAmounts l v r hok
    rw [hk.totalValueOutstanding, hk.managementFeeOutstanding]; exact ih
  | impair l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.manageImpair_keepsAmounts l v _ r hok
    rw [hk.totalValueOutstanding, hk.managementFeeOutstanding]; exact ih
  | unimpair l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.changeImpairment_keepsAmounts l v false r hok
    rw [hk.totalValueOutstanding, hk.managementFeeOutstanding]; exact ih
  | pay l _ t' v amount p r _ a _ _ _ _ hp hfits hok ih =>
    obtain ⟨⟨lg, i, hr, hat, rfl, rfl⟩, hfit⟩ := hfits
    have hok' : (l.pay lg.vault .regular amount lg.now).run = .ok (.ok r) := hok
    rw [ih, Loan.pay_amountToPool_exact l lg hr i hat .regular amount p r hp hok' hfit,
      Loan.regularPayment_vault_part l lg hr i hat amount p r hp hok']
    ring

/-- The loan part of the vault line of `Lending.Reachable.regularPayoff`. -/
lemma Loan.Reachable.regularPayoff_vault_proof (start loan : Loan) (t₀ t : UInt32) (cost toVault toBroker : ℚ)
    (hrun : Loan.RegularPayoff Loan.PaysVaultUncoarsened start t₀ loan t cost toVault toBroker)
    (hpaid : loan.paymentRemaining = 0) :
    toVault = start.totalValueOutstanding.toRat - start.managementFeeOutstanding.toRat := by
  rw [Loan.RegularPayoff.vault_eq hrun, (loan.valid.paid_zeroed hpaid).1, (loan.valid.paid_zeroed hpaid).2.2,
    Number.toRat_zero]
  ring

/-- What a regular payoff run whose payments don't coarsen the broker's cover paid the broker so far. The
management fee it took off the loan, plus one LoanServiceFee per payment it took. -/
private lemma Loan.RegularPayoff.broker_eq {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32}
    {cost toVault toBroker : ℚ} (hs : start.Reachable t₀)
    (hfit : start.totalValueOutstanding.toRat + start.fees.serviceFee.toRat * start.paymentRemaining.toNat <
      2 ^ 61 * 10 ^ start.loanScale)
    (h : Loan.RegularPayoff Loan.PaysCoverUncoarsened start t₀ loan t cost toVault toBroker) :
    toBroker = (start.managementFeeOutstanding.toRat - loan.managementFeeOutstanding.toRat) +
      start.fees.serviceFee.toRat * (start.paymentRemaining.toNat - loan.paymentRemaining.toNat : ℕ) ∧
      loan.paymentRemaining.toNat ≤ start.paymentRemaining.toNat := by
  induction h with
  | refl => simp
  | refresh l l' _ b _ _ _ _ _ hl ih =>
    have hk := Loan.KeepsAmounts.of_raw (l := l) hl rfl rfl rfl
    rw [hk.managementFeeOutstanding, hk.paymentRemaining]; exact ih
  | accept l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.accept_keepsAmounts l v r hok
    rw [hk.managementFeeOutstanding, hk.paymentRemaining]; exact ih
  | impair l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.manageImpair_keepsAmounts l v _ r hok
    rw [hk.managementFeeOutstanding, hk.paymentRemaining]; exact ih
  | unimpair l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.changeImpairment_keepsAmounts l v false r hok
    rw [hk.managementFeeOutstanding, hk.paymentRemaining]; exact ih
  | pay l t' t'' v amount p r _ _ b hrun _ _ hp hfits hok ih =>
    obtain ⟨ihb, ihle⟩ := ih
    obtain ⟨⟨lg, i, hr, hat, rfl, rfl⟩, hfit'⟩ := hfits
    have hok' : (l.pay lg.vault .regular amount lg.now).run = .ok (.ok r) := hok
    have hrf := hrun.reachableFrom
    have hreach : l.Reachable t' := by
      obtain ⟨s0, t0, hc0, hr0⟩ := hs
      exact ⟨s0, t0, hc0, hr0.trans hrf⟩
    have hft := Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hrf
    have hmono := Loan.ReachableFrom.outstanding_monotone_proof hrf
    have hfee0 : 0 ≤ start.fees.serviceFee.toRat := start.exact.serviceFee_nonneg
    have hB : l.totalValueOutstanding.toRat + l.fees.serviceFee.toRat * l.paymentRemaining.toNat <
        2 ^ 61 * 10 ^ l.loanScale := by
      rw [hft.2.1, hft.2.2.2.2.2.2.1]
      have : start.fees.serviceFee.toRat * l.paymentRemaining.toNat ≤
          start.fees.serviceFee.toRat * start.paymentRemaining.toNat :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast ihle) hfee0
      linarith [hmono.totalValueOutstanding]
    obtain ⟨-, -, hfp, hle', gfp⟩ := Loan.regularPayment_sums l t' lg.vault amount lg.now p r hreach hB hp hok
    rw [(hr.loanAt_scale hat).1] at gfp
    rw [hft.2.1] at hfp
    refine ⟨?_, le_trans hle' ihle⟩
    rw [ihb, Loan.pay_amountToBroker_exact l lg hr i hat .regular amount p r hp hok' gfp hfit', hfp]
    have e : start.paymentRemaining.toNat - r.loan'.paymentRemaining.toNat =
        (start.paymentRemaining.toNat - l.paymentRemaining.toNat) +
          (l.paymentRemaining.toNat - r.loan'.paymentRemaining.toNat) := by omega
    rw [e]
    push_cast
    ring

/-- The loan part of the broker line of `Lending.Reachable.regularPayoff`. -/
lemma Loan.Reachable.regularPayoff_broker_proof (start loan : Loan) (t₀ t : UInt32) (cost toVault toBroker : ℚ)
    (hs : start.Reachable t₀)
    (hrun : Loan.RegularPayoff Loan.PaysCoverUncoarsened start t₀ loan t cost toVault toBroker)
    (hpaid : loan.paymentRemaining = 0)
    (hfit : start.totalValueOutstanding.toRat + start.fees.serviceFee.toRat * start.paymentRemaining.toNat <
      10 ^ 16 * 10 ^ start.loanScale) :
    toBroker = start.managementFeeOutstanding.toRat +
      start.fees.serviceFee.toRat * start.paymentRemaining.toNat := by
  have h16 : (10 : ℚ) ^ 16 * 10 ^ start.loanScale ≤ 2 ^ 61 * 10 ^ start.loanScale :=
    mul_le_mul_of_nonneg_right (by norm_num) (zpow_pos (by norm_num) _).le
  obtain ⟨hb, -⟩ := Loan.RegularPayoff.broker_eq hs (by linarith) hrun
  rw [hb, (loan.valid.paid_zeroed hpaid).2.2, hpaid]
  simp [Number.toRat_zero]

end XRPL.Model.Lending
