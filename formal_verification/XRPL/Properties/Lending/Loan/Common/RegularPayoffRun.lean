import XRPL.Properties.Lending.Loan.Common.PaymentCount
import XRPL.Properties.Lending.Loan.Common.RegularPayoff
import XRPL.Properties.Lending.Loan.Common.PaySums

/-! # A loan paid off by regular payments

From a reachable loan, a run of regular payments that pays the loan off charges its TotalValueOutstanding plus one
LoanServiceFee per payment left, as each instalment takes exactly one payment. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.scheduledComponents Loan.doPayment UnsettledPayment.payInstalments Loan.settlePayment
  from XRPL.Model.Lending.Loan.LoanPay
open private Loan.doPayment_interestDue from XRPL.Properties.Lending.Loan.Common.InterestDue
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- With one payment left the next scheduled instalment is the last. -/
private lemma Loan.scheduledComponents_last {l : Loan} {pc : PaymentComponents} (h1 : l.paymentRemaining = 1)
    (hpc : Loan.scheduledComponents l = .ok pc) : pc.isFinal = true := by
  unfold Loan.scheduledComponents at hpc
  obtain ⟨_, -, hpc⟩ := bind_ok_peel _ _ _ hpc
  obtain ⟨_, -, hpc⟩ := bind_ok_peel _ _ _ hpc
  dsimp only at hpc
  rw [if_pos (by simp [h1])] at hpc
  obtain rfl := (Except.ok.inj hpc).symm
  rfl

/-- A scheduled instalment takes exactly one payment from a loan that needs every payment it has left. -/
private lemma Loan.doPayment_count (l l' : Loan) (pc : PaymentComponents) (fee : Number)
    (hpr0 : l.paymentRemaining ≠ 0)
    (hn : l.NeedsAllPayments) (hsc : Loan.scheduledComponents l = .ok pc)
    (hdo : Loan.doPayment l { pc with untrackedManagementFee := fee } = .ok l') :
    1 + l'.paymentRemaining.toNat = l.paymentRemaining.toNat := by
  have hpos : 1 ≤ l.paymentRemaining.toNat := by
    have := UInt32.toNat_inj.not.mpr hpr0
    simp at this; omega
  by_cases h1 : l.paymentRemaining = 1
  · have hf := Loan.scheduledComponents_last h1 hsc
    rw [Loan.doPayment_final _ _ _ hf hdo, h1]
    rfl
  · have h2 : 2 ≤ l.paymentRemaining.toNat := by
      have := UInt32.toNat_inj.not.mpr h1
      simp at this; omega
    have hf := hn.not_final h2 _ hsc
    rw [(Loan.doPayment_notFinal _ _ _ hf hdo).1,
      UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using hpos)]
    simp only [UInt32.toNat_one]
    omega

/-- The instalment loop takes exactly one payment per instalment from a loan that needs every payment it has
left. -/
private lemma UnsettledPayment.payInstalments_counts {α : Type} (amount : Number) :
    ∀ (n : Nat) (payment p' : UnsettledPayment α), UnsettledPayment.payInstalments payment n amount = .ok p' →
      -81 ≤ payment.loan.loanScale →
      (payment.loan.broker.numericType.isIntegral = true → payment.loan.loanScale ≤ 0) →
      0 ≤ payment.loan.toExact.interestDue → payment.loan.NeedsAllPayments →
      p'.count + p'.loan.paymentRemaining.toNat = payment.count + payment.loan.paymentRemaining.toNat := by
  intro n
  induction n with
  | zero =>
    intro payment p' h _ _ _ _
    rw [UnsettledPayment.payInstalments] at h
    obtain rfl := Except.ok.inj h
    rfl
  | succ n ih =>
    intro payment p' h hlo hint hi hn
    rw [UnsettledPayment.payInstalments] at h
    unfold_ter at h
    walk_ok
    · rfl
    · rfl
    all_goals
      have hpr0 : payment.loan.paymentRemaining ≠ 0 := by
        simpa using ‹¬(payment.loan.paymentRemaining == 0) = true›
      have hdo := ‹Loan.doPayment _ _ = _›
      have hsc := ‹Loan.scheduledComponents payment.loan = _›
      have hstep := Loan.doPayment_count _ _ _ _ hpr0 hn hsc hdo
    · dsimp only; omega
    · have h3 := ‹UnsettledPayment.payInstalments _ n amount = _›
      have hneeds := Loan.doPayment_needs _ _ _ _ hlo hint hi hn hpr0 hsc hdo rfl rfl rfl rfl
      have hst := Loan.doPayment_sameTerms _ _ _ hdo
      rw [ih _ p' h3 (by dsimp only; rw [hst.loanScale]; exact hlo)
        (by dsimp only; rw [hst.loanScale, hst.broker]; exact hint) hneeds.2 hneeds.1]
      dsimp only
      omega

/-- The settlement keeps the paid loan's amounts and count. -/
private lemma UnsettledPayment.settle_keeps (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault)
    (hs : (Loan.settlePayment p.loan p.pool p.amounts p.scheduledInterest).run = .ok (.ok r)) :
    r.loan'.totalValueOutstanding = p.loan.totalValueOutstanding ∧
      r.loan'.principalOutstanding = p.loan.principalOutstanding ∧
      r.loan'.managementFeeOutstanding = p.loan.managementFeeOutstanding ∧
      r.loan'.paymentRemaining = p.loan.paymentRemaining := by
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, hloan, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have h1 := (RawLoan.to_lawful_ok hloan).1
  exact ⟨(congrArg RawLoan.totalValueOutstanding h1 :), (congrArg RawLoan.principalOutstanding h1 :),
    (congrArg RawLoan.managementFeeOutstanding h1 :), (congrArg RawLoan.paymentRemaining h1 :)⟩

/-- The scale, asset and interest facts every reachable loan has. -/
private lemma Loan.Reachable.scale_facts {loan : Loan} {t : UInt32} (hr : loan.Reachable t) :
    -81 ≤ loan.loanScale ∧ (loan.broker.numericType.isIntegral = true → loan.loanScale ≤ 0) ∧
      0 ≤ loan.toExact.interestDue := by
  obtain ⟨start, t₀, hc, hr'⟩ := hr
  have hft := Loan.ReachableFrom.fixed_terms_proof _ _ _ _ hr'
  have hls := hft.2.2.2.2.2.2.1
  have hnt := Loan.ReachableFrom.numericType hr'
  have hlo := Loan.Created.loanScale_ge hc
  refine ⟨by rw [hls]; omega,
    fun h => by rw [hls]; exact Loan.Created.loanScale_integral hc (by rw [← hnt]; exact h),
    Loan.Reachable.interestDue_nonneg ⟨start, t₀, hc, hr'⟩⟩

/-- What a regular payment on a reachable loan charges and pays, read exactly. The value it takes off plus one
LoanServiceFee per payment taken, split as principal and interest for the vault and fees for the broker. -/
lemma Loan.regularPayment_sums (loan : Loan) (t : UInt32) (v : Vault) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (r : LoanWithAmounts Vault) (hreach : loan.Reachable t)
    (hB : loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat <
      2 ^ 61 * 10 ^ loan.loanScale)
    (hp : (loan.payInstalments v .regular amount now).run = .ok (.ok p))
    (hok : (loan.regularPayment v amount now).run = .ok (.ok r)) :
    p.totalPaid.toRat = (loan.totalValueOutstanding.toRat - r.loan'.totalValueOutstanding.toRat) +
        loan.fees.serviceFee.toRat * (loan.paymentRemaining.toNat - r.loan'.paymentRemaining.toNat : ℕ) ∧
      p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat =
        (loan.totalValueOutstanding.toRat - r.loan'.totalValueOutstanding.toRat) -
          (loan.managementFeeOutstanding.toRat - r.loan'.managementFeeOutstanding.toRat) ∧
      p.amounts.feePaid.toRat = (loan.managementFeeOutstanding.toRat - r.loan'.managementFeeOutstanding.toRat) +
        loan.fees.serviceFee.toRat * (loan.paymentRemaining.toNat - r.loan'.paymentRemaining.toNat : ℕ) ∧
      r.loan'.paymentRemaining.toNat ≤ loan.paymentRemaining.toNat ∧
      Number.OnGrid loan.loanScale p.amounts.feePaid := by
  obtain ⟨hlo, hint, hi⟩ := Loan.Reachable.scale_facts hreach
  have hn := Loan.Reachable.needsAllPayments hreach
  obtain ⟨gfee, -, -⟩ := Loan.Reachable.fees_onGrid hreach
  have hfee0 : 0 ≤ loan.fees.serviceFee.toRat := loan.exact.serviceFee_nonneg
  have hP0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hM0 : 0 ≤ loan.managementFeeOutstanding.toRat := loan.exact.managementFeeOutstanding_nonneg
  have hiD : 0 ≤ loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
      loan.managementFeeOutstanding.toRat := hi
  obtain ⟨p', hp', hs⟩ := Loan.pay_ok loan v .regular amount now r hok
  rw [hp] at hp'
  obtain rfl := Except.ok.inj (Except.ok.inj hp')
  obtain ⟨hT', hP', hM', hR'⟩ := UnsettledPayment.settle_keeps p r hs
  obtain ⟨si, -, hloop, -⟩ := Loan.payScheduled_loop loan v amount now p hp
  have u1 : loan.unimpaired.totalValueOutstanding = loan.totalValueOutstanding := rfl
  have u2 : loan.unimpaired.principalOutstanding = loan.principalOutstanding := rfl
  have u3 : loan.unimpaired.managementFeeOutstanding = loan.managementFeeOutstanding := rfl
  have u4 : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
  have hstart : (⟨loan.unimpaired, p.pool, PaymentAmounts.zero, Number.zero, 0, si⟩ :
      UnsettledPayment Vault).Moves loan.loanScale loan.broker.numericType
      loan.fees.serviceFee loan.totalValueOutstanding.toRat loan.principalOutstanding.toRat
      loan.managementFeeOutstanding.toRat
      (loan.totalValueOutstanding.toRat + loan.fees.serviceFee.toRat * loan.paymentRemaining.toNat) :=
    ⟨rfl, rfl, rfl, hi, by simp [Number.toRat_zero, u1], by simp [PaymentAmounts.zero, Number.toRat_zero, u2],
      by simp [PaymentAmounts.zero, Number.toRat_zero, u1, u2, u3],
      by simp [PaymentAmounts.zero, Number.toRat_zero, u3], le_refl _, le_refl _, le_refl _,
      by simp [u4], Number.OnGrid.zero _, Number.OnGrid.zero _, Number.OnGrid.zero _, Number.OnGrid.zero _⟩
  have hm := UnsettledPayment.payInstalments_moves amount loan.loanScale loan.broker.numericType loan.fees.serviceFee
    _ _ _ _ hlo hint gfee hfee0 hB (by linarith) (by linarith) _ _ p hloop hstart
  have hcount := UnsettledPayment.payInstalments_counts amount _ _ p hloop hlo hint hi
    (hn.of_same rfl rfl rfl rfl rfl)
  simp only [Nat.zero_add] at hcount
  have hpr : p.loan.paymentRemaining.toNat ≤ loan.paymentRemaining.toNat := by
    have : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
    rw [this] at hcount; omega
  have hcq : ((loan.paymentRemaining.toNat - p.loan.paymentRemaining.toNat : ℕ) : ℚ) = p.count := by
    have : loan.unimpaired.paymentRemaining = loan.paymentRemaining := rfl
    rw [this] at hcount
    exact_mod_cast (by omega : loan.paymentRemaining.toNat - p.loan.paymentRemaining.toNat = p.count)
  rw [hT', hM', hR', hcq]
  refine ⟨hm.charged, ?_, hm.feePart, hpr, hm.fee_grid⟩
  rw [hm.principal, hm.interest]
  ring

/-- A run from `start` in which only regular payments pay the loan, each one satisfying `fits` on its vault and at
its close time. `cost`, `toVault` and `toBroker` sum what they charge, credit the vault and pay the broker. -/
inductive Loan.RegularPayoff (fits : Loan → Vault → UInt32 → UnsettledPayment Vault → Prop) (start : Loan)
    (t₀ : UInt32) :
    Loan → UInt32 → ℚ → ℚ → ℚ → Prop where
  | refl : Loan.RegularPayoff fits start t₀ start t₀ 0 0 0
  | refresh (loan loan' : Loan) (t : UInt32) (broker : LoanBroker) (cost toVault toBroker : ℚ) :
      Loan.RegularPayoff fits start t₀ loan t cost toVault toBroker →
      broker.numericType = loan.broker.numericType → -- a loan's broker never changes its asset
      RawLoan.to_lawful { loan.toRawLoan with broker := broker } = .ok loan' →
      Loan.RegularPayoff fits start t₀ loan' t cost toVault toBroker
  | accept (loan : Loan) (t t' : UInt32) (v : Vault) (r : LoanWithPool Vault) (cost toVault toBroker : ℚ) :
      Loan.RegularPayoff fits start t₀ loan t cost toVault toBroker → t ≤ t' →
      loan.canAccept v t' = .ok .tesSUCCESS → (loan.accept v).run = .ok (.ok r) →
      Loan.RegularPayoff fits start t₀ r.loan' t' cost toVault toBroker
  | impair (loan : Loan) (t t' : UInt32) (v : Vault) (r : LoanWithPool Vault) (cost toVault toBroker : ℚ) :
      Loan.RegularPayoff fits start t₀ loan t cost toVault toBroker → t ≤ t' →
      loan.canManage .impair t' = .tesSUCCESS → (loan.manageImpair v t').run = .ok (.ok r) →
      Loan.RegularPayoff fits start t₀ r.loan' t' cost toVault toBroker
  | unimpair (loan : Loan) (t t' : UInt32) (v : Vault) (r : LoanWithPool Vault) (cost toVault toBroker : ℚ) :
      Loan.RegularPayoff fits start t₀ loan t cost toVault toBroker → t ≤ t' →
      loan.canManage .unimpair t' = .tesSUCCESS → (loan.manageUnimpair v).run = .ok (.ok r) →
      Loan.RegularPayoff fits start t₀ r.loan' t' cost toVault toBroker
  | pay (loan : Loan) (t t' : UInt32) (v : Vault) (amount : Number) (p : UnsettledPayment Vault)
      (r : LoanWithAmounts Vault) (cost toVault toBroker : ℚ) :
      Loan.RegularPayoff fits start t₀ loan t cost toVault toBroker → t ≤ t' →
      loan.canPay .regular = .tesSUCCESS → (loan.payInstalments v .regular amount t').run = .ok (.ok p) →
      fits loan v t' p → (loan.regularPayment v amount t').run = .ok (.ok r) →
      Loan.RegularPayoff fits start t₀ r.loan' t' (cost + p.totalPaid.toRat) (toVault + r.amountToPool.toRat)
        (toBroker + r.amountToBroker.toRat)

/-- A regular payoff run is a run of a reachable loan. -/
lemma Loan.RegularPayoff.reachableFrom {fits : Loan → Vault → UInt32 → UnsettledPayment Vault → Prop}
    {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32} {cost toVault toBroker : ℚ}
    (h : Loan.RegularPayoff fits start t₀ loan t cost toVault toBroker) : Loan.ReachableFrom start t₀ loan t := by
  induction h with
  | refl => exact .refl
  | refresh _ _ _ b _ _ _ _ hnt hl ih => exact .refresh _ _ _ b ih hnt hl
  | accept _ _ _ v r _ _ _ _ hle hc hok ih => exact .accept _ _ _ v r ih hle hc hok
  | impair _ _ _ v r _ _ _ _ hle hc hok ih => exact .impair _ _ _ v r ih hle hc hok
  | unimpair _ _ _ v r _ _ _ _ hle hc hok ih => exact .unimpair _ _ _ v r ih hle hc hok
  | pay _ _ _ v amount _ r _ _ _ _ hle hc _ _ hok ih => exact .regularPayment _ _ _ v amount r ih hle hc hok

/-- The steps of a run that move no funds keep TotalValueOutstanding, ManagementFeeOutstanding and the count. -/
structure Loan.KeepsAmounts (l l' : Loan) : Prop where
  totalValueOutstanding : l'.totalValueOutstanding = l.totalValueOutstanding
  managementFeeOutstanding : l'.managementFeeOutstanding = l.managementFeeOutstanding
  paymentRemaining : l'.paymentRemaining = l.paymentRemaining

/-- A loan rebuilt from the same amounts and count keeps them. -/
lemma Loan.KeepsAmounts.of_raw {l l' : Loan} {raw : RawLoan} (hl : raw.to_lawful = .ok l')
    (h1 : raw.totalValueOutstanding = l.totalValueOutstanding)
    (h2 : raw.managementFeeOutstanding = l.managementFeeOutstanding)
    (h3 : raw.paymentRemaining = l.paymentRemaining) : Loan.KeepsAmounts l l' := by
  have hr := (RawLoan.to_lawful_ok hl).1
  exact ⟨by rw [← h1, ← hr], by rw [← h2, ← hr], by rw [← h3, ← hr]⟩

/-- An accept keeps the amounts. -/
lemma Loan.accept_keepsAmounts (l : Loan) (v : Vault) (r : LoanWithPool Vault)
    (h : (l.accept v).run = .ok (.ok r)) : Loan.KeepsAmounts l r.loan' := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok
  have hl := ‹RawLoan.to_lawful _ = Except.ok _›
  exact Loan.KeepsAmounts.of_raw hl rfl rfl rfl

/-- Changing the impairment keeps the amounts. -/
lemma Loan.changeImpairment_keepsAmounts (l : Loan) (v : Vault) (b : Bool) (r : LoanWithPool Vault)
    (h : (Loan.changeImpairment l v b).run = .ok (.ok r)) : Loan.KeepsAmounts l r.loan' := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals
    have hl := ‹RawLoan.to_lawful _ = Except.ok _›
    exact Loan.KeepsAmounts.of_raw hl rfl rfl rfl

/-- An impair keeps the amounts. -/
lemma Loan.manageImpair_keepsAmounts (l : Loan) (v : Vault) (now : UInt32) (r : LoanWithPool Vault)
    (h : (l.manageImpair v now).run = .ok (.ok r)) : Loan.KeepsAmounts l r.loan' := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok
  exact Loan.changeImpairment_keepsAmounts l v true r ‹_›

/-- What a regular payoff run charged so far. The value it took off the loan, plus one LoanServiceFee per
payment it took. -/
private lemma Loan.RegularPayoff.cost_eq {fits : Loan → Vault → UInt32 → UnsettledPayment Vault → Prop}
    {start : Loan} {t₀ : UInt32} {loan : Loan} {t : UInt32} {cost toVault toBroker : ℚ} (hs : start.Reachable t₀)
    (hfit : start.totalValueOutstanding.toRat + start.fees.serviceFee.toRat * start.paymentRemaining.toNat <
      2 ^ 61 * 10 ^ start.loanScale)
    (h : Loan.RegularPayoff fits start t₀ loan t cost toVault toBroker) :
    cost = (start.totalValueOutstanding.toRat - loan.totalValueOutstanding.toRat) +
      start.fees.serviceFee.toRat * (start.paymentRemaining.toNat - loan.paymentRemaining.toNat : ℕ) ∧
      loan.paymentRemaining.toNat ≤ start.paymentRemaining.toNat := by
  induction h with
  | refl => simp
  | refresh l l' _ b _ _ _ _ _ hl ih =>
    have hk := Loan.KeepsAmounts.of_raw (l := l) hl rfl rfl rfl
    rw [hk.totalValueOutstanding, hk.paymentRemaining]; exact ih
  | accept l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.accept_keepsAmounts l v r hok
    rw [hk.totalValueOutstanding, hk.paymentRemaining]; exact ih
  | impair l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.manageImpair_keepsAmounts l v _ r hok
    rw [hk.totalValueOutstanding, hk.paymentRemaining]; exact ih
  | unimpair l _ _ v r _ _ _ _ _ _ hok ih =>
    have hk := Loan.changeImpairment_keepsAmounts l v false r hok
    rw [hk.totalValueOutstanding, hk.paymentRemaining]; exact ih
  | pay l t' t'' v amount p r c a b hrun _ _ hp _ hok ih =>
    obtain ⟨ihc, ihle⟩ := ih
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
    obtain ⟨hcost, -, -, hle', -⟩ := Loan.regularPayment_sums l t' v amount t'' p r hreach hB hp hok
    rw [hft.2.1] at hcost
    refine ⟨?_, le_trans hle' ihle⟩
    rw [ihc, hcost]
    have e : start.paymentRemaining.toNat - r.loan'.paymentRemaining.toNat =
        (start.paymentRemaining.toNat - l.paymentRemaining.toNat) +
          (l.paymentRemaining.toNat - r.loan'.paymentRemaining.toNat) := by omega
    rw [e]
    push_cast
    ring

/-- The loan part of the cost line of `Lending.Reachable.regularPayoff`. -/
lemma Loan.Reachable.regularPayoff_cost_proof (start loan : Loan) (t₀ t : UInt32) (cost toVault toBroker : ℚ)
    (hs : start.Reachable t₀)
    (hrun : Loan.RegularPayoff (fun _ _ _ _ => True) start t₀ loan t cost toVault toBroker)
    (hpaid : loan.paymentRemaining = 0)
    (hfit : start.totalValueOutstanding.toRat + start.fees.serviceFee.toRat * start.paymentRemaining.toNat <
      10 ^ 16 * 10 ^ start.loanScale) :
    cost = start.totalValueOutstanding.toRat + start.fees.serviceFee.toRat * start.paymentRemaining.toNat := by
  have h16 : (10 : ℚ) ^ 16 * 10 ^ start.loanScale ≤ 2 ^ 61 * 10 ^ start.loanScale :=
    mul_le_mul_of_nonneg_right (by norm_num) (zpow_pos (by norm_num) _).le
  obtain ⟨hcost, -⟩ := Loan.RegularPayoff.cost_eq hs (by linarith) hrun
  rw [hcost, (loan.valid.paid_zeroed hpaid).1, hpaid]
  simp [Number.toRat_zero]

end XRPL.Model.Lending
