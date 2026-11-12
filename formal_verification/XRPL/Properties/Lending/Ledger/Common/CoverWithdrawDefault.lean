import XRPL.Properties.Lending.Ledger.Common.Scope
import XRPL.Properties.Lending.Ledger.Common.VaultSteps
import XRPL.Properties.Lending.Loan.Common.ManageLedger
import XRPL.Properties.Lending.Loan.Common.TheoreticalPrincipal
import XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs
import XRPL.Properties.Lending.LoanBroker.Common.WithdrawAccuracy
import XRPL.Properties.Protocol.Common.TenthBipsTotality

/-! # A cover withdrawal before a default

A LoanBrokerCoverWithdraw leaves the broker at or above its minimum cover. A default takes at most the
liquidation amount from the cover, and the liquidation amount is never above the minimum cover. So the
default pays the vault the same amount with or without the withdrawal. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private LoanBroker.hasMinimumCover_iff from XRPL.Properties.Lending.LoanBroker.Common.MinimumCoverProofs

/-- `Number.min` returns its first argument when that one is not above the second. -/
private lemma Number.min_eq_left_of_le (x y : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (h : x.toRat ≤ y.toRat) : Number.min x y = x := by
  unfold Number.min
  rw [if_neg]
  intro hlt
  exact absurd ((operator_lt_iff _ _ hy hx).mp hlt) (not_lt.mpr h)

/-- A broker that holds its minimum cover holds at least the liquidation amount of a default. DebtTotal is `t`
base units, at most `10^16` of them, as on every reachable ledger. -/
private lemma LoanBroker.liquidationAmount_le_cover (b : LoanBroker) (e : Int) (t : ℕ)
    (he : -10 ≤ e ∧ e ≤ 0) (ht : t ≤ 10 ^ 16) (hdebt : b.debtTotal.toRat = (t : ℚ) * 10 ^ e)
    (hmin : b.HasMinimumCover e) (minimumCover liquidationAmount : Number)
    (hmc : tenthBipsOfValue b.debtTotal b.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover b.coverRateLiquidation .upward = .ok liquidationAmount) :
    liquidationAmount.toRat ≤ b.coverAvailable.toRat := by
  have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ e ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) he.2
  have ht16 : (t : ℚ) ≤ 10 ^ 16 := by exact_mod_cast ht
  have hrmin : b.coverRateMinimum.toNat ≤ 100000 := by
    have := b.valid.coverRateMinimum_cap; unfold maxCoverRate at this; exact UInt32.le_iff_toNat_le.mp this
  have hrliq : b.coverRateLiquidation.toNat ≤ 100000 := by
    have := b.valid.coverRateLiquidation_cap; unfold maxCoverRate at this; exact UInt32.le_iff_toNat_le.mp this

  -- the minimum cover before rounding is at most DebtTotal, and at least `10^-15` when nonzero
  obtain ⟨mc, hmc', hmcn, hmc0, hmcle, hmclo⟩ := tenthBipsOfValue_upward_ok b.debtTotal b.coverRateMinimum (-10)
    b.wf.debtTotal_norm b.exact.debtTotal_nonneg (by rw [hdebt]; nlinarith) (by norm_num)
    (fun h0 => by
      rw [hdebt]
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · exfalso; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ h0 (by rw [hdebt, h]; simp)
        · exact h
      calc (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ e := zpow_le_zpow_right₀ (by norm_num) he.1
        _ ≤ (t : ℚ) * 10 ^ e := le_mul_of_one_le_left hp.le (by exact_mod_cast ht1))
    hrmin
  rw [hmc, Except.ok.injEq] at hmc'
  subst hmc'
  have hmclt : minimumCover.toRat < 10 ^ 20 := by
    rw [hdebt] at hmcle
    nlinarith

  -- the liquidation amount is at most the minimum cover before rounding
  obtain ⟨liq, hliq', -, -, hliqle, -⟩ := tenthBipsOfValue_upward_ok minimumCover b.coverRateLiquidation (-15)
    hmcn hmc0 hmclt (by norm_num) (fun h0 => by simpa using hmclo h0) hrliq
  rw [hliq, Except.ok.injEq] at hliq'
  subst hliq'

  -- the stored check compares CoverAvailable with the minimum cover rounded up to base units
  have hmin' := hmin
  unfold LoanBroker.HasMinimumCover RawLoanBroker.hasMinimumCover at hmin'
  obtain ⟨m, hm, -⟩ := bind_ok_peel _ _ _ hmin'
  have hcover : m.toRat ≤ b.coverAvailable.toRat := (LoanBroker.hasMinimumCover_iff b e m hm).mp hmin
  have hround : minimumCover.toRat ≤ m.toRat := by
    by_cases h0 : minimumCover.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero _ h0]
      exact LoanBroker.minimumCover_nonneg b e m (by omega) hm
    · have hlarge : (10 : ℚ) ^ (-81 : ℤ) ≤ minimumCover.toRat :=
        le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-81 : ℤ) ≤ -10 - 5)) (hmclo h0)
      unfold minimumBrokerCover at hm
      rw [hmc, ok_bind] at hm
      exact STAmount.roundToNumericType_upward_ge_of_large _ _ m e hmcn hlarge (by omega) hm
  linarith

/-- Two copies of a loan whose brokers differ only in CoverAvailable get the same cover from a default, when each
broker holds at least the liquidation amount. -/
private lemma Loan.defaultCover_eq_of_cover (loan₁ loan₂ : Loan) (v : Vault)
    (hloan : loan₂.toRawLoan = { loan₁.toRawLoan with broker := loan₂.broker })
    (hbroker : loan₂.broker.toRawLoanBroker =
      { loan₁.broker.toRawLoanBroker with coverAvailable := loan₂.broker.coverAvailable })
    (hc₁ : ∀ minimumCover liquidationAmount : Number,
      tenthBipsOfValue loan₁.broker.debtTotal loan₁.broker.coverRateMinimum .upward = .ok minimumCover →
      tenthBipsOfValue minimumCover loan₁.broker.coverRateLiquidation .upward = .ok liquidationAmount →
      liquidationAmount.toRat ≤ loan₁.broker.coverAvailable.toRat)
    (hc₂ : ∀ minimumCover liquidationAmount : Number,
      tenthBipsOfValue loan₁.broker.debtTotal loan₁.broker.coverRateMinimum .upward = .ok minimumCover →
      tenthBipsOfValue minimumCover loan₁.broker.coverRateLiquidation .upward = .ok liquidationAmount →
      liquidationAmount.toRat ≤ loan₂.broker.coverAvailable.toRat) :
    loan₁.defaultCover v = loan₂.defaultCover v := by
  have hdebt : loan₂.broker.debtTotal = loan₁.broker.debtTotal := (congrArg RawLoanBroker.debtTotal hbroker :)
  have hcrm : loan₂.broker.coverRateMinimum = loan₁.broker.coverRateMinimum :=
    (congrArg RawLoanBroker.coverRateMinimum hbroker :)
  have hcrl : loan₂.broker.coverRateLiquidation = loan₁.broker.coverRateLiquidation :=
    (congrArg RawLoanBroker.coverRateLiquidation hbroker :)
  have hnt : loan₂.broker.numericType = loan₁.broker.numericType := (congrArg RawLoanBroker.numericType hbroker :)
  have hpo : loan₂.principalOutstanding = loan₁.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hloan :)
  unfold Loan.defaultCover
  dsimp only
  rw [hdebt, hcrm, hcrl, hnt, hpo]
  cases hmc : tenthBipsOfValue loan₁.broker.debtTotal loan₁.broker.coverRateMinimum .upward with
  | error err => rfl
  | ok minimumCover =>
    rw [ok_bind, ok_bind]
    cases hliq : tenthBipsOfValue minimumCover loan₁.broker.coverRateLiquidation .upward with
    | error err => rfl
    | ok liquidationAmount =>
      rw [ok_bind, ok_bind]
      -- the cover is not the smallest of the three, in either copy
      have hmcn : minimumCover.isNormalized :=
        (tenthBipsOfValue_upward_facts _ _ _ loan₁.broker.wf.debtTotal_norm loan₁.broker.exact.debtTotal_nonneg
          hmc).1
      have hmc0 : 0 ≤ minimumCover.toRat :=
        (tenthBipsOfValue_upward_facts _ _ _ loan₁.broker.wf.debtTotal_norm loan₁.broker.exact.debtTotal_nonneg
          hmc).2
      have hliqn : liquidationAmount.isNormalized := (tenthBipsOfValue_upward_facts _ _ _ hmcn hmc0 hliq).1
      obtain ⟨hmv, hmn⟩ := Number.min_toRat liquidationAmount loan₁.principalOutstanding hliqn
        loan₁.wf.principalOutstanding_norm
      have hle : (Number.min liquidationAmount loan₁.principalOutstanding).toRat ≤ liquidationAmount.toRat := by
        rw [hmv]; exact min_le_left _ _
      rw [Number.min_eq_left_of_le _ _ hmn loan₁.broker.wf.coverAvailable_norm
          (le_trans hle (hc₁ _ _ hmc hliq)),
        Number.min_eq_left_of_le _ _ hmn loan₂.broker.wf.coverAvailable_norm (le_trans hle (hc₂ _ _ hmc hliq))]

/-- Two copies of a loan that differ only in their broker and get the same cover from a default leave the same
vault after it. -/
private lemma Loan.manageDefault_pool_eq (loan₁ loan₂ : Loan) (v : Vault) (r₁ r₂ : LoanWithAmounts Vault)
    (hloan : loan₂.toRawLoan = { loan₁.toRawLoan with broker := loan₂.broker })
    (hcover : loan₁.defaultCover v = loan₂.defaultCover v)
    (h₁ : (loan₁.manageDefault v).run = .ok (.ok r₁)) (h₂ : (loan₂.manageDefault v).run = .ok (.ok r₂)) :
    r₁.pool' = r₂.pool' := by
  have hi : loan₂.interestDue = loan₁.interestDue := by
    show loan₂.toRawLoan.interestDue = loan₁.toRawLoan.interestDue
    rw [hloan]
    rfl
  have hchange (i dc : Number) : loan₂.defaultChange i dc = loan₁.defaultChange i dc := by
    unfold Loan.defaultChange
    rw [show loan₂.principalOutstanding = loan₁.principalOutstanding from
        (congrArg RawLoan.principalOutstanding hloan :),
      show loan₂.isImpaired = loan₁.isImpaired from (congrArg RawLoan.isImpaired hloan :)]
  rw [Loan.manageDefault_run] at h₁ h₂
  rw [hi, ← hcover] at h₂
  cases hint : loan₁.interestDue with
  | error err => rw [hint] at h₁; cases h₁
  | ok interestDue =>
    rw [hint] at h₁ h₂
    dsimp only at h₁ h₂
    cases hdc : loan₁.defaultCover v with
    | error err => rw [hdc] at h₁; cases h₁
    | ok dc =>
      rw [hdc] at h₁ h₂
      dsimp only at h₁ h₂
      rw [hchange] at h₂
      cases hadj : AssetPool.adjustBalances v (loan₁.defaultChange interestDue dc) with
      | error err => rw [hadj] at h₁; cases h₁
      | ok res =>
        rw [hadj] at h₁ h₂
        cases res with
        | error ter => cases h₁
        | ok v' =>
          dsimp only at h₁ h₂
          -- both runs return the vault `v'` once the broker and loan updates pass
          split at h₁
          · cases h₁
          split at h₁
          · cases h₁
          split at h₁
          · cases h₁
          split at h₁
          · cases h₁
          split at h₂
          · cases h₂
          split at h₂
          · cases h₂
          split at h₂
          · cases h₂
          split at h₂
          · cases h₂
          simp only [Except.ok.injEq] at h₁ h₂
          rw [← h₁, ← h₂]

/-- Proof body of `Lending.coverWithdraw_default_same`. -/
lemma LendingLedger.coverWithdraw_default_same_proof (l la lab lb : LendingLedger) (hr : l.Reachable) (k i : Nat)
    (amount : STAmount) (ha : (l.apply (.loanBrokerCoverWithdraw k amount)).run = .ok (.ok la))
    (hab : (la.apply (.loanManage i .default)).run = .ok (.ok lab))
    (hb : (l.apply (.loanManage i .default)).run = .ok (.ok lb)) :
    lab.vault = lb.vault := by
  obtain ⟨_, loan, r, -, hat, -, hdef, -, hv, -⟩ := LendingLedger.loanDefault_ok hb
  obtain ⟨_, loan₂, r₂, -, hat₂, -, hdef₂, -, hv₂, -⟩ := LendingLedger.loanDefault_ok hab
  obtain ⟨hloans, -, hvault, -⟩ := LendingLedger.broker_ops_scope_proof l la _ rfl ha
  rw [hv₂, hv]
  rw [hvault] at hdef₂
  -- both ledgers store the same loan entry at `i`, and read it with their own copy of its broker
  obtain ⟨e, he, hbk, hraw⟩ := hat.stored
  obtain ⟨e₂, he₂, hbk₂, hraw₂⟩ := hat₂.stored
  have hee : e₂ = e := by
    have : la.loan? i = l.loan? i := by unfold LendingLedger.loan?; rw [hloans]
    rw [this, he] at he₂
    exact (Option.some.inj he₂).symm
  subst hee
  have hloan : loan₂.toRawLoan = { loan.toRawLoan with broker := loan₂.broker } := by
    rw [hraw₂, hraw]

  -- the withdrawal rewrote only the broker at `k`
  have hpre := (LendingLedger.apply_checked ha).1
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_broker rfl ha
  simp only [LendingLedger.applyBroker] at hu
  unfold_ter at hu
  walk_ok
  rename_i _ b₀ hb₀ _ _ ter hcan _ hter _ _ res hwd
  have hwd : (b₀.coverWithdraw l.vault amount).run = .ok (.ok res) := hwd
  have hcan' : b₀.canCoverWithdraw l.vault amount = .ok .tesSUCCESS := by
    rw [hcan]
    simp only [Bool.not_eq_true, Bool.not_eq_false', TER.isTesSuccess_iff] at hter
    rw [hter]
  have hklt := LendingLedger.broker?_lt hb₀
  have hslot (j : Nat) : (l.commitBroker { index := k, broker := some res.loanBroker' }).broker? j =
      if j = k then some res.loanBroker' else l.broker? j := by
    rw [LendingLedger.broker?_commitBroker]
    simp only [if_pos hklt]
  rw [hslot] at hbk₂
  by_cases hk : e₂.brokerIndex = k
  · -- the loan's own broker: its cover fell, and it still holds the minimum cover
    rw [if_pos hk] at hbk₂
    have hb₂ : loan₂.broker = res.loanBroker' := (Option.some.inj hbk₂).symm
    have hb₁ : loan.broker = b₀ := by
      rw [hk, hb₀] at hbk
      exact (Option.some.inj hbk).symm
    obtain ⟨a, hcl, happ⟩ := LoanBroker.coverWithdraw_ok_inv b₀ l.vault amount res hwd
    obtain ⟨m, c', -, -, -, hrawb⟩ := LoanBroker.applyCoverTransaction_debit_inv b₀ a res happ
    have hbroker : loan₂.broker.toRawLoanBroker =
        { loan.broker.toRawLoanBroker with coverAvailable := loan₂.broker.coverAvailable } := by
      rw [hb₂, hb₁, hrawb]
    have hpa : (isCanonicalAmount amount l.vault.numericType && isPositiveAmount amount) = true := by
      by_contra hne
      simp only [Bool.not_eq_true] at hne
      simp only [LendingTx.preflight, hne] at hpre
      exact absurd hpre (by decide)
    rw [Bool.and_eq_true] at hpa
    have hnz : amount.mValue ≠ 0 := by
      have := hpa.2
      simp only [isPositiveAmount, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
      exact this.2
    have hac : amount.Canonical := (isCanonicalAmount_canonical amount _ hr.holdsAsset.maxValue_le hpa.1 hnz).1
    obtain ⟨hlo, hhi, -⟩ := Vault.baseExponent_bounds l.vault
    have hmin₂ : res.loanBroker'.HasMinimumCover l.vault.baseExponent :=
      LoanBroker.coverWithdraw_keeps_minimum_proof b₀ l.vault amount res hcan' hwd
    have hle : res.loanBroker'.toExact.coverAvailable ≤ b₀.toExact.coverAvailable :=
      LoanBroker.coverWithdraw_decreases_cover_proof b₀ l.vault amount res hwd hac
        ⟨by show (-96 : ℤ) ≤ l.vault.baseExponent; omega, by show l.vault.baseExponent ≤ 80; omega⟩
    have hmin₁ : b₀.HasMinimumCover l.vault.baseExponent :=
      LoanBroker.hasMinimumCover_of_cover_le res.loanBroker' b₀ _
        (congrArg RawLoanBroker.numericType hrawb :).symm (congrArg RawLoanBroker.debtTotal hrawb :).symm
        (congrArg RawLoanBroker.coverRateMinimum hrawb :).symm hle hmin₂
    obtain ⟨t, ht, htv⟩ := hr.loanAt_debt_units hat
    have hdebt₂ : loan₂.broker.debtTotal = loan.broker.debtTotal := (congrArg RawLoanBroker.debtTotal hbroker :)
    have hcrm₂ : loan₂.broker.coverRateMinimum = loan.broker.coverRateMinimum :=
      (congrArg RawLoanBroker.coverRateMinimum hbroker :)
    have hcrl₂ : loan₂.broker.coverRateLiquidation = loan.broker.coverRateLiquidation :=
      (congrArg RawLoanBroker.coverRateLiquidation hbroker :)
    have hcover := Loan.defaultCover_eq_of_cover loan loan₂ l.vault hloan hbroker
      (fun mc liq hmc hliq => LoanBroker.liquidationAmount_le_cover loan.broker _ t ⟨hlo, hhi⟩ ht htv
        (hb₁ ▸ hmin₁) mc liq hmc hliq)
      (fun mc liq hmc hliq => LoanBroker.liquidationAmount_le_cover loan₂.broker _ t ⟨hlo, hhi⟩ ht
        (by rw [hdebt₂]; exact htv) (hb₂ ▸ hmin₂) mc liq (by rw [hdebt₂, hcrm₂]; exact hmc)
        (by rw [hcrl₂]; exact hliq))
    exact (Loan.manageDefault_pool_eq loan loan₂ l.vault r r₂ hloan hcover hdef hdef₂).symm
  · -- another broker's loan: the default reads the same loan and broker as without the withdrawal
    rw [if_neg hk] at hbk₂
    rw [hbk] at hbk₂
    have hbeq : loan₂.broker = loan.broker := (Option.some.inj hbk₂).symm
    have hcover : loan.defaultCover l.vault = loan₂.defaultCover l.vault := by
      unfold Loan.defaultCover
      rw [hbeq, show loan₂.principalOutstanding = loan.principalOutstanding from
        (congrArg RawLoan.principalOutstanding hloan :)]
    exact (Loan.manageDefault_pool_eq loan loan₂ l.vault r r₂ hloan hcover hdef hdef₂).symm

end XRPL.Model.Lending
