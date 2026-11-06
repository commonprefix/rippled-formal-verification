import XRPL.Properties.Lending.Ledger.Common.DefaultOrderDefs
import XRPL.Properties.Lending.Ledger.Common.PaymentShareValue
import XRPL.Properties.Lending.Ledger.Common.YieldSum
import XRPL.Properties.Lending.Ledger.Common.CoverGridInv
import XRPL.Properties.Lending.Ledger.Common.IntegralCoverInv

/-! # Proof body for the order of two defaults on a ledger

On the base grid a default's cover joins AssetsAvailable exactly. Loans on two brokers each pay the same cover in
either order. Two loans on one broker that the liquidation amount does not cap pay min(PrincipalOutstanding₁ +
PrincipalOutstanding₂, CoverAvailable) together. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A whole number of `10^s` units floored to `10^s` units is itself. -/
private lemma floor_grid (x : ℚ) (m : ℤ) (s : ℤ) (hx : x = m * 10 ^ s) : (⌊x / 10 ^ s⌋ : ℚ) * 10 ^ s = x := by
  have hp : (10 : ℚ) ^ s ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [hx, mul_div_cancel_right₀ _ hp, Int.floor_intCast]

/-- A liquidation amount of at least min(principal, cover) does not change the capped amount. -/
private lemma min_min_of_le (q p c : ℚ) (h : min p c ≤ q) : min (min q p) c = min p c := by
  rw [min_assoc]
  exact min_eq_right h

/-- A count of base units below `2^63` is a normalized Number. -/
private lemma Vault.units_number (v : Vault) (k : ℤ) (hk : 0 ≤ k ∧ k < 2 ^ 63) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨hlo, hhi, -⟩ := Vault.baseExponent_bounds v
  exact Number.exists_normalized_int_mul_pow k v.baseExponent ⟨by omega, hk.2⟩
    (by unfold minExponent maxExponent; omega)

/-- A successful default on the ledger ran on the stored loan with its broker refreshed and wrote its result. -/
private lemma LendingLedger.default_step {l l' : LendingLedger} {i : Nat}
    (h : (l.apply (.loanManage i .default)).run = .ok (.ok l')) :
    ∃ e loan r, l.loan? i = some e ∧ l.broker? e.brokerIndex = some loan.broker ∧
      e.loan.withBroker loan.broker = .ok loan ∧ loan.canManage .default l.now = .ok .tesSUCCESS ∧
      (loan.manageDefault l.vault).run = .ok (.ok r) ∧
      l' = l.commitLoan (LoanEffect.ofLoan i e r.loan' r.pool') := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, b, loan, r, he, hb, hw, hc, hok, rfl⟩ := l.applyLoan_manage_inv u i .default hu
  have hlb : loan.broker = b := (congrArg RawLoan.broker (Loan.withBroker_eq hw) :)
  subst hlb
  simp only [Loan.manage] at hok
  unfold_ter at hok
  walk_ok
  rename_i rd hd
  exact ⟨e, loan, rd, he, hb, hw, hc, hd, rfl⟩

/-- A successful default wrote the broker with the principal off DebtTotal and the cover off CoverAvailable. -/
private lemma Loan.manageDefault_broker_record (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r)) :
    r.loan'.broker.toRawLoanBroker = { loan.broker.toRawLoanBroker with
      debtTotal := r.loan'.broker.debtTotal, coverAvailable := r.loan'.broker.coverAvailable } ∧
    loan.broker.debtTotal.operator_sub loan.principalOutstanding .to_nearest = .ok r.loan'.broker.debtTotal ∧
    loan.broker.coverAvailable.operator_sub r.amountToPool .to_nearest = .ok r.loan'.broker.coverAvailable ∧
    r.amountToPool.isNormalized := by
  obtain ⟨_, d, c, _, b, -, hdc, -, -, hd, hc, hb, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  have hbr : r.loan'.broker = b := by rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hloan]; rfl
  have hd' : r.loan'.broker.debtTotal = d := by
    rw [hbr, show b.debtTotal = b.toRawLoanBroker.debtTotal from rfl, hb]; rfl
  have hc' : r.loan'.broker.coverAvailable = c := by
    rw [hbr, show b.coverAvailable = b.toRawLoanBroker.coverAvailable from rfl, hb]; rfl
  refine ⟨?_, by rw [hd']; exact hd, by rw [hc']; exact hc, Loan.defaultCover_isNormalized loan v _ hdc⟩
  rw [hd', hc', hbr, hb]
  rfl

/-- A default on a vault that is not coarsened. The cover is the capped amount floored to whole base units and joins
AssetsAvailable exactly, and every other balance moves by exactly what the loan holds. -/
private lemma LendingLedger.default_at_base {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) {r : LoanWithAmounts Vault} (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    (∃ minimumCover liquidationAmount : Number,
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount ∧
      r.amountToPool.toRat = (⌊min (min liquidationAmount.toRat loan.principalOutstanding.toRat)
        loan.broker.coverAvailable.toRat / 10 ^ l.vault.baseExponent⌋ : ℚ) * 10 ^ l.vault.baseExponent) ∧
    0 ≤ r.amountToPool.toRat ∧ r.amountToPool.toRat ≤ loan.principalOutstanding.toRat ∧
    r.pool'.assetsAvailable.toRat = l.vault.assetsAvailable.toRat + r.amountToPool.toRat ∧
    r.pool'.assetsDeployed.toRat = l.vault.assetsDeployed.toRat - loan.principalOutstanding.toRat ∧
    r.pool'.assetsReserved = l.vault.assetsReserved ∧
    r.pool'.lossUnrealized.toRat = l.vault.lossUnrealized.toRat -
      (if loan.isImpaired then loan.principalOutstanding.toRat else 0) ∧
    r.pool'.yieldUnrealized.toRat = l.vault.yieldUnrealized.toRat - loan.toExact.interestDue ∧
    r.loan'.broker.debtTotal.toRat = loan.broker.debtTotal.toRat - loan.principalOutstanding.toRat := by
  obtain ⟨mc, liq, hmin, hliq⟩ := Loan.manageDefault_cover_steps loan l.vault r hok
  obtain ⟨a, ha, hroom⟩ := hr.loanAt_room hat htotal
  have hcap : min (min liq.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat ≤
      loan.principalOutstanding.toRat := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcap0 := Loan.cappedCover_nonneg loan mc liq hmin hliq
  obtain ⟨hdc, haa⟩ := Loan.manageDefault_at_base loan l.vault mc liq a r hok hmin hliq (hr.loanAt_scale hat).2 ha
    (by linarith)
  obtain ⟨hAD, hD⟩ := Loan.manageDefault_principal_proof loan l.vault r hok (hr.deployed_fits hat)
    (hr.debt_fits hat)
  have hyu := Loan.manageDefault_yield_proof loan l.vault r hok (hr.yield_fits hat hr.yield_lt)
  obtain ⟨_, -, hs⟩ := Loan.manageDefault_sums loan l.vault r hok

  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  set capped := min (min liq.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat
  have hfl := Int.floor_le (capped / 10 ^ l.vault.baseExponent)
  rw [le_div_iff₀ hp] at hfl
  have hfl0 : (0 : ℚ) ≤ ⌊capped / 10 ^ l.vault.baseExponent⌋ := by
    exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hcap0 hp.le)
  refine ⟨⟨mc, liq, hmin, hliq, hdc⟩, by rw [hdc]; positivity, by rw [hdc]; linarith, haa, by linarith,
    Number.eq_of_add_zero hs.reserved, ?_, hyu, by linarith⟩

  -- an impaired loan releases its principal from LossUnrealized
  cases himp : loan.isImpaired
  · have hl := hs.loss
    simp only [Loan.defaultChange, himp, Bool.false_eq_true, ↓reduceIte] at hl
    rw [Number.eq_of_add_zero hl]
    simp
  · simp only [↓reduceIte]
    exact Loan.manageDefault_loss_proof loan l.vault r hok himp (hr.unimpair_fits hat)

/-- A default keeps the vault's base scale. -/
private lemma Loan.manageDefault_baseExponent (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r)) : r.pool'.baseExponent = v.baseExponent := by
  have hrec := Loan.manageDefault_vault_record loan v r hok
  have hnt : r.pool'.numericType = v.numericType := (congrArg RawVault.numericType hrec :)
  have hsc : r.pool'.scale = v.scale := (congrArg RawVault.scale hrec :)
  unfold Vault.baseExponent
  rw [hnt, hsc]

/-- Two reads of one stored loan with different broker copies agree on what a default takes from the vault. -/
private lemma Loan.withBroker_same {e : Loan} {b b' : LoanBroker} {x y : Loan} (hx : e.withBroker b = .ok x)
    (hy : e.withBroker b' = .ok y) :
    y.principalOutstanding = x.principalOutstanding ∧ y.isImpaired = x.isImpaired ∧
      y.toExact.interestDue = x.toExact.interestDue := by
  have h1 := Loan.withBroker_eq hx
  have h2 := Loan.withBroker_eq hy
  refine ⟨?_, ?_, ?_⟩
  · rw [show y.principalOutstanding = y.toRawLoan.principalOutstanding from rfl, h2,
      show x.principalOutstanding = x.toRawLoan.principalOutstanding from rfl, h1]
  · rw [show y.isImpaired = y.toRawLoan.isImpaired from rfl, h2,
      show x.isImpaired = x.toRawLoan.isImpaired from rfl, h1]
  · show y.toRawLoan.totalValueOutstanding.toRat - y.toRawLoan.principalOutstanding.toRat -
      y.toRawLoan.managementFeeOutstanding.toRat = x.toRawLoan.totalValueOutstanding.toRat -
      x.toRawLoan.principalOutstanding.toRat - x.toRawLoan.managementFeeOutstanding.toRat
    rw [h1, h2]

/-- A default of loan `i` leaves every other loan slot as it was. -/
private lemma LendingLedger.loan?_default_other {l : LendingLedger} {i j : Nat} {e : LoanEntry} {loan' : Loan}
    {v' : Vault} (hji : j ≠ i) (he : l.loan? i = some e) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).loan? j = l.loan? j := by
  rw [LendingLedger.loan?_commitLoan]
  simp [LoanEffect.ofLoan, LendingLedger.loan?_lt he, hji]

/-- The same loan cannot default twice. The defaulted loan fails the LoanManage preclaim. -/
private lemma LendingLedger.default_twice {l la lab : LendingLedger} {i : Nat}
    (ha : (l.apply (.loanManage i .default)).run = .ok (.ok la))
    (hab : (la.apply (.loanManage i .default)).run = .ok (.ok lab)) : False := by
  obtain ⟨e, loan, r, he, -, -, -, hok, rfl⟩ := LendingLedger.default_step ha
  obtain ⟨e', loan', -, he', -, hw', hc', -, -⟩ := LendingLedger.default_step hab
  rw [LendingLedger.loan?_commitLoan] at he'
  simp only [LoanEffect.ofLoan, LendingLedger.loan?_lt he, ↓reduceIte, Option.some.injEq] at he'
  subst he'
  have hdef : loan'.isDefault = true := by
    rw [show loan'.isDefault = loan'.toRawLoan.isDefault from rfl, Loan.withBroker_eq hw']
    exact (Loan.manageDefault_closes_proof loan l.vault r hok).2.2.2.2.2
  unfold Loan.canManage at hc'
  simp [hdef] at hc'

/-- A default on a vault that is not coarsened keeps it not coarsened: it pays the vault at most the principal it
takes off AssetsDeployed. -/
private lemma LendingLedger.default_room {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) {r : LoanWithAmounts Vault} (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ r.pool'.baseExponent := by
  obtain ⟨-, -, hle, haa, had, -⟩ := LendingLedger.default_at_base hr hat hok htotal
  rw [Loan.manageDefault_baseExponent loan l.vault r hok, haa, had]
  linarith

/-- The broker slot a default writes holds the defaulted broker, the others are as they were. -/
private lemma LendingLedger.broker?_default {l : LendingLedger} {i : Nat} {e : LoanEntry} {loan' : Loan} {v' : Vault}
    {b : LoanBroker} (hb : l.broker? e.brokerIndex = some b) (k : Nat) :
    (l.commitLoan (LoanEffect.ofLoan i e loan' v')).broker? k =
      if k = e.brokerIndex then some loan'.broker else l.broker? k :=
  LendingLedger.broker?_commitLoan l _ b hb k

/-- The smaller of two whole numbers of `g` units is the smaller count of `g` units. -/
private lemma min_units (x y : ℚ) (a b : ℤ) (g : ℚ) (hg : 0 ≤ g) (hx : x = a * g) (hy : y = b * g) :
    min x y = ((min a b : ℤ) : ℚ) * g := by
  rw [hx, hy, Int.cast_min, min_mul_of_nonneg _ _ hg]

/-- Both orders leave the same vault and brokers. -/
private lemma LendingLedger.defaults_comm_pool (l la lb lab lba : LendingLedger) (hr : l.Reachable) (i j : Nat)
    (ha : (l.apply (.loanManage i .default)).run = .ok (.ok la))
    (hab : (la.apply (.loanManage j .default)).run = .ok (.ok lab))
    (hb : (l.apply (.loanManage j .default)).run = .ok (.ok lb))
    (hba : (lb.apply (.loanManage i .default)).run = .ok (.ok lba))
    (hliq : l.DefaultUncapped i ∧ la.DefaultUncapped j ∧ l.DefaultUncapped j ∧ lb.DefaultUncapped i)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hcover : ∀ loan, l.LoanAt i loan →
      loan.broker.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) :
    lab.vault = lba.vault ∧ lab.brokers = lba.brokers := by
  have hij : i ≠ j := fun h => LendingLedger.default_twice ha (h ▸ hab)
  have hra := hr.apply ha
  have hrb := hr.apply hb
  obtain ⟨hliqA, hliqAB, hliqB, hliqBA⟩ := hliq
  obtain ⟨ea, A, rA, hea, hbA, hwA, -, hokA, hla⟩ := LendingLedger.default_step ha
  obtain ⟨eb, B, rB, heb, hbB, hwB, -, hokB, hlb⟩ := LendingLedger.default_step hb
  obtain ⟨eb', B', rAB, heb', hbB', hwB', -, hokAB, hlab⟩ := LendingLedger.default_step hab
  obtain ⟨ea', A', rBA, hea', hbA', hwA', -, hokBA, hlba⟩ := LendingLedger.default_step hba
  have hatA : l.LoanAt i A := ⟨ea, A.broker, hea, hbA, hwA⟩
  have hatB : l.LoanAt j B := ⟨eb, B.broker, heb, hbB, hwB⟩
  have hatB' : la.LoanAt j B' := ⟨eb', B'.broker, heb', hbB', hwB'⟩
  have hatA' : lb.LoanAt i A' := ⟨ea', A'.broker, hea', hbA', hwA'⟩

  -- the second default of each order reads the other loan's stored entry
  rw [hla, LendingLedger.loan?_default_other (Ne.symm hij) hea, heb, Option.some.injEq] at heb'
  rw [hlb, LendingLedger.loan?_default_other hij heb, hea, Option.some.injEq] at hea'
  subst heb' hea'
  obtain ⟨hPB, hIB, hYB⟩ := Loan.withBroker_same hwB hwB'
  obtain ⟨hPA, hIA, hYA⟩ := Loan.withBroker_same hwA hwA'

  have hlav : la.vault = rA.pool' := by rw [hla]; rfl
  have hlbv : lb.vault = rB.pool' := by rw [hlb]; rfl
  have hbeA := Loan.manageDefault_baseExponent A l.vault rA hokA
  have hbeB := Loan.manageDefault_baseExponent B l.vault rB hokB
  have htotA : la.vault.assetsAvailable.toRat + la.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ la.vault.baseExponent := by
    rw [hlav]; exact LendingLedger.default_room hr hatA hokA htotal
  have htotB : lb.vault.assetsAvailable.toRat + lb.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ lb.vault.baseExponent := by
    rw [hlbv]; exact LendingLedger.default_room hr hatB hokB htotal

  obtain ⟨⟨mcA, lqA, hmA, hlA, hdcA⟩, -, -, haaA, hadA, harA, hluA, hyuA, hdA⟩ :=
    LendingLedger.default_at_base hr hatA hokA htotal
  obtain ⟨⟨mcB, lqB, hmB, hlB, hdcB⟩, -, -, haaB, hadB, harB, hluB, hyuB, hdB⟩ :=
    LendingLedger.default_at_base hr hatB hokB htotal
  obtain ⟨⟨mcAB, lqAB, hmAB, hlAB, hdcAB⟩, -, -, haaAB, hadAB, harAB, hluAB, hyuAB, hdAB⟩ :=
    LendingLedger.default_at_base hra hatB' hokAB htotA
  obtain ⟨⟨mcBA, lqBA, hmBA, hlBA, hdcBA⟩, -, -, haaBA, hadBA, harBA, hluBA, hyuBA, hdBA⟩ :=
    LendingLedger.default_at_base hrb hatA' hokBA htotB
  have hliqAB' := hliqAB B' mcAB lqAB hatB' hmAB hlAB
  have hliqBA' := hliqBA A' mcBA lqBA hatA' hmBA hlBA
  rw [hlav, hbeA] at hdcAB
  rw [hlbv, hbeB] at hdcBA
  rw [hlav] at haaAB hadAB harAB hluAB hyuAB
  rw [hlbv] at haaBA hadBA harBA hluBA hyuBA
  rw [hPB] at hdcAB hadAB hluAB hdAB hliqAB'
  rw [hIB] at hluAB
  rw [hYB] at hyuAB
  rw [hPA] at hdcBA hadBA hluBA hdBA hliqBA'
  rw [hIA] at hluBA
  rw [hYA] at hyuBA
  have hlabv : lab.vault = rAB.pool' := by rw [hlab]; rfl
  have hlbav : lba.vault = rBA.pool' := by rw [hlba]; rfl
  have hlabb : lab.brokers = (l.brokers.set ea.brokerIndex (some rA.loan'.broker)).set eb.brokerIndex
      (some rAB.loan'.broker) := by rw [hlab, hla]; rfl
  have hlbab : lba.brokers = (l.brokers.set eb.brokerIndex (some rB.loan'.broker)).set ea.brokerIndex
      (some rBA.loan'.broker) := by rw [hlba, hlb]; rfl
  obtain ⟨recA, hdsA, hcsA, hnA⟩ := Loan.manageDefault_broker_record _ _ _ hokA
  obtain ⟨recB, hdsB, hcsB, hnB⟩ := Loan.manageDefault_broker_record _ _ _ hokB
  obtain ⟨recAB, hdsAB, hcsAB, hnAB⟩ := Loan.manageDefault_broker_record _ _ _ hokAB
  obtain ⟨recBA, hdsBA, hcsBA, hnBA⟩ := Loan.manageDefault_broker_record _ _ _ hokBA
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _

  have key : rA.amountToPool.toRat + rAB.amountToPool.toRat = rB.amountToPool.toRat + rBA.amountToPool.toRat ∧
      lab.brokers = lba.brokers := by
    by_cases hk : ea.brokerIndex = eb.brokerIndex
    · -- one broker: the second default reads the broker the first one wrote
      have hAB : A.broker = B.broker := by
        have h := hbA
        rw [hk, hbB] at h
        exact (Option.some.inj h).symm
      have hB'b : B'.broker = rA.loan'.broker := by
        have h := hbB'
        rw [hla, LendingLedger.broker?_default hbA, if_pos hk.symm] at h
        exact (Option.some.inj h).symm
      have hA'b : A'.broker = rB.loan'.broker := by
        have h := hbA'
        rw [hlb, LendingLedger.broker?_default hbB, if_pos hk] at h
        exact (Option.some.inj h).symm

      obtain ⟨pA, -, hpA, -, -⟩ := hr.loanAt_principal hatA
      obtain ⟨pB, -, hpB, -, -⟩ := hr.loanAt_principal hatB
      obtain ⟨-, c, hc⟩ := hr.cover_onGrid hbA
      have hcB : B.broker.coverAvailable.toRat = (c : ℚ) * 10 ^ l.vault.baseExponent := by rw [← hAB]; exact hc
      have hc0 : 0 ≤ c := by
        have h0 : 0 ≤ A.broker.coverAvailable.toRat := A.broker.exact.coverAvailable_nonneg
        rw [hc] at h0
        have : (0 : ℚ) ≤ c := le_of_mul_le_mul_right (by rw [zero_mul]; exact h0) hp
        exact_mod_cast this
      have hc63 : c < 2 ^ 63 := by
        have h := hcover A hatA
        rw [hc] at h
        have : (c : ℚ) < 2 ^ 63 := lt_of_mul_lt_mul_right h hp.le
        exact_mod_cast this

      -- loan A then loan B: each pays min(PrincipalOutstanding, CoverAvailable) of the cover left
      have eA : rA.amountToPool.toRat = ((min (pA : ℤ) c : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [hdcA, min_min_of_le _ _ _ (hliqA A mcA lqA hatA hmA hlA),
          min_units _ _ pA c _ hp.le (by rw [hpA]; push_cast; ring) hc]
        exact floor_grid _ _ _ rfl
      have eC1 : rA.loan'.broker.coverAvailable.toRat =
          ((c - min (pA : ℤ) c : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        obtain ⟨w, hw, hwv⟩ := Vault.units_number l.vault (c - min (pA : ℤ) c) ⟨by omega, by omega⟩
        rw [Number.operator_sub_exact_of_fits A.broker.wf.coverAvailable_norm hnA hcsA
          ⟨w, hw, by rw [hwv, hc, eA]; push_cast; ring⟩, hc, eA]
        push_cast; ring
      have eAB : rAB.amountToPool.toRat =
          ((min (pB : ℤ) (c - min (pA : ℤ) c) : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [hdcAB, min_min_of_le _ _ _ hliqAB', hB'b,
          min_units _ _ pB _ _ hp.le (by rw [hpB]; push_cast; ring) eC1]
        exact floor_grid _ _ _ rfl
      have eC12 : rAB.loan'.broker.coverAvailable.toRat =
          ((c - min (pA : ℤ) c - min (pB : ℤ) (c - min (pA : ℤ) c) : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [hB'b] at hcsAB
        obtain ⟨w, hw, hwv⟩ := Vault.units_number l.vault (c - min (pA : ℤ) c - min (pB : ℤ) (c - min (pA : ℤ) c))
          ⟨by omega, by omega⟩
        rw [Number.operator_sub_exact_of_fits rA.loan'.broker.wf.coverAvailable_norm hnAB hcsAB
          ⟨w, hw, by rw [hwv, eC1, eAB]; push_cast; ring⟩, eC1, eAB]
        push_cast; ring

      -- loan B then loan A
      have eB : rB.amountToPool.toRat = ((min (pB : ℤ) c : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [hdcB, min_min_of_le _ _ _ (hliqB B mcB lqB hatB hmB hlB),
          min_units _ _ pB c _ hp.le (by rw [hpB]; push_cast; ring) hcB]
        exact floor_grid _ _ _ rfl
      have eC2 : rB.loan'.broker.coverAvailable.toRat =
          ((c - min (pB : ℤ) c : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        obtain ⟨w, hw, hwv⟩ := Vault.units_number l.vault (c - min (pB : ℤ) c) ⟨by omega, by omega⟩
        rw [Number.operator_sub_exact_of_fits B.broker.wf.coverAvailable_norm hnB hcsB
          ⟨w, hw, by rw [hwv, hcB, eB]; push_cast; ring⟩, hcB, eB]
        push_cast; ring
      have eBA : rBA.amountToPool.toRat =
          ((min (pA : ℤ) (c - min (pB : ℤ) c) : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [hdcBA, min_min_of_le _ _ _ hliqBA', hA'b,
          min_units _ _ pA _ _ hp.le (by rw [hpA]; push_cast; ring) eC2]
        exact floor_grid _ _ _ rfl
      have eC21 : rBA.loan'.broker.coverAvailable.toRat =
          ((c - min (pB : ℤ) c - min (pA : ℤ) (c - min (pB : ℤ) c) : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
        rw [hA'b] at hcsBA
        obtain ⟨w, hw, hwv⟩ := Vault.units_number l.vault (c - min (pB : ℤ) c - min (pA : ℤ) (c - min (pB : ℤ) c))
          ⟨by omega, by omega⟩
        rw [Number.operator_sub_exact_of_fits rB.loan'.broker.wf.coverAvailable_norm hnBA hcsBA
          ⟨w, hw, by rw [hwv, eC2, eBA]; push_cast; ring⟩, eC2, eBA]
        push_cast; ring

      have eD : rAB.loan'.broker.debtTotal = rBA.loan'.broker.debtTotal :=
        rAB.loan'.broker.wf.debtTotal_norm.toRat_inj rBA.loan'.broker.wf.debtTotal_norm
          (by rw [hdAB, hB'b, hdA, hdBA, hA'b, hdB, hAB]; ring)
      have eC : rAB.loan'.broker.coverAvailable = rBA.loan'.broker.coverAvailable := by
        refine rAB.loan'.broker.wf.coverAvailable_norm.toRat_inj rBA.loan'.broker.wf.coverAvailable_norm ?_
        rw [eC12, eC21]
        have : c - min (pA : ℤ) c - min (pB : ℤ) (c - min (pA : ℤ) c) =
            c - min (pB : ℤ) c - min (pA : ℤ) (c - min (pB : ℤ) c) := by omega
        rw [this]
      have hbr : rAB.loan'.broker = rBA.loan'.broker := by
        apply broker_eq_of_raw
        rw [recAB, recBA, hB'b, hA'b, recA, recB, hAB, eD, eC]
      refine ⟨?_, ?_⟩
      · rw [eA, eAB, eB, eBA, ← add_mul, ← add_mul, ← Int.cast_add, ← Int.cast_add]
        have : min (pA : ℤ) c + min (pB : ℤ) (c - min (pA : ℤ) c) =
            min (pB : ℤ) c + min (pA : ℤ) (c - min (pB : ℤ) c) := by omega
        rw [this]
      · rw [hlabb, hlbab, hk, List.set_set, List.set_set, hbr]
    · -- two brokers: each default reads its own broker as stored
      have hBB : B'.broker = B.broker := by
        have h := hbB'
        rw [hla, LendingLedger.broker?_default hbA, if_neg (Ne.symm hk), hbB] at h
        exact (Option.some.inj h).symm
      have hAA : A'.broker = A.broker := by
        have h := hbA'
        rw [hlb, LendingLedger.broker?_default hbB, if_neg hk, hbA] at h
        exact (Option.some.inj h).symm
      rw [hBB, hwB, Except.ok.injEq] at hwB'
      rw [hAA, hwA, Except.ok.injEq] at hwA'
      subst hwB' hwA'
      rw [hmB, Except.ok.injEq] at hmAB
      subst hmAB
      rw [hlB, Except.ok.injEq] at hlAB
      subst hlAB
      rw [hmA, Except.ok.injEq] at hmBA
      subst hmBA
      rw [hlA, Except.ok.injEq] at hlBA
      subst hlBA

      -- on the base grid the cover does not depend on AssetsAvailable
      have hdc₁ : rAB.amountToPool = rB.amountToPool := hnAB.toRat_inj hnB (by rw [hdcAB, hdcB])
      have hdc₂ : rBA.amountToPool = rA.amountToPool := hnBA.toRat_inj hnA (by rw [hdcBA, hdcA])
      have hbr₁ : rAB.loan'.broker = rB.loan'.broker := by
        rw [hdsB, Except.ok.injEq] at hdsAB
        rw [hdc₁, hcsB, Except.ok.injEq] at hcsAB
        apply broker_eq_of_raw
        rw [recAB, recB, hdsAB, hcsAB]
      have hbr₂ : rBA.loan'.broker = rA.loan'.broker := by
        rw [hdsA, Except.ok.injEq] at hdsBA
        rw [hdc₂, hcsA, Except.ok.injEq] at hcsBA
        apply broker_eq_of_raw
        rw [recBA, recA, hdsBA, hcsBA]
      refine ⟨by rw [hdc₁, hdc₂]; ring, ?_⟩
      rw [hlabb, hlbab, hbr₁, hbr₂]
      exact List.set_comm _ _ hk

  obtain ⟨hT, hbrk⟩ := key
  refine ⟨?_, hbrk⟩
  rw [hlabv, hlbav]
  have eAA : rAB.pool'.assetsAvailable = rBA.pool'.assetsAvailable :=
    rAB.pool'.wf.assetsAvailable_norm.toRat_inj rBA.pool'.wf.assetsAvailable_norm
      (by rw [haaAB, haaA, haaBA, haaB]; linarith)
  have eAD : rAB.pool'.assetsDeployed = rBA.pool'.assetsDeployed :=
    rAB.pool'.wf.assetsDeployed_norm.toRat_inj rBA.pool'.wf.assetsDeployed_norm
      (by rw [hadAB, hadA, hadBA, hadB]; ring)
  have eAR : rAB.pool'.assetsReserved = rBA.pool'.assetsReserved := by rw [harAB, harA, harBA, harB]
  have eLU : rAB.pool'.lossUnrealized = rBA.pool'.lossUnrealized :=
    rAB.pool'.wf.lossUnrealized_norm.toRat_inj rBA.pool'.wf.lossUnrealized_norm
      (by rw [hluAB, hluA, hluBA, hluB]; ring)
  have eYU : rAB.pool'.yieldUnrealized = rBA.pool'.yieldUnrealized :=
    rAB.pool'.wf.yieldUnrealized_norm.toRat_inj rBA.pool'.wf.yieldUnrealized_norm
      (by rw [hyuAB, hyuA, hyuBA, hyuB]; ring)
  apply vault_eq_of_raw
  rw [Loan.manageDefault_vault_record _ _ _ hokAB, Loan.manageDefault_vault_record _ _ _ hokBA, hlav, hlbv,
    Loan.manageDefault_vault_record _ _ _ hokA, Loan.manageDefault_vault_record _ _ _ hokB, eAA, eAD, eAR, eLU, eYU]

/-- A defaulted loan read with any broker copy is the stored loan defaulted: the broker it was read with is gone. -/
private lemma Loan.default_withBroker {e loan : Loan} {b₀ : LoanBroker} {v : Vault} {r : LoanWithAmounts Vault}
    (hw : e.withBroker b₀ = .ok loan) (hok : (loan.manageDefault v).run = .ok (.ok r)) (b : LoanBroker) :
    r.loan'.withBroker b = (e.defaultedLoan b).to_lawful := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, hloan, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  unfold Loan.withBroker
  rw [hloan]
  unfold Loan.defaultedLoan
  rw [Loan.withBroker_eq hw]

/-- Both orders leave every loan reading the same once they leave the same brokers. Only the broker copy
stored with each defaulted loan differs, and every transaction replaces it with the ledger's broker. -/
private lemma LendingLedger.defaults_comm_loans {l la lb lab lba : LendingLedger} {i j : Nat}
    (ha : (l.apply (.loanManage i .default)).run = .ok (.ok la))
    (hab : (la.apply (.loanManage j .default)).run = .ok (.ok lab))
    (hb : (l.apply (.loanManage j .default)).run = .ok (.ok lb))
    (hba : (lb.apply (.loanManage i .default)).run = .ok (.ok lba))
    (hbrk : lab.brokers = lba.brokers) (k : Nat) (loan : Loan) :
    lab.LoanAt k loan ↔ lba.LoanAt k loan := by
  have hij : i ≠ j := fun h => LendingLedger.default_twice ha (h ▸ hab)
  obtain ⟨ea, A, rA, hea, -, hwA, -, hokA, hla⟩ := LendingLedger.default_step ha
  obtain ⟨eb, B, rB, heb, -, hwB, -, hokB, hlb⟩ := LendingLedger.default_step hb
  obtain ⟨eb', B', rAB, heb', -, hwB', -, hokAB, hlab⟩ := LendingLedger.default_step hab
  obtain ⟨ea', A', rBA, hea', -, hwA', -, hokBA, hlba⟩ := LendingLedger.default_step hba
  rw [hla, LendingLedger.loan?_default_other (Ne.symm hij) hea, heb, Option.some.injEq] at heb'
  rw [hlb, LendingLedger.loan?_default_other hij heb, hea, Option.some.injEq] at hea'
  subst heb' hea'
  have hla' : la.loan? j = some eb := by rw [hla, LendingLedger.loan?_default_other (Ne.symm hij) hea, heb]
  have hlb' : lb.loan? i = some ea := by rw [hlb, LendingLedger.loan?_default_other hij heb, hea]

  have hslot : ∀ b : LoanBroker, (lab.loan? k).map (fun e => (e.brokerIndex, e.loan.withBroker b)) =
      (lba.loan? k).map (fun e => (e.brokerIndex, e.loan.withBroker b)) := by
    intro b
    rw [hlab, LendingLedger.loan?_commit_ofLoan _ hla', hla, LendingLedger.loan?_commit_ofLoan _ hea,
      hlba, LendingLedger.loan?_commit_ofLoan _ hlb', hlb, LendingLedger.loan?_commit_ofLoan _ heb]
    by_cases hkj : k = j
    · subst hkj
      simp only [↓reduceIte, if_neg (Ne.symm hij), Option.map_some]
      rw [Loan.default_withBroker hwB' hokAB, Loan.default_withBroker hwB hokB]
    · by_cases hki : k = i
      · subst hki
        simp only [hkj, ↓reduceIte, Option.map_some]
        rw [Loan.default_withBroker hwA hokA, Loan.default_withBroker hwA' hokBA]
      · simp only [hkj, hki, ↓reduceIte]
  have hbr : ∀ x, lab.broker? x = lba.broker? x := fun x => by unfold LendingLedger.broker?; rw [hbrk]

  have hread : ∀ (L L' : LendingLedger), (∀ x, L.broker? x = L'.broker? x) →
      (∀ b : LoanBroker, (L.loan? k).map (fun e => (e.brokerIndex, e.loan.withBroker b)) =
        (L'.loan? k).map (fun e => (e.brokerIndex, e.loan.withBroker b))) →
      L.LoanAt k loan → L'.LoanAt k loan := by
    intro L L' hb hs ⟨e, b, he, heb, hw⟩
    have h := hs b
    rw [he] at h
    cases he' : L'.loan? k with
    | none => rw [he'] at h; cases h
    | some e' =>
      rw [he'] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨e', b, he', by rw [← h.1, ← hb]; exact heb, by rw [← h.2]; exact hw⟩
  exact ⟨hread lab lba hbr hslot, hread lba lab (fun x => (hbr x).symm) (fun b => (hslot b).symm)⟩

/-- Proof body of `Lending.defaults_comm`. -/
lemma LendingLedger.defaults_comm_proof (l la lb lab lba : LendingLedger) (hr : l.Reachable) (i j : Nat)
    (ha : (l.apply (.loanManage i .default)).run = .ok (.ok la))
    (hab : (la.apply (.loanManage j .default)).run = .ok (.ok lab))
    (hb : (l.apply (.loanManage j .default)).run = .ok (.ok lb))
    (hba : (lb.apply (.loanManage i .default)).run = .ok (.ok lba))
    (hliq : l.DefaultUncapped i ∧ la.DefaultUncapped j ∧ l.DefaultUncapped j ∧ lb.DefaultUncapped i)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hcover : ∀ loan, l.LoanAt i loan →
      loan.broker.coverAvailable.toRat < 2 ^ 63 * (10 : ℚ) ^ l.vault.baseExponent) :
    lab.vault = lba.vault ∧ lab.brokers = lba.brokers ∧ ∀ k loan, lab.LoanAt k loan ↔ lba.LoanAt k loan := by
  obtain ⟨hv, hb'⟩ := LendingLedger.defaults_comm_pool l la lb lab lba hr i j ha hab hb hba hliq htotal hcover
  exact ⟨hv, hb', LendingLedger.defaults_comm_loans ha hab hb hba hb'⟩

end XRPL.Model.Lending
