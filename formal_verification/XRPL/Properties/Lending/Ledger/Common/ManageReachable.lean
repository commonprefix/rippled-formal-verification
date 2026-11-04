import XRPL.Properties.Lending.Ledger.Common.BaseGrid
import XRPL.Properties.Lending.Ledger.Common.CashPrecision
import XRPL.Properties.Lending.Loan.Common.ShareValue

/-! # Management actions on the loan a reachable ledger stores

LossUnrealized, AssetsDeployed, the broker's DebtTotal and the stored loan's PrincipalOutstanding are whole base
units, at most `10^16` of them, so every sum a management action makes fits a Number. While the vault holds less
than `10^16` base units, a default stays on the base grid. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- The loan read at `i` is the stored loan with the ledger's copy of its broker. -/
lemma LendingLedger.LoanAt.stored {l : LendingLedger} {i : Nat} {loan : Loan} (h : l.LoanAt i loan) :
    ∃ e, l.loan? i = some e ∧ l.broker? e.brokerIndex = some loan.broker ∧
      loan.toRawLoan = { e.loan.toRawLoan with broker := loan.broker } := by
  obtain ⟨e, b, he, hb, hw⟩ := h
  have hraw := Loan.withBroker_eq hw
  have hbr : loan.broker = b := by rw [show loan.broker = loan.toRawLoan.broker from rfl, hraw]
  rw [hbr]
  exact ⟨e, he, hb, hraw⟩

/-- A count of base units below `2^63` is a normalized Number. -/
private lemma Vault.units_fit (v : Vault) (k : ℤ) (hk : -2 ^ 63 < k ∧ k < 2 ^ 63) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨hlo, hhi, -⟩ := Vault.baseExponent_bounds v
  exact Number.exists_normalized_int_mul_pow k v.baseExponent hk (by unfold minExponent maxExponent; omega)

/-- A whole number of base units at most `10^16` base units counts at most `10^16`. -/
private lemma units_le {x : ℚ} {n : ℕ} {b : Int} (hx : x = (n : ℚ) * 10 ^ b)
    (h : x ≤ 10 ^ 16 * (10 : ℚ) ^ b) : n ≤ 10 ^ 16 := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  rw [hx] at h
  have : (n : ℚ) ≤ 10 ^ 16 := le_of_mul_le_mul_right h hp
  exact_mod_cast this

/-- The stored loan's PrincipalOutstanding is whole base units, at most `10^16` of them, and fits in
AssetsDeployed and in its broker's DebtTotal. -/
lemma LendingLedger.Reachable.loanAt_principal {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) :
    ∃ p : ℕ, p ≤ 10 ^ 16 ∧ loan.principalOutstanding.toRat = (p : ℚ) * 10 ^ l.vault.baseExponent ∧
      loan.principalOutstanding.toRat ≤ l.vault.assetsDeployed.toRat ∧
      loan.principalOutstanding.toRat ≤ loan.broker.debtTotal.toRat := by
  obtain ⟨e, he, hb, hraw⟩ := hat.stored
  have hpo : loan.principalOutstanding = e.loan.principalOutstanding :=
    (congrArg RawLoan.principalOutstanding hraw :)
  obtain ⟨p, hp⟩ := hr.scaleInv.principal_grid he
  refine ⟨p, units_le hp (hr.lossInv.principal i e he), by rw [hpo]; exact hp, ?_, ?_⟩
  · have := LendingLedger.principalIf_le_sum l (fun _ => true) i
    rw [he] at this
    rw [hpo, hr.debtInv.deployed]
    simpa [LoanEntry.principalIf] using this
  · have := l.principalOn_le_sum e.brokerIndex i
    rw [he] at this
    rw [hpo, hr.debtInv.debt _ _ hb]
    simpa [LoanEntry.principalOn] using this

/-- LossUnrealized is whole base units, at most `10^16` of them. -/
lemma LendingLedger.Reachable.loss_units {l : LendingLedger} (hr : l.Reachable) :
    ∃ n : ℕ, n ≤ 10 ^ 16 ∧ l.vault.lossUnrealized.toRat = (n : ℚ) * 10 ^ l.vault.baseExponent := by
  obtain ⟨n, hn⟩ := hr.lossInv.grid
  exact ⟨n, units_le hn hr.lossInv.bound, hn⟩

/-- AssetsDeployed is whole base units, at most `10^16` of them. -/
lemma LendingLedger.Reachable.deployed_units {l : LendingLedger} (hr : l.Reachable) :
    ∃ d : ℕ, d ≤ 10 ^ 16 ∧ l.vault.assetsDeployed.toRat = (d : ℚ) * 10 ^ l.vault.baseExponent := by
  obtain ⟨d, hd⟩ := hr.scaleInv.principalSum_grid (fun _ => true)
  have hd' : l.vault.assetsDeployed.toRat = (d : ℚ) * 10 ^ l.vault.baseExponent := by rw [hr.debtInv.deployed, hd]
  exact ⟨d, units_le hd' hr.lossInv.deployed, hd'⟩

/-- The stored loan's broker holds a DebtTotal of whole base units, at most `10^16` of them. -/
lemma LendingLedger.Reachable.loanAt_debt_units {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) :
    ∃ t : ℕ, t ≤ 10 ^ 16 ∧ loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ l.vault.baseExponent := by
  obtain ⟨e, -, hb, -⟩ := hat.stored
  obtain ⟨t, ht⟩ := hr.scaleInv.brokerPrincipal_grid e.brokerIndex
  have hdt := hr.debtInv.debt _ _ hb
  have hle : loan.broker.debtTotal.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
    rw [hdt]
    refine le_trans (l.brokerPrincipal_le _) ?_
    rw [← hr.debtInv.deployed]
    exact hr.lossInv.deployed
  exact ⟨t, units_le (by rw [hdt, ht]) hle, by rw [hdt, ht]⟩

/-- LossUnrealized plus the stored loan's PrincipalOutstanding fits a Number. -/
lemma LendingLedger.Reachable.impair_fits {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = l.vault.lossUnrealized.toRat + loan.principalOutstanding.toRat := by
  obtain ⟨n, hn, hnv⟩ := hr.loss_units
  obtain ⟨p, hp, hpv, -⟩ := hr.loanAt_principal hat
  obtain ⟨w, hw, hwv⟩ := Vault.units_fit l.vault ((n : ℤ) + p) (by omega)
  exact ⟨w, hw, by rw [hwv, hnv, hpv]; push_cast; ring⟩

/-- LossUnrealized minus the stored loan's PrincipalOutstanding fits a Number. -/
lemma LendingLedger.Reachable.unimpair_fits {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = l.vault.lossUnrealized.toRat - loan.principalOutstanding.toRat := by
  obtain ⟨n, hn, hnv⟩ := hr.loss_units
  obtain ⟨p, hp, hpv, -⟩ := hr.loanAt_principal hat
  obtain ⟨w, hw, hwv⟩ := Vault.units_fit l.vault ((n : ℤ) - p) (by omega)
  exact ⟨w, hw, by rw [hwv, hnv, hpv]; push_cast; ring⟩

/-- AssetsDeployed minus the stored loan's PrincipalOutstanding fits a Number. -/
lemma LendingLedger.Reachable.deployed_fits {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = l.vault.assetsDeployed.toRat - loan.principalOutstanding.toRat := by
  obtain ⟨d, hd, hdv⟩ := hr.deployed_units
  obtain ⟨p, hp, hpv, -⟩ := hr.loanAt_principal hat
  obtain ⟨w, hw, hwv⟩ := Vault.units_fit l.vault ((d : ℤ) - p) (by omega)
  exact ⟨w, hw, by rw [hwv, hdv, hpv]; push_cast; ring⟩

/-- The broker's DebtTotal minus the stored loan's PrincipalOutstanding fits a Number. -/
lemma LendingLedger.Reachable.debt_fits {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = loan.broker.debtTotal.toRat - loan.principalOutstanding.toRat := by
  obtain ⟨t, ht, htv⟩ := hr.loanAt_debt_units hat
  obtain ⟨p, hp, hpv, -⟩ := hr.loanAt_principal hat
  obtain ⟨w, hw, hwv⟩ := Vault.units_fit l.vault ((t : ℤ) - p) (by omega)
  exact ⟨w, hw, by rw [hwv, htv, hpv]; push_cast; ring⟩

/-- YieldUnrealized minus the stored loan's interestDue fits a Number, while YieldUnrealized is below `10^16`
base units. The interest is whole base units, at least `-1` of them. -/
lemma LendingLedger.Reachable.yield_fits {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) (hyu : l.vault.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = l.vault.yieldUnrealized.toRat - loan.toExact.interestDue := by
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨y, hyv⟩ := hr.yieldGridInv.grid.nat l.vault.exact.yieldUnrealized_nonneg
  have hy : y < 10 ^ 16 := by
    rw [hyv] at hyu
    have : (y : ℚ) < 10 ^ 16 := lt_of_mul_lt_mul_right hyu hp10.le
    exact_mod_cast this
  obtain ⟨hls, -⟩ := hr.loanAt_scale hat
  obtain ⟨t, ht, htv⟩ := loan.grid.totalValueOutstanding_atExponent
  obtain ⟨p, -, hpv⟩ := loan.grid.principalOutstanding_atExponent
  obtain ⟨m, -, hmv⟩ := loan.grid.managementFeeOutstanding_atExponent
  change loan.totalValueOutstanding.toRat = (t : ℚ) * 10 ^ loan.loanScale at htv
  change loan.principalOutstanding.toRat = (p : ℚ) * 10 ^ loan.loanScale at hpv
  change loan.managementFeeOutstanding.toRat = (m : ℚ) * 10 ^ loan.loanScale at hmv
  change t < loan.broker.numericType.mantissaBound at ht
  rw [hls] at htv hpv hmv
  have hb := NumericType.mantissaBound_le loan.broker.numericType
  have hi : loan.toExact.interestDue = (((t : ℤ) - p - m : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
    show loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat - loan.managementFeeOutstanding.toRat = _
    rw [htv, hpv, hmv]; push_cast; ring

  -- the interest is at least zero, so at least `-1` unit
  have htol : -((10 : ℚ) ^ l.vault.baseExponent) ≤ loan.toExact.interestDue := by
    have h0 := loan.exact.interest_nonneg
    have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
    linarith
  have hlo : (-1 : ℤ) ≤ (t : ℤ) - p - m := by
    rw [hi] at htol
    have : ((-1 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent ≤
        (((t : ℤ) - p - m : ℤ) : ℚ) * 10 ^ l.vault.baseExponent := by
      rw [show ((-1 : ℤ) : ℚ) * 10 ^ l.vault.baseExponent = -(10 ^ l.vault.baseExponent) by push_cast; ring]
      exact htol
    exact_mod_cast le_of_mul_le_mul_right this hp10
  obtain ⟨w, hw, hwv⟩ := Vault.units_fit l.vault ((y : ℤ) - ((t : ℤ) - p - m)) (by omega)
  exact ⟨w, hw, by rw [hwv, hyv, hi]; push_cast; ring⟩

/-- While the vault holds less than `10^16` base units, the stored loan's principal fits beside
AssetsAvailable. AssetsAvailable + PrincipalOutstanding stays a whole base unit below `10^16` base units. -/
lemma LendingLedger.Reachable.loanAt_room {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∃ a : ℕ, l.vault.assetsAvailable.toRat = (a : ℚ) * 10 ^ l.vault.baseExponent ∧
      l.vault.assetsAvailable.toRat + loan.principalOutstanding.toRat ≤
        (10 : ℚ) ^ (16 + l.vault.baseExponent) - 10 ^ l.vault.baseExponent := by
  have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  obtain ⟨a, ha⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨d, -, hd⟩ := hr.deployed_units
  obtain ⟨-, -, -, hpad, -⟩ := hr.loanAt_principal hat
  refine ⟨a, ha, ?_⟩
  -- AssetsTotal is whole base units below `10^16` of them, so at least a unit below
  have had : a + d < 10 ^ 16 := by
    rw [ha, hd, ← add_mul] at htotal
    have : ((a + d : ℕ) : ℚ) < 10 ^ 16 := by push_cast; exact lt_of_mul_lt_mul_right htotal hp10.le
    exact_mod_cast this
  have had' : ((a + d : ℕ) : ℚ) + 1 ≤ 10 ^ 16 := by
    have : a + d + 1 ≤ 10 ^ 16 := by omega
    exact_mod_cast this
  have hpow : (10 : ℚ) ^ (16 + l.vault.baseExponent) = 10 ^ 16 * 10 ^ l.vault.baseExponent := by
    rw [zpow_add₀ (by norm_num)]; norm_num
  have hsum : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat =
      ((a + d : ℕ) : ℚ) * 10 ^ l.vault.baseExponent := by rw [ha, hd]; push_cast; ring
  rw [hpow]
  linarith [mul_le_mul_of_nonneg_right had' hp10.le]

/-- A successful default computed the minimum cover and the liquidation amount. -/
lemma Loan.manageDefault_cover_steps (loan : Loan) (v : Vault) (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault v).run = .ok (.ok r)) :
    ∃ minimumCover liquidationAmount : Number,
      tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover ∧
      tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount := by
  obtain ⟨_, _, _, _, _, -, hdc, -⟩ := Loan.manageDefault_ok_parts loan v r hok
  obtain ⟨mc, liq, -, -, hmc, hliq, -⟩ := Loan.defaultCover_parts loan v _ hdc
  exact ⟨mc, liq, hmc, hliq⟩

/-- The capped liquidation amount is at most PrincipalOutstanding. -/
private lemma capped_le_principal (liquidationAmount principal cover : ℚ) :
    min (min liquidationAmount principal) cover ≤ principal :=
  le_trans (min_le_left _ _) (min_le_right _ _)

variable (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan) (hat : l.LoanAt i loan)
include hr hat

/-- The default step of the lower bound part of `Lending.manageDefault_cover`, read on the default's result. -/
lemma LendingLedger.loanDefault_cover_lower_bound (minimumCover liquidationAmount : Number)
    (r : LoanWithAmounts Vault) (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    ∀ e, numberExponent r.pool'.assetsAvailable l.vault.baseExponent l.vault.numericType = .ok e →
      min (min liquidationAmount.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat -
        r.amountToPool.toRat < 10 ^ e := by
  intro e he
  obtain ⟨a, ha, hroom⟩ := hr.loanAt_room hat htotal
  have hc := capped_le_principal liquidationAmount.toRat loan.principalOutstanding.toRat
    loan.broker.coverAvailable.toRat
  obtain ⟨hlt, hexp⟩ := Loan.manageDefault_cover_lower_bound_at_base loan l.vault _ _ a r hok hmin hliq
    (hr.loanAt_scale hat).2 ha (by linarith)
  rw [hexp e he]
  exact hlt

/-- The default step of the nonnegative part of `Lending.manageDefault_cover`, read on the default's result. -/
lemma LendingLedger.loanDefault_cover_nonneg (r : LoanWithAmounts Vault)
    (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    0 ≤ r.amountToPool.toRat := by
  obtain ⟨mc, liq, hmin, hliq⟩ := Loan.manageDefault_cover_steps loan l.vault r hok
  obtain ⟨a, ha, hroom⟩ := hr.loanAt_room hat htotal
  have hc := capped_le_principal liq.toRat loan.principalOutstanding.toRat loan.broker.coverAvailable.toRat
  exact Loan.manageDefault_cover_nonneg_at_base loan l.vault mc liq a r hok hmin hliq (hr.loanAt_scale hat).2 ha
    (by linarith)

/-- The default step of the monotone part of `Lending.manageDefault_cover`, read on the default's result. The loan
with the larger cover is the stored one. -/
lemma LendingLedger.loanDefault_cover_monotone (loan₁ : Loan) (r₁ r₂ : LoanWithAmounts Vault)
    (hloan : loan.toRawLoan = { loan₁.toRawLoan with broker := loan.broker })
    (hbroker : loan.broker.toRawLoanBroker =
      { loan₁.broker.toRawLoanBroker with coverAvailable := loan.broker.coverAvailable })
    (hle : loan₁.broker.coverAvailable.toRat ≤ loan.broker.coverAvailable.toRat)
    (hok₁ : (loan₁.manageDefault l.vault).run = .ok (.ok r₁))
    (hok₂ : (loan.manageDefault l.vault).run = .ok (.ok r₂))
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    l.vault.toExact.assetsTotal - r₂.pool'.toExact.assetsTotal ≤
      l.vault.toExact.assetsTotal - r₁.pool'.toExact.assetsTotal := by
  obtain ⟨mc, liq, hmin, hliq⟩ := Loan.manageDefault_cover_steps loan₁ l.vault r₁ hok₁
  obtain ⟨a, ha, hroom⟩ := hr.loanAt_room hat htotal
  have hpo : loan.principalOutstanding = loan₁.principalOutstanding := by
    rw [show loan.principalOutstanding = loan.toRawLoan.principalOutstanding from rfl, hloan]
  have hnt : loan₁.broker.numericType = l.vault.numericType := by
    rw [← (hr.loanAt_scale hat).2, show loan.broker.numericType = loan.broker.toRawLoanBroker.numericType from rfl,
      hbroker]
  rw [hpo] at hroom
  have hc := capped_le_principal liq.toRat loan₁.principalOutstanding.toRat loan.broker.coverAvailable.toRat
  exact Loan.manageDefault_cover_monotone_at_base l.vault loan₁ loan mc liq a r₁ r₂ hloan hbroker hle hok₁
    hok₂ hmin hliq hnt ha (by linarith)

/-- Proof body of `Lending.default_fully_covered`. -/
lemma LendingLedger.default_fully_covered_proof (minimumCover liquidationAmount : Number)
    (r : LoanWithAmounts Vault) (hok : (loan.manageDefault l.vault).run = .ok (.ok r))
    (hmin : tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover)
    (hliq : tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount)
    (hcov : loan.principalOutstanding.toRat ≤ min liquidationAmount.toRat loan.broker.coverAvailable.toRat)
    (htotal : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    r.amountToPool.toRat = loan.principalOutstanding.toRat ∧
      r.pool'.toExact.assetsTotal = l.vault.toExact.assetsTotal := by
  obtain ⟨a, ha, hroom⟩ := hr.loanAt_room hat htotal
  obtain ⟨p, -, hp, -⟩ := hr.loanAt_principal hat
  exact Loan.default_fully_covered_at_base loan l.vault _ _ a p r hok hmin hliq hcov (hr.loanAt_scale hat).2 ha hp
    hroom (hr.deployed_fits hat)

end XRPL.Model.Lending
