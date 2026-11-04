import XRPL.Properties.Lending.Ledger.Common.RecheckLoanSet
import XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
import XRPL.Properties.Lending.Ledger.Common.YieldSum

/-! # LoanSet exits on a reachable ledger

A LoanSet that passed `canCreate` reads a vault at its base scale. With AssetsAvailable plus AssetsDeployed below
`10^16` base units the balances a LoanSet moves and the broker's DebtTotal are whole base units below `10^16`. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private atExponent_of_int from XRPL.Properties.Lending.Loan.Common.OrderCreates
open private Vault.total_lt_of_scale from XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs

/-- On a reachable ledger whose AssetsAvailable plus AssetsDeployed is below `10^16` base units, AssetsAvailable,
AssetsDeployed, AssetsReserved, YieldUnrealized and DebtTotal are whole base units below `10^16`. -/
lemma LendingLedger.Reachable.createGrid_of_room {l : LendingLedger} (hr : l.Reachable) {j : Nat}
    {broker : LoanBroker} (hb : l.broker? j = some broker)
    (hroom : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent) :
    Loan.CreateGrid broker l.vault := by
  have hex := l.vault.exact
  have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := hex.assetsAvailable_nonneg
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := hex.assetsDeployed_nonneg
  have hAR0 : 0 ≤ l.vault.assetsReserved.toRat := hex.assetsReserved_nonneg
  have hARD : l.vault.assetsReserved.toRat ≤ l.vault.assetsDeployed.toRat := hex.assetsReserved_le
  have hYU0 : 0 ≤ l.vault.yieldUnrealized.toRat := hex.yieldUnrealized_nonneg
  have hdt := hr.debtInv.debt j broker hb
  have hdtle : broker.debtTotal.toRat ≤ l.vault.assetsDeployed.toRat := by
    rw [hdt, hr.debtInv.deployed]; exact l.brokerPrincipal_le j
  have hdt0 : 0 ≤ broker.debtTotal.toRat := broker.exact.debtTotal_nonneg
  obtain ⟨na, hna⟩ := hr.assetsAvailable_units hr.holdsAsset
  obtain ⟨nd, hnd⟩ := hr.scaleInv.principalSum_grid (fun _ => true)
  rw [← hr.debtInv.deployed] at hnd
  obtain ⟨nr, hnr⟩ := hr.reservedInv.grid
  obtain ⟨ny, hny⟩ := hr.yieldGridInv.grid.nat hYU0
  obtain ⟨nt, hnt⟩ := hr.scaleInv.brokerPrincipal_grid j
  exact ⟨atExponent_of_int _ na _ (by rw [hna]; push_cast; ring) hAA0 (by linarith),
    atExponent_of_int _ nd _ (by rw [hnd]; push_cast; ring) hAD0 (by linarith),
    atExponent_of_int _ nr _ (by rw [hnr]; push_cast; ring) hAR0 (by linarith),
    atExponent_of_int _ ny _ (by rw [hny]; push_cast; ring) hYU0 hr.yield_lt,
    atExponent_of_int _ nt _ (by rw [hdt, hnt]; push_cast; ring) hdt0 (by linarith)⟩

/-- An IOU vault that passed `canCreate` holds AssetsAvailable plus AssetsDeployed below `10^16` base units. -/
private lemma Loan.canCreate_room {l : LendingLedger} (hr : l.Reachable) {j : Nat} {broker : LoanBroker}
    (hb : l.broker? j = some broker) (principal : Number) (fees : LoanFees) (schedule : LoanSchedule)
    (twoStep : Bool) (hfr : l.vault.numericType = .fractional)
    (hc : Loan.canCreate broker l.vault principal fees schedule l.now twoStep = .ok .tesSUCCESS) :
    l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
  obtain ⟨atot, hat, hexp⟩ := Loan.canCreate_exponent broker l.vault principal fees schedule l.now twoStep hc
  rw [hr.scaleInv.brokers j broker hb] at hexp
  have he : AssetPool.exponent l.vault l.vault.numericType = .ok l.vault.baseExponent := by
    unfold AssetPool.exponent
    rw [Vault.pool_assetsTotal, hat]
    exact hexp
  have h := Vault.total_lt_of_scale l.vault _ hfr he le_rfl
  rwa [zpow_add₀ (by norm_num)] at h

/-- Proof body of `create_error_codes`. -/
lemma Loan.create_error_codes_reachable_proof (l : LendingLedger) (hr : l.Reachable) (j : Nat)
    (broker : LoanBroker) (hb : l.broker? j = some broker) (principal : Number) (rates : LoanRates)
    (fees : LoanFees) (schedule : LoanSchedule) (twoStep allowsOverpayment pending : Bool) (ter : TER)
    (hpre : Loan.CreatePreflight broker principal rates fees schedule)
    (hc : Loan.canCreate broker l.vault principal fees schedule l.now twoStep = .ok .tesSUCCESS)
    (hroom : l.vault.numericType.isIntegral = true →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent)
    (hcount : broker.loanCount + 1 ≠ 0)
    (hok : (Loan.create broker l.vault principal rates fees schedule allowsOverpayment pending).run =
      .ok (.error ter)) :
    ter = .tecINSUFFICIENT_FUNDS ∨ ter = .tecPRECISION_LOSS ∨ ter = .tecLIMIT_EXCEEDED := by
  have hroom' : l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat <
      10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := by
    cases hint : l.vault.numericType.isIntegral
    · exact Loan.canCreate_room hr hb principal fees schedule twoStep
        (NumericType.eq_fractional_of_not_integral (by simpa using hint)) hc
    · exact hroom hint
  exact Loan.create_error_codes_proof broker l.vault principal rates fees schedule allowsOverpayment pending ter hpre
    hr.holdsAsset (hr.createGrid_of_room hb hroom') hcount hok

end XRPL.Model.Lending
