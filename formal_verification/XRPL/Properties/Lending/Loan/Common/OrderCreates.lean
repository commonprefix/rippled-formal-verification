import XRPL.Properties.Lending.Loan.Common.Reserved
import XRPL.Properties.Lending.Loan.Common.Twin

/-! # Proof bodies for the order of two new loans

On the base grid a new loan moves whole base units, and the Open-limit check keeps the balances below
`10^16` units. So the next create is on the base grid too, and both orders add up the same balances. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- A value of `z` base units, at least `0` and below `10^16` units, is a whole number of base units. -/
private lemma atExponent_of_int (x : ℚ) (z : ℤ) (s : ℤ) (hx : x = (z : ℚ) * 10 ^ s) (h0 : 0 ≤ x)
    (hlt : x < 10 ^ 16 * (10 : ℚ) ^ s) : Number.AtExponent x s (10 ^ 16) := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hz : 0 ≤ z := by
    have : (0 : ℚ) ≤ z := by
      by_contra hc
      push Not at hc
      have := mul_neg_of_neg_of_pos hc hp
      linarith
    exact_mod_cast this
  refine ⟨z.toNat, ?_, ?_⟩
  · have : (z : ℚ) < 10 ^ 16 := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hp.le
      linarith
    have h2 : z < 10 ^ 16 := by exact_mod_cast this
    omega
  · rw [hx]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hz).symm

/-- The Open limit `9·10^15` base units plus half a unit is below `10^16` base units. -/
private lemma open_bound_lt (s : ℤ) :
    ((9 * 10 ^ 16 + 5 : ℕ) : ℚ) * (10 : ℚ) ^ (s - 1) < 10 ^ 16 * (10 : ℚ) ^ s := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
  rw [show ((9 * 10 ^ 16 + 5 : ℕ) : ℚ) * (10 ^ s / 10) = ((9 * 10 ^ 16 + 5 : ℕ) / 10 : ℚ) * 10 ^ s by ring]
  exact mul_lt_mul_of_pos_right (by norm_num) hp

variable (broker : LoanBroker) (v : Vault) (principal : Number) (rates : LoanRates) (fees : LoanFees)
  (schedule : LoanSchedule) (allowsOverpayment pending : Bool) (r : LoanWithDisbursement Vault)

/-- A successful create wrote its five new balances into the vault record, and the new DebtTotal and one
more loan into the broker record. -/
private lemma Loan.create_record
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.pool'.toRawVault = { v.toRawVault with
      assetsAvailable := r.pool'.assetsAvailable
      assetsDeployed := r.pool'.assetsDeployed
      assetsReserved := r.pool'.assetsReserved
      lossUnrealized := r.pool'.lossUnrealized
      yieldUnrealized := r.pool'.yieldUnrealized } ∧
    r.loan'.broker.toRawLoanBroker = { broker.toRawLoanBroker with
      debtTotal := r.loan'.broker.debtTotal
      loanCount := broker.loanCount + 1 } := by
  obtain ⟨_, _, _, _, broker', _, _, _, _, _, -, -, -, hpool, hl, hb⟩ :=
    Loan.create_pool_sums broker v principal rates fees schedule allowsOverpayment pending r hok
  have hbr : r.loan'.broker = broker' := by
    rw [show r.loan'.broker = r.loan'.toRawLoan.broker from rfl, hl]; rfl
  refine ⟨by rw [hpool], ?_⟩
  rw [hbr, hb]

/-- A create keeps the vault's base scale. -/
private lemma Loan.create_baseExponent
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    r.pool'.baseExponent = v.baseExponent := by
  have hrec := (Loan.create_record broker v principal rates fees schedule allowsOverpayment pending r hok).1
  have hnt : r.pool'.numericType = v.numericType := (congrArg RawVault.numericType hrec :)
  have hsc : r.pool'.scale = v.scale := (congrArg RawVault.scale hrec :)
  unfold Vault.baseExponent
  rw [hnt, hsc]

/-- A create leaves room in the vault. It passed the Open-limit check, so AssetsAvailable plus
AssetsDeployed, and YieldUnrealized, were each below `10^16` base units. -/
private lemma Loan.create_room (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent ∧
      v.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent := by
  obtain ⟨hzone, -⟩ := Loan.create_inside_open_zone broker v principal rates fees schedule allowsOverpayment pending r
    hp hpos hst hok
  obtain ⟨props, loanState, debtTotal', broker', hchecks, hl, hb⟩ :=
    Loan.create_loan_eq broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨hiN, hi0⟩ := Loan.create_checkedInterest_nonneg broker v principal rates fees schedule allowsOverpayment
    pending r props loanState debtTotal' broker' hp hpos hst hok hchecks hl hb
  have hyu := (Vault.exceedsOpenLimit_false_bound v loanState.interestDue hiN hchecks.open_zone).2.1
  have hlt := open_bound_lt v.baseExponent
  exact ⟨by linarith, by linarith⟩

/-- A new loan moves whole base units. PrincipalRequested and the interest of the new loan are whole
numbers of base units. -/
private lemma Loan.create_units (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (har : ∃ n : ℕ, v.assetsReserved.toRat = (n : ℚ) * 10 ^ v.baseExponent)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r)) :
    ∃ (j : ℕ) (z : ℤ), principal.toRat = (j : ℚ) * 10 ^ v.baseExponent ∧
      r.loan'.toExact.interestDue = (z : ℚ) * 10 ^ v.baseExponent := by
  have hls := Loan.create_loanScale_proof broker v principal rates fees schedule allowsOverpayment pending r hp hpos
    hst hnt hok
  obtain ⟨-, -, hpo, -, -⟩ := Loan.create_reserved broker v principal rates fees schedule allowsOverpayment pending
    r hp hpos hst hnt har hok
  obtain ⟨m₁, -, h₁⟩ := r.loan'.grid.totalValueOutstanding_atExponent
  obtain ⟨m₂, -, h₂⟩ := r.loan'.grid.principalOutstanding_atExponent
  obtain ⟨m₃, -, h₃⟩ := r.loan'.grid.managementFeeOutstanding_atExponent
  simp only [RawLoan.toExact] at h₁ h₂ h₃
  rw [hls] at h₁ h₂ h₃
  refine ⟨m₂, (m₁ : ℤ) - m₂ - m₃, by rw [← hpo]; exact h₂, ?_⟩
  show r.loan'.totalValueOutstanding.toRat - r.loan'.principalOutstanding.toRat -
    r.loan'.managementFeeOutstanding.toRat = _
  rw [h₁, h₂, h₃]
  push_cast
  ring

/-- The base grid after a create. The balances moved by whole base units and stay below `10^16` units
while the vault has room, so a next create on a broker with its debt on the grid is on the base grid. -/
private lemma Loan.create_grid_next (bo : LoanBroker) (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (hgrid : Loan.CreateGrid broker v)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hroom : r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent)
    (hyield : r.pool'.yieldUnrealized.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent)
    (hdebt : Number.AtExponent bo.debtTotal.toRat v.baseExponent (10 ^ 16)) :
    Loan.CreateGrid bo r.pool' := by
  obtain ⟨haa, had, -, har, hyu, -⟩ := Loan.create_balances broker v principal rates fees schedule
    allowsOverpayment pending r hp hpos hst hgrid hok
  have hbe := Loan.create_baseExponent broker v principal rates fees schedule allowsOverpayment pending r hok
  obtain ⟨a, -, hav⟩ := hgrid.assetsAvailable
  obtain ⟨d, -, hdv⟩ := hgrid.assetsDeployed
  obtain ⟨n, -, hnv⟩ := hgrid.assetsReserved
  obtain ⟨y, -, hyv⟩ := hgrid.yieldUnrealized
  obtain ⟨j, z, hj, hz⟩ := Loan.create_units broker v principal rates fees schedule allowsOverpayment pending r hp
    hpos hst hnt ⟨n, hnv⟩ hok
  have hex := r.pool'.exact
  have hAA0 : 0 ≤ r.pool'.assetsAvailable.toRat := hex.assetsAvailable_nonneg
  have hAD0 : 0 ≤ r.pool'.assetsDeployed.toRat := hex.assetsDeployed_nonneg
  have hAR0 : 0 ≤ r.pool'.assetsReserved.toRat := hex.assetsReserved_nonneg
  have hYU0 : 0 ≤ r.pool'.yieldUnrealized.toRat := hex.yieldUnrealized_nonneg
  have hARD : r.pool'.assetsReserved.toRat ≤ r.pool'.assetsDeployed.toRat := hex.assetsReserved_le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hbe]
  · exact atExponent_of_int _ ((a : ℤ) - j) _ (by rw [haa, hav, hj]; push_cast; ring) hAA0 (by linarith)
  · exact atExponent_of_int _ ((d : ℤ) + j) _ (by rw [had, hdv, hj]; push_cast; ring) hAD0 (by linarith)
  · refine atExponent_of_int _ ((n : ℤ) + if pending then (j : ℤ) else 0) _ ?_ hAR0 (by linarith)
    rw [har, hnv, hj]
    cases pending <;> simp only [if_true, if_false, Bool.false_eq_true] <;> push_cast <;> ring
  · refine atExponent_of_int _ ((y : ℤ) + if pending then 0 else z) _ ?_ hYU0 hyield
    rw [hyu, hyv, hz]
    cases pending <;> simp only [if_true, if_false, Bool.false_eq_true] <;> push_cast <;> ring
  · exact hdebt

/-- The new DebtTotal of a create on the base grid is a whole number of base units, below `10^16` units when
the old one plus PrincipalRequested is. -/
private lemma Loan.create_debt_grid (hp : principal.isNormalized) (hpos : 0 < principal.toRat)
    (hst : STAmount.isRounded broker.numericType principal = false) (hnt : broker.numericType = v.numericType)
    (hgrid : Loan.CreateGrid broker v)
    (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment pending).run = .ok (.ok r))
    (hdebt : broker.debtTotal.toRat + principal.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent) :
    Number.AtExponent r.loan'.broker.debtTotal.toRat v.baseExponent (10 ^ 16) := by
  obtain ⟨-, -, -, -, -, hdt⟩ := Loan.create_balances broker v principal rates fees schedule
    allowsOverpayment pending r hp hpos hst hgrid hok
  obtain ⟨n, -, hnv⟩ := hgrid.assetsReserved
  obtain ⟨t, -, htv⟩ := hgrid.debtTotal
  obtain ⟨j, -, hj, -⟩ := Loan.create_units broker v principal rates fees schedule allowsOverpayment pending r hp
    hpos hst hnt ⟨n, hnv⟩ hok
  have hval : r.loan'.broker.debtTotal.toRat = (((t : ℤ) + j : ℤ) : ℚ) * 10 ^ v.baseExponent := by
    rw [hdt, htv, hj]; push_cast; ring
  exact atExponent_of_int _ _ _ hval (by rw [hval]; positivity) (by rw [hdt]; exact hdebt)

/-- Both orders of two creates on the base grid write the same vault. Loan 1 is created on `b₁` first and on
`c₁` second, loan 2 on `b₂` first and on `c₂` second. -/
private lemma creates_comm_vault (b₁ b₂ c₁ c₂ : LoanBroker) (p₁ p₂ : Number) (ra₁ ra₂ : LoanRates)
    (f₁ f₂ : LoanFees) (s₁ s₂ : LoanSchedule) (ao₁ ao₂ pn₁ pn₂ : Bool) (r₁ r₁₂ r₂ r₂₁ : LoanWithDisbursement Vault)
    (hp₁ : p₁.isNormalized) (hpos₁ : 0 < p₁.toRat) (hst₁ : STAmount.isRounded b₁.numericType p₁ = false)
    (hp₂ : p₂.isNormalized) (hpos₂ : 0 < p₂.toRat) (hst₂ : STAmount.isRounded b₂.numericType p₂ = false)
    (hnt₁ : c₁.numericType = b₁.numericType) (hm₁ : c₁.managementFeeRate = b₁.managementFeeRate)
    (hnt₂ : c₂.numericType = b₂.numericType) (hm₂ : c₂.managementFeeRate = b₂.managementFeeRate)
    (hg₁ : Loan.CreateGrid b₁ v) (hg₂ : Loan.CreateGrid b₂ v)
    (hg₁₂ : Loan.CreateGrid c₂ r₁.pool') (hg₂₁ : Loan.CreateGrid c₁ r₂.pool')
    (h₁ : (Loan.create b₁ v p₁ ra₁ f₁ s₁ ao₁ pn₁).run = .ok (.ok r₁))
    (h₁₂ : (Loan.create c₂ r₁.pool' p₂ ra₂ f₂ s₂ ao₂ pn₂).run = .ok (.ok r₁₂))
    (h₂ : (Loan.create b₂ v p₂ ra₂ f₂ s₂ ao₂ pn₂).run = .ok (.ok r₂))
    (h₂₁ : (Loan.create c₁ r₂.pool' p₁ ra₁ f₁ s₁ ao₁ pn₁).run = .ok (.ok r₂₁)) :
    r₁₂.pool' = r₂₁.pool' := by
  have hst₁' : STAmount.isRounded c₁.numericType p₁ = false := by rw [hnt₁]; exact hst₁
  have hst₂' : STAmount.isRounded c₂.numericType p₂ = false := by rw [hnt₂]; exact hst₂
  obtain ⟨a₁, d₁, l₁, e₁, y₁, -⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₁ hpos₁ hst₁ hg₁ h₁
  obtain ⟨a₂, d₂, l₂, e₂, y₂, -⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₂ hpos₂ hst₂ hg₂ h₂
  obtain ⟨a₁₂, d₁₂, l₁₂, e₁₂, y₁₂, -⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₂ hpos₂ hst₂' hg₁₂ h₁₂
  obtain ⟨a₂₁, d₂₁, l₂₁, e₂₁, y₂₁, -⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₁ hpos₁ hst₁' hg₂₁ h₂₁
  -- each loan owes the same interest in either order
  have hbe₁ := Loan.create_baseExponent _ _ _ _ _ _ _ _ _ h₁
  have hbe₂ := Loan.create_baseExponent _ _ _ _ _ _ _ _ _ h₂
  have hi₁ := (Loan.create_twin b₁ c₁ v r₂.pool' p₁ ra₁ f₁ s₁ ao₁ pn₁ r₁ r₂₁ hnt₁ hm₁ hbe₂ h₁ h₂₁).interestDue_eq
  have hi₂ := (Loan.create_twin b₂ c₂ v r₁.pool' p₂ ra₂ f₂ s₂ ao₂ pn₂ r₂ r₁₂ hnt₂ hm₂ hbe₁ h₂ h₁₂).interestDue_eq
  rw [hi₁] at y₂₁
  rw [hi₂] at y₁₂
  have hw₁₂ := r₁₂.pool'.wf
  have hw₂₁ := r₂₁.pool'.wf
  have eAA : r₁₂.pool'.assetsAvailable = r₂₁.pool'.assetsAvailable :=
    hw₁₂.assetsAvailable_norm.toRat_inj hw₂₁.assetsAvailable_norm (by rw [a₁₂, a₁, a₂₁, a₂]; ring)
  have eAD : r₁₂.pool'.assetsDeployed = r₂₁.pool'.assetsDeployed :=
    hw₁₂.assetsDeployed_norm.toRat_inj hw₂₁.assetsDeployed_norm (by rw [d₁₂, d₁, d₂₁, d₂]; ring)
  have eLU : r₁₂.pool'.lossUnrealized = r₂₁.pool'.lossUnrealized :=
    hw₁₂.lossUnrealized_norm.toRat_inj hw₂₁.lossUnrealized_norm (by rw [l₁₂, l₁, l₂₁, l₂])
  have eAR : r₁₂.pool'.assetsReserved = r₂₁.pool'.assetsReserved :=
    hw₁₂.assetsReserved_norm.toRat_inj hw₂₁.assetsReserved_norm (by rw [e₁₂, e₁, e₂₁, e₂]; ring)
  have eYU : r₁₂.pool'.yieldUnrealized = r₂₁.pool'.yieldUnrealized :=
    hw₁₂.yieldUnrealized_norm.toRat_inj hw₂₁.yieldUnrealized_norm (by rw [y₁₂, y₁, y₂₁, y₂]; ring)
  apply vault_eq_of_raw
  rw [(Loan.create_record _ _ _ _ _ _ _ _ _ h₁₂).1, (Loan.create_record _ _ _ _ _ _ _ _ _ h₂₁).1,
    (Loan.create_record _ _ _ _ _ _ _ _ _ h₁).1, (Loan.create_record _ _ _ _ _ _ _ _ _ h₂).1,
    eAA, eAD, eAR, eLU, eYU]

/-- The broker a create wrote keeps the asset and the management fee rate. -/
private lemma create_broker_terms (hok : (Loan.create broker v principal rates fees schedule allowsOverpayment
    pending).run = .ok (.ok r)) :
    r.loan'.broker.numericType = broker.numericType ∧
      r.loan'.broker.managementFeeRate = broker.managementFeeRate := by
  have hb := (Loan.create_record broker v principal rates fees schedule allowsOverpayment pending r hok).2
  exact ⟨(congrArg RawLoanBroker.numericType hb :), (congrArg RawLoanBroker.managementFeeRate hb :)⟩

/-- Proof body of `creates_comm`, two loans on one broker. -/
lemma Loan.creates_comm_same_proof (b : LoanBroker) (p₁ p₂ : Number) (ra₁ ra₂ : LoanRates) (f₁ f₂ : LoanFees)
    (s₁ s₂ : LoanSchedule) (ao₁ ao₂ pn₁ pn₂ : Bool) (r₁ r₁₂ r₂ r₂₁ : LoanWithDisbursement Vault)
    (hp₁ : p₁.isNormalized) (hpos₁ : 0 < p₁.toRat) (hst₁ : STAmount.isRounded b.numericType p₁ = false)
    (hp₂ : p₂.isNormalized) (hpos₂ : 0 < p₂.toRat) (hst₂ : STAmount.isRounded b.numericType p₂ = false)
    (hnt : b.numericType = v.numericType) (hgrid : Loan.CreateGrid b v)
    (hdebt₁ : b.debtTotal.toRat + p₁.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent)
    (hdebt₂ : b.debtTotal.toRat + p₂.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent)
    (h₁ : (Loan.create b v p₁ ra₁ f₁ s₁ ao₁ pn₁).run = .ok (.ok r₁))
    (h₁₂ : (Loan.create r₁.loan'.broker r₁.pool' p₂ ra₂ f₂ s₂ ao₂ pn₂).run = .ok (.ok r₁₂))
    (h₂ : (Loan.create b v p₂ ra₂ f₂ s₂ ao₂ pn₂).run = .ok (.ok r₂))
    (h₂₁ : (Loan.create r₂.loan'.broker r₂.pool' p₁ ra₁ f₁ s₁ ao₁ pn₁).run = .ok (.ok r₂₁)) :
    r₁₂.pool' = r₂₁.pool' ∧ r₁₂.loan'.broker = r₂₁.loan'.broker := by
  obtain ⟨hnt₁, hm₁⟩ := create_broker_terms _ _ _ _ _ _ _ _ _ h₁
  obtain ⟨hnt₂, hm₂⟩ := create_broker_terms _ _ _ _ _ _ _ _ _ h₂
  have hst₁' : STAmount.isRounded r₂.loan'.broker.numericType p₁ = false := by rw [hnt₂]; exact hst₁
  have hst₂' : STAmount.isRounded r₁.loan'.broker.numericType p₂ = false := by rw [hnt₁]; exact hst₂
  have hbe₁ := Loan.create_baseExponent _ _ _ _ _ _ _ _ _ h₁
  have hbe₂ := Loan.create_baseExponent _ _ _ _ _ _ _ _ _ h₂
  -- after either create the vault and the broker are still on the base grid
  have hg₁₂ : Loan.CreateGrid r₁.loan'.broker r₁.pool' := by
    obtain ⟨hroom, hyield⟩ := Loan.create_room _ _ _ _ _ _ _ _ _ hp₂ hpos₂ hst₂' h₁₂
    rw [hbe₁] at hroom hyield
    exact Loan.create_grid_next b v p₁ ra₁ f₁ s₁ ao₁ pn₁ r₁ _ hp₁ hpos₁ hst₁ hnt hgrid h₁ hroom hyield
      (Loan.create_debt_grid b v p₁ ra₁ f₁ s₁ ao₁ pn₁ r₁ hp₁ hpos₁ hst₁ hnt hgrid h₁ hdebt₁)
  have hg₂₁ : Loan.CreateGrid r₂.loan'.broker r₂.pool' := by
    obtain ⟨hroom, hyield⟩ := Loan.create_room _ _ _ _ _ _ _ _ _ hp₁ hpos₁ hst₁' h₂₁
    rw [hbe₂] at hroom hyield
    exact Loan.create_grid_next b v p₂ ra₂ f₂ s₂ ao₂ pn₂ r₂ _ hp₂ hpos₂ hst₂ hnt hgrid h₂ hroom hyield
      (Loan.create_debt_grid b v p₂ ra₂ f₂ s₂ ao₂ pn₂ r₂ hp₂ hpos₂ hst₂ hnt hgrid h₂ hdebt₂)
  refine ⟨creates_comm_vault v b b r₂.loan'.broker r₁.loan'.broker p₁ p₂ ra₁ ra₂ f₁ f₂ s₁ s₂ ao₁ ao₂ pn₁ pn₂
    r₁ r₁₂ r₂ r₂₁ hp₁ hpos₁ hst₁ hp₂ hpos₂ hst₂ hnt₂ hm₂ hnt₁ hm₁ hgrid hgrid hg₁₂ hg₂₁ h₁ h₁₂ h₂ h₂₁, ?_⟩
  obtain ⟨-, -, -, -, -, t₁⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₁ hpos₁ hst₁ hgrid h₁
  obtain ⟨-, -, -, -, -, t₂⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₂ hpos₂ hst₂ hgrid h₂
  obtain ⟨-, -, -, -, -, t₁₂⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₂ hpos₂ hst₂' hg₁₂ h₁₂
  obtain ⟨-, -, -, -, -, t₂₁⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₁ hpos₁ hst₁' hg₂₁ h₂₁
  have eDT : r₁₂.loan'.broker.debtTotal = r₂₁.loan'.broker.debtTotal :=
    r₁₂.loan'.broker.wf.debtTotal_norm.toRat_inj r₂₁.loan'.broker.wf.debtTotal_norm
      (by rw [t₁₂, t₁, t₂₁, t₂]; ring)
  apply broker_eq_of_raw
  rw [(Loan.create_record _ _ _ _ _ _ _ _ _ h₁₂).2, (Loan.create_record _ _ _ _ _ _ _ _ _ h₂₁).2,
    (Loan.create_record _ _ _ _ _ _ _ _ _ h₁).2, (Loan.create_record _ _ _ _ _ _ _ _ _ h₂).2, eDT]

/-- Proof body of `creates_comm`, two loans on two brokers. -/
lemma Loan.creates_comm_other_proof (b₁ b₂ : LoanBroker) (p₁ p₂ : Number) (ra₁ ra₂ : LoanRates)
    (f₁ f₂ : LoanFees) (s₁ s₂ : LoanSchedule) (ao₁ ao₂ pn₁ pn₂ : Bool) (r₁ r₁₂ r₂ r₂₁ : LoanWithDisbursement Vault)
    (hp₁ : p₁.isNormalized) (hpos₁ : 0 < p₁.toRat) (hst₁ : STAmount.isRounded b₁.numericType p₁ = false)
    (hp₂ : p₂.isNormalized) (hpos₂ : 0 < p₂.toRat) (hst₂ : STAmount.isRounded b₂.numericType p₂ = false)
    (hnt₁ : b₁.numericType = v.numericType) (hnt₂ : b₂.numericType = v.numericType)
    (hg₁ : Loan.CreateGrid b₁ v) (hg₂ : Loan.CreateGrid b₂ v)
    (h₁ : (Loan.create b₁ v p₁ ra₁ f₁ s₁ ao₁ pn₁).run = .ok (.ok r₁))
    (h₁₂ : (Loan.create b₂ r₁.pool' p₂ ra₂ f₂ s₂ ao₂ pn₂).run = .ok (.ok r₁₂))
    (h₂ : (Loan.create b₂ v p₂ ra₂ f₂ s₂ ao₂ pn₂).run = .ok (.ok r₂))
    (h₂₁ : (Loan.create b₁ r₂.pool' p₁ ra₁ f₁ s₁ ao₁ pn₁).run = .ok (.ok r₂₁)) :
    r₁₂.pool' = r₂₁.pool' ∧ r₂₁.loan'.broker = r₁.loan'.broker ∧ r₁₂.loan'.broker = r₂.loan'.broker := by
  have hbe₁ := Loan.create_baseExponent _ _ _ _ _ _ _ _ _ h₁
  have hbe₂ := Loan.create_baseExponent _ _ _ _ _ _ _ _ _ h₂
  -- after either create the vault is still on the base grid, and the other broker did not move
  have hg₁₂ : Loan.CreateGrid b₂ r₁.pool' := by
    obtain ⟨hroom, hyield⟩ := Loan.create_room _ _ _ _ _ _ _ _ _ hp₂ hpos₂ hst₂ h₁₂
    rw [hbe₁] at hroom hyield
    exact Loan.create_grid_next b₁ v p₁ ra₁ f₁ s₁ ao₁ pn₁ r₁ _ hp₁ hpos₁ hst₁ hnt₁ hg₁ h₁ hroom hyield
      hg₂.debtTotal
  have hg₂₁ : Loan.CreateGrid b₁ r₂.pool' := by
    obtain ⟨hroom, hyield⟩ := Loan.create_room _ _ _ _ _ _ _ _ _ hp₁ hpos₁ hst₁ h₂₁
    rw [hbe₂] at hroom hyield
    exact Loan.create_grid_next b₂ v p₂ ra₂ f₂ s₂ ao₂ pn₂ r₂ _ hp₂ hpos₂ hst₂ hnt₂ hg₂ h₂ hroom hyield
      hg₁.debtTotal
  refine ⟨creates_comm_vault v b₁ b₂ b₁ b₂ p₁ p₂ ra₁ ra₂ f₁ f₂ s₁ s₂ ao₁ ao₂ pn₁ pn₂ r₁ r₁₂ r₂ r₂₁ hp₁ hpos₁
    hst₁ hp₂ hpos₂ hst₂ rfl rfl rfl rfl hg₁ hg₂ hg₁₂ hg₂₁ h₁ h₁₂ h₂ h₂₁, ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, t₁⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₁ hpos₁ hst₁ hg₁ h₁
    obtain ⟨-, -, -, -, -, t₂₁⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₁ hpos₁ hst₁ hg₂₁ h₂₁
    have eDT : r₂₁.loan'.broker.debtTotal = r₁.loan'.broker.debtTotal :=
      r₂₁.loan'.broker.wf.debtTotal_norm.toRat_inj r₁.loan'.broker.wf.debtTotal_norm (by rw [t₂₁, t₁])
    apply broker_eq_of_raw
    rw [(Loan.create_record _ _ _ _ _ _ _ _ _ h₂₁).2, (Loan.create_record _ _ _ _ _ _ _ _ _ h₁).2, eDT]
  · obtain ⟨-, -, -, -, -, t₂⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₂ hpos₂ hst₂ hg₂ h₂
    obtain ⟨-, -, -, -, -, t₁₂⟩ := Loan.create_balances _ _ _ _ _ _ _ _ _ hp₂ hpos₂ hst₂ hg₁₂ h₁₂
    have eDT : r₁₂.loan'.broker.debtTotal = r₂.loan'.broker.debtTotal :=
      r₁₂.loan'.broker.wf.debtTotal_norm.toRat_inj r₂.loan'.broker.wf.debtTotal_norm (by rw [t₁₂, t₂])
    apply broker_eq_of_raw
    rw [(Loan.create_record _ _ _ _ _ _ _ _ _ h₁₂).2, (Loan.create_record _ _ _ _ _ _ _ _ _ h₂).2, eDT]

end XRPL.Model.Lending
