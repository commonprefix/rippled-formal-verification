import XRPL.Properties.Lending.Loan.Common.ManageExits
import XRPL.Properties.Lending.Loan.Common.SetLawful

/-! # An impair succeeds when the vault has room

An impair only moves LossUnrealized. On a late loan it succeeds when the asset stores AssetsAvailable exactly,
and the new LossUnrealized stays between zero and AssetsDeployed. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- An amount the asset stores is below `10^96`. -/
lemma STAmount.Representable.lt_pow (nt : NumericType) (x : ℚ) (h : STAmount.Representable nt x) :
    x < 10 ^ 96 := by
  rcases h with rfl | h
  · norm_num
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨-, k, -, hk, rfl⟩ := h
    have : (k : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by exact_mod_cast hk
    have h2 : ((2 ^ 63 - 1 : ℕ) : ℚ) < 10 ^ 96 := by norm_num
    linarith
  | fractional =>
    obtain ⟨m, e, -, hm, -, he, rfl⟩ := h
    have hm' : (m : ℚ) ≤ 10 ^ 16 - 1 := by
      have : m ≤ 10 ^ 16 - 1 := by omega
      have h3 : ((10 ^ 16 - 1 : ℕ) : ℚ) = 10 ^ 16 - 1 := by norm_num
      rw [← h3]; exact_mod_cast this
    have he' : (10 : ℚ) ^ e ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) he
    have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    have h80 : (10 : ℚ) ^ (80 : ℤ) = 10 ^ 80 := by norm_num
    rw [h80] at he'
    calc (m : ℚ) * 10 ^ e ≤ (10 ^ 16 - 1) * 10 ^ 80 :=
          mul_le_mul hm' he' hp.le (by norm_num)
      _ < 10 ^ 96 := by norm_num

/-- AssetsDeployed is below `10^96`, as the asset stores it. -/
private lemma Vault.assetsDeployed_lt_pow (v : Vault) : v.assetsDeployed.toRat < 10 ^ 96 :=
  STAmount.Representable.lt_pow _ _ ((STAmount.isRounded_eq_false_iff _ _ v.wf.assetsDeployed_norm
    v.exact.assetsDeployed_nonneg).mp v.valid.assetsDeployed_representable)

/-- An update that moves no cash rounds AssetsAvailable without error to a value at least zero, when the asset
stores it exactly. -/
private lemma cash_zero_sum (v : Vault) (c : PoolBalanceChange) (hc : c.cash = Number.zero)
    (haa : STAmount.isRounded v.numericType v.assetsAvailable = false) :
    ∃ aa', (∃ aa, v.assetsAvailable.operator_add c.cash .to_nearest = .ok aa ∧
      STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa') ∧ 0 ≤ aa'.signum := by
  obtain ⟨aa', hround⟩ := STAmount.roundToNumericType_ok_of_isRounded_false _ _ haa
  refine ⟨aa', ⟨v.assetsAvailable, by rw [hc, Number.operator_add_zero_right], hround⟩, ?_⟩
  exact Number.signum_nonneg_of_toRat aa' (STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround)
    (STAmount.roundToNumericType_nonneg _ _ _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg hround)

variable (loan : Loan) (v : Vault) (now : UInt32)

/-- An impair of a late loan succeeds when AssetsDeployed has room for its principal. The asset stores
AssetsAvailable exactly, and LossUnrealized + PrincipalOutstanding is at most AssetsDeployed. -/
lemma Loan.manageImpair_ok_of_room (haa : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hlate : loan.nextPaymentDueDate < now)
    (hroom : v.lossUnrealized.toRat + loan.principalOutstanding.toRat ≤ v.assetsDeployed.toRat) :
    ∃ r, (loan.manageImpair v now).run = .ok (.ok r) := by
  have hpn := loan.wf.principalOutstanding_norm
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hln := v.wf.lossUnrealized_norm
  have hl0 : 0 ≤ v.lossUnrealized.toRat := v.exact.lossUnrealized_nonneg
  have had := Vault.assetsDeployed_lt_pow v
  obtain ⟨lu', hsum⟩ := Number.operator_add_ok_of_lt v.lossUnrealized loan.principalOutstanding .to_nearest hln
    hpn hl0 (by linarith) hp0 (by linarith)
  have hlun := operator_add_isNormalized_to_nearest_sz _ _ _ hln hpn hsum
  have hlu0 : 0 ≤ lu'.toRat := operator_add_nonneg _ _ _ hln hpn hsum (by linarith)
  have hluv : lu'.toRat ≤ v.assetsDeployed.toRat :=
    operator_add_le_of_le_normalized _ _ _ _ hln hpn hsum v.wf.assetsDeployed_norm hroom
  obtain ⟨aa', hcash, haa0⟩ := cash_zero_sum v { loss := loan.principalOutstanding } rfl haa
  have hs : Vault.AdjustSums v { loss := loan.principalOutstanding } aa' v.assetsDeployed lu'
      v.assetsReserved v.yieldUnrealized :=
    ⟨hcash, Number.operator_add_zero_right _ _, hsum, Number.operator_add_zero_right _ _,
      Number.operator_add_zero_right _ _⟩
  have hle : lu'.operator_gt v.assetsDeployed = false := by
    unfold Number.operator_gt
    exact (operator_lt_eq_false_iff _ _ v.wf.assetsDeployed_norm hlun).mpr hluv
  have hadj := Vault.adjustBalances_ok v _ _ _ _ _ _ hs
    ⟨haa0, Number.signum_nonneg_of_toRat _ v.wf.assetsDeployed_norm v.exact.assetsDeployed_nonneg,
      Number.signum_nonneg_of_toRat _ hlun hlu0,
      Number.signum_nonneg_of_toRat _ v.wf.yieldUnrealized_norm v.exact.yieldUnrealized_nonneg,
      Number.signum_nonneg_of_toRat _ v.wf.assetsReserved_norm v.exact.assetsReserved_nonneg⟩ hle
  obtain ⟨v', loan', hok, -⟩ := Loan.manageImpair_success_proof loan v now _ hlate hadj
  exact ⟨_, hok⟩

end XRPL.Model.Lending
