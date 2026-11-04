import XRPL.Properties.Vault.Proofs.DepositTight.LowerExact
import XRPL.Properties.Vault.Proofs.DepositTight.Charge
import XRPL.Properties.Vault.Common.Reduction

/-! # The shortfall side of the deposit share count under the mint cap -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc

/-- A value on the grid `10^E` floors to within `1 - d·10^E` of itself when every grid point above it
sits at least `d` steps above it. -/
private lemma grid_floor (q : ℚ) (k : ℕ) (E : ℤ) (d : ℤ) (hE : E ≤ 0) (hq : q = (k : ℚ) * 10 ^ E)
    (hk : ∀ N : ℤ, (k : ℤ) < N * 10 ^ (-E).toNat → (k : ℤ) ≤ N * 10 ^ (-E).toNat - d) :
    q - 1 + d * 10 ^ E ≤ (⌊q⌋ : ℚ) := by
  set j := (-E).toNat
  have hj : E = -(j : ℤ) := by omega
  have hpow : (10 : ℚ) ^ E = 1 / 10 ^ j := by rw [hj, zpow_neg, zpow_natCast, one_div]
  have h10 : (0 : ℚ) < 10 ^ j := by positivity
  have hq10 : q * 10 ^ j = ((k : ℤ) : ℚ) := by rw [hq, hpow]; push_cast; field_simp
  have hk1 : (k : ℤ) < (⌊q⌋ + 1) * 10 ^ j := by
    have : ((k : ℤ) : ℚ) < ((⌊q⌋ : ℚ) + 1) * 10 ^ j := by
      rw [← hq10]; exact mul_lt_mul_of_pos_right (Int.lt_floor_add_one q) h10
    exact_mod_cast this
  have hk2 : ((k : ℤ) : ℚ) ≤ ((⌊q⌋ : ℚ) + 1) * 10 ^ j - d := by exact_mod_cast hk _ hk1
  have key : (q - 1 + d * 10 ^ E) * 10 ^ j ≤ (⌊q⌋ : ℚ) * 10 ^ j := by
    have : (q - 1 + d * 10 ^ E) * 10 ^ j = q * 10 ^ j - 10 ^ j + d := by rw [hpow]; field_simp
    rw [this, hq10]; linarith
  exact le_of_mul_le_mul_right key h10

set_option maxHeartbeats 1600000 in
-- Long case analysis over the quotient's grid, in one declaration.
/-- Under the mint cap the issued shares fall short of the ideal by less than one share plus `4879·10⁻²²`
relatively: the `.to_nearest` quotient lands at most half a grid step below the exact value. -/
private lemma shares_lower_mint (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat) (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hok : assetsToSharesDeposit v amount = .ok shares)
    (hnz : shares.isZero = false)
    (hmint : v.sharesTotal.toRat + shares.toRat ≤ 9223372036854775807) :
    v.idealSharesDepositAt navN.toRat amount.toRat * (1 - 4879 / 10 ^ 22) - 1 < shares.toRat := by
  by_cases hmz : navN.mantissa_ = 0
  · -- empty vault: the shares are the floor of the exact ideal
    obtain ⟨-, hideal_pos, hshval⟩ := empty_shares_floor v amount shares hc hpos navN hat hmz hok hnz
    rw [hshval]
    have hfl := Int.sub_one_lt_floor (v.idealSharesDepositAt navN.toRat amount.toRat)
    nlinarith [hideal_pos]
  · -- nonempty vault: `mul` then `div` round to nearest, then the floor
    obtain ⟨amountN, P, Q, T, hanval, hannorm, -, hnavnorm, -, hnav_pos, -, hP, hPnorm, hPm,
      hQ, hQnorm, hQm, hQpos, hT, hTnorm, -, hTden, hsh⟩ :=
      deposit_nonempty_chain_facts v navN hat hmz amount shares hc hpos hok hnz
    have hS_one : 1 ≤ v.sharesTotal.toRat := Vault.sharesTotal_one_le v navN hat hmz
    have hS_pos : 0 < v.sharesTotal.toRat := by linarith
    set T0 : ℚ := v.sharesTotal.toRat * amount.toRat with hT0_def
    have hT0_pos : 0 < T0 := mul_pos hS_pos hpos
    have hPb : |P.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
      have h : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
          ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7)) :=
        operator_mul_rounds_to_nearest v.sharesTotal amountN P v.wf.sharesTotal_norm hannorm hP hPm
      rwa [hanval, ← hT0_def, abs_of_pos hT0_pos] at h
    have hPlo := (abs_le.mp hPb).1
    have hPpos : 0 < P.toRat := by nlinarith
    have hPN_pos : 0 < P.toRat / navN.toRat := div_pos hPpos hnav_pos
    have hideal : v.idealSharesDepositAt navN.toRat amount.toRat = T0 / navN.toRat := by
      unfold RawVault.idealSharesDepositAt
      rw [if_neg (ne_of_gt hnav_pos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, ← hT0_def]
    obtain ⟨hTval, -⟩ := Number.truncate_floor Q T hQnorm (Number.negative_false_of_pos Q hQpos) hT
    have hshval : shares.toRat = T.toRat :=
      STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide) hTnorm hTden hsh
    have hlow := operator_div_lower_exact P navN Q hPnorm hnavnorm hQ hQm
    rw [abs_of_pos hPN_pos, abs_of_pos hQpos] at hlow
    rw [hshval, hTval] at hmint ⊢
    rw [hideal]
    set A := navN.toRat
    set I := T0 / A with hI_def
    have hVlo : I * (1 - 5 / (2 ^ 63 + 7)) ≤ P.toRat / A := by
      rw [hI_def, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hnav_pos)
    set V := P.toRat / A
    set q := Q.toRat
    have hfl := Int.sub_one_lt_floor q
    have hbad : ∀ X : ℚ, 9223372036854775807 ≤ X → X ≤ q → False := by
      intro X hX hXq; linarith
    have hclose : ∀ γ t B : ℚ, 0 < γ → V ≤ B * γ → V - ⌊q⌋ ≤ 1 - t * γ →
        B * (5 / (2 ^ 63 + 7) - 4879 / 10 ^ 22) < t * (1 - 5 / (2 ^ 63 + 7)) →
        I * (1 - 4879 / 10 ^ 22) - 1 < ⌊q⌋ := by
      intro γ t B hγ hVB hs hc
      have h2 : B * (5 / (2 ^ 63 + 7) - 4879 / 10 ^ 22) * γ
          < t * (1 - 5 / (2 ^ 63 + 7)) * γ := mul_lt_mul_of_pos_right hc hγ
      linarith
    have hp10 : ∀ E : ℤ, 1 ≤ E → (10 : ℚ) ≤ 10 ^ E := fun E hE => by
      calc (10 : ℚ) = 10 ^ (1 : ℤ) := by norm_num
        _ ≤ 10 ^ E := zpow_le_zpow_right₀ (by norm_num) hE
    have hp1 : ∀ E : ℤ, 0 ≤ E → (1 : ℚ) ≤ 10 ^ E := fun E hE => one_le_zpow₀ (by norm_num) hE
    rcases hlow with ⟨hVq, E, n, hn1, hn2, hn10, hqn⟩ | ⟨E, m, hm, hqm, hVlt, hcase⟩ |
        ⟨E, hqE, hVE⟩
    · by_cases hnr : n ≤ 9223372036854775807
      · have hE : E ≤ 0 := by
          by_contra hE
          have h := hp10 E (by omega)
          have hn' : (10 : ℚ) ^ 18 ≤ n := by exact_mod_cast hn1
          exact hbad (10 ^ 18 * 10) (by norm_num) (by rw [hqn]; nlinarith)
        have hfg := grid_floor q n E 1 hE hqn (fun N h => by omega)
        have hγ : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
        have hnq : (n : ℚ) ≤ 9223372036854775807 := by exact_mod_cast hnr
        refine hclose (10 ^ E) 1 9223372036854775807 hγ ?_ ?_ (by norm_num)
        · rw [hqn] at hVq; nlinarith
        · push_cast at hfg; linarith
      · obtain ⟨n', rfl⟩ : ∃ n', n = 10 * n' := ⟨n / 10, by have := hn10 (by omega); omega⟩
        have hqn' : q = (n' : ℚ) * 10 ^ (E + 1) := by
          rw [hqn, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; push_cast; ring
        have hE : E + 1 ≤ 0 := by
          by_contra hE
          have h := hp1 E (by omega)
          have hn' : (9223372036854775808 : ℚ) ≤ ((10 * n' : ℕ) : ℚ) := by
            exact_mod_cast (by omega : 9223372036854775808 ≤ 10 * n')
          exact hbad ((10 * n' : ℕ) : ℚ) (by linarith)
            (by rw [hqn]; exact le_mul_of_one_le_right (by positivity) h)
        have hfg := grid_floor q n' (E + 1) 1 hE hqn' (fun N h => by omega)
        have hγ : (0 : ℚ) < 10 ^ (E + 1) := zpow_pos (by norm_num) _
        have hnq : (n' : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (by omega : n' ≤ 9223372036854775807)
        refine hclose (10 ^ (E + 1)) 1 9223372036854775807 hγ ?_ ?_ (by norm_num)
        · rw [hqn'] at hVq; nlinarith
        · push_cast at hfg; linarith
    · have hγ : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
      rcases hcase with ⟨hVh, hmr⟩ | rfl | rfl
      · have hE : E ≤ 0 := by
          by_contra hE
          have h := hp10 E (by omega)
          have hm' : (922337203685477581 : ℚ) ≤ m := by exact_mod_cast hm
          exact hbad (922337203685477581 * 10) (by norm_num) (by rw [hqm]; nlinarith)
        have hfg := grid_floor q m E 1 hE hqm (fun N h => by omega)
        have hmq : (m : ℚ) ≤ 9223372036854775807 := by exact_mod_cast hmr
        refine hclose (10 ^ E) (1 / 2) (9223372036854775807 + 1 / 2) hγ ?_ ?_ (by norm_num)
        · nlinarith
        · push_cast at hfg; linarith
      · have hE : E ≤ -1 := by
          by_contra hE
          have h := hp1 E (by omega)
          exact hbad 9223372036854775807 (le_refl _) (by rw [hqm]; push_cast; nlinarith)
        have hfg := grid_floor q _ E 3 (by omega) hqm (fun N h => by
          obtain ⟨i, hi⟩ : ∃ i, (-E).toNat = i + 1 := ⟨(-E).toNat - 1, by omega⟩
          rw [hi, pow_succ, show N * (10 ^ i * 10) = N * 10 ^ i * 10 by ring] at h ⊢
          generalize N * 10 ^ i = X at h ⊢
          push_cast at h ⊢
          omega)
        refine hclose (10 ^ E) 2 (9223372036854775807 + 1) hγ ?_ ?_ (by norm_num)
        · push_cast at hVlt; linarith
        · push_cast at hfg hVlt hqm; linarith
      · have hE : E ≤ -1 := by
          by_contra hE
          have h := hp1 E (by omega)
          exact hbad 9223372036854775810 (by norm_num) (by rw [hqm]; push_cast; nlinarith)
        have hfg := grid_floor q _ E 10 (by omega) hqm (fun N h => by
          obtain ⟨i, hi⟩ : ∃ i, (-E).toNat = i + 1 := ⟨(-E).toNat - 1, by omega⟩
          rw [hi, pow_succ, show N * (10 ^ i * 10) = N * 10 ^ i * 10 by ring] at h ⊢
          generalize N * 10 ^ i = X at h ⊢
          push_cast at h ⊢
          omega)
        refine hclose (10 ^ E) 9 (9223372036854775810 + 1) hγ ?_ ?_ (by norm_num)
        · push_cast at hVlt; linarith
        · push_cast at hfg hVlt hqm; linarith
    · have hγ : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
      have hE : E ≤ -1 := by
        by_contra hE
        have h := hp1 E (by omega)
        exact hbad 9223372036854775807 (le_refl _) (by rw [hqE]; nlinarith)
      have hfg := grid_floor q 9223372036854775807 E 3 (by omega) (by rw [hqE]; push_cast; ring)
        (fun N h => by
          obtain ⟨i, hi⟩ : ∃ i, (-E).toNat = i + 1 := ⟨(-E).toNat - 1, by omega⟩
          rw [hi, pow_succ, show N * (10 ^ i * 10) = N * 10 ^ i * 10 by ring] at h ⊢
          generalize N * 10 ^ i = X at h ⊢
          push_cast at h ⊢
          omega)
      refine hclose (10 ^ E) (3 / 2) (9223372036854775808 + 1 / 2) hγ hVE ?_ (by norm_num)
      push_cast at hfg; linarith

end XRPL.Model.SingleAssetVault.DepTight

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

/-- Sharp shortfall of the share count under the mint cap. With the issued shares fitting the `maxRep`
cap, they fall short of the ideal by less than one share plus `4879·10⁻²²` relatively. -/
lemma Vault.deposit_sharesIssued_lower_mint_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (t : UInt32) (hcanon : amountDeposit.Canonical) (hposA : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hposA).run = .ok (.ok r))
    (hmint : v.sharesTotal.toRat + r.shares.toRat ≤ maxRep.toNat) :
    v.idealSharesDepositAt navN.toRat roundedAmount.toRat * (1 - 4879 / 10 ^ 22) - 1 < r.shares.toRat := by
  obtain ⟨ra, -, -, hra, hrc, hrp, hats, hsz, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hposA hcanon r hok
  rw [hrounded, Except.ok.injEq, Except.ok.injEq] at hra
  subst hra
  rw [maxRep_val] at hmint
  exact shares_lower_mint v roundedAmount r.shares hrc hrp navN hat hats hsz (by exact_mod_cast hmint)

end XRPL.Model.SingleAssetVault
