import XRPL.Properties.Vault.Proofs.DepositTight.DivExact
import XRPL.Properties.Vault.Proofs.DepositTight.Price
import XRPL.Properties.Vault.Proofs.DepositAccuracy
import XRPL.Properties.Vault.Common.Reduction

/-! # Sharp upper bound on the deposit share count -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc

/-- The issued shares are the floor of a value within `sharesOverε` relatively of the ideal share count. -/
private lemma shares_spec_exact (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hok : assetsToSharesDeposit v amount = .ok shares)
    (hnz : shares.isZero = false) :
    ∃ q : ℚ, shares.toRat = (⌊q⌋ : ℚ) ∧
      |q - v.idealSharesDepositAt navN.toRat amount.toRat| ≤
        v.idealSharesDepositAt navN.toRat amount.toRat * sharesOverε ∧
      0 < v.idealSharesDepositAt navN.toRat amount.toRat := by
  by_cases hmz : navN.mantissa_ = 0
  · -- empty vault: the shares are the floor of the exact ideal
    obtain ⟨-, hideal_pos, hshval⟩ := empty_shares_floor v amount shares hc hpos navN hat hmz hok hnz
    refine ⟨_, hshval, ?_, hideal_pos⟩
    rw [sub_self, abs_zero]
    exact mul_nonneg hideal_pos.le (by unfold sharesOverε; norm_num)
  · -- nonempty vault: `mul` then `div` round to nearest, then the floor
    obtain ⟨amountN, P, Q, T, hanval, hannorm, -, hnavnorm, -, hnav_pos, hSTm, hP, hPnorm, hPm,
      hQ, hQnorm, hQm, hQpos, hT, hTnorm, -, hTden, hsh⟩ :=
      deposit_nonempty_chain_facts v navN hat hmz amount shares hc hpos hok hnz
    have hS_pos : 0 < v.sharesTotal.toRat :=
      lt_of_le_of_ne v.wf.sharesTotal_nonneg (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero _ hSTm))
    set T0 : ℚ := v.sharesTotal.toRat * amount.toRat with hT0_def
    have hT0_pos : 0 < T0 := mul_pos hS_pos hpos
    have hideal : v.idealSharesDepositAt navN.toRat amount.toRat = T0 / navN.toRat := by
      unfold RawVault.idealSharesDepositAt
      rw [if_neg (ne_of_gt hnav_pos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, ← hT0_def]
    have hIpos : 0 < T0 / navN.toRat := div_pos hT0_pos hnav_pos
    -- the product stage
    have hPb : |P.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
      have h : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
          ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7)) :=
        operator_mul_rounds_to_nearest v.sharesTotal amountN P v.wf.sharesTotal_norm hannorm hP hPm
      rwa [hanval, ← hT0_def, abs_of_pos hT0_pos] at h
    obtain ⟨hPlo, hPhi⟩ := abs_le.mp hPb
    have hPpos : 0 < P.toRat := by nlinarith
    have hPN_pos : 0 < P.toRat / navN.toRat := div_pos hPpos hnav_pos
    have hVlo : T0 / navN.toRat * (1 - 5 / (2 ^ 63 + 7)) ≤ P.toRat / navN.toRat := by
      rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right (by linarith) hnav_pos.le
    have hVhi : P.toRat / navN.toRat ≤ T0 / navN.toRat * (1 + 5 / (2 ^ 63 + 7)) := by
      rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right (by linarith) hnav_pos.le
    -- the division stage
    have hQb : |Q.toRat - P.toRat / navN.toRat| ≤ P.toRat / navN.toRat * (5 / (2 ^ 63 + 7)) := by
      have h := operator_div_rounds_to_nearest_exact P navN Q hPnorm hnavnorm hQ hQm
      rwa [show (((2 ^ 63 + 7 : ℕ)) : ℚ) = 2 ^ 63 + 7 by push_cast; ring, abs_of_pos hPN_pos] at h
    obtain ⟨hQlo, hQhi⟩ := abs_le.mp hQb
    -- the two relative errors compound to `sharesOverε`
    have hover := mul_le_mul_of_nonneg_left (show (1 + 5 / (2 ^ 63 + 7)) * (1 + 5 / (2 ^ 63 + 7))
      ≤ (1 : ℚ) + sharesOverε by unfold sharesOverε; norm_num) hIpos.le
    -- floor and exact packing
    obtain ⟨hTval, -⟩ := Number.truncate_floor Q T hQnorm (Number.negative_false_of_pos Q hQpos) hT
    have hshval : shares.toRat = T.toRat :=
      STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide) hTnorm hTden hsh
    refine ⟨Q.toRat, by rw [hshval, hTval], ?_, by rw [hideal]; exact hIpos⟩
    rw [hideal, abs_le]
    constructor <;> linarith

end XRPL.Model.SingleAssetVault.DepTight

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc
open XRPL.Model.SingleAssetVault.DepTight

/-- Sharp share count bound. The issued shares are within `sharesOverε` relatively
of the ideal above, and less one whole share below. -/
lemma Vault.deposit_sharesCreated_upper_sharp_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (t : UInt32) (hcanon : amountDeposit.Canonical) (hposA : 0 < amountDeposit.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hrounded : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount))
    (r : VaultWithAmounts) (hok : (v.deposit amountDeposit false t hposA).run = .ok (.ok r)) :
    r.shares.toRat.den = 1 ∧ 0 ≤ r.shares.toRat ∧
    v.idealSharesDepositAt navN.toRat roundedAmount.toRat * (1 - sharesOverε) - 1 < r.shares.toRat ∧
    r.shares.toRat ≤ v.idealSharesDepositAt navN.toRat roundedAmount.toRat * (1 + sharesOverε) := by
  obtain ⟨ra, -, -, hra, hrc, hrp, hats, hsz, -⟩ :=
    DepAcc.Vault.deposit_success_reduces v amountDeposit t hposA hcanon r hok
  rw [hrounded, Except.ok.injEq, Except.ok.injEq] at hra
  subst hra
  obtain ⟨q, hqval, hqbound, hqpos⟩ :=
    shares_spec_exact v roundedAmount r.shares hrc hrp navN hat hats hsz
  rw [hqval]
  have hfl := Int.floor_le q
  have hfl2 := Int.sub_one_lt_floor q
  obtain ⟨hlo, hhi⟩ := abs_le.mp hqbound
  refine ⟨Rat.den_intCast _, ?_, ?_, ?_⟩
  · have hε1 : sharesOverε < 1 := by unfold sharesOverε; norm_num
    have hqpos' : 0 < q := by nlinarith
    have h0 : (0 : ℤ) ≤ ⌊q⌋ := Int.floor_nonneg.mpr (le_of_lt hqpos')
    exact_mod_cast h0
  · linarith
  · linarith

end XRPL.Model.SingleAssetVault
