import XRPL.Properties.Vault.Proofs.Support.DepositExchange
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Support.NavUnderflow
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.Nearest

/-! # Withdrawal exchange of shares for assets

The net asset value a withdrawal prices against is nonnegative, so the shares it burns are a
positive canonical MPT amount, whether named directly or priced from an asset amount. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The net asset value a withdrawal prices against is nonnegative, and normalized. The loss it
subtracts never exceeds the deployed assets the total covers. -/
lemma Vault.assetsTotalForWithdrawal_nonneg (v : Vault) (waive : Bool) (nav : Number)
    (h : v.assetsTotalForWithdrawal waive = .ok nav) : nav.isNormalized ∧ 0 ≤ nav.toRat := by
  simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind] at h
  cases hat : v.assetsTotal with
  | error e => rw [hat] at h; cases h
  | ok assetsTotal =>
    rw [hat] at h
    dsimp only at h
    obtain ⟨hatn, hge⟩ := Vault.assetsTotal_ge_deployed v assetsTotal hat
    have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
    cases waive
    · have hLU : v.lossUnrealized.toRat ≤ v.assetsDeployed.toRat := v.exact.lossUnrealized_le
      exact ⟨operator_sub_isNormalized_to_nearest_sz _ _ _ hatn v.wf.lossUnrealized_norm h,
        operator_sub_nonneg _ _ _ hatn v.wf.lossUnrealized_norm h (by linarith)⟩
    · rw [Number.operator_sub_zero] at h
      obtain rfl := Except.ok.inj h
      exact ⟨hatn, by linarith⟩

/-- The net asset value a withdrawal prices against. The total is the cash plus the deployed assets rounded
down, and the net asset value is that total less the loss (nothing when waived) rounded to the nearest Number. -/
lemma Vault.assetsTotalForWithdrawal_steps_proof (v : Vault) (waive : Bool) (nav : Number)
    (h : v.assetsTotalForWithdrawal waive = .ok nav) :
    ∃ total : Number, v.assetsTotal = .ok total ∧
      total.RoundsToRepresentable (v.assetsAvailable.toRat + v.assetsDeployed.toRat) .downward ∧
      nav.RoundsToRepresentable (total.toRat - (if waive then 0 else v.lossUnrealized.toRat)) .to_nearest ∧
      nav.RoundsToNearest (total.toRat - (if waive then 0 else v.lossUnrealized.toRat)) := by
  simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind] at h
  cases hat : v.assetsTotal with
  | error e => rw [hat] at h; cases h
  | ok total =>
    rw [hat] at h
    dsimp only at h
    obtain ⟨htn, -⟩ := Vault.assetsTotal_ge_deployed v total hat
    refine ⟨total, rfl, ?_, ?_, ?_⟩
    · by_cases hm : total.mantissa_ = 0
      · -- an empty total: the exact sum is zero too
        have h0 := (Vault.assetsTotal_eq_zero_iff v total hat).mp hm
        have hs0 : v.assetsAvailable.toRat + v.assetsDeployed.toRat = 0 := h0
        rw [hs0]
        refine ⟨Number.zero, by unfold Number.lower; simp, ?_⟩
        rw [Number.toRat_eq_zero_of_mantissa_zero total hm, Number.toRat_zero]
      · have hr := operator_add_rounded_downward _ _ _ v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm
          (show v.assetsAvailable.operator_add v.assetsDeployed .downward = .ok total from hat) hm
        exact hr
    · cases waive
      · simpa using operator_sub_rounded_to_nearest _ _ _ htn v.wf.lossUnrealized_norm h
      · have h' := operator_sub_rounded_to_nearest _ _ _ htn (Or.inl rfl) h
        simpa [Number.toRat_zero] using h'
    · cases waive
      · -- a zero result is an exact zero, the subtraction never flushes on a lawful vault
        have hLU0 : 0 ≤ v.lossUnrealized.toRat := v.exact.lossUnrealized_nonneg
        have hLU : v.lossUnrealized.toRat ≤ v.assetsDeployed.toRat := v.exact.lossUnrealized_le
        have hn := Number.operator_sub_nearest _ _ _ htn v.wf.lossUnrealized_norm h (by
          by_cases h0 : nav.mantissa_ = 0
          · exact Or.inr (Vault.assetsTotal_sub_zero_exact v total _ nav hat v.wf.lossUnrealized_norm hLU0 hLU h h0)
          · exact Or.inl h0)
        simpa using hn
      · rw [Number.operator_sub_zero] at h
        obtain rfl := Except.ok.inj h
        exact Number.roundsToNearest_of_eq (by simp)

/-- The shares a withdrawal by assets burns are positive when nonzero. It prices a nonnegative
canonical-or-zero amount against a nonnegative net asset value and truncates. -/
lemma assetsToSharesWithdraw_pos (v : Vault) (amount shares : STAmount) (waive : Bool)
    (hc : amount.CanonicalOrZero) (hnn : 0 ≤ amount.toRat)
    (hok : assetsToSharesWithdraw v amount true waive = .ok shares) (hnz : shares.isZero = false) :
    0 < shares.toRat := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  have hne0 : shares.toRat ≠ 0 := STAmount.toRat_ne_zero shares hmv
  suffices h : 0 ≤ shares.toRat from lt_of_le_of_ne h (Ne.symm hne0)
  unfold assetsToSharesWithdraw at hok
  obtain ⟨navN, hnav, hok⟩ := bind_ok_peel _ _ _ hok
  dsimp only at hok
  by_cases hmz : navN.mantissa_ = 0
  · -- a zero net asset value burns no shares
    rw [if_pos (by simp [hmz])] at hok
    obtain rfl := Except.ok.inj hok
    exact absurd hnz (by decide)
  rw [if_neg (by simp [hmz])] at hok
  obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨T0, hT0, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨T, hT, hsh⟩ := bind_ok_peel _ _ _ hok
  have hTm : T.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
  have hT0m : T0.mantissa_ ≠ 0 := Number.truncate_source_ne_zero T0 T hT hTm
  obtain ⟨hnavnorm, hnavnn⟩ := Vault.assetsTotalForWithdrawal_nonneg v waive navN hnav
  have hnavpos : 0 < navN.toRat :=
    lt_of_le_of_ne hnavnn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero navN hmz))
  have hPm : P.mantissa_ ≠ 0 :=
    operator_div_numerator_ne_zero_sz P navN T0 .to_nearest
      (Number.not_operator_eq_zero_of_mantissa_ne hmz) hT0 hT0m
  obtain ⟨hanval, hannorm⟩ := hc.toNumber_exact amountN hamN
  obtain ⟨hSTm, hanm⟩ := operator_mul_operands_ne_zero v.wf.sharesTotal_norm hannorm hP hPm
  have hPnorm : P.isNormalized :=
    operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
      v.wf.sharesTotal_norm hannorm hSTm hanm hP hPm
  have hT0norm : T0.isNormalized :=
    operator_div_result_isNormalized P navN T0 .to_nearest hPnorm hnavnorm hPm hmz hT0 hT0m
  have hann : 0 ≤ amountN.toRat := by rw [hanval]; exact hnn
  have hSTnn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
  have hPnn : 0 ≤ P.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
    (operator_mul_rounded_to_nearest _ _ _ v.wf.sharesTotal_norm hannorm hP) (mul_nonneg hSTnn hann)
  have hT0nn : 0 ≤ T0.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
    (operator_div_rounded_to_nearest _ _ _ hPnorm hnavnorm hT0) (div_nonneg hPnn (le_of_lt hnavpos))
  have hT0pos : 0 < T0.toRat :=
    lt_of_le_of_ne hT0nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero T0 hT0m))
  obtain ⟨hTval, hTnorm⟩ :=
    Number.truncate_floor T0 T hT0norm (Number.negative_false_of_pos T0 hT0pos) hT
  have hshval : shares.toRat = T.toRat :=
    STAmount.ofNumber_integral_exact .int64 T .to_nearest shares (by decide)
      (hTnorm hTm) (by rw [hTval]; exact Rat.den_intCast _) hsh
  rw [hshval, hTval]
  exact_mod_cast Int.floor_nonneg.mpr hT0nn

/-- The shares of a truncating `assetsToSharesWithdraw` of a nonnegative amount are nonnegative. -/
lemma assetsToSharesWithdraw_nonneg (v : Vault) (amount shares : STAmount) (waive : Bool)
    (hc : amount.CanonicalOrZero) (hnn : 0 ≤ amount.toRat)
    (hok : assetsToSharesWithdraw v amount true waive = .ok shares) : 0 ≤ shares.toRat := by
  by_cases hz : shares.isZero = true
  · exact le_of_eq ((STAmount.toRat_eq_zero_iff _).mpr (by simpa [STAmount.isZero] using hz)).symm
  · exact le_of_lt (assetsToSharesWithdraw_pos v amount shares waive hc hnn hok (by simpa using hz))

/-- The assets a share count is worth at withdrawal are nonnegative. -/
lemma Vault.sharesToAssetsWithdraw_nonneg (v : Vault) (shares assets : STAmount) (waive : Bool)
    (hc : shares.CanonicalOrZero) (hnn : 0 ≤ shares.toRat)
    (hok : v.sharesToAssetsWithdraw shares waive = .ok assets) : 0 ≤ assets.toRat := by
  simp only [Vault.sharesToAssetsWithdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  -- a zero net asset value pays zero
  · exact (STAmount.zero_toRat _).ge
  -- otherwise the net asset value times the shares, over the share total
  · have hnav : v.assetsTotalForWithdrawal waive = .ok _ := ‹_›
    have hsn : shares.toNumber .to_nearest = .ok _ := ‹_›
    have hmul : Number.operator_mul _ _ .to_nearest = .ok _ := ‹_›
    have hdiv : Number.operator_div _ v.sharesTotal .to_nearest = .ok _ := ‹_›
    have hof : STAmount.ofNumber v.numericType _ .to_nearest = .ok _ := ‹_›
    obtain ⟨hnavn, hnav0⟩ := Vault.assetsTotalForWithdrawal_nonneg v waive _ hnav
    obtain ⟨hsv, hsnorm⟩ := hc.toNumber_exact _ hsn
    have hNSn := Number.operator_mul_isNormalized _ _ _ _ hnavn hsnorm hmul
    have hNS0 := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
      (operator_mul_rounded_to_nearest _ _ _ hnavn hsnorm hmul) (mul_nonneg hnav0 (by rw [hsv]; exact hnn))
    have hann := Number.operator_div_isNormalized _ _ _ _ hNSn v.wf.sharesTotal_norm hdiv
    have han0 := Number.RoundsToRepresentable.nonneg_of_nonneg _ _
      (operator_div_rounded_to_nearest _ _ _ hNSn v.wf.sharesTotal_norm hdiv)
      (div_nonneg hNS0 v.wf.sharesTotal_nonneg)
    exact STAmount.ofNumber_nonneg _ _ _ _ hann (Number.negative_false_of_nonneg _ hann han0) hof

/-- The shares of `assetsToSharesWithdraw` pack through `ofNumber .int64`: a canonical `int64` record. -/
lemma assetsToSharesWithdraw_int64_canonical (v : Vault) (amount shares : STAmount) (t w : Bool)
    (hok : assetsToSharesWithdraw v amount t w = .ok shares) :
    shares.IntegralCanonical ∧ shares.mNumericType = .int64 := by
  simp only [assetsToSharesWithdraw, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | exact ⟨zero_int64_IntegralCanonical, STAmount.zero_mNumericType _⟩
    | exact STAmount.ofNumber_integral_canonical .int64 _ .to_nearest shares (by decide) ‹_›

/-- The shares a withdrawal burns are a positive canonical MPT amount. -/
lemma computeWithdraw_shares_form (v : Vault) (amount : WithdrawAmount) (w : Bool) (amounts : VaultAmounts)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType) (hpos : 0 < amount.amount.toRat)
    (hcomp : (computeWithdraw v amount w).run = .ok (.ok amounts)) :
    amounts.shares.IntegralCanonical ∧ amounts.shares.mNumericType = .int64 ∧ 0 < amounts.shares.toRat := by
  simp only [computeWithdraw] at hcomp
  unfold_ter at hcomp
  walk_ok
  all_goals simp only [WithdrawAmount.amount, WithdrawAmount.InAsset] at hc hty hpos
  -- by shares: the named shares
  · exact ⟨(hc.1 (by simp only [STAmount.integral, hty]; decide)).1, hty, hpos⟩
  -- by assets: the truncated priced shares, nonzero
  · have ha2s : assetsToSharesWithdraw v _ true w = .ok _ := ‹_›
    obtain ⟨hic, hint⟩ := assetsToSharesWithdraw_int64_canonical v _ _ true w ha2s
    exact ⟨hic, hint, assetsToSharesWithdraw_pos v _ _ w (Or.inl hc) hpos.le ha2s
      (by simpa using ‹¬ _ = true›)⟩

/-- The shares a successful withdrawal burns are a positive canonical MPT amount. -/
lemma Vault.withdraw_shares_form (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.shares.IntegralCanonical ∧ r.shares.mNumericType = .int64 ∧ 0 < r.shares.toRat := by
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals
    have hcomp : (computeWithdraw v amount waive).run = .ok (.ok _) := ‹_›
    have h := computeWithdraw_shares_form v amount waive _ hc hty hpos hcomp
    exact h

end XRPL.Model.SingleAssetVault
