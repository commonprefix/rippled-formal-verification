import XRPL.Properties.Vault.Proofs.WithdrawExits
import XRPL.Properties.Vault.Proofs.AssociateAssetPreserve
import XRPL.Properties.Vault.Proofs.Support.GridFloor
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent

/-! # The vault update a withdrawal makes

A withdrawal subtracts its payout from the cash and its burned shares from the share total. A final
withdrawal pays out all the cash. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A non-final withdrawal pays nothing, or pays through the fee: it prices the burned shares, takes
the fee from that rounding up, rounds the rest down into the asset and clamps it onto the grid of the cash left. -/
lemma Vault.withdraw_payout_cases (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) :
    ∃ priced : STAmount, v.sharesToAssetsWithdraw r.shares waive = .ok priced ∧
      ((r.assets.toRat = 0 ∧ (v.earlyExitFeeRateAt t = maxEarlyExitFeeRate ∨ priced.toRat = 0)) ∨
        ∃ (pricedNumber fee payoutNumber paidNumber : Number) (payout : STAmount),
          v.earlyExitFeeRateAt t ≠ maxEarlyExitFeeRate ∧
          priced.toNumber .to_nearest = .ok pricedNumber ∧
          tenthBipsOfValue pricedNumber (v.earlyExitFeeRateAt t) .upward = .ok fee ∧
          pricedNumber.operator_sub fee .downward = .ok payoutNumber ∧
          STAmount.ofNumber v.numericType payoutNumber .downward = .ok payout ∧
          payout.isZero = false ∧
          clampToSumExponent v.assetsAvailable payout.operator_neg v.baseExponent = .ok r.assets ∧
          r.assets.isFractionalNonPositive = .ok false ∧
          r.assets.toNumber .to_nearest = .ok paidNumber ∧
          v.assetsAvailable.operator_lt paidNumber = false) := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals dsimp only at hlt hsic hs64 hspos ⊢
  -- the run is not final
  all_goals
    have hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok _ := ‹_›
    have hnf : ¬ STAmount.operator_eq _ _ = true :=
      (Vault.isFinalWithdrawal_iff v _ _ hsic hs64 hspos hst).not.mpr (ne_of_lt hlt)
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  all_goals
    have hcomp : (computeWithdraw v amount waive).run = .ok (.ok _) := ‹_›
    refine ⟨_, computeWithdraw_ok_priced v amount waive _ hcomp, ?_⟩
  · -- a 100% fee pays nothing
    have hmaxr : (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = true := ‹_›
    exact Or.inl ⟨STAmount.zero_toRat _, Or.inl (beq_iff_eq.mp hmaxr)⟩
  · -- the last check passed: the clamped payout is not a nonpositive fractional amount
    have hfnp0 : STAmount.isFractionalNonPositive _ = .ok _ := ‹_›
    have hfnp := hfnp0.trans (congrArg Except.ok (show _ = false by assumption))
    have hlow : (v.earlyExitFeeRateAt t == maxEarlyExitFeeRate) = false := ‹_›
    exact Or.inr ⟨_, _, _, _, _, fun h => by rw [h] at hlow; exact absurd hlow (by decide),
      ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hfnp, ‹_›, ‹_›⟩
  · -- a zero priced amount pays nothing
    have hnz : ¬ (_ = false ∧ STAmount.isZero _ = false) := ‹_›
    simp only [hnf, true_and, Bool.not_eq_false] at hnz
    unfold STAmount.isZero at hnz
    have h0 := (STAmount.toRat_eq_zero_iff _).mpr (by simpa using hnz)
    exact Or.inl ⟨h0, Or.inr h0⟩

/-- A passed dust check converts the cash into the asset: the check reads the cash as an amount
before it compares, so a failed conversion would refuse the debit. -/
lemma Vault.checkDebitNotDust_converts (v : Vault) (n : Number) (hn : n.operator_eq Number.zero = false)
    (h : v.checkDebitNotDust n = .ok .tesSUCCESS) :
    ∃ c, STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok c := by
  simp only [Vault.checkDebitNotDust, hn, Bool.false_eq_true, if_false, bind, Except.bind, pure, Except.pure,
    tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at h
  walk_ok
  all_goals exact ⟨_, ‹_›⟩

/-- A converted cash of a whole-number asset is below `2^63`: the amount stays within the type's
maximum, and the conversion moves the cash by at most half a unit. -/
lemma Vault.cash_lt_of_converts (v : Vault) (hint : v.numericType.isIntegral = true)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat) (c : STAmount)
    (hc : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok c) :
    v.assetsAvailable.toRat < 2 ^ 63 := by
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hhalf := STAmount.ofNumber_integral_within_half _ _ _ hint v.wf.assetsAvailable_norm
    (Number.negative_false_of_nonneg _ v.wf.assetsAvailable_norm hAA0) hc
  obtain ⟨hic, hct⟩ := STAmount.ofNumber_integral_canonical _ _ _ _ hint hc
  have hcle : c.toRat ≤ 2 ^ 63 - 1 := by
    have hrange := hic.in_range
    rw [hct] at hrange
    have hm := hmax hint
    have hmr : maxRep.toNat = 2 ^ 63 - 1 := by decide
    have hv : c.mValue.toNat ≤ 2 ^ 63 - 1 := by omega
    have hv' : (c.mValue.toNat : ℚ) ≤ 2 ^ 63 - 1 := by
      have : ((c.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by exact_mod_cast hv
      norm_num at this ⊢
      linarith
    have habs := STAmount.abs_toRat c
    rw [hic.offset_zero, zpow_zero, mul_one] at habs
    linarith [le_abs_self c.toRat]
  have := abs_le.mp hhalf
  linarith

/-- A dust-check code that is not unequal to `tesSUCCESS` is `tesSUCCESS`. -/
lemma ter_success_of_bne (d : TER) (h : (d != TER.tesSUCCESS) = false) : d = .tesSUCCESS := by
  cases d <;> first | rfl | exact absurd h (by decide)

/-- A non-final withdrawal that pays something passes the dust check on a nonzero amount. -/
lemma Vault.withdraw_paid_dust (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hlt : r.shares.toRat < v.toExact.sharesTotal) (hpay : 0 < r.assets.toRat) :
    ∃ n : Number, n.operator_eq Number.zero = false ∧ v.checkDebitNotDust n = .ok .tesSUCCESS := by
  obtain ⟨hsic, hs64, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  simp only [Vault.withdraw] at hok
  unfold_ter at hok
  walk_ok
  all_goals dsimp only at hlt hsic hs64 hspos hpay ⊢
  all_goals
    have hst : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok _ := ‹_›
    have hnf : ¬ STAmount.operator_eq _ _ = true :=
      (Vault.isFinalWithdrawal_iff v _ _ hsic hs64 hspos hst).not.mpr (ne_of_lt hlt)
  all_goals try (simp only [Bool.not_eq_true', Bool.not_eq_true, Bool.and_eq_true] at *)
  all_goals try (exfalso; simp_all; done)
  -- the dust check ran on the priced amount, which is nonzero because something is paid
  all_goals
    have hcomp : (computeWithdraw v amount waive).run = .ok (.ok ‹VaultAmounts›) := ‹_›
    have hpf := (Vault.sharesToAssetsWithdraw_form v _ _ waive hmax
      (computeWithdraw_ok_priced v amount waive _ hcomp)).1
    have hX : (‹VaultAmounts›).assets.toNumber .to_nearest = .ok _ := ‹_›
    have hdust : v.checkDebitNotDust _ = .ok _ := ‹_›
    have hd : (_ != TER.tesSUCCESS) = false := ‹_›
    have hm : (‹VaultAmounts›).assets.mValue ≠ 0 := by
      intro h0
      first
        | (rw [(STAmount.toRat_eq_zero_iff _).mpr h0] at hpay; exact lt_irrefl _ hpay)
        | (have hz : (‹VaultAmounts›).assets.isZero = true := by simp [STAmount.isZero, h0]
           simp_all)
    have hXv := (hpf.toNumber_exact _ hX).1
    refine ⟨_, Number.operator_eq_zero_false_of_mantissa_ne _ (Number.mantissa_ne_zero_of_toRat_ne_zero ?_),
      hdust.trans (congrArg Except.ok (ter_success_of_bne _ hd))⟩
    rw [hXv]
    exact fun h => hm ((STAmount.toRat_eq_zero_iff _).mp h)

/-- A nonzero fractional clamp floors the amount onto the grid of the cash it leaves, a grid no
finer than the base grid. -/
lemma Vault.clamp_floor (v : Vault) (X clamped : STAmount) (hX : X.CanonicalOrZero)
    (hXt : X.mNumericType = .fractional) (hX0 : 0 ≤ X.toRat) (hnz : clamped.mValue ≠ 0)
    (hcl : clampToSumExponent v.assetsAvailable X.operator_neg v.baseExponent = .ok clamped) :
    ∃ (dN : Number) (e : ℤ), X.operator_neg.toNumber .to_nearest = .ok dN ∧
      postSumExponent v.assetsAvailable dN v.baseExponent .fractional = .ok e ∧ v.baseExponent ≤ e ∧
      clamped.toRat = (⌊X.toRat / 10 ^ e⌋ : ℚ) * 10 ^ e := by
  have hpf : X.operator_neg.FracCanonZero :=
    STAmount.operator_neg_fczr _ (hX.fracCanonZero (by unfold STAmount.integral; rw [hXt]; rfl))
  obtain ⟨dN, e, hdN, hps, hge, hfl⟩ := clampToSumExponent_frac_floor _ _ _ _ hpf
    v.baseExponent_range.1 v.baseExponent_range.2 hnz hcl
  have hnt : X.operator_neg.numericType = .fractional := by
    show X.operator_neg.mNumericType = _
    rw [(STAmount.operator_neg_fields X).1, hXt]
  rw [hnt] at hps
  rw [STAmount.operator_neg_toRat, abs_neg, abs_of_nonneg hX0] at hfl
  exact ⟨dN, e, hdN, hps, hge, hfl⟩

/-- A fractional clamp sits on a grid between `10⁻¹⁰` and `10⁸⁰` that keeps the cash it leaves within
`2^63` of its steps: it floors onto the 16-digit grid of the cash less the debit. -/
lemma Vault.clamp_fit (v : Vault) (X clamped : STAmount) (hX : X.FracCanonZero) (hX0 : 0 ≤ X.toRat)
    (hnz : clamped.mValue ≠ 0)
    (hcl : clampToSumExponent v.assetsAvailable X.operator_neg v.baseExponent = .ok clamped) :
    ∃ e z : ℤ, -10 ≤ e ∧ e ≤ 80 ∧ clamped.toRat = (z : ℚ) * 10 ^ e ∧
      (e ≤ v.assetsAvailable.exponent_ → v.assetsAvailable.toRat - clamped.toRat < 2 ^ 63 * 10 ^ e) := by
  obtain ⟨dN, e, hdN, hps, hge, hfl⟩ := Vault.clamp_floor v X clamped hX.canonicalOrZero hX.1 hX0 hnz hcl
  obtain ⟨-, -, he80⟩ := postSumExponent_range _ _ _ _ _ v.baseExponent_range.1 v.baseExponent_range.2 hps
  have hb := (Vault.baseExponent_bounds v).1
  refine ⟨e, ⌊X.toRat / 10 ^ e⌋, by omega, he80, hfl, fun _ => ?_⟩
  have hpe : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  -- the cash less the unclamped debit sits below `10 ^ (e + 16)`, the reach of the sum's grid
  obtain ⟨s0, hs0, hne⟩ := postSumExponent_reduces _ _ _ _ _ hps
  obtain ⟨hdv, hdn⟩ := STAmount.CanonicalOrZero.toNumber_exact
    (STAmount.CanonicalOrZero.operator_neg (STAmount.FracCanonZero.canonicalOrZero hX)) dN hdN
  rw [STAmount.operator_neg_toRat] at hdv
  have hr1 := operator_add_rounded_to_nearest _ _ _ v.wf.assetsAvailable_norm hdn hs0
  have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hdn hs0
  have hlt := numberExponent_frac_lt s0 v.baseExponent e hs0n (by omega) hne
  obtain ⟨m, hmn, hmv⟩ := Exact.exists_normalized_grid 1 (e + 16) le_rfl (by norm_num)
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have ht : v.assetsAvailable.toRat - X.toRat < 10 ^ (e + 16) := by
    by_contra h
    push Not at h
    have := Number.RoundsToRepresentable.ge_of_ge_normalized s0 _ hr1 m hmn (by
      rw [hmv, hdv]; push_cast; linarith)
    rw [hmv] at this
    push_cast at this
    linarith
  -- the clamp loses less than one step of the grid
  have hfloor : X.toRat - 10 ^ e < clamped.toRat := by
    have h := Int.lt_floor_add_one (X.toRat / 10 ^ e)
    rw [hfl]
    have h' : X.toRat < ((⌊X.toRat / 10 ^ e⌋ : ℚ) + 1) * 10 ^ e := by rwa [div_lt_iff₀ hpe] at h
    linarith
  have h16 : (10 : ℚ) ^ (e + 16) = 10 ^ 16 * 10 ^ e := by
    rw [zpow_add₀ (by norm_num), mul_comm]; norm_num
  have hbig : (10 : ℚ) ^ 16 + 1 ≤ 2 ^ 63 := by norm_num
  nlinarith

/-- An integral debit sits on the unit grid, and the cash a passed dust check reads is below
`2^63`, so the cash less the debit stays within `2^63` units. -/
lemma Vault.integral_debit_fit (v : Vault) (hint : v.numericType.isIntegral = true)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (debit c : STAmount) (hd : debit.IntegralCanonical) (hpos : 0 < debit.toRat)
    (hc : STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest = .ok c) :
    ∃ e z : ℤ, -10 ≤ e ∧ e ≤ 80 ∧ debit.toRat = (z : ℚ) * 10 ^ e ∧
      (e ≤ v.assetsAvailable.exponent_ → v.assetsAvailable.toRat - debit.toRat < 2 ^ 63 * 10 ^ e) := by
  have hv := STAmount.toRat_of_nonneg debit (STAmount.mIsNegative_false_of_pos _ hpos)
  rw [hd.offset_zero, zpow_zero, mul_one] at hv
  refine ⟨0, debit.mValue.toNat, by norm_num, by norm_num, by rw [hv, zpow_zero, mul_one]; push_cast; rfl,
    fun _ => ?_⟩
  have := Vault.cash_lt_of_converts v hint hmax c hc
  rw [zpow_zero, mul_one]
  linarith

/-- Proof of `Vault.withdraw_final_iff`. -/
lemma Vault.withdraw_final_iff_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t : UInt32)
    (hpos : 0 < amount.amount.toRat) (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r)) :
    r.shares.toRat = v.toExact.sharesTotal ↔
      r.vault'.toRawVault = { v.toRawVault with assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  have hST := Vault.withdraw_sharesTotal v amount waive t hpos hc hty r hok
  have hcast := RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  obtain ⟨aa', st', hfr⟩ := Vault.withdraw_frame v amount waive t hpos r hok
  have hAA : r.vault'.assetsAvailable = aa' := (congrArg RawVault.assetsAvailable hfr).trans rfl
  have hSTv : r.vault'.sharesTotal = st' := (congrArg RawVault.sharesTotal hfr).trans rfl
  constructor
  · intro hfin
    have hst0 : r.vault'.sharesTotal = Number.zero :=
      Number.eq_zero_of_mantissa_zero _ r.vault'.wf.sharesTotal_norm
        (Number.toRat_eq_zero_iff.mp (by rw [hST, ← hcast, hfin]; ring))
    have haa0 := (r.vault'.valid.empty_shares hst0).1
    rw [hfr, ← hAA, ← hSTv, haa0, hst0]
  · intro h
    have hst0 : r.vault'.sharesTotal = Number.zero := congrArg RawVault.sharesTotal h
    rw [hst0, Number.toRat_zero] at hST
    rw [hcast]
    linarith

/-- A reachable vault stores its cash exactly and deploys nothing, so the final payout is all the cash and the whole
share total is worth exactly that. -/
lemma Vault.withdraw_final_payout_proof (v : Vault) (amount : WithdrawAmount) (waive : Bool) (t t0 : UInt32)
    (hpos : 0 < amount.amount.toRat) (hr : Vault.Reachable v t0)
    (hc : amount.amount.Canonical) (hty : amount.InAsset v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (r : VaultWithAmounts) (hok : (v.withdraw amount waive t hpos).run = .ok (.ok r))
    (hfinal : r.shares.toRat = v.toExact.sharesTotal) :
    r.assets.toRat = v.idealAssetsWithdraw waive r.shares.toRat := by
  obtain ⟨hpay, -, -⟩ := Vault.withdraw_final_proof v amount waive t t0 hpos hr hc hty hmax r hok hfinal
  obtain ⟨-, -, hspos⟩ := Vault.withdraw_shares_form v amount waive t hpos hc hty r hok
  obtain ⟨atot, nav, hat, hnav, hq⟩ := Vault.Reachable.withdrawNavExact_proof v t0 hr waive
  have hsub : v.assetsTotalForWithdrawal waive = .ok nav := by
    simp only [Vault.assetsTotalForWithdrawal, bind, Except.bind, hat]; exact hnav
  have hST : (v.toExact.sharesTotal : ℚ) ≠ 0 := by rw [← hfinal]; exact ne_of_gt hspos
  rw [hpay]
  unfold RawVault.idealAssetsWithdraw
  rw [hfinal, mul_div_assoc, div_self hST, mul_one, ← hq]
  exact (Vault.Reachable.nav_eq_cash v t0 hr waive nav hsub).symm

end XRPL.Model.SingleAssetVault
