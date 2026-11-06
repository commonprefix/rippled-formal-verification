import XRPL.Properties.Lending.Loan.Common.PayoffSettle
import XRPL.Properties.Lending.Loan.Common.CreditTotal
import XRPL.Properties.Lending.Ledger.Common.PaymentShareLarge

/-! # The settlement of a payment succeeds

A settlement credits the vault, moves AssetsDeployed, DebtTotal and YieldUnrealized, and pays the fee to the owner or
the cover. Within range it succeeds when the vault gets a credit or the loan is paid off. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay
open private LoanBroker.settle_lawful Loan.withBroker_lawful from XRPL.Properties.Lending.Loan.Common.RecheckPayLoan
open private near_lt_pow STAmount.roundToNumericType_none_exp from XRPL.Properties.Lending.Loan.Common.PayoffSettle
open private vault_credit_at_base from XRPL.Properties.Lending.Loan.Common.PayBounds
open private sumRoundAndSubtract_credit_large from XRPL.Properties.Lending.Ledger.Common.PaymentShareLarge

/-- The vault update of a payment succeeds and leaves a lawful vault. AssetsAvailable takes the credit,
AssetsDeployed gives up the principal and YieldUnrealized moves by `yd`. -/
private lemma Vault.pay_adjust (v : Vault) (hasset : Vault.HoldsAsset v) (toPool pp yd : Number)
    (hgA : Number.OnGrid v.baseExponent v.assetsAvailable) (hAAl : v.assetsAvailable.toRat < 10 ^ 89)
    (htoN : toPool.isNormalized) (hgm : Number.OnGrid v.baseExponent toPool)
    (hAAm : 0 ≤ v.assetsAvailable.toRat + toPool.toRat) (htol : toPool.toRat < 10 ^ 20)
    (hfit : (v.numericType = .fractional ∧ v.assetsAvailable.toRat + toPool.toRat < 10 ^ 89) ∨
      (v.numericType.isIntegral = true ∧
        v.assetsAvailable.toRat + toPool.toRat + 1 ≤ v.numericType.maxValue.toNat))
    (hgP : Number.OnGrid v.baseExponent pp) (hP0 : 0 ≤ pp.toRat)
    (hdep : ∃ d : ℕ, d < 10 ^ 16 ∧ v.assetsDeployed.toRat = (d : ℚ) * 10 ^ v.baseExponent)
    (hADpos : 0 < v.assetsDeployed.toRat)
    (hLU : v.lossUnrealized.toRat + pp.toRat ≤ v.assetsDeployed.toRat)
    (hAR : v.assetsReserved.toRat + pp.toRat ≤ v.assetsDeployed.toRat)
    (hydN : yd.isNormalized) (hyd0 : 0 ≤ v.yieldUnrealized.toRat + yd.toRat) (hydl : |yd.toRat| < 10 ^ 150)
    (hYU : v.yieldUnrealized.toRat < 10 ^ 150) :
    ∃ raw v' at', (v.adjustBalances ⟨toPool, pp.operator_neg, yd, Number.zero, Number.zero⟩).run =
      .ok (.ok raw) ∧ raw.to_lawful = .ok v' ∧ v'.assetsTotal = .ok at' ∧
      ∃ aa, v.assetsAvailable.operator_add toPool .to_nearest = .ok aa ∧
        STAmount.roundToNumericType v.numericType aa .to_nearest = .ok v'.assetsAvailable := by
  have hbase := Vault.baseExponent_scale_range v
  have hs : minExponent + 18 ≤ v.baseExponent ∧ v.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ v.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hint0 : v.numericType.isIntegral = true → v.baseExponent = 0 := by
    intro h; unfold Vault.baseExponent NumericType.baseExponent; rw [if_pos h]
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAAN := v.wf.assetsAvailable_norm
  obtain ⟨d, hd16, hdv⟩ := hdep

  -- AssetsAvailable takes the credit
  have htol' : |toPool.toRat| < 10 ^ 150 := by
    rw [abs_lt]
    constructor <;> linarith [show (10 : ℚ) ^ 89 < 10 ^ 150 by norm_num, show (10 : ℚ) ^ 20 < 10 ^ 150 by norm_num]
  obtain ⟨aa, haa⟩ := Number.operator_add_ok_of_abs _ _ .to_nearest hAAN htoN
    (by rw [abs_of_nonneg hAA0]; linarith [show (10 : ℚ) ^ 89 < 10 ^ 200 by norm_num])
    (by linarith [show (10 : ℚ) ^ 150 < 10 ^ 200 by norm_num])
  have haaN := operator_add_isNormalized_to_nearest_sz _ _ _ hAAN htoN haa
  have haa0 := operator_add_nonneg _ _ _ hAAN htoN haa hAAm
  obtain ⟨aa', haa'⟩ : ∃ aa', STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa' := by
    rcases hfit with ⟨h, h1⟩ | ⟨hint, h1⟩
    · rw [h]
      have := (Number.add_near _ _ _ hAAN htoN haa).le hAAm
      exact STAmount.roundToNumericType_frac_none_ok aa haaN haa0 (lt_of_le_of_lt this (near_lt_pow _ h1))
    · have hb0 := hint0 hint
      have haav : aa.toRat = v.assetsAvailable.toRat + toPool.toRat := by
        refine Number.OnGrid.add_toRat hgA hgm hs ?_ haa
        rw [hb0, zpow_zero, mul_one, abs_of_nonneg hAAm]
        have hm : v.numericType.maxValue.toNat ≤ 2 ^ 63 := by
          rcases hasset with h | h | h <;> rw [h] <;> decide
        have hm' : (v.numericType.maxValue.toNat : ℚ) ≤ 2 ^ 63 := by exact_mod_cast hm
        linarith
      have hnt : v.numericType = .native ∨ v.numericType = .int64 := by
        rcases hasset with h | h | h
        · rw [h] at hint; cases hint
        · exact Or.inl h
        · exact Or.inr h
      refine STAmount.roundToNumericType_integral_ok _ aa .to_nearest none hnt haaN haa0 ?_
      rw [haav]
      exact h1
  have haa'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa'
  have haa'0 := STAmount.roundToNumericType_nonneg _ _ _ haaN haa0 haa'

  -- AssetsDeployed gives up the principal
  obtain ⟨-, k, hk⟩ := id hgP
  have hk0 : 0 ≤ k := by
    have : (0 : ℚ) ≤ k * 10 ^ v.baseExponent := by rw [← hk]; exact hP0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp10
  have hLU0 : 0 ≤ v.lossUnrealized.toRat := v.exact.lossUnrealized_nonneg
  have hAR0 : 0 ≤ v.assetsReserved.toRat := v.exact.assetsReserved_nonneg
  have hkd : k ≤ d := by
    have h1 : (k : ℚ) * 10 ^ v.baseExponent ≤ (d : ℚ) * 10 ^ v.baseExponent := by
      rw [← hk, ← hdv]; linarith
    have := le_of_mul_le_mul_right h1 hp10
    exact_mod_cast this
  have hgD : Number.OnGrid v.baseExponent v.assetsDeployed := ⟨v.wf.assetsDeployed_norm, d, by rw [hdv]; norm_cast⟩
  have hAD16 : v.assetsDeployed.toRat ≤ 10 ^ 16 := by
    rw [hdv]
    have : (d : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hd16.le
    have h2 : (d : ℚ) * 10 ^ v.baseExponent ≤ (d : ℚ) * 1 := mul_le_mul_of_nonneg_left hp1 (by positivity)
    linarith
  obtain ⟨ad', had'⟩ := Number.operator_add_ok_of_abs v.assetsDeployed pp.operator_neg .to_nearest
    v.wf.assetsDeployed_norm (Number.operator_neg_isNormalized _ hgP.1)
    (by rw [abs_of_nonneg (by linarith)]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    (by rw [Number.toRat_neg, abs_neg, abs_of_nonneg hP0]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
  have had'N := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsDeployed_norm
    (Number.operator_neg_isNormalized _ hgP.1) had'
  have had'v : ad'.toRat = v.assetsDeployed.toRat - pp.toRat := by
    have h63 : |v.assetsDeployed.toRat + pp.operator_neg.toRat| < 2 ^ 63 * 10 ^ v.baseExponent := by
      rw [Number.toRat_neg, ← sub_eq_add_neg, abs_of_nonneg (by linarith), hdv]
      have : (d : ℚ) < 2 ^ 63 := by
        have : (d : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hd16.le
        linarith [show (10 : ℚ) ^ 16 < 2 ^ 63 by norm_num]
      nlinarith
    have := Number.OnGrid.add_toRat hgD hgP.neg hs h63 had'
    rw [this, Number.toRat_neg]; ring
  have had'u : ad'.toRat = ((d - k.toNat : ℕ) : ℚ) * 10 ^ v.baseExponent := by
    rw [had'v, hdv, hk]
    have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    have hkd' : k.toNat ≤ d := by omega
    push_cast [Nat.cast_sub hkd']
    rw [show ((k.toNat : ℕ) : ℚ) = (k : ℚ) by exact_mod_cast hkn]
    ring

  -- YieldUnrealized moves by `yd`
  have hYU0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  obtain ⟨yu', hyu'⟩ := Number.operator_add_ok_of_abs v.yieldUnrealized yd .to_nearest
    v.wf.yieldUnrealized_norm hydN
    (by rw [abs_of_nonneg hYU0]; linarith [show (10 : ℚ) ^ 150 < 10 ^ 200 by norm_num])
    (by linarith [show (10 : ℚ) ^ 150 < 10 ^ 200 by norm_num])
  have hyu'N := operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.yieldUnrealized_norm hydN hyu'
  have hyu'0 := operator_add_nonneg _ _ _ v.wf.yieldUnrealized_norm hydN hyu' hyd0

  -- the update passes its checks, and the vault it writes is lawful
  have hsums : Vault.AdjustSums v ⟨toPool, pp.operator_neg, yd, Number.zero, Number.zero⟩ aa' ad'
      v.lossUnrealized v.assetsReserved yu' :=
    ⟨⟨aa, haa, haa'⟩, had', Number.operator_add_zero_right _ _, Number.operator_add_zero_right _ _, hyu'⟩
  have hlule : v.lossUnrealized.toRat ≤ ad'.toRat := by rw [had'v]; linarith
  have harle : v.assetsReserved.toRat ≤ ad'.toRat := by rw [had'v]; linarith
  have hle : v.lossUnrealized.operator_gt ad' = false := by
    unfold Number.operator_gt
    exact (operator_lt_eq_false_iff _ _ had'N v.wf.lossUnrealized_norm).mpr hlule
  have had'0 : 0 ≤ ad'.toRat := le_trans hLU0 hlule
  have hadj := Vault.adjustBalances_ok v _ _ _ _ _ _ hsums
    ⟨Number.signum_nonneg_of_toRat _ haa'N haa'0, Number.signum_nonneg_of_toRat _ had'N had'0,
      Number.signum_nonneg_of_toRat _ v.wf.lossUnrealized_norm hLU0, Number.signum_nonneg_of_toRat _ hyu'N hyu'0,
      Number.signum_nonneg_of_toRat _ v.wf.assetsReserved_norm hAR0⟩ hle
  obtain ⟨v', hv', hv'r⟩ := Vault.balances_lawful v aa' ad' v.assetsReserved v.lossUnrealized yu'
    ⟨haa'N, had'N, v.wf.assetsReserved_norm, v.wf.lossUnrealized_norm, hyu'N⟩
    ⟨haa'0, had'0, hAR0, hLU0, hyu'0⟩ hlule harle
    (hasset.isRounded_units ad' (d - k.toNat) had'N (by omega) had'u)
    (Vault.adjustBalances_cash_valid v _ _ hasset.maxValue_le hgm hadj haa'0).1
    (Vault.adjustBalances_cash_valid v _ _ hasset.maxValue_le hgm hadj haa'0).2 (by
      intro h0
      obtain ⟨-, hd0⟩ := v.valid.empty_shares h0
      exfalso
      have : v.assetsDeployed.toRat = 0 := by rw [hd0]; exact Number.toRat_zero
      linarith)

  have hat : ∃ at', v'.assetsTotal = .ok at' := by
    have hvt : v'.assetsTotal = aa'.operator_add ad' .downward := by
      show RawVault.assetsTotal v'.toRawVault = _
      rw [hv'r]
      rfl
    rw [hvt]
    have h1 := STAmount.roundToNumericType_none_exp v.numericType aa aa' hasset haa'
    have h2 := Number.exponent_le_of_abs_lt_big ad' had'N (by
      rw [abs_of_nonneg had'0]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    exact Number.operator_add_ok_of_exp _ _ _ haa'N had'N h1 (by unfold maxExponent; omega)
  obtain ⟨at', hat'⟩ := hat
  have hv'a : v'.assetsAvailable = aa' := by
    show v'.toRawVault.assetsAvailable = _
    rw [hv'r]
  exact ⟨_, v', at', hadj, hv', hat', aa, haa, by rw [hv'a]; exact haa'⟩

/-- A nonnegative IOU amount below `10^90` has an exponent. -/
private lemma numberExponent_frac_ok (n : Number) (b : Int) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat)
    (hlt : n.toRat < 10 ^ 90) : ∃ e, numberExponent n b .fractional = .ok e := by
  unfold numberExponent
  by_cases hz : n.operator_eq Number.zero = true
  · rw [if_pos hz]; exact ⟨b, rfl⟩
  · rw [if_neg hz]
    obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr n .downward hn (by rw [abs_of_nonneg h0]; exact hlt)
    rw [hst]
    exact ⟨_, rfl⟩

/-- A credit of at least one base unit moves AssetsAvailable while AssetsAvailable is below `10^16` base units.
At the base scale the credit lands exactly, and past it the floor of the sum stays above AssetsAvailable. -/
private lemma vault_credit_moves (nt : NumericType) (A c toPool aa A' : Number) (b : Int) (st : STAmount)
    (hnt : nt = .fractional ∨ nt = .native ∨ nt = .int64) (hint : nt.isIntegral = true → b = 0)
    (hbr : (-10 : ℤ) ≤ b ∧ b ≤ 0) (hA : A.isNormalized) (hArep : STAmount.isRounded nt A = false)
    (hAg : ∃ a : ℕ, A.toRat = (a : ℚ) * 10 ^ b) (hA16 : A.toRat < 10 ^ 16 * 10 ^ b)
    (hc : c.isNormalized) (hcg : ∃ k : ℕ, c.toRat = (k : ℚ) * 10 ^ b) (hc0 : 0 < c.toRat)
    (hfit : A.toRat + c.toRat < 2 ^ 63 * 10 ^ b)
    (hst : sumRoundAndSubtract A c b nt .downward = .ok st) (hto : st.toNumber .to_nearest = .ok toPool)
    (haa : A.operator_add toPool .to_nearest = .ok aa)
    (hA' : STAmount.roundToNumericType nt aa .to_nearest = .ok A') : A' ≠ A := by
  intro heq
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  obtain ⟨a, ha⟩ := hAg
  obtain ⟨k, hk⟩ := hcg
  have hA0 : 0 ≤ A.toRat := by rw [ha]; positivity
  have hk1 : (1 : ℚ) ≤ k := by
    have : (0 : ℚ) < k := by
      by_contra h0
      push Not at h0
      have : c.toRat ≤ 0 := by rw [hk]; exact mul_nonpos_of_nonpos_of_nonneg h0 hp.le
      linarith
    have : (0 : ℕ) < k := by exact_mod_cast this
    exact_mod_cast this
  have hcb : 10 ^ b ≤ c.toRat := by rw [hk]; nlinarith
  have hs : minExponent + 18 ≤ b ∧ b ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  have hpow16 : (10 : ℚ) ^ (16 + b) = 10 ^ 16 * 10 ^ b := by rw [zpow_add₀ (by norm_num)]; norm_num
  by_cases hroom : A.toRat + c.toRat ≤ (10 : ℚ) ^ (16 + b) - 10 ^ b
  · -- at the base scale the credit is the whole amount
    obtain ⟨htv, hA'v⟩ := vault_credit_at_base nt A c toPool aa A' b st a hint hbr hA ha hc hc0.le hroom hst hto
      haa hA'
    have hfl : ⌊c.toRat / 10 ^ b⌋ = (k : ℤ) := by
      rw [hk, mul_div_assoc, div_self hp.ne', mul_one]; exact Int.floor_natCast k
    rw [hfl] at htv
    rw [heq] at hA'v
    push_cast at htv
    nlinarith
  -- past the base scale
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow ((a + k : ℕ) : ℤ) b (by
      constructor
      · omega
      · have : ((a + k : ℕ) : ℚ) * 10 ^ b < (2 ^ 63 : ℚ) * 10 ^ b := by
          push_cast; rw [add_mul, ← ha, ← hk]; exact hfit
        exact_mod_cast lt_of_mul_lt_mul_right this hp.le) hs
  have hwv' : w.toRat = A.toRat + c.toRat := by rw [hwv, ha, hk]; push_cast; ring
  rcases hnt with hfr | hnat
  · subst hfr
    by_cases hcl : c.toRat ≤ 10 ^ 16 * 10 ^ b
    · obtain ⟨-, hlt⟩ := sumRoundAndSubtract_credit_floor A c b st toPool aa A' hA hA0 hArep ⟨a, ha⟩ hc hc0.le
        hcl        hbr ⟨w, hw, hwv'⟩ hst hto haa hA'
      have hA'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hA'
      obtain ⟨e, he⟩ := numberExponent_frac_ok A' b hA'n (by rw [heq]; exact hA0) (by
        rw [heq]
        have : (10 : ℚ) ^ 16 * 10 ^ b ≤ 10 ^ 16 := mul_le_of_le_one_right (by norm_num)
          (zpow_le_one_of_nonpos₀ (by norm_num) hbr.2)
        linarith [show (10 : ℚ) ^ 16 < 10 ^ 90 by norm_num])
      have heb := numberExponent_at_base A' b .fractional e hA'n (by rw [heq]; exact hA0) (by omega)
        (fun h => by cases h) (by rw [heq, hpow16]; exact hA16) he
      have := hlt e he
      rw [heb, heq] at this
      linarith
    · push Not at hcl
      have := sumRoundAndSubtract_credit_large A c b st toPool aa A' hA hA0 ⟨a, ha⟩ hc ⟨k, hk⟩ hcl hbr hfit hst
        hto        haa hA'
      rw [heq] at this
      have h3 : (10 : ℚ) ^ (b + 3) = 1000 * 10 ^ b := by
        rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
      rw [h3] at this
      nlinarith
  · have hint' : nt.isIntegral = true := by rcases hnat with rfl | rfl <;> rfl
    have hb0 := hint hint'
    subst hb0
    simp only [zpow_zero, mul_one] at *
    have hA'v := sumRoundAndSubtract_credit_exact_integral A c 0 _ st toPool aa A' hint' hA hA0 hArep hc hc0.le
      ⟨by norm_num, by norm_num⟩ hfit hst hto haa hA'
    obtain ⟨-, hcrx⟩ :=
      sumRoundAndSubtract_downward_le A c 0 _ st hA hA0 hc hc0.le ⟨by norm_num, by norm_num⟩ hst
    obtain ⟨hcrv, -⟩ := hcrx toPool hto
    have hsv : st.toRat = c.toRat := by
      unfold sumRoundAndSubtract at hst
      rw [if_pos hint'] at hst
      obtain ⟨x, hx, hst⟩ := bind_ok_peel _ _ _ hst
      obtain rfl : x = st := Except.ok.inj hst
      exact STAmount.ofNumber_integral_exact _ c _ x hint' hc (by rw [hk]; exact Rat.den_natCast k) hx
    rw [heq, hcrv, hsv] at hA'v
    linarith

/-- A payment whose instalments passed succeeds while AssetsAvailable is below `10^16` base units, when the broker
and the vault still carry the loan, its fee settlement computes and the vault gets a credit or the loan is paid off. -/
lemma Loan.pay_ok_of_room (loan : Loan) (v : Vault) (pt : LoanPaymentType) (amount : Number) (now : UInt32)
    (p : UnsettledPayment Vault) (hpay : (loan.payInstalments v pt amount now).run = .ok (.ok p))
    (hnt : p.loan.broker.numericType = p.pool.numericType) (hasset : Vault.HoldsAsset p.pool)
    (hArep : STAmount.isRounded p.pool.numericType p.pool.assetsAvailable = false)
    (hAg : ∃ a : ℕ, p.pool.assetsAvailable.toRat = (a : ℚ) * 10 ^ p.pool.baseExponent)
    (hA16 : p.pool.assetsAvailable.toRat < 10 ^ 16 * 10 ^ p.pool.baseExponent)
    (hgP : Number.OnGrid p.pool.baseExponent p.amounts.principalPaid)
    (hgI : Number.OnGrid p.pool.baseExponent p.amounts.interestPaid)
    (hP0 : 0 ≤ p.amounts.principalPaid.toRat) (hI0 : 0 ≤ p.amounts.interestPaid.toRat)
    (hPI : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat < 2 ^ 62 * 10 ^ p.pool.baseExponent)
    (hparts : (p.amounts.principalPaid.signum < 0 || p.amounts.interestPaid.signum < 0 ||
      p.amounts.feePaid.signum < 0) = false)
    (yd : Number)
    (hyield : ∃ i', p.loan.interestDue = .ok i' ∧ i'.operator_sub p.scheduledInterest .to_nearest = .ok yd)
    (hydN : yd.isNormalized) (hyd0 : 0 ≤ p.pool.yieldUnrealized.toRat + yd.toRat) (hydl : |yd.toRat| < 10 ^ 150)
    (hYU : p.pool.yieldUnrealized.toRat < 10 ^ 150) (toBroker cover' : Number)
    (hfee : (p.loan.broker.hasMinimumCover p.pool.baseExponent = .ok true ∧
        toBroker = p.amounts.feePaid ∧ cover' = p.loan.broker.coverAvailable) ∨
      (p.loan.broker.hasMinimumCover p.pool.baseExponent = .ok false ∧
        ∃ feeToCover, sumRoundAndSubtract p.loan.broker.coverAvailable p.amounts.feePaid
            p.pool.baseExponent p.loan.broker.numericType .downward = .ok feeToCover ∧
          feeToCover.toNumber .to_nearest = .ok toBroker ∧
          p.loan.broker.coverAvailable.operator_add toBroker .to_nearest = .ok cover'))
    (hcovN : cover'.isNormalized) (hcov0 : 0 ≤ cover'.toRat)
    (hdebt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧ p.loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ p.pool.baseExponent)
    (hPDT : p.amounts.principalPaid.toRat ≤ p.loan.broker.debtTotal.toRat) (hcount : p.loan.broker.loanCount ≠ 0)
    (hdep : ∃ d : ℕ, d < 10 ^ 16 ∧ p.pool.assetsDeployed.toRat = (d : ℚ) * 10 ^ p.pool.baseExponent)
    (hADpos : 0 < p.pool.assetsDeployed.toRat)
    (hLU : p.pool.lossUnrealized.toRat + p.amounts.principalPaid.toRat ≤ p.pool.assetsDeployed.toRat)
    (hAR : p.pool.assetsReserved.toRat + p.amounts.principalPaid.toRat ≤ p.pool.assetsDeployed.toRat)
    (hAAfit : p.pool.numericType.isIntegral = true → p.pool.assetsAvailable.toRat + p.amounts.principalPaid.toRat +
      p.amounts.interestPaid.toRat + 1 ≤ p.pool.numericType.maxValue.toNat)
    (hmove : p.loan.paymentRemaining = 0 ∨ 0 < p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat) :
    ∃ r, (loan.pay v pt amount now).run = .ok (.ok r) := by
  have hbase := Vault.baseExponent_scale_range p.pool
  have hs : minExponent + 18 ≤ p.pool.baseExponent ∧ p.pool.baseExponent ≤ maxExponent - 1 := by
    unfold minExponent maxExponent; omega
  have hp10 : (0 : ℚ) < 10 ^ p.pool.baseExponent := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ p.pool.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2
  have hint0 : p.pool.numericType.isIntegral = true → p.pool.baseExponent = 0 := by
    intro h; unfold Vault.baseExponent NumericType.baseExponent; rw [if_pos h]
  have hAA0 : 0 ≤ p.pool.assetsAvailable.toRat := p.pool.exact.assetsAvailable_nonneg
  have hAAN := p.pool.wf.assetsAvailable_norm
  have hgA : Number.OnGrid p.pool.baseExponent p.pool.assetsAvailable := by
    obtain ⟨a, ha⟩ := hAg; exact ⟨hAAN, a, by rw [ha]; norm_cast⟩
  have hA16' : p.pool.assetsAvailable.toRat < 10 ^ 16 := by
    have : (10 : ℚ) ^ 16 * 10 ^ p.pool.baseExponent ≤ 10 ^ 16 := mul_le_of_le_one_right (by norm_num) hp1
    linarith
  have hPI' : p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat < 10 ^ 20 := by
    have : (2 : ℚ) ^ 62 * 10 ^ p.pool.baseExponent ≤ 2 ^ 62 := mul_le_of_le_one_right (by norm_num) hp1
    linarith [show (2 : ℚ) ^ 62 < 10 ^ 20 by norm_num]

  obtain ⟨tp, htp⟩ := Number.operator_add_ok_of_abs _ _ .to_nearest hgP.1 hgI.1
    (by rw [abs_of_nonneg hP0]; linarith [show (10 : ℚ) ^ 20 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hI0]; linarith [show (10 : ℚ) ^ 20 < 10 ^ 200 by norm_num])
  have htpv : tp.toRat = p.amounts.principalPaid.toRat + p.amounts.interestPaid.toRat :=
    Number.OnGrid.add_exact hgP hgI hP0 hI0 (by nlinarith) hs htp
  have htpN := operator_add_isNormalized_to_nearest_sz _ _ _ hgP.1 hgI.1 htp
  have hgtp := Number.OnGrid.add hgP hgI hs htp

  have hcredit : p.pool.numericType.CreditFits p.pool.assetsAvailable.toRat tp.toRat := by
    rcases hasset with h | h | h
    · exact Or.inl ⟨h, by rw [htpv]; linarith [show (10 : ℚ) ^ 16 + 10 ^ 20 < 10 ^ 89 by norm_num]⟩
    · refine Or.inr ⟨Or.inl h, ?_⟩
      have := hAAfit (by rw [h]; rfl)
      rw [htpv]; linarith
    · refine Or.inr ⟨Or.inr h, ?_⟩
      have := hAAfit (by rw [h]; rfl)
      rw [htpv]; linarith
  obtain ⟨st, toPool, hst, htoPool, htoN, htole, hAAm⟩ := sumRoundAndSubtract_credit_ok p.pool.assetsAvailable tp
    p.pool.baseExponent p.pool.numericType hAAN htpN hAA0 (by rw [htpv]; linarith) ⟨by omega, by omega⟩ hcredit
  rw [htpv] at htole
  have hgm : Number.OnGrid p.pool.baseExponent toPool :=
    sumRoundAndSubtract_onGrid _ _ _ _ _ st toPool hgA hbase hint0 hst htoPool

  -- DebtTotal gives up the principal
  obtain ⟨t, ht16, htv⟩ := hdebt
  have hdtN := p.loan.broker.wf.debtTotal_norm
  have hdt0 : 0 ≤ p.loan.broker.debtTotal.toRat := p.loan.broker.exact.debtTotal_nonneg
  have hdt16 : p.loan.broker.debtTotal.toRat ≤ 10 ^ 16 := by
    rw [htv]
    have : (t : ℚ) ≤ 10 ^ 16 := by exact_mod_cast ht16
    have h2 : (t : ℚ) * 10 ^ p.pool.baseExponent ≤ (t : ℚ) * 1 := mul_le_mul_of_nonneg_left hp1 (by positivity)
    linarith
  obtain ⟨dt', hdt'⟩ := Number.operator_sub_ok_of_abs _ _ .to_nearest hdtN hgP.1
    (by rw [abs_of_nonneg hdt0]; linarith [show (10 : ℚ) ^ 16 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hP0]; linarith [show (10 : ℚ) ^ 20 < 10 ^ 200 by norm_num])
  obtain ⟨i', hi', hyd'⟩ := hyield
  have hsums : p.SettleSums toPool yd toBroker cover' dt' :=
    ⟨hparts, ⟨i', hi', hyd'⟩, ⟨tp, st, htp, by rw [hnt]; exact hst, htoPool⟩, hfee, hdt'⟩

  -- the vault, the broker and the loan pass their re-checks
  have hfit : (p.pool.numericType = .fractional ∧ p.pool.assetsAvailable.toRat + toPool.toRat < 10 ^ 89) ∨
      (p.pool.numericType.isIntegral = true ∧
        p.pool.assetsAvailable.toRat + toPool.toRat + 1 ≤ p.pool.numericType.maxValue.toNat) := by
    rcases hasset with h | h | h
    · exact Or.inl ⟨h, by linarith [show (10 : ℚ) ^ 16 + 10 ^ 20 < 10 ^ 89 by norm_num]⟩
    · have hi : p.pool.numericType.isIntegral = true := by rw [h]; rfl
      exact Or.inr ⟨hi, by linarith [hAAfit hi]⟩
    · have hi : p.pool.numericType.isIntegral = true := by rw [h]; rfl
      exact Or.inr ⟨hi, by linarith [hAAfit hi]⟩
  obtain ⟨raw, v', at', hadj, hv', hat, aa, haa, haa'⟩ := Vault.pay_adjust p.pool hasset toPool
    p.amounts.principalPaid yd hgA (by linarith [show (10 : ℚ) ^ 16 < 10 ^ 89 by norm_num]) htoN hgm hAAm
    (by linarith) hfit hgP hP0 hdep hADpos hLU hAR hydN hyd0 hydl hYU
  obtain ⟨broker', hb'⟩ := LoanBroker.settle_lawful p.loan.broker p.amounts.principalPaid dt' cover' hgP.1
    hP0 hPDT hcount hdt' hcovN hcov0
  have hbnt : broker'.numericType = p.loan.broker.numericType :=
    (congrArg RawLoanBroker.numericType (RawLoanBroker.to_lawful_ok hb').1 :)
  obtain ⟨loan', hl'⟩ := Loan.withBroker_lawful p.loan broker' hbnt

  have hmoved : v'.assetsAvailable ≠ p.pool.assetsAvailable ∨ p.loan.paymentRemaining = 0 := by
    rcases hmove with h0 | hpos
    · exact Or.inr h0
    left
    obtain ⟨a, ha⟩ := hAg
    obtain ⟨-, k, hk⟩ := hgtp
    have hk0 : 0 ≤ k := by
      have : (0 : ℚ) ≤ k * 10 ^ p.pool.baseExponent := by rw [← hk, htpv]; linarith
      exact_mod_cast nonneg_of_mul_nonneg_left this hp10
    refine vault_credit_moves p.pool.numericType p.pool.assetsAvailable tp toPool aa v'.assetsAvailable
      p.pool.baseExponent st hasset hint0 hbase hAAN hArep ⟨a, ha⟩ hA16 htpN ⟨k.toNat, ?_⟩
      (by rw [htpv]; exact hpos)
      (by rw [htpv]; nlinarith) hst htoPool haa haa'
    rw [hk]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hk0).symm
  exact ⟨_, Loan.payment_success_proof loan v amount now pt p toPool yd toBroker cover' dt' raw v' broker' loan' at'
    hpay hsums hadj hv' hb' hl' hat hmoved⟩

end XRPL.Model.Lending
