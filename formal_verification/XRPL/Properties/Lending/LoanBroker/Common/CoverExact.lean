import XRPL.Properties.Lending.LoanBroker.Common.OpenZone

/-! # Exact cover updates in the Open zone

On a broker in the Open zone every cover operation moves CoverAvailable by whole base units and the `Number`
arithmetic is exact: a deposit credits at most the amount, and a withdrawal or a clawback debits at most the cover. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A to-nearest sum of two amounts on a grid, not negative and at most the Open limit, is exact. -/
private lemma grid_add_exact (x y d : Number) (s : Int) (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (h0 : 0 ≤ x.toRat + y.toRat)
    (hok : x.operator_add y .to_nearest = .ok d) (hle : d.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ s) :
    d.toRat = x.toRat + y.toRat := by
  obtain ⟨hxn, jx, hjx⟩ := hx
  obtain ⟨hyn, jy, hjy⟩ := hy
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hsum : x.toRat + y.toRat = ((jx + jy : ℤ) : ℚ) * 10 ^ s := by rw [hjx, hjy]; push_cast; ring
  have hj0 : 0 ≤ jx + jy := by
    have : (0 : ℚ) ≤ ((jx + jy : ℤ) : ℚ) * 10 ^ s := hsum ▸ h0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  by_cases hj : jx + jy ≤ 9 * 10 ^ 15
  · rw [Number.operator_add_toRat_of_grid x y d jx jy s hxn hyn hjx hjy ⟨by omega, by omega⟩ hs hok, hsum]
  · -- past the limit the rounded sum is above it too
    exfalso
    obtain ⟨w, hw, hwv⟩ :=
      Number.exists_normalized_int_mul_pow (9 * 10 ^ 15 + 1) s (by constructor <;> norm_num) hs
    have hR := operator_add_rounded_to_nearest x y d hxn hyn hok
    have hwle : w.toRat ≤ x.toRat + y.toRat := by
      rw [hwv, hsum]
      have h9 : 9 * 10 ^ 15 + 1 ≤ jx + jy := by omega
      have : ((9 * 10 ^ 15 + 1 : ℤ) : ℚ) ≤ ((jx + jy : ℤ) : ℚ) := by exact_mod_cast h9
      nlinarith
    have := Number.RoundsToRepresentable.ge_of_le hR (Or.inl rfl) w hw hwle
    rw [hwv] at this
    push_cast at this
    nlinarith

/-- A to-nearest difference of two amounts on a grid, the second between zero and the first, the first
at most the Open limit, is exact. -/
lemma grid_sub_exact (x y d : Number) (s : Int) (hx : Number.OnGrid s x) (hy : Number.OnGrid s y)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) (hy0 : 0 ≤ y.toRat) (hyx : y.toRat ≤ x.toRat)
    (hxL : x.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ s)
    (hok : x.operator_sub y .to_nearest = .ok d) : d.toRat = x.toRat - y.toRat := by
  obtain ⟨hxn, jx, hjx⟩ := hx
  obtain ⟨hyn, jy, hjy⟩ := hy
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hjy0 : 0 ≤ jy := by
    have : (0 : ℚ) ≤ (jy : ℚ) * 10 ^ s := hjy ▸ hy0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hjyx : jy ≤ jx := by
    have : (jy : ℚ) * 10 ^ s ≤ (jx : ℚ) * 10 ^ s := hjy ▸ hjx ▸ hyx
    exact_mod_cast le_of_mul_le_mul_right this hp
  have hjxL : jx ≤ 9 * 10 ^ 15 := by
    have : (jx : ℚ) * 10 ^ s ≤ 9 * 10 ^ 15 * 10 ^ s := hjx ▸ hxL
    exact_mod_cast le_of_mul_le_mul_right this hp
  rw [Number.operator_sub_toRat_of_grid x y d jx jy s hxn hyn hjx hjy ⟨by omega, by omega⟩ hs hok, hjx, hjy]
  push_cast; ring

/-- A value at most a cover in the Open zone is below `10^(16 + b)`. -/
lemma LoanBroker.OpenZone.lt_pow_sixteen (lb : LoanBroker) (b : Int) (hz : lb.OpenZone b) (x : ℚ)
    (hx : x ≤ lb.coverAvailable.toRat) : x < 10 ^ (16 + b) := by
  have hL : lb.coverAvailable.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ b := hz.coverLimit
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  rw [zpow_add₀ (by norm_num)]
  norm_num
  linarith

/-- A deposit in the Open zone credits whole base units exactly: the credit is positive, at most the
amount, and CoverAvailable grows by exactly the credit. -/
lemma LoanBroker.coverDeposit_exact (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hz : lb.OpenZone v.baseExponent) (hnt : v.numericType = lb.numericType)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverDeposit v amount = .ok .tesSUCCESS)
    (hok : (lb.coverDeposit v amount).run = .ok (.ok res)) :
    (lb.roundedCoverAmount v amount).run = .ok (.ok res.amount') ∧
      (∃ j : ℕ, res.amount'.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent) ∧
      0 < res.amount'.toRat ∧ res.amount'.toRat ≤ amount.toRat ∧
      res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable + res.amount'.toRat := by
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  have hint : lb.numericType.isIntegral = true → v.baseExponent = 0 := fun h => hbint (hnt ▸ h)
  have hb : (-96 : ℤ) ≤ AssetPool.baseExponent v ∧ AssetPool.baseExponent v ≤ 80 := v.baseExponent_range
  obtain ⟨r, hr, happ⟩ := LoanBroker.coverDeposit_ok_inv lb v amount res hok
  obtain ⟨m, c', hm, hadd, hamt, hraw⟩ := LoanBroker.applyCoverTransaction_credit_inv lb r res happ
  have hcv : res.loanBroker'.coverAvailable = c' := by
    have h := congrArg RawLoanBroker.coverAvailable hraw; exact h
  rw [hamt]
  obtain ⟨aN, -, hs, hrpos⟩ := LoanBroker.roundedCoverAmount_ok lb v amount r hr
  obtain ⟨hrle, hrnum⟩ := LoanBroker.roundedCoverAmount_le lb v amount r hc hpos.le hb hr
  obtain ⟨hmv, -⟩ := hrnum m hm
  have hmg := sumRoundAndSubtract_onGrid _ _ _ _ _ r m hz.cover ⟨hblo, hbhi⟩ hint hs hm
  have hsum0 : 0 ≤ lb.toExact.coverAvailable + m.toRat := add_nonneg lb.exact.coverAvailable_nonneg
    (by rw [hmv]; exact ((STAmount.signum_pos_iff_toRat_pos r).mp hrpos).le)
  have hle := LoanBroker.coverDeposit_le lb v amount res hz.cover hint hcan hok
  have hcL : c'.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ v.baseExponent := by
    rw [← hcv]; exact le_trans hle (max_le hz.coverLimit le_rfl)
  have hexact := grid_add_exact _ _ _ _ hz.cover hmg (Vault.baseExponent_grid v).2 hsum0 hadd hcL
  have hr0 := (STAmount.signum_pos_iff_toRat_pos r).mp hrpos
  have hA0 : 0 ≤ lb.coverAvailable.toRat := lb.exact.coverAvailable_nonneg
  obtain ⟨j, -, hj⟩ := Number.OnGrid.units_le m _ hmg (by rw [hmv]; exact hr0.le) (by linarith)
  refine ⟨hr, ⟨j, by rw [← hmv, hj]⟩, hr0, hrle, ?_⟩
  show res.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat + r.toRat
  rw [hcv, hexact, hmv]

/-- A withdrawal in the Open zone debits whole base units exactly: the debit is positive, at most
the amount and at most the cover, and CoverAvailable drops by exactly the debit. -/
lemma LoanBroker.coverWithdraw_exact (lb : LoanBroker) (v : Vault) (amount : STAmount)
    (res : LoanBrokerCoverResult) (hz : lb.OpenZone v.baseExponent)
    (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hcan : lb.canCoverWithdraw v amount = .ok .tesSUCCESS)
    (hok : (lb.coverWithdraw v amount).run = .ok (.ok res)) :
    clampToSumExponent lb.coverAvailable amount.operator_neg (AssetPool.baseExponent v) = .ok res.amount' ∧
      (∃ j : ℕ, res.amount'.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent) ∧
      0 < res.amount'.toRat ∧ res.amount'.toRat ≤ amount.toRat ∧
      res.amount'.toRat ≤ lb.toExact.coverAvailable ∧
      res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable - res.amount'.toRat := by
  obtain ⟨hblo, hbhi, -⟩ := v.baseExponent_bounds
  obtain ⟨a, hcl, happ⟩ := LoanBroker.coverWithdraw_ok_inv lb v amount res hok
  obtain ⟨a2, aN, c2, hcl2, hnz, hnum, hge, -, -⟩ := LoanBroker.canCoverWithdraw_ok lb v amount hcan
  rw [hcl, Except.ok.injEq] at hcl2
  subst hcl2
  obtain ⟨m, c', hm, hsub, hamt, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb a res happ
  rw [hnum, Except.ok.injEq] at hm
  subst hm
  have hcv : res.loanBroker'.coverAvailable = c' := by
    have h := congrArg RawLoanBroker.coverAvailable hraw; exact h
  rw [hamt]
  obtain ⟨hac, ha0, hale, ⟨j, hj⟩⟩ := clampToSumExponent_debit_facts lb.coverAvailable amount a _ (Or.inl hc)
    hpos.le v.baseExponent_range (fun _ => hbhi) hcl
  obtain ⟨hav, -⟩ := STAmount.CanonicalOrZero.toNumber_exact hac aN hnum
  have hng := Vault.clamp_onGrid v _ _ _ (STAmount.CanonicalOrZero.operator_neg (Or.inl hc)) hcl aN hnum
  have hle : aN.toRat ≤ lb.coverAvailable.toRat :=
    (operator_lt_eq_false_iff _ _ lb.wf.coverAvailable_norm hng.1).mp hge
  have hexact := grid_sub_exact _ _ _ _ hz.cover hng (Vault.baseExponent_grid v).2 (by rw [hav]; exact ha0) hle
    hz.coverLimit hsub
  refine ⟨hcl, ⟨j, hj⟩, (STAmount.isZero_eq_false_iff_pos a ha0).mp hnz, hale, by rw [← hav]; exact hle, ?_⟩
  show res.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat - a.toRat
  rw [hcv, hexact, hav]

/-- A clawback in the Open zone debits whole base units exactly: the debit is positive and at most
the cover, and CoverAvailable drops by exactly the debit. -/
lemma LoanBroker.coverClawback_exact (lb : LoanBroker) (v : Vault) (amount : Option STAmount)
    (res : LoanBrokerCoverResult) (hz : lb.OpenZone v.baseExponent)
    (hmax : lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hok : (lb.coverClawback v amount).run = .ok (.ok res)) :
    (lb.roundedCoverClawback v amount).run = .ok (.ok res.amount') ∧
      (∃ j : ℕ, res.amount'.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent) ∧
      0 < res.amount'.toRat ∧ res.amount'.toRat ≤ lb.toExact.coverAvailable ∧
      res.loanBroker'.toExact.coverAvailable = lb.toExact.coverAvailable - res.amount'.toRat := by
  obtain ⟨c, hc, happ⟩ := LoanBroker.coverClawback_ok_inv lb v amount res hok
  obtain ⟨_, _, claw, claw', _, _, _, _, hof, hcl, hnz⟩ := LoanBroker.roundedCoverClawback_ok lb v amount c hc
  obtain ⟨m, c', hm, hsub, hamt, hraw⟩ := LoanBroker.applyCoverTransaction_debit_inv lb c res happ
  have hcv : res.loanBroker'.coverAvailable = c' := by
    have h := congrArg RawLoanBroker.coverAvailable hraw; exact h
  rw [hamt]
  have hneg := (STAmount.ofNumber_canonicalOrZero _ _ _ claw' hmax hof).1.operator_neg
  obtain ⟨hcc, -, hc0⟩ := clampToSumExponent_canonicalOrZero lb.coverAvailable _ c _ hneg
    v.baseExponent_range.1 v.baseExponent_range.2 hcl
  obtain ⟨hmv, -⟩ := STAmount.CanonicalOrZero.toNumber_exact hcc m hm
  have hng := Vault.clamp_onGrid v _ _ _ hneg hcl m hm
  -- the clawback leaves a lawful cover, so on the grid it cannot debit more than the cover
  have hc'0 : 0 ≤ c'.toRat := by rw [← hcv]; exact res.loanBroker'.exact.coverAvailable_nonneg
  have hle : m.toRat ≤ lb.coverAvailable.toRat := by
    by_contra hgt
    push Not at hgt
    obtain ⟨-, jc, hjc⟩ := hz.cover
    obtain ⟨hmn, jm, hjm⟩ := hng
    have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
    have hj : jc < jm := by
      have : (jc : ℚ) * 10 ^ v.baseExponent < (jm : ℚ) * 10 ^ v.baseExponent := hjc ▸ hjm ▸ hgt
      exact_mod_cast lt_of_mul_lt_mul_right this hp.le
    obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (-1) v.baseExponent (by constructor <;> norm_num)
      (Vault.baseExponent_grid v).2
    have hR := operator_sub_rounded_to_nearest _ _ _ lb.wf.coverAvailable_norm hmn hsub
    have hwle : lb.coverAvailable.toRat - m.toRat ≤ w.toRat := by
      rw [hwv, hjc, hjm]
      have : ((jc - jm : ℤ) : ℚ) ≤ -1 := by exact_mod_cast (by omega : jc - jm ≤ -1)
      push_cast at this ⊢; nlinarith
    have := Number.RoundsToRepresentable.le_of_ge hR (Or.inl rfl) w hw hwle
    rw [hwv] at this
    push_cast at this
    linarith
  have hexact := grid_sub_exact _ _ _ _ hz.cover hng (Vault.baseExponent_grid v).2 (by rw [hmv]; exact hc0) hle
    hz.coverLimit hsub
  obtain ⟨j, -, hj⟩ := Number.OnGrid.units_le m _ hng (by rw [hmv]; exact hc0) (hle.trans hz.coverLimit)
  refine ⟨hc, ⟨j, by rw [← hmv, hj]⟩, (STAmount.isZero_eq_false_iff_pos c hc0).mp hnz,
    by rw [← hmv]; exact hle, ?_⟩
  show res.loanBroker'.coverAvailable.toRat = lb.coverAvailable.toRat - c.toRat
  rw [hcv, hexact, hmv]

end XRPL.Model.Lending
