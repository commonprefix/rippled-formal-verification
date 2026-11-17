import XRPL.Properties.Lending.Ledger.Common.AcceptTotal
import XRPL.Properties.Lending.Ledger.Common.AssetFit
import XRPL.Properties.Lending.Ledger.Common.BrokerProofs
import XRPL.Properties.Lending.Ledger.Common.ManageReachable
import XRPL.Properties.Lending.Ledger.Common.RecheckApply
import XRPL.Properties.Protocol.STAmount.Range.Success

/-! # Where LoanAccept, LoanDelete and LoanManage can fail the model

Each step of the three operations either computes or is a lawfulness re-check. A sum of balances computes because
every balance of a lawful vault, broker and loan is far below the largest `Number`. The one step that reads a
range is the rounding of the new AssetsAvailable to the asset, which needs the sum within the asset's largest
amount. So an operation fails the model only with `notLawful`, which the re-check proofs exclude. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault TotalStores)

open private Vault.assetsDeployed_lt_pow cash_zero_sum from XRPL.Properties.Lending.Loan.Common.ManageTotal
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage
open private Vault.HoldsAsset.integral_room from XRPL.Properties.Lending.Loan.Common.DefaultCoverTotal

namespace NoExceptionLoanManage

/-- A normalized `Number` whose exponent leaves the room an addition needs. -/
def Headroom (n : Number) : Prop := n.isNormalized ∧ n.exponent_ + 22 ≤ maxExponent

/-- A normalized value below `10^200` in size has headroom. -/
lemma Headroom.of_abs_lt {n : Number} (hn : n.isNormalized) (h : |n.toRat| < 10 ^ 200) : Headroom n := by
  refine ⟨hn, ?_⟩
  by_cases hm : n.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero n hn hm]
    show (-2147483648 : Int) + 22 ≤ maxExponent
    unfold maxExponent; norm_num
  · have := Number.exponent_lt_of_abs_lt n hn hm 182 (by norm_num; exact h)
    unfold maxExponent; omega

/-- A normalized value from zero to below `10^96` has headroom. -/
lemma Headroom.of_nonneg_lt {n : Number} (hn : n.isNormalized) (h0 : 0 ≤ n.toRat) (h : n.toRat < 10 ^ 96) :
    Headroom n :=
  Headroom.of_abs_lt hn (by
    rw [abs_of_nonneg h0]
    exact lt_trans h (pow_lt_pow_right₀ (by norm_num) (by norm_num)))

lemma Headroom.zero : Headroom Number.zero :=
  Headroom.of_abs_lt Number.zero_isNormalized (by rw [Number.toRat_zero]; norm_num)

/-- The negation keeps the headroom. -/
lemma Headroom.neg {n : Number} (h : Headroom n) : Headroom n.operator_neg := by
  refine ⟨Number.operator_neg_isNormalized n h.1, ?_⟩
  unfold Number.operator_neg
  split_ifs
  · show (-2147483648 : Int) + 22 ≤ maxExponent
    unfold maxExponent; norm_num
  · exact h.2

/-- Two values with headroom add without an error, in every mode. -/
lemma Headroom.add_ok {x y : Number} (hx : Headroom x) (hy : Headroom y) (mode : rounding_mode) :
    ∃ r, x.operator_add y mode = .ok r :=
  Number.operator_add_ok_of_exp x y mode hx.1 hy.1 hx.2 hy.2

/-- Two values with headroom subtract without an error, in every mode. -/
lemma Headroom.sub_ok {x y : Number} (hx : Headroom x) (hy : Headroom y) (mode : rounding_mode) :
    ∃ r, x.operator_sub y mode = .ok r :=
  Number.operator_sub_ok_of_exp x y mode hx.1 hy.1 hx.2 hy.2

/-- The lawfulness re-check of a vault fails only with `notLawful`. -/
lemma vault_to_lawful_error {rv : RawVault} {e : Error} (h : rv.to_lawful = .error e) : e = .notLawful := by
  unfold RawVault.to_lawful at h
  split at h
  · cases h
  · cases h; rfl

/-- The lawfulness re-check of a loan fails only with `notLawful`. -/
lemma loan_to_lawful_error {rl : RawLoan} {e : Error} (h : rl.to_lawful = .error e) : e = .notLawful := by
  unfold RawLoan.to_lawful at h
  split at h
  · cases h
  · cases h; rfl

/-- The lawfulness re-check of a broker fails only with `notLawful`. -/
lemma broker_to_lawful_error {rb : RawLoanBroker} {e : Error} (h : rb.to_lawful = .error e) : e = .notLawful := by
  unfold RawLoanBroker.to_lawful at h
  split at h
  · cases h
  · cases h; rfl

/-- A vault update whose five sums compute returns a result code, while the new total is an amount of the asset
(C++ `syncAssetsTotal` stores it). -/
lemma adjustBalances_ne_error (v : Vault) (c : PoolBalanceChange) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu')
    (hst : 0 ≤ aa'.signum → 0 ≤ ad'.signum → TotalStores v.numericType aa' ad') (e : Error) :
    (v.adjustBalances c).run ≠ .error e := by
  by_cases hneg : aa'.signum < 0 ∨ ad'.signum < 0 ∨ lu'.signum < 0 ∨ yu'.signum < 0 ∨ ar'.signum < 0
  · rw [Vault.adjustBalances_bad_ledger v c _ _ _ _ _ hs hneg]; exact nofun
  · have hnn : 0 ≤ aa'.signum ∧ 0 ≤ ad'.signum ∧ 0 ≤ lu'.signum ∧ 0 ≤ yu'.signum ∧ 0 ≤ ar'.signum := by
      simp only [not_or, not_lt] at hneg; exact hneg
    cases hgt : lu'.operator_gt ad'
    · rw [Vault.adjustBalances_ok v c _ _ _ _ _ hs hnn hgt (hst hnn.1 hnn.2.1)]; exact nofun
    · rw [Vault.adjustBalances_limit_exceeded v c _ _ _ _ _ hs hnn hgt]; exact nofun

/-- A balance change whose five sums compute fails only at the lawfulness re-check of the new vault, while the new
total is an amount of the asset. -/
lemma poolAdjust_error (v : Vault) (c : PoolBalanceChange) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu')
    (hst : 0 ≤ aa'.signum → 0 ≤ ad'.signum → TotalStores v.numericType aa' ad') {e : Error}
    (h : AssetPool.adjustBalances v c = .error e) : e = .notLawful := by
  rw [Vault.pool_adjustBalances] at h
  unfold_ter at h
  walk_ok
  · exact absurd ‹_› (adjustBalances_ne_error v c _ _ _ _ _ hs hst _)
  · exact vault_to_lawful_error ‹_›

/-- An update that moves no cash and no deployed assets keeps the total the vault stored. -/
lemma totalStores_kept (v : Vault) (hts : v.TotalStored) (c : PoolBalanceChange) (hc : c.cash = Number.zero)
    (hd : c.deployed = Number.zero) (aa' ad' lu' ar' yu' : Number)
    (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu') : TotalStores v.numericType aa' ad' := by
  have had := hs.deployed
  rw [hd, Number.operator_add_zero_right] at had
  cases had
  exact Vault.cash_zero_totalStores v c hc v.valid.assetsAvailable_representable hts aa' hs.cash

/-- The five sums of a vault update compute when the cash side does and the other changes have headroom. -/
lemma adjustSums_exists (v : Vault) (c : PoolBalanceChange)
    (hcash : ∃ aa aa', v.assetsAvailable.operator_add c.cash .to_nearest = .ok aa ∧
      STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa')
    (hd : Headroom c.deployed) (hl : Headroom c.loss) (hr : Headroom c.reserved) (hy : Headroom c.yield)
    (hyu : Headroom v.yieldUnrealized) :
    ∃ aa' ad' lu' ar' yu', Vault.AdjustSums v c aa' ad' lu' ar' yu' := by
  have hAD := Vault.assetsDeployed_lt_pow v
  have hAD0 := v.exact.assetsDeployed_nonneg
  obtain ⟨aa, aa', h1, h2⟩ := hcash
  obtain ⟨ad', had⟩ := (Headroom.of_nonneg_lt v.wf.assetsDeployed_norm hAD0 hAD).add_ok hd .to_nearest
  obtain ⟨lu', hlu⟩ := (Headroom.of_nonneg_lt v.wf.lossUnrealized_norm v.exact.lossUnrealized_nonneg
    (lt_of_le_of_lt v.exact.lossUnrealized_le hAD)).add_ok hl .to_nearest
  obtain ⟨ar', har⟩ := (Headroom.of_nonneg_lt v.wf.assetsReserved_norm v.exact.assetsReserved_nonneg
    (lt_of_le_of_lt v.exact.assetsReserved_le hAD)).add_ok hr .to_nearest
  obtain ⟨yu', hyu'⟩ := hyu.add_ok hy .to_nearest
  exact ⟨aa', ad', lu', ar', yu', ⟨aa, h1, h2⟩, had, hlu, har, hyu'⟩

/-- A change that moves no cash rounds AssetsAvailable without an error: the asset stores it exactly. -/
lemma cash_zero (v : Vault) (c : PoolBalanceChange) (hc : c.cash = Number.zero) :
    ∃ aa aa', v.assetsAvailable.operator_add c.cash .to_nearest = .ok aa ∧
      STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa' := by
  obtain ⟨aa', ⟨aa, h1, h2⟩, -⟩ := cash_zero_sum v c hc v.valid.assetsAvailable_representable
  exact ⟨aa, aa', h1, h2⟩

/-- The interest a lawful loan still owes has headroom. -/
lemma interestDue_headroom (loan : Loan) (x : Number) (hx : loan.interestDue = .ok x) : Headroom x := by
  refine Headroom.of_abs_lt (RawLoan.interestDue_isNormalized loan x hx) ?_
  rw [Loan.interestDue_toExact loan x hx]
  obtain ⟨t, ht, htv⟩ := loan.grid.totalValueOutstanding_atExponent
  obtain ⟨p, hp, hpv⟩ := loan.grid.principalOutstanding_atExponent
  obtain ⟨m, hm, hmv⟩ := loan.grid.managementFeeOutstanding_atExponent
  change loan.totalValueOutstanding.toRat = (t : ℚ) * 10 ^ loan.loanScale at htv
  change loan.principalOutstanding.toRat = (p : ℚ) * 10 ^ loan.loanScale at hpv
  change loan.managementFeeOutstanding.toRat = (m : ℚ) * 10 ^ loan.loanScale at hmv
  change t < loan.broker.numericType.mantissaBound at ht
  change p < loan.broker.numericType.mantissaBound at hp
  change m < loan.broker.numericType.mantissaBound at hm
  have hb := NumericType.mantissaBound_le loan.broker.numericType
  have hs := loan.wf.loanScale_range
  have hp10 : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have hp80 : (10 : ℚ) ^ loan.loanScale ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hs.2
  have ht' : (t : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le ht hb
  have hp' : (p : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le hp hb
  have hm' : (m : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le hm hb
  have ht0 : (0 : ℚ) ≤ t := by positivity
  have hp0 : (0 : ℚ) ≤ p := by positivity
  have hm0 : (0 : ℚ) ≤ m := by positivity
  show |loan.totalValueOutstanding.toRat - loan.principalOutstanding.toRat -
    loan.managementFeeOutstanding.toRat| < _
  rw [htv, hpv, hmv, ← sub_mul, ← sub_mul, abs_mul, abs_of_pos hp10]
  have habs : |(t : ℚ) - p - m| ≤ 2 ^ 65 := by rw [abs_le]; constructor <;> linarith
  calc |(t : ℚ) - p - m| * 10 ^ loan.loanScale ≤ 2 ^ 65 * 10 ^ (80 : ℤ) :=
        mul_le_mul habs hp80 hp10.le (by norm_num)
    _ < 10 ^ 200 := by norm_num

/-- PrincipalOutstanding of a lawful loan has headroom. -/
lemma principal_headroom (loan : Loan) : Headroom loan.principalOutstanding := by
  refine Headroom.of_abs_lt loan.wf.principalOutstanding_norm ?_
  obtain ⟨p, hp, hpv⟩ := loan.grid.principalOutstanding_atExponent
  change loan.principalOutstanding.toRat = (p : ℚ) * 10 ^ loan.loanScale at hpv
  change p < loan.broker.numericType.mantissaBound at hp
  have hb := NumericType.mantissaBound_le loan.broker.numericType
  have hs := loan.wf.loanScale_range
  have hp10 : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have hp80 : (10 : ℚ) ^ loan.loanScale ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hs.2
  have hp' : (p : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le hp hb
  have hp0 : (0 : ℚ) ≤ p := by positivity
  rw [hpv, abs_of_nonneg (by positivity)]
  calc (p : ℚ) * 10 ^ loan.loanScale ≤ 2 ^ 63 * 10 ^ (80 : ℤ) := mul_le_mul hp'.le hp80 hp10.le (by norm_num)
    _ < 10 ^ 200 := by norm_num

/-- PrincipalOutstanding of a lawful loan is below `10^200`. -/
lemma principal_lt_pow (loan : Loan) : loan.principalOutstanding.toRat < 10 ^ 200 := by
  obtain ⟨p, hp, hpv⟩ := loan.grid.principalOutstanding_atExponent
  change loan.principalOutstanding.toRat = (p : ℚ) * 10 ^ loan.loanScale at hpv
  change p < loan.broker.numericType.mantissaBound at hp
  have hb := NumericType.mantissaBound_le loan.broker.numericType
  have hs := loan.wf.loanScale_range
  have hp10 : (0 : ℚ) < 10 ^ loan.loanScale := zpow_pos (by norm_num) _
  have hp80 : (10 : ℚ) ^ loan.loanScale ≤ 10 ^ (80 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hs.2
  have hp' : (p : ℚ) < 2 ^ 63 := by exact_mod_cast lt_of_lt_of_le hp hb
  rw [hpv]
  calc (p : ℚ) * 10 ^ loan.loanScale ≤ 2 ^ 63 * 10 ^ (80 : ℤ) := mul_le_mul hp'.le hp80 hp10.le (by norm_num)
    _ < 10 ^ 200 := by norm_num

/-- A LoanAccept operation fails the model only at a lawfulness re-check. -/
lemma accept_error (loan : Loan) (v : Vault) (hyu : Headroom v.yieldUnrealized) (hts : v.TotalStored) {e : Error}
    (h : (loan.accept v).run = .error e) : e = .notLawful := by
  simp only [Loan.accept] at h
  unfold_ter at h
  walk_ok'
  · obtain ⟨x, hx⟩ := Loan.interestDue_ok loan
    rw [hx] at ‹loan.interestDue = Except.error e›
    cases ‹Except.ok x = Except.error e›
  · rename_i x hx _ _ hadj
    obtain ⟨aa', ad', lu', ar', yu', hs⟩ := adjustSums_exists v
      { yield := x, reserved := loan.principalOutstanding.operator_neg } (cash_zero v _ rfl) Headroom.zero
      Headroom.zero (principal_headroom loan).neg (interestDue_headroom loan x hx) hyu
    exact poolAdjust_error v _ _ _ _ _ _ hs (fun _ _ => totalStores_kept v hts _ rfl rfl _ _ _ _ _ hs) hadj
  · exact loan_to_lawful_error ‹_›
  · obtain ⟨a, ha, -⟩ := Loan.acceptAmount_ok loan
    rw [ha] at ‹_ = Except.error e›
    cases ‹Except.ok a = Except.error e›

/-- A rounded value lies between any two normalized values that bracket the exact one. -/
lemma rounds_between {r : Number} {q : ℚ} {mode : rounding_mode} (hr : Number.RoundsToRepresentable r q mode)
    {lo hi : Number} (hlo : lo.isNormalized) (hhi : hi.isNormalized) (h1 : lo.toRat ≤ q) (h2 : q ≤ hi.toRat) :
    lo.toRat ≤ r.toRat ∧ r.toRat ≤ hi.toRat := by
  have hlower : ∀ n, Number.lower q = some n → r.toRat = n.toRat → lo.toRat ≤ r.toRat ∧ r.toRat ≤ hi.toRat :=
    fun n hn hv => by
      rw [hv]; exact ⟨Number.lower_tight q n hn lo hlo h1, le_trans (Number.lower_le q n hn) h2⟩
  have hupper : ∀ n, Number.upper q = some n → r.toRat = n.toRat → lo.toRat ≤ r.toRat ∧ r.toRat ≤ hi.toRat :=
    fun n hn hv => by
      rw [hv]; exact ⟨le_trans h1 (Number.le_upper q n hn), Number.upper_tight q n hn hi hhi h2⟩
  cases mode <;> simp only [Number.RoundsToRepresentable] at hr
  · rcases hr with ⟨n, hn, hv⟩ | ⟨n, hn, hv⟩
    · exact hlower n hn hv
    · exact hupper n hn hv
  · obtain ⟨n, hn, hv⟩ := hr
    split at hn
    · exact hlower n hn hv
    · exact hupper n hn hv
  · obtain ⟨n, hn, hv⟩ := hr; exact hlower n hn hv
  · obtain ⟨n, hn, hv⟩ := hr; exact hupper n hn hv

/-- A sum of two normalized values, not in `upward`, is normalized and stays between any two normalized values
that bracket zero and the exact sum. -/
lemma add_between {x y r : Number} {mode : rounding_mode} (hmode : mode ≠ .upward) (hx : x.isNormalized)
    (hy : y.isNormalized) (hok : x.operator_add y mode = .ok r) {lo hi : Number} (hlo : lo.isNormalized)
    (hhi : hi.isNormalized) (h1 : lo.toRat ≤ x.toRat + y.toRat) (h2 : x.toRat + y.toRat ≤ hi.toRat)
    (hlo0 : lo.toRat ≤ 0) (hhi0 : 0 ≤ hi.toRat) :
    r.isNormalized ∧ lo.toRat ≤ r.toRat ∧ r.toRat ≤ hi.toRat := by
  refine ⟨Number.operator_add_isNormalized_any x y r mode hx hy hok, ?_⟩
  by_cases h0 : r.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero r h0]; exact ⟨hlo0, hhi0⟩
  · cases mode with
    | to_nearest => exact rounds_between (Number.operator_add_rounded_to_nearest x y r hx hy hok) hlo hhi h1 h2
    | towards_zero =>
      exact rounds_between (Number.operator_add_rounded_towards_zero x y r hx hy hok) hlo hhi h1 h2
    | downward => exact rounds_between (Number.operator_add_rounded_downward x y r hx hy hok h0) hlo hhi h1 h2
    | upward => exact absurd rfl hmode

/-- `10^k` is a normalized `Number` for `k` up to `190`. -/
lemma pow_number (k : ℕ) (hk : k ≤ 190) : ∃ w : Number, w.isNormalized ∧ w.toRat = 10 ^ k := by
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (k : ℤ) (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  exact ⟨w, hw, by rw [hwv, zpow_natCast]; norm_num⟩

/-- A sum of two normalized values, not in `upward`, whose exact sum is from zero to `10^k`, is from zero to
`10^k` and has headroom. -/
lemma add_nonneg_facts {x y r : Number} {mode : rounding_mode} (hmode : mode ≠ .upward) (hx : x.isNormalized)
    (hy : y.isNormalized) (hok : x.operator_add y mode = .ok r) (k : ℕ) (hk : k ≤ 190)
    (h0 : 0 ≤ x.toRat + y.toRat) (hle : x.toRat + y.toRat ≤ 10 ^ k) :
    Headroom r ∧ 0 ≤ r.toRat ∧ r.toRat ≤ 10 ^ k := by
  obtain ⟨w, hw, hwv⟩ := pow_number k hk
  obtain ⟨hrn, hr0, hrle⟩ := add_between hmode hx hy hok Number.zero_isNormalized hw
    (by rw [Number.toRat_zero]; exact h0) (by rw [hwv]; exact hle) (by rw [Number.toRat_zero])
    (by rw [hwv]; positivity)
  rw [Number.toRat_zero] at hr0
  rw [hwv] at hrle
  refine ⟨Headroom.of_abs_lt hrn ?_, hr0, hrle⟩
  rw [abs_of_nonneg hr0]
  exact lt_of_le_of_lt hrle (pow_lt_pow_right₀ (by norm_num) (by omega))

/-- AssetsAvailable is below `10^96`, as the asset stores it. -/
lemma available_lt_pow (v : Vault) : v.assetsAvailable.toRat < 10 ^ 96 :=
  STAmount.Representable.lt_pow _ _ ((STAmount.isRounded_eq_false_iff _ _ v.wf.assetsAvailable_norm
    v.exact.assetsAvailable_nonneg).mp v.valid.assetsAvailable_representable)

/-- The Open-limit check computes for a value with headroom, while YieldUnrealized is below `10^96`. -/
lemma exceedsOpenLimit_ok (v : Vault) (x : Number) (hx : Headroom x) (hyu : v.yieldUnrealized.toRat < 10 ^ 96) :
    ∃ b, v.exceedsOpenLimit x = .ok b := by
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hY0 : 0 ≤ v.yieldUnrealized.toRat := v.exact.yieldUnrealized_nonneg
  have hAA := available_lt_pow v
  have hAD := Vault.assetsDeployed_lt_pow v
  have hbase := Vault.baseExponent_scale_range v

  obtain ⟨atot, hat⟩ := Number.operator_add_ok_of_lt v.assetsAvailable v.assetsDeployed .downward
    v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm hAA0 hAA hAD0 hAD
  obtain ⟨hatH, hat0, hatle⟩ := add_nonneg_facts (by decide) v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm hat
    97 (by norm_num) (by linarith) (by linarith [show (2 : ℚ) * 10 ^ 96 ≤ 10 ^ 97 by norm_num])

  obtain ⟨s₁, hs₁⟩ := hatH.add_ok (Headroom.of_nonneg_lt v.wf.yieldUnrealized_norm hY0 hyu) .towards_zero
  obtain ⟨hs₁H, -, -⟩ := add_nonneg_facts (by decide) hatH.1 v.wf.yieldUnrealized_norm hs₁ 98 (by norm_num)
    (by linarith) (by linarith [show (10 : ℚ) ^ 97 + 10 ^ 96 ≤ 10 ^ 98 by norm_num])

  obtain ⟨capacity, hcap⟩ := hs₁H.add_ok hx .towards_zero
  obtain ⟨limit, hlim, -, -⟩ := Number.from_rep_exact (9 : Int64) (15 + v.baseExponent) .to_nearest (by decide)
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  refine ⟨capacity.operator_gt limit, ?_⟩
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit XRPL.Model.SingleAssetVault.Vault.openLimit
  rw [show v.assetsTotal = .ok atot from hat]
  simp only [bind, Except.bind, pure, Except.pure, hs₁, hcap, hlim]

/-- A lawful loan's interestDue never fails. -/
lemma interestDue_ne_error (loan : Loan) (e : Error) : loan.interestDue ≠ .error e := by
  obtain ⟨x, hx⟩ := Loan.interestDue_ok loan
  rw [hx]; exact nofun

/-- The Open-limit check of a loan's interestDue never fails while YieldUnrealized is below `10^96`. -/
lemma interest_openLimit_ne_error (loan : Loan) (v : Vault) (hyu : v.yieldUnrealized.toRat < 10 ^ 96) {x : Number}
    {e : Error} (hx : loan.interestDue = .ok x) : v.exceedsOpenLimit x ≠ .error e := by
  obtain ⟨b, hb⟩ := exceedsOpenLimit_ok v x (interestDue_headroom loan x hx) hyu
  rw [hb]; exact nofun

/-- The LoanAccept checks compute while YieldUnrealized is below `10^96`. -/
lemma canAccept_ne_error (loan : Loan) (v : Vault) (now : UInt32) (hyu : v.yieldUnrealized.toRat < 10 ^ 96)
    (e : Error) : loan.canAccept v now ≠ .error e := by
  intro h
  unfold Loan.canAccept at h
  simp only [bind, Except.bind, pure, Except.pure, Vault.pool_exceedsOpenLimit] at h
  walk_ok'
  all_goals first
    | exact interestDue_ne_error loan _ ‹_›
    | exact interest_openLimit_ne_error loan v hyu ‹_› ‹_›

/-- A loan transaction that fails the model failed in its loan operation. -/
lemma applyLoan_error {l : LendingLedger} {tx : LendingTx} (hl : tx.isLoan = true) {e : Error}
    (h : (l.apply tx).run = .error e) : (l.applyLoan tx).run = .error e := by
  obtain ⟨-, ha⟩ := LendingLedger.apply_error h
  cases tx <;> simp only [LendingTx.isLoan, Bool.false_eq_true] at hl <;>
  · simp only [LendingLedger.applyChecked, LendingTx.isVault, LendingTx.isBroker, Bool.false_eq_true,
      ↓reduceIte] at ha
    split at ha
    · cases ha
    · exact TerExcept.map_error ha

/-- On a reachable ledger YieldUnrealized is below `10^96`. -/
lemma yield_lt_pow {l : LendingLedger} (hr : l.Reachable) : l.vault.yieldUnrealized.toRat < 10 ^ 96 := by
  have h := hr.yield_lt
  obtain ⟨-, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  nlinarith

/-- On a reachable ledger AssetsDeployed is below `10^80`. -/
lemma deployed_lt_pow {l : LendingLedger} (hr : l.Reachable) : l.vault.assetsDeployed.toRat < 10 ^ 80 := by
  obtain ⟨d, hd, hdv⟩ := hr.deployed_units
  obtain ⟨-, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hd' : (d : ℚ) ≤ 10 ^ 16 := by exact_mod_cast hd
  rw [hdv]
  have h1 : (d : ℚ) * 10 ^ l.vault.baseExponent ≤ (d : ℚ) * 1 := mul_le_mul_of_nonneg_left hp1 (by positivity)
  linarith [show (10 : ℚ) ^ 16 < 10 ^ 80 by norm_num]

/-- The LoanManage checks never fail: a lawful loan keeps its grace period end within the ledger clock. -/
lemma canManage_ne_error (loan : Loan) (action : LoanManageAction) (now : UInt32) (e : Error) :
    loan.canManage action now ≠ .error e := by
  unfold Loan.canManage
  rw [UInt32.addChecked_of_lt loan.gracePeriodEnd_lt]
  simp only [bind, Except.bind, pure, Except.pure]
  split_ifs <;> exact nofun

/-- A change of LossUnrealized alone fails the model only at the lawfulness re-check of the new vault. -/
lemma loss_change_error (v : Vault) (x : Number) (hx : Headroom x) (hyu : Headroom v.yieldUnrealized)
    (hts : v.TotalStored) {e : Error} (h : AssetPool.adjustBalances v { loss := x } = .error e) :
    e = .notLawful := by
  obtain ⟨aa', ad', lu', ar', yu', hs⟩ := adjustSums_exists v { loss := x } (cash_zero v _ rfl) Headroom.zero hx
    Headroom.zero Headroom.zero hyu
  exact poolAdjust_error v _ _ _ _ _ _ hs (fun _ _ => totalStores_kept v hts _ rfl rfl _ _ _ _ _ hs) h

/-- An impair or an unimpair fails the model only at a lawfulness re-check. -/
lemma changeImpairment_error (loan : Loan) (v : Vault) (impaired : Bool) (hyu : Headroom v.yieldUnrealized)
    (hts : v.TotalStored) {e : Error} (h : (Loan.changeImpairment loan v impaired).run = .error e) :
    e = .notLawful := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok'
  all_goals first
    | exact loss_change_error v _ (principal_headroom loan) hyu hts ‹_›
    | exact loss_change_error v _ (principal_headroom loan).neg hyu hts ‹_›
    | exact loan_to_lawful_error ‹_›

/-- An impair fails the model only at a lawfulness re-check. -/
lemma manageImpair_error (loan : Loan) (v : Vault) (now : UInt32) (hyu : Headroom v.yieldUnrealized)
    (hts : v.TotalStored) {e : Error} (h : (loan.manageImpair v now).run = .error e) : e = .notLawful := by
  simp only [Loan.manageImpair] at h
  unfold_ter at h
  walk_ok'
  exact changeImpairment_error loan v true hyu hts ‹_›

/-- The asset's largest amount is a normalized `Number`. -/
lemma maxAmount_number (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = nt.maxAmount := by
  rcases hnt with rfl | rfl | rfl
  · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16 - 1) 80 (by constructor <;> norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    exact ⟨w, hw, by rw [hwv, NumericType.maxAmount_fractional]; norm_num⟩
  · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 17) 0 (by constructor <;> norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    refine ⟨w, hw, ?_⟩
    rw [hwv]
    show ((10 ^ 17 : ℤ) : ℚ) * 10 ^ (0 : ℤ) = ((100000000000000000 : UInt64).toNat : ℚ)
    norm_num
    decide
  · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (2 ^ 63 - 1) 0 (by constructor <;> norm_num)
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
    refine ⟨w, hw, ?_⟩
    rw [hwv]
    show ((2 ^ 63 - 1 : ℤ) : ℚ) * 10 ^ (0 : ℤ) = ((9223372036854775807 : UInt64).toNat : ℚ)
    norm_num
    decide

/-- A value from zero to the asset's largest amount rounds to the asset without an error. -/
lemma round_ok_of_le_max (nt : NumericType)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64) (x : Number)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat) (hle : x.toRat ≤ nt.maxAmount) :
    ∃ y, STAmount.roundToNumericType nt x .to_nearest = .ok y := by
  have hin : STAmount.RoundsInRange nt .to_nearest x.toRat := by
    rcases hnt with rfl | rfl | rfl
    · rw [NumericType.maxAmount_fractional] at hle
      show |x.toRat| < 99999999999999995 * 10 ^ 79
      rw [abs_of_nonneg h0]
      linarith [show ((10 : ℚ) ^ 16 - 1) * 10 ^ 80 < 99999999999999995 * 10 ^ 79 by norm_num]
    · left
      rw [abs_of_nonneg h0]
      have : x.toRat ≤ ((100000000000000000 : UInt64).toNat : ℚ) := hle
      linarith
    · left
      rw [abs_of_nonneg h0]
      have : x.toRat ≤ ((9223372036854775807 : UInt64).toNat : ℚ) := hle
      linarith
  obtain ⟨ret, hret⟩ := (STAmount.ofNumber_ok_iff nt x .to_nearest hx hnt (Or.inl h0)).mpr hin
  unfold STAmount.roundToNumericType
  rw [hret]
  show ∃ y, ret.toNumber .to_nearest = .ok y
  cases hint : nt.isIntegral
  · rw [NumericType.eq_fractional_of_not_integral hint] at hret
    obtain ⟨n, hn, -⟩ := (STAmount.ofNumber_fractional_fczr x .to_nearest ret hret).toNumber_ok .to_nearest
    exact ⟨n, hn⟩
  · obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ ret hint hret
    have hmaxrep : nt.maxValue.toNat ≤ maxRep.toNat := by
      rcases hnt with rfl | rfl | rfl
      · cases hint
      all_goals decide
    have hsmall : ret.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 := hic.in_range
      rw [hty] at h1
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨sn, hsn, -⟩ := STAmount.toNumber_integral_small_exact ret .to_nearest hic hsmall
    exact ⟨sn, hsn⟩

/-- Adding an amount from zero to AssetsAvailable and rounding the sum to the asset never fails, while the sum is
at most the asset's largest amount. -/
lemma cash_ok (v : Vault) (hasset : Vault.HoldsAsset v) (c : Number) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hroom : v.assetsAvailable.toRat + c.toRat ≤ v.numericType.maxAmount) :
    ∃ aa aa', v.assetsAvailable.operator_add c .to_nearest = .ok aa ∧
      STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa' := by
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hmax := NumericType.maxAmount_lt v.numericType
  obtain ⟨aa, haa⟩ := Number.operator_add_ok_of_lt v.assetsAvailable c .to_nearest v.wf.assetsAvailable_norm hc
    hAA0 (available_lt_pow v) hc0 (by linarith)
  obtain ⟨w, hw, hwv⟩ := maxAmount_number v.numericType hasset
  obtain ⟨haan, haa0, haale⟩ := add_between (by decide) v.wf.assetsAvailable_norm hc haa Number.zero_isNormalized hw
    (by rw [Number.toRat_zero]; linarith) (by rw [hwv]; exact hroom) (by rw [Number.toRat_zero])
    (by rw [hwv]; linarith)
  rw [Number.toRat_zero] at haa0
  rw [hwv] at haale
  obtain ⟨aa', haa'⟩ := round_ok_of_le_max v.numericType hasset aa haan haa0 haale
  exact ⟨aa, aa', haa, haa'⟩

/-- The total after an update that takes `out` from AssetsDeployed and credits at most `out` to AssetsAvailable is an
amount of the asset, when the vault stored its total. XRP and MPT amounts are whole units. -/
lemma totalStores_of_transfer (v : Vault) (hasset : Vault.HoldsAsset v) (hts : v.TotalStored)
    (c : PoolBalanceChange) (out : Number) (hout : out.isNormalized) (hout0 : 0 ≤ out.toRat)
    (hdep : c.deployed = out.operator_neg) (hcn : c.cash.isNormalized) (hc0 : 0 ≤ c.cash.toRat)
    (hcle : c.cash.toRat ≤ out.toRat) (hole : out.toRat ≤ v.assetsDeployed.toRat)
    (hroom : v.assetsAvailable.toRat + c.cash.toRat ≤ v.numericType.maxAmount)
    (hwhole : v.numericType.isIntegral = true → c.cash.toRat.den = 1 ∧ out.toRat.den = 1)
    (hiou : v.numericType = .fractional → v.assetsDeployed.toRat < 10 ^ 80)
    (aa' ad' lu' ar' yu' : Number) (hs : Vault.AdjustSums v c aa' ad' lu' ar' yu') (haa : 0 ≤ aa'.signum)
    (had : 0 ≤ ad'.signum) : TotalStores v.numericType aa' ad' := by
  obtain ⟨aa, haa1, haa2⟩ := hs.cash
  have had1 := hs.deployed
  rw [hdep] at had1
  have hAAN := v.wf.assetsAvailable_norm
  have hADN := v.wf.assetsDeployed_norm
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hnegN := Number.operator_neg_isNormalized _ hout
  have haaN := Number.operator_add_isNormalized_to_nearest_sz _ _ _ hAAN hcn haa1
  have haa0 : 0 ≤ aa.toRat := Number.operator_add_nonneg _ _ _ hAAN hcn haa1 (by linarith)
  have haa'N := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa2
  have haa'0 : 0 ≤ aa'.toRat := (Number.signum_nonneg_iff_toRat haa'N).mp haa
  have had'N := Number.operator_add_isNormalized_to_nearest_sz _ _ _ hADN hnegN had1
  have had'0 : 0 ≤ ad'.toRat := (Number.signum_nonneg_iff_toRat had'N).mp had
  refine XRPL.Model.SingleAssetVault.TotalStores.of_stored_cash hts hasset hAAN hADN hAA0 hAD0 aa' ad' haa'N had'N
    haa'0 had'0 (STAmount.isRounded_roundToNumericType _ _ _ haaN haa0 haa2) (fun hi => ?_) (fun hi => ?_)
  · -- whole units: both sums are exact
    obtain ⟨hcd, hod⟩ := hwhole hi
    obtain ⟨hAAd, -⟩ := STAmount.whole_of_stored _ hi _ hAAN hAA0 v.valid.assetsAvailable_representable
    obtain ⟨hADd, hAD63⟩ := STAmount.whole_of_stored _ hi _ hADN hAD0 v.valid.assetsDeployed_representable
    have hmN : v.numericType.maxValue.toNat ≤ 9223372036854775807 := by
      rcases hasset with h | h | h
      · rw [h] at hi; cases hi
      · rw [h]; decide
      · rw [h]; decide
    have hm : v.numericType.maxAmount ≤ 9223372036854775807 := by
      unfold NumericType.maxAmount
      rw [if_pos hi]
      exact_mod_cast hmN
    have haav : aa.toRat = v.assetsAvailable.toRat + c.cash.toRat :=
      Number.add_whole_exact hAAN hcn haa1 hAAd hcd (by linarith) (by linarith)
    have had'v : ad'.toRat = v.assetsDeployed.toRat - out.toRat := by
      rw [Number.add_whole_exact hADN hnegN had1 hADd (by rw [Number.toRat_neg, Rat.den_neg_eq_den]; exact hod)
        (by rw [Number.toRat_neg]; linarith) (by rw [Number.toRat_neg]; linarith), Number.toRat_neg]
      ring
    have hle := STAmount.round_whole_le _ hi hasset.maxValue_le aa aa' haaN haa0
      (by rw [haav]; exact Rat.den_one_add _ _ hAAd hcd) haa2
    rw [had'v]
    linarith
  · -- an IOU: the deployed balance does not grow
    obtain ⟨-, -, hle⟩ := add_between (by decide) hADN hnegN had1 hnegN hADN
      (by rw [Number.toRat_neg]; linarith) (by rw [Number.toRat_neg]; linarith)
      (by rw [Number.toRat_neg]; linarith) hAD0
    linarith [hiou (NumericType.eq_fractional_of_not_integral hi)]

/-- Releasing a loan from a broker that counts it fails only at the lawfulness re-check of the broker. -/
lemma releaseLoan_error (lb : LoanBroker) (d : Number) (hc0 : lb.loanCount ≠ 0) {e : Error}
    (h : lb.releaseLoan d = .error e) : e = .notLawful := by
  unfold LoanBroker.releaseLoan at h
  rw [UInt32.subChecked_of_le (UInt32.one_le_of_ne_zero hc0)] at h
  exact broker_to_lawful_error h

/-- The vault update of a pending LoanDelete fails only at the lawfulness re-check, while the asset stores the
principal and AssetsAvailable plus the principal is at most the asset's largest amount. -/
lemma deletePending_adjust_error (loan : Loan) (v : Vault) (hasset : Vault.HoldsAsset v)
    (hyu : Headroom v.yieldUnrealized) (hts : v.TotalStored) (hnt : loan.broker.numericType = v.numericType)
    (hpad : loan.principalOutstanding.toRat ≤ v.assetsDeployed.toRat)
    (hiou : v.numericType = .fractional → v.assetsDeployed.toRat < 10 ^ 80)
    (hpo : STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false)
    (hroom : v.assetsAvailable.toRat + loan.principalOutstanding.toRat ≤ v.numericType.maxAmount) {p' : Number}
    (hp' : STAmount.roundToNumericType loan.broker.numericType loan.principalOutstanding .to_nearest = .ok p')
    {e : Error}
    (h : AssetPool.adjustBalances v
      { cash := p', deployed := loan.principalOutstanding.operator_neg, reserved := p'.operator_neg } = .error e) :
    e = .notLawful := by
  have hpn := loan.wf.principalOutstanding_norm
  have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hp'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hp'
  have hp'v := STAmount.roundToNumericType_of_isRounded_false _ _ _ hpn hpo hp'
  have hp'H : Headroom p' := Headroom.of_nonneg_lt hp'n (by rw [hp'v]; exact hp0)
    (by rw [hp'v]; linarith [NumericType.maxAmount_lt v.numericType])
  obtain ⟨aa', ad', lu', ar', yu', hs⟩ := adjustSums_exists v
    { cash := p', deployed := loan.principalOutstanding.operator_neg, reserved := p'.operator_neg }
    (cash_ok v hasset p' hp'n (by rw [hp'v]; exact hp0) (by rw [hp'v]; exact hroom))
    (principal_headroom loan).neg Headroom.zero hp'H.neg Headroom.zero hyu
  -- the principal moves from AssetsDeployed to AssetsAvailable, so the total does not grow
  have hwhole : v.numericType.isIntegral = true →
      p'.toRat.den = 1 ∧ loan.principalOutstanding.toRat.den = 1 := fun hi => by
    have hd := (STAmount.whole_of_stored _ (by rw [hnt]; exact hi) _ hpn hp0 hpo).1
    exact ⟨by rw [hp'v]; exact hd, hd⟩
  exact poolAdjust_error v _ _ _ _ _ _ hs
    (totalStores_of_transfer v hasset hts
      { cash := p', deployed := loan.principalOutstanding.operator_neg, reserved := p'.operator_neg }
      loan.principalOutstanding hpn hp0 rfl hp'n (by rw [hp'v]; exact hp0) (le_of_eq hp'v) hpad
      (by rw [hp'v]; exact hroom) hwhole hiou _ _ _ _ _ hs) h

/-- A LoanDelete operation fails the model only at a lawfulness re-check. The broker counts the loan, and for
a pending loan the asset stores the principal and AssetsAvailable plus the principal. -/
lemma delete_error (loan : Loan) (v : Vault) (hasset : Vault.HoldsAsset v) (hyu : Headroom v.yieldUnrealized)
    (hts : v.TotalStored) (hnt : loan.broker.numericType = v.numericType)
    (hpad : loan.principalOutstanding.toRat ≤ v.assetsDeployed.toRat)
    (hiou : v.numericType = .fractional → v.assetsDeployed.toRat < 10 ^ 80)
    (hc0 : loan.broker.loanCount ≠ 0) (hdt : Headroom loan.broker.debtTotal)
    (hpo : loan.isPending = true → STAmount.isRounded loan.broker.numericType loan.principalOutstanding = false)
    (hroom : loan.isPending = true →
      v.assetsAvailable.toRat + loan.principalOutstanding.toRat ≤ v.numericType.maxAmount)
    {e : Error} (h : (loan.delete v).run = .error e) : e = .notLawful := by
  simp only [Loan.delete, Loan.deletePending, Loan.deleteActive] at h
  unfold_ter at h
  walk_ok'
  · obtain ⟨y, hy⟩ := STAmount.roundToNumericType_ok_of_isRounded_false _ _ (hpo ‹_›)
    rw [hy] at ‹_ = Except.error e›
    cases ‹Except.ok y = Except.error e›
  · exact deletePending_adjust_error loan v hasset hyu hts hnt hpad hiou (hpo ‹_›) (hroom ‹_›) ‹_› ‹_›
  · obtain ⟨d, hd⟩ := hdt.sub_ok (principal_headroom loan) .to_nearest
    rw [hd] at ‹_ = Except.error e›
    cases ‹Except.ok d = Except.error e›
  · exact releaseLoan_error _ _ hc0 ‹_›
  · exact releaseLoan_error _ _ hc0 ‹_›

/-- The cover a default pays computes, between zero and both PrincipalOutstanding and CoverAvailable. DebtTotal and
the principal are at most `10^16` base units, and an IOU vault is on the base grid with room for the principal. -/
lemma defaultCover_facts (loan : Loan) (v : Vault) (hasset : Vault.HoldsAsset v)
    (hnt : loan.broker.numericType = v.numericType) (hls : loan.loanScale = v.baseExponent)
    (hdt : ∃ t : ℕ, t ≤ 10 ^ 16 ∧ loan.broker.debtTotal.toRat = (t : ℚ) * 10 ^ v.baseExponent)
    (hp : loan.principalOutstanding.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ v.baseExponent)
    (hfrac : v.numericType = .fractional →
      (∃ a : ℕ, v.assetsAvailable.toRat = (a : ℚ) * 10 ^ v.baseExponent) ∧
      v.assetsAvailable.toRat + loan.principalOutstanding.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent ∧
      loan.broker.debtTotal.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent) :
    ∃ dc, loan.defaultCover v = .ok dc ∧ dc.isNormalized ∧ 0 ≤ dc.toRat ∧
      dc.toRat ≤ min loan.principalOutstanding.toRat loan.broker.coverAvailable.toRat ∧
      (v.numericType.isIntegral = true → dc.toRat.den = 1) := by
  set b := v.baseExponent with hbdef
  have hbase := v.baseExponent_bounds
  have hp10 : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2.1
  have hPO0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hCA0 : 0 ≤ loan.broker.coverAvailable.toRat := loan.broker.exact.coverAvailable_nonneg
  have hDT0 : 0 ≤ loan.broker.debtTotal.toRat := loan.broker.exact.debtTotal_nonneg
  obtain ⟨t, ht, htv⟩ := hdt
  have ht16 : (t : ℚ) ≤ 10 ^ 16 := by exact_mod_cast ht
  have hPO16 : loan.principalOutstanding.toRat ≤ 10 ^ 16 := by nlinarith

  cases hint : v.numericType.isIntegral
  · -- an IOU on the base grid: the cover is the capped liquidation amount floored to whole base units
    have hfr := NumericType.eq_fractional_of_not_integral hint
    obtain ⟨⟨a, hav⟩, hroom, hdtlt⟩ := hfrac hfr
    obtain ⟨p, -, hpv⟩ := loan.grid.principalOutstanding_atExponent
    simp only [RawLoan.toExact] at hpv
    rw [hls] at hpv
    have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
    have ha16 : a < 10 ^ 16 := by
      have h1 : (a : ℚ) * 10 ^ b < (10 ^ 16 : ℕ) * 10 ^ b := by push_cast; rw [← hav]; linarith
      exact_mod_cast lt_of_mul_lt_mul_right h1 hp10.le
    have ht16' : t < 10 ^ 16 := by
      have h1 : (t : ℚ) * 10 ^ b < (10 ^ 16 : ℕ) * 10 ^ b := by push_cast; rw [← htv]; exact hdtlt
      exact_mod_cast lt_of_mul_lt_mul_right h1 hp10.le
    have hap : a + p < 10 ^ 16 := by
      have h1 : ((a + p : ℕ) : ℚ) * 10 ^ b < (10 ^ 16 : ℕ) * 10 ^ b := by
        push_cast; rw [add_mul, ← hav, ← hpv]; exact hroom
      exact_mod_cast lt_of_mul_lt_mul_right h1 hp10.le
    obtain ⟨dc, hdc⟩ := Loan.defaultCover_ok loan v hasset hnt hls ⟨a, ha16, hav⟩ hroom ⟨t, ht16', htv⟩
    obtain ⟨mc, liq, -, -, hmc, hliq, -, -, -⟩ := Loan.defaultCover_parts loan v dc hdc
    have hcap0 := Loan.cappedCover_nonneg loan mc liq hmc hliq
    have hpow16 : (10 : ℚ) ^ (16 + b) = 10 ^ 16 * 10 ^ b := by rw [zpow_add₀ (by norm_num)]; norm_num
    have hdcv := Loan.defaultCover_at_base loan v dc mc liq a hdc hmc hliq hnt hav (by
      rw [hpow16]
      have h1 : v.assetsAvailable.toRat + loan.principalOutstanding.toRat = ((a + p : ℕ) : ℚ) * 10 ^ b := by
        rw [hav, hpv]; push_cast; ring
      have h2 : ((a + p : ℕ) : ℚ) ≤ 10 ^ 16 - 1 := by
        have : a + p ≤ 10 ^ 16 - 1 := by omega
        have h3 : ((10 ^ 16 - 1 : ℕ) : ℚ) = 10 ^ 16 - 1 := by norm_num
        rw [← h3]; exact_mod_cast this
      have h4 : min (min liq.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat ≤
          loan.principalOutstanding.toRat := min_le_of_left_le (min_le_right _ _)
      nlinarith)
    set capped := min (min liq.toRat loan.principalOutstanding.toRat) loan.broker.coverAvailable.toRat with hcapdef
    have hk0 : 0 ≤ ⌊capped / 10 ^ b⌋ := Int.floor_nonneg.mpr (div_nonneg hcap0 hp10.le)
    have hkcap : (⌊capped / 10 ^ b⌋ : ℚ) * 10 ^ b ≤ capped := by
      have := Int.floor_le (capped / 10 ^ b)
      rwa [le_div_iff₀ hp10] at this
    refine ⟨dc, hdc, Loan.defaultCover_isNormalized loan v dc hdc, ?_, ?_,
      fun hi => absurd hi (by decide)⟩
    · rw [hdcv]
      have : (0 : ℚ) ≤ (⌊capped / 10 ^ b⌋ : ℚ) := by exact_mod_cast hk0
      positivity
    · rw [hdcv]
      exact le_trans hkcap (le_min (min_le_of_left_le (min_le_right _ _)) (min_le_right _ _))
  · -- XRP or an MPT: the cover does not read AssetsAvailable
    have hint' : loan.broker.numericType.isIntegral = true := by rw [hnt]; exact hint
    have hb0 : b = 0 := Vault.baseExponent_integral v hint
    rw [hb0, zpow_zero, mul_one] at htv hp
    obtain ⟨room, hoff, hmaxrep⟩ := Vault.HoldsAsset.integral_room hasset hint
    rw [← hnt] at room hoff hmaxrep
    have hbv := loan.broker.valid
    have hrmin : loan.broker.coverRateMinimum.toNat ≤ 100000 := by
      have := hbv.coverRateMinimum_cap; unfold maxCoverRate at this; exact UInt32.le_iff_toNat_le.mp this
    have hrliq : loan.broker.coverRateLiquidation.toNat ≤ 100000 := by
      have := hbv.coverRateLiquidation_cap; unfold maxCoverRate at this; exact UInt32.le_iff_toNat_le.mp this
    obtain ⟨mc, hmc, hmcn, hmc0, hmcle, hmclo⟩ := tenthBipsOfValue_upward_ok loan.broker.debtTotal
      loan.broker.coverRateMinimum 0 loan.broker.wf.debtTotal_norm hDT0 (by rw [htv]; linarith) (by norm_num)
      (fun h0 => by
        rw [htv]
        have ht1 : 1 ≤ t := by
          rcases Nat.eq_zero_or_pos t with h | h
          · exfalso; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ h0 (by rw [htv, h]; simp)
          · exact h
        have : (1 : ℚ) ≤ t := by exact_mod_cast ht1
        simpa using this)
      hrmin
    obtain ⟨liq, hliq, hliqn, hliq0, -, -⟩ := tenthBipsOfValue_upward_ok mc loan.broker.coverRateLiquidation (-5)
      hmcn hmc0 (by rw [htv] at hmcle; linarith) (by norm_num) (fun h0 => by simpa using hmclo h0) hrliq
    obtain ⟨hm1, hm1n⟩ := Number.min_toRat liq loan.principalOutstanding hliqn loan.wf.principalOutstanding_norm
    obtain ⟨hm2, hm2n⟩ := Number.min_toRat _ loan.broker.coverAvailable hm1n loan.broker.wf.coverAvailable_norm
    obtain ⟨capped, hcapeq⟩ : ∃ x, x = Number.min (Number.min liq loan.principalOutstanding)
        loan.broker.coverAvailable := ⟨_, rfl⟩
    rw [← hcapeq] at hm2 hm2n
    have hcap0 : 0 ≤ capped.toRat := by rw [hm2, hm1]; exact le_min (le_min hliq0 hPO0) hCA0
    have hcapPO : capped.toRat ≤ loan.principalOutstanding.toRat := by
      rw [hm2, hm1]; exact min_le_of_left_le (min_le_right _ _)
    have hcapCA : capped.toRat ≤ loan.broker.coverAvailable.toRat := by rw [hm2]; exact min_le_right _ _

    -- the cap rounds to the asset towards zero
    obtain ⟨c, hc⟩ : ∃ c, STAmount.roundToNumericType loan.broker.numericType capped .towards_zero = .ok c := by
      unfold STAmount.roundToNumericType
      obtain ⟨ret, hret⟩ := STAmount.ofNumber_integral_ok_of_lt _ capped .towards_zero hint' hoff hm2n hcap0
        (by linarith) (by linarith)
      rw [hret]
      obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ ret hint' hret
      have hsmall : ret.mValue.toNat ≤ 2 ^ 63 - 1 := by
        have h1 := hic.in_range
        rw [hty] at h1
        have : maxRep.toNat = 2 ^ 63 - 1 := by decide
        omega
      obtain ⟨sn, hsn, -⟩ := STAmount.toNumber_integral_small_exact ret _ hic hsmall
      exact ⟨sn, hsn⟩
    obtain ⟨hc0, hcle, hcn⟩ := STAmount.roundToNumericType_towards_zero_le _ _ _ hm2n hcap0 hc

    -- the credit is the rounded cap as an amount of the asset
    obtain ⟨st, hof⟩ := STAmount.ofNumber_integral_ok_of_lt _ c .downward hint' hoff hcn hc0 (by linarith)
      (by linarith)
    have hst : sumRoundAndSubtract v.assetsAvailable c v.baseExponent loan.broker.numericType .downward =
        .ok st := by
      unfold sumRoundAndSubtract
      rw [if_pos hint', hof]
      rfl
    obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ st hint' hof
    have hsmall : st.mValue.toNat ≤ 2 ^ 63 - 1 := by
      have h1 := hic.in_range
      rw [hty] at h1
      have : maxRep.toNat = 2 ^ 63 - 1 := by decide
      omega
    obtain ⟨dc, hdc, hdcv, hdcn⟩ := STAmount.toNumber_integral_small_exact st .to_nearest hic hsmall
    have hst0 : 0 ≤ st.toRat ∧ st.toRat ≤ c.toRat := by
      by_cases hz : st.mValue = 0
      · rw [STAmount.toRat_eq_zero_of_mValue_zero st hz]; exact ⟨le_refl _, hc0⟩
      · obtain ⟨h1, -, h2⟩ := STAmount.ofNumber_downward_floor_bounds _ c st hcn
          (Number.negative_false_of_nonneg c hcn hc0) hof hz
        exact ⟨h2, h1⟩
    refine ⟨dc, ?_, hdcn, by rw [hdcv]; exact hst0.1, ?_, fun _ => by rw [hdcv]; exact hic.den_eq_one⟩
    · show (tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward >>= fun minimumCover =>
        tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward >>= fun liquidationAmount =>
        STAmount.roundToNumericType loan.broker.numericType
          (Number.min (Number.min liquidationAmount loan.principalOutstanding) loan.broker.coverAvailable)
          .towards_zero >>= fun coveredAmount =>
        sumRoundAndSubtract v.assetsAvailable coveredAmount v.baseExponent loan.broker.numericType .downward >>=
          fun defaultCovered => defaultCovered.toNumber .to_nearest) = _
      rw [hmc, ok_bind, hliq, ok_bind, ← hcapeq, hc, ok_bind, hst, ok_bind, hdc]
    · rw [hdcv]
      exact le_min (by linarith) (by linarith)

/-- What a default needs from the cover it pays: it computes, it lies between zero and both
PrincipalOutstanding and CoverAvailable, and on XRP or an MPT it is a whole number of units. -/
structure CoverFacts (loan : Loan) (v : Vault) : Prop where
  ok : ∀ e : Error, loan.defaultCover v ≠ .error e
  bounds : ∀ dc : Number, loan.defaultCover v = .ok dc → dc.isNormalized ∧ 0 ≤ dc.toRat ∧
    dc.toRat ≤ min loan.principalOutstanding.toRat loan.broker.coverAvailable.toRat ∧
    (v.numericType.isIntegral = true → dc.toRat.den = 1)

/-- A cover that computes within its bounds gives the facts a default needs. -/
lemma CoverFacts.of_ok {loan : Loan} {v : Vault}
    (h : ∃ dc, loan.defaultCover v = .ok dc ∧ dc.isNormalized ∧ 0 ≤ dc.toRat ∧
      dc.toRat ≤ min loan.principalOutstanding.toRat loan.broker.coverAvailable.toRat ∧
      (v.numericType.isIntegral = true → dc.toRat.den = 1)) : CoverFacts loan v := by
  obtain ⟨dc, hdc, hfacts⟩ := h
  refine ⟨fun e he => ?_, fun dc' hdc' => ?_⟩
  · rw [hdc] at he
    cases he
  · rw [hdc] at hdc'
    cases hdc'
    exact hfacts

/-- A default fails the model only at a lawfulness re-check, while the cover computes and AssetsAvailable plus
the smaller of PrincipalOutstanding and CoverAvailable is at most the asset's largest amount. -/
lemma manageDefault_error (loan : Loan) (v : Vault) (hasset : Vault.HoldsAsset v)
    (hyu : Headroom v.yieldUnrealized) (hts : v.TotalStored) (hls : loan.loanScale = v.baseExponent)
    (hpad : loan.principalOutstanding.toRat ≤ v.assetsDeployed.toRat)
    (hiou : v.numericType = .fractional → v.assetsDeployed.toRat < 10 ^ 80)
    (hdt : Headroom loan.broker.debtTotal)
    (hca : Headroom loan.broker.coverAvailable) (hcover : CoverFacts loan v)
    (hroom : v.assetsAvailable.toRat + min loan.principalOutstanding.toRat loan.broker.coverAvailable.toRat ≤
      v.numericType.maxAmount)
    {e : Error} (h : (loan.manageDefault v).run = .error e) : e = .notLawful := by
  rw [Loan.manageDefault_run] at h
  cases hi : loan.interestDue with
  | error e' => exact (interestDue_ne_error loan e' hi).elim
  | ok i =>
    rw [hi] at h
    dsimp only at h
    cases hdc : loan.defaultCover v with
    | error e' => exact (hcover.ok e' hdc).elim
    | ok dc =>
      rw [hdc] at h
      dsimp only at h
      obtain ⟨hdcn, hdc0, hdcle, hdcw⟩ := hcover.bounds dc hdc
      have hdcH : Headroom dc := Headroom.of_abs_lt hdcn (by
        rw [abs_of_nonneg hdc0]
        exact lt_of_le_of_lt (le_trans hdcle (min_le_left _ _)) (principal_lt_pow loan))
      have hloss : Headroom (loan.defaultChange i dc).loss := by
        show Headroom (if loan.isImpaired then loan.principalOutstanding.operator_neg else Number.zero)
        split
        · exact (principal_headroom loan).neg
        · exact Headroom.zero

      -- the five sums of the vault update compute
      obtain ⟨aa', ad', lu', ar', yu', hs⟩ := adjustSums_exists v (loan.defaultChange i dc)
        (cash_ok v hasset dc hdcn hdc0 (by linarith)) (principal_headroom loan).neg hloss Headroom.zero
        (interestDue_headroom loan i hi).neg hyu
      -- the cover is at most the principal that leaves AssetsDeployed, so the total does not grow
      have hwhole : v.numericType.isIntegral = true →
          dc.toRat.den = 1 ∧ loan.principalOutstanding.toRat.den = 1 := fun hint => by
        obtain ⟨p, -, hpv⟩ := loan.grid.principalOutstanding_atExponent
        simp only [RawLoan.toExact] at hpv
        rw [hls, Vault.baseExponent_integral v hint, zpow_zero, mul_one] at hpv
        exact ⟨hdcw hint, by rw [hpv]; exact Rat.den_natCast p⟩
      cases hadj : AssetPool.adjustBalances v (loan.defaultChange i dc) with
      | error e' =>
        rw [hadj] at h
        cases h
        exact poolAdjust_error v _ _ _ _ _ _ hs
          (totalStores_of_transfer v hasset hts (loan.defaultChange i dc) loan.principalOutstanding
            loan.wf.principalOutstanding_norm loan.exact.principalOutstanding_nonneg rfl hdcn hdc0
            (le_trans hdcle (min_le_left _ _)) hpad (le_trans (add_le_add_right hdcle _) hroom) hwhole hiou
            _ _ _ _ _ hs) hadj
      | ok res =>
        rw [hadj] at h
        cases res with
        | error ter => cases h
        | ok v' =>
          dsimp only at h
          obtain ⟨d, hd⟩ := hdt.sub_ok (principal_headroom loan) .to_nearest
          rw [hd] at h
          dsimp only at h
          obtain ⟨c, hc⟩ := hca.sub_ok hdcH .to_nearest
          rw [hc] at h
          dsimp only at h
          cases hb : (loan.defaultedBroker d c).to_lawful with
          | error e' =>
            rw [hb] at h
            cases h
            exact broker_to_lawful_error hb
          | ok b' =>
            rw [hb] at h
            dsimp only at h
            cases hl : (loan.defaultedLoan b').to_lawful with
            | error e' =>
              rw [hl] at h
              cases h
              exact loan_to_lawful_error hl
            | ok l' =>
              rw [hl] at h
              cases h

/-- A management action other than a default fails the model only at a lawfulness re-check. -/
lemma manage_error (loan : Loan) (action : LoanManageAction) (v : Vault) (now : UInt32)
    (hyu : Headroom v.yieldUnrealized) (hts : v.TotalStored)
    (hdefault : ∀ {e : Error}, action = .default → (loan.manageDefault v).run = .error e → e = .notLawful)
    {e : Error} (h : (loan.manage action v now).run = .error e) : e = .notLawful := by
  cases action with
  | impair => exact manageImpair_error loan v now hyu hts h
  | unimpair => exact changeImpairment_error loan v false hyu hts h
  | default =>
    simp only [Loan.manage] at h
    unfold_ter at h
    walk_ok'
    exact hdefault rfl ‹_›

/-- On a reachable ledger the DebtTotal of a stored loan's broker has headroom. -/
lemma debt_headroom {l : LendingLedger} (hr : l.Reachable) {i : Nat} {loan : Loan}
    (hat : l.LoanAt i loan) : Headroom loan.broker.debtTotal := by
  obtain ⟨t, ht, htv⟩ := hr.loanAt_debt_units hat
  obtain ⟨-, hbhi, -⟩ := Vault.baseExponent_bounds l.vault
  have hp1 : (10 : ℚ) ^ l.vault.baseExponent ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbhi
  have hp : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
  have ht' : (t : ℚ) ≤ 10 ^ 16 := by exact_mod_cast ht
  refine Headroom.of_nonneg_lt loan.broker.wf.debtTotal_norm (by rw [htv]; positivity) ?_
  rw [htv]
  nlinarith

end NoExceptionLoanManage

end XRPL.Model.Lending
