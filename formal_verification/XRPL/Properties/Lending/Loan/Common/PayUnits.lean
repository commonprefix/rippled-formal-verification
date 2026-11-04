import XRPL.Properties.Lending.Loan.Common.PaySteps
import XRPL.Properties.Protocol.Number.Sub.ZeroShape

/-! # Payment amounts in whole units

A payment's sums are exact when every operand is a whole number of LoanScale units well below `2^63` units. These
lemmas read back what the vault update, the full payoff and the instalment amounts compute. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.fullComponents roundAndSplitInterest from XRPL.Model.Lending.Loan.LoanPay

/-- A vault update that passes wrote the five sums. -/
lemma Vault.adjustBalances_ok_inv (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (h : (v.adjustBalances c).run = .ok (.ok raw)) :
    Vault.AdjustSums v c raw.assetsAvailable raw.assetsDeployed raw.lossUnrealized raw.assetsReserved
      raw.yieldUnrealized ∧
    raw = { v.toRawVault with
      assetsAvailable := raw.assetsAvailable, assetsDeployed := raw.assetsDeployed,
      assetsReserved := raw.assetsReserved, lossUnrealized := raw.lossUnrealized,
      yieldUnrealized := raw.yieldUnrealized } := by
  simp only [ExceptT.run, XRPL.Model.SingleAssetVault.Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  exact ⟨⟨⟨_, ‹_›, ‹_›⟩, ‹_›, ‹_›, ‹_›, ‹_›⟩, rfl⟩

/-- The vault a successful pool update returns holds the five sums. -/
lemma Vault.poolAdjust_sums (v v' : Vault) (c : PoolBalanceChange) (h : AssetPool.adjustBalances v c = .ok (.ok v')) :
    Vault.AdjustSums v c v'.assetsAvailable v'.assetsDeployed v'.lossUnrealized v'.assetsReserved
      v'.yieldUnrealized ∧ v'.numericType = v.numericType ∧ v'.scale = v.scale := by
  obtain ⟨raw, hadj, hv'⟩ := Vault.poolAdjust_ok_inv v c v' h
  obtain ⟨hs, heq⟩ := Vault.adjustBalances_ok_inv v c raw hadj
  have h1 := (RawVault.to_lawful_ok hv').1
  rw [show v'.assetsAvailable = v'.toRawVault.assetsAvailable from rfl,
    show v'.assetsDeployed = v'.toRawVault.assetsDeployed from rfl,
    show v'.lossUnrealized = v'.toRawVault.lossUnrealized from rfl,
    show v'.assetsReserved = v'.toRawVault.assetsReserved from rfl,
    show v'.yieldUnrealized = v'.toRawVault.yieldUnrealized from rfl,
    show v'.numericType = v'.toRawVault.numericType from rfl, show v'.scale = v'.toRawVault.scale from rfl, h1]
  refine ⟨hs, ?_, ?_⟩
  · rw [heq]
  · rw [heq]

/-- A rounding to nearest of a value at or below `-10^b` stays below zero. -/
lemma Number.neg_of_rounds_le (d : Number) (q : ℚ) (b : Int) (hb : minExponent + 18 ≤ b ∧ b ≤ maxExponent - 1)
    (hR : d.RoundsToRepresentable q .to_nearest) (hq : q ≤ -(10 : ℚ) ^ b) : d.toRat < 0 := by
  have hpos : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (-1) b (by constructor <;> norm_num) hb
  rcases hR with ⟨n, hn, hdv⟩ | ⟨n, hn, hdv⟩
  · rw [hdv]; have := Number.lower_le q n hn; linarith
  · rw [hdv]
    have := Number.upper_tight q n hn w hw (by rw [hwv]; push_cast; linarith)
    rw [hwv] at this; push_cast at this; linarith

/-- The values a full payoff computes. -/
lemma Loan.fullComponents_ok_inv (l : Loan) (now : UInt32) (pc : PaymentComponents)
    (h : Loan.fullComponents l now = .ok pc) :
    ∃ rate tpo fi net split state cf ppi tracked cfm uf ui,
      l.periodicRate = .ok rate ∧
      loanPrincipalFromPeriodicPayment l.periodicPayment rate l.paymentRemaining = .ok tpo ∧
      computeFullPaymentInterest tpo rate now l.schedule.paymentInterval l.previousPaymentDueDate
        l.schedule.startDate l.rates.closeInterestRate = .ok fi ∧
      roundAndSplitInterest fi l.broker.managementFeeRate .downward l.broker.numericType l.loanScale =
        .ok (net, split) ∧
      l.state = .ok state ∧
      STAmount.roundToNumericType l.broker.numericType l.fees.closePaymentFee .to_nearest (some l.loanScale) =
        .ok cf ∧
      state.principalOutstanding.operator_add state.interestDue .to_nearest = .ok ppi ∧
      ppi.operator_add state.managementFeeDue .to_nearest = .ok tracked ∧
      cf.operator_add split .to_nearest = .ok cfm ∧
      cfm.operator_sub state.managementFeeDue .to_nearest = .ok uf ∧
      net.operator_sub state.interestDue .to_nearest = .ok ui ∧
      pc = { totalValueDelta := tracked, principalDelta := state.principalOutstanding,
             managementFeeDelta := state.managementFeeDue, isFinal := true, untrackedInterest := ui,
             untrackedManagementFee := uf } := by
  unfold Loan.fullComponents at h
  simp only [bind, Except.bind] at h
  walk_ok
  have hpc := (Except.ok.inj ‹pure _ = Except.ok pc›).symm
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hpc⟩

/-- The interest split: the rounded interest, its management fee, and the rest. -/
lemma roundAndSplitInterest_ok_inv (interest : Number) (rate : TenthBips16) (mode : rounding_mode)
    (nt : NumericType) (s : Int) (net fee : Number)
    (h : roundAndSplitInterest interest rate mode nt s = .ok (net, fee)) :
    ∃ interest', STAmount.roundToNumericType nt interest mode (some s) = .ok interest' ∧
      computeManagementFee nt interest' rate s = .ok fee ∧
      interest'.operator_sub fee .to_nearest = .ok net := by
  unfold roundAndSplitInterest at h
  simp only [bind, Except.bind] at h
  walk_ok
  have h1 := Except.ok.inj ‹pure _ = Except.ok (net, fee)›
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact ⟨_, ‹_›, ‹_›, ‹_›⟩

/-- The amounts an instalment pays. -/
lemma PaymentComponents.paidAmounts_ok_inv (pc : PaymentComponents) (amounts : PaymentAmounts)
    (h : pc.paidAmounts = .ok amounts) :
    ∃ vap id, pc.totalValueDelta.operator_sub pc.principalDelta .to_nearest = .ok vap ∧
      vap.operator_sub pc.managementFeeDelta .to_nearest = .ok id ∧
      id.operator_add pc.untrackedInterest .to_nearest = .ok amounts.interestPaid ∧
      pc.managementFeeDelta.operator_add pc.untrackedManagementFee .to_nearest = .ok amounts.feePaid ∧
      amounts.principalPaid = pc.principalDelta := by
  unfold PaymentComponents.paidAmounts PaymentComponents.interestDelta at h
  simp only [bind, Except.bind] at h
  walk_ok
  have h1 := (Except.ok.inj ‹pure _ = Except.ok amounts›).symm
  subst h1
  exact ⟨_, _, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

/-- `x` is `k` units of `10^s`. -/
structure UnitsAt (x : Number) (s : Int) (k : ℤ) : Prop where
  norm : x.isNormalized
  val : x.toRat = (k : ℚ) * 10 ^ s

lemma UnitsAt.add {x y d : Number} {s : Int} {a b : ℤ} (hx : UnitsAt x s a) (hy : UnitsAt y s b)
    (hab : -2 ^ 63 < a + b ∧ a + b < 2 ^ 63) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hok : x.operator_add y .to_nearest = .ok d) : UnitsAt d s (a + b) :=
  ⟨operator_add_isNormalized_to_nearest_sz x y d hx.norm hy.norm hok,
    Number.operator_add_toRat_of_grid x y d a b s hx.norm hy.norm hx.val hy.val hab hs hok⟩

lemma UnitsAt.sub {x y d : Number} {s : Int} {a b : ℤ} (hx : UnitsAt x s a) (hy : UnitsAt y s b)
    (hab : -2 ^ 63 < a - b ∧ a - b < 2 ^ 63) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hok : x.operator_sub y .to_nearest = .ok d) : UnitsAt d s (a - b) :=
  ⟨operator_sub_isNormalized_to_nearest_sz x y d hx.norm hy.norm hok,
    Number.operator_sub_toRat_of_grid x y d a b s hx.norm hy.norm hx.val hy.val hab hs hok⟩

lemma UnitsAt.of_atExponent {x : Number} {s : Int} {B : ℕ} (hx : x.isNormalized)
    (h : Number.AtExponent x.toRat s B) : ∃ k : ℕ, k < B ∧ UnitsAt x s k := by
  obtain ⟨k, hk, hv⟩ := h
  exact ⟨k, hk, hx, by rw [hv]; push_cast; rfl⟩

lemma Loan.loanScale_bounds (l : Loan) : minExponent + 18 ≤ l.loanScale ∧ l.loanScale ≤ maxExponent - 1 := by
  have h := l.wf.loanScale_range
  unfold cMinOffset cMaxOffset at h
  unfold minExponent maxExponent
  omega

/-- The loan's outstanding amounts and its interestDue in LoanScale units. -/
lemma Loan.state_units (l : Loan) (state : LoanState) (h : l.state = .ok state) :
    ∃ t p m : ℕ, t < l.toExact.numericType.mantissaBound ∧ p < l.toExact.numericType.mantissaBound ∧
      m < l.toExact.numericType.mantissaBound ∧
      UnitsAt state.valueOutstanding l.loanScale t ∧ UnitsAt state.principalOutstanding l.loanScale p ∧
      UnitsAt state.managementFeeDue l.loanScale m ∧
      UnitsAt state.interestDue l.loanScale ((t : ℤ) - p - m) ∧ -1 ≤ (t : ℤ) - p - m ∧
      state.valueOutstanding = l.totalValueOutstanding ∧ state.principalOutstanding = l.principalOutstanding ∧
      state.managementFeeDue = l.managementFeeOutstanding := by
  have he := Loan.exact l
  have heg := Loan.grid l
  obtain ⟨t, ht, htv⟩ := UnitsAt.of_atExponent l.wf.totalValueOutstanding_norm heg.totalValueOutstanding_atExponent
  obtain ⟨p, hp, hpv⟩ := UnitsAt.of_atExponent l.wf.principalOutstanding_norm heg.principalOutstanding_atExponent
  obtain ⟨m, hm, hmv⟩ := UnitsAt.of_atExponent l.wf.managementFeeOutstanding_norm
    heg.managementFeeOutstanding_atExponent
  have hB := NumericType.mantissaBound_le l.toExact.numericType
  have hs := Loan.loanScale_bounds l
  unfold Loan.state LoanState.build at h
  simp only [bind, Except.bind] at h
  walk_ok
  have hst := (Except.ok.inj ‹pure _ = Except.ok state›).symm
  subst hst
  have h1 := UnitsAt.sub htv hpv (by constructor <;> omega) hs ‹_›
  -- the interest is at least zero
  have hge : -1 ≤ (t : ℤ) - p - m := by
    have htol := he.interest_nonneg
    unfold RawLoan.Exact.interestDue at htol
    have hpos : (0 : ℚ) < 10 ^ l.loanScale := zpow_pos (by norm_num) _
    have hv : (RawLoan.toExact l.toRawLoan).totalValueOutstanding - (RawLoan.toExact l.toRawLoan).principalOutstanding -
        (RawLoan.toExact l.toRawLoan).managementFeeOutstanding = (((t : ℤ) - p - m : ℤ) : ℚ) * 10 ^ l.loanScale := by
      show l.totalValueOutstanding.toRat - l.principalOutstanding.toRat - l.managementFeeOutstanding.toRat = _
      rw [htv.val, hpv.val, hmv.val, show l.toExact.loanScale = l.loanScale from rfl]; push_cast; ring
    rw [hv] at htol
    by_contra hlt
    have hle : ((t : ℤ) - p - m : ℤ) ≤ -2 := by omega
    have hle' : (((t : ℤ) - p - m : ℤ) : ℚ) ≤ -2 := by exact_mod_cast hle
    nlinarith
  have h2 := UnitsAt.sub h1 hmv (by constructor <;> omega) hs ‹_›
  exact ⟨t, p, m, ht, hp, hm, htv, hpv, hmv, h2, hge, rfl, rfl, rfl⟩

/-- The management fee on an interest is a normalized number. -/
lemma computeManagementFee_isNormalized (nt : NumericType) (value : Number) (rate : TenthBips16) (s : Int)
    (fee : Number) (h : computeManagementFee nt value rate s = .ok fee) : fee.isNormalized := by
  unfold computeManagementFee at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · exact STAmount.roundToNumericType_isNormalized _ _ _ _ _ h

end XRPL.Model.Lending
