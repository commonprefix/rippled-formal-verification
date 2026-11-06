import XRPL.Properties.Lending.Loan.Common.PayoffComponents
import XRPL.Properties.Lending.Loan.Common.RecheckPayLoan

/-! # A credit to the vault or the cover computes

A payment checks the broker's minimum cover and credits the vault and maybe the cover. Within range these all
compute, each credit is at most what was paid, and the balance it lands on stays at least zero. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The credit a payment's amount fits: an IOU sum below `10^89`, or an XRP or MPT delta a unit below the
asset's maximum. -/
def _root_.XRPL.Model.Protocol.NumericType.CreditFits (nt : NumericType) (A c : ℚ) : Prop :=
  (nt = .fractional ∧ A + c < 10 ^ 89) ∨ ((nt = .native ∨ nt = .int64) ∧ c + 1 ≤ nt.maxValue.toNat)

/-- A downward credit computes and converts back to a `Number`. It is at most the delta, and the balance plus
the credit stays at least zero. -/
lemma sumRoundAndSubtract_credit_ok (A c : Number) (b : Int) (nt : NumericType) (hA : A.isNormalized)
    (hc : c.isNormalized) (hA0 : 0 ≤ A.toRat) (hc0 : 0 ≤ c.toRat) (hb : -81 ≤ b ∧ b ≤ 79)
    (hfit : nt.CreditFits A.toRat c.toRat) :
    ∃ st m, sumRoundAndSubtract A c b nt .downward = .ok st ∧ st.toNumber .to_nearest = .ok m ∧
      m.isNormalized ∧ m.toRat ≤ c.toRat ∧ 0 ≤ A.toRat + m.toRat := by
  obtain ⟨st, hst, hm⟩ : ∃ st, sumRoundAndSubtract A c b nt .downward = .ok st ∧
      ∃ m, st.toNumber .to_nearest = .ok m := by
    rcases hfit with ⟨rfl, hlt⟩ | ⟨hnt, hmax⟩
    · obtain ⟨st, hst, hf⟩ := sumRoundAndSubtract_frac_downward_ok_any A c b hA hc hA0 hc0 hb hlt
      obtain ⟨m, hm, -, -⟩ := hf.toNumber_ok .to_nearest
      exact ⟨st, hst, m, hm⟩
    · obtain ⟨st, hst⟩ := sumRoundAndSubtract_integral_ok A c b nt .downward hnt hc hc0 hmax
      have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
      have hmr : nt.maxValue.toNat ≤ maxRep.toNat := by rcases hnt with rfl | rfl <;> decide
      have hst' := hst
      unfold sumRoundAndSubtract at hst'
      rw [if_pos hint] at hst'
      obtain ⟨x, hx, hst'⟩ := bind_ok_peel _ _ _ hst'
      obtain rfl : x = st := Except.ok.inj hst'
      obtain ⟨hcan, hxnt⟩ := STAmount.ofNumber_integral_canonical nt c .downward x hint hx
      obtain ⟨m, hm, -⟩ := STAmount.toNumber_integral_exact x .to_nearest hcan (by rw [hxnt]; exact hmr)
      exact ⟨x, hst, m, hm⟩
  obtain ⟨m, hm⟩ := hm
  have hb' : (-96 : ℤ) ≤ b ∧ b ≤ 80 := ⟨by omega, by omega⟩
  obtain ⟨hle, hmv⟩ := sumRoundAndSubtract_downward_le A c b nt st hA hA0 hc hc0 hb' hst
  obtain ⟨hmeq, hmn⟩ := hmv m hm
  have hAb : nt = .fractional → A.toRat < 10 ^ 96 := by
    intro hnt
    rcases hfit with ⟨-, hlt⟩ | ⟨hnt', -⟩
    · linarith [show (10 : ℚ) ^ 89 < 10 ^ 96 by norm_num]
    · rcases hnt' with h | h <;> rw [h] at hnt <;> cases hnt
  exact ⟨st, m, hst, hm, hmn, by rw [hmeq]; exact hle,
    sumRoundAndSubtract_downward_cover_nonneg A c b nt st m hA hA0 hAb hc hc0 hb' hst hm⟩

/-- The broker's minimum cover check computes for a DebtTotal of at most `10^16` base units, and at least one when
not zero, on an IOU, XRP or MPT asset with CoverRateMinimum at most 100%. -/
lemma RawLoanBroker.hasMinimumCover_ok (rb : RawLoanBroker) (b : Int)
    (hnt : rb.numericType = .fractional ∨ rb.numericType = .native ∨ rb.numericType = .int64)
    (hdt : rb.debtTotal.isNormalized) (hdt0 : 0 ≤ rb.debtTotal.toRat)
    (hgrid : rb.debtTotal.mantissa_ ≠ 0 → (10 : ℚ) ^ b ≤ rb.debtTotal.toRat)
    (hlt : rb.debtTotal.toRat ≤ 10 ^ 16 * 10 ^ b) (hb : -81 ≤ b ∧ b ≤ 0)
    (hrate : rb.coverRateMinimum.toNat ≤ 100000) :
    ∃ x, rb.hasMinimumCover b = .ok x := by
  have hp : (10 : ℚ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hb.2
  have hdt16 : rb.debtTotal.toRat ≤ 10 ^ 16 := by nlinarith [zpow_pos (by norm_num : (0 : ℚ) < 10) b]
  obtain ⟨mc, hmc, hmcn, hmc0, hmcle, -⟩ := tenthBipsOfValue_upward_ok rb.debtTotal rb.coverRateMinimum b hdt hdt0
    (by linarith [show (10 : ℚ) ^ 16 < 10 ^ 20 by norm_num]) (by omega) hgrid hrate
  have hfits : rb.numericType.Fits mc.toRat := by
    rcases hnt with h | h | h
    · exact Or.inl ⟨h, by linarith [show (10 : ℚ) ^ 16 < 10 ^ 90 by norm_num]⟩
    · refine Or.inr ⟨Or.inl h, ?_⟩
      rw [h]
      have : ((NumericType.native.maxValue.toNat : ℕ) : ℚ) = 10 ^ 17 := by decide
      rw [this]
      linarith [show (10 : ℚ) ^ 16 + 1 ≤ 10 ^ 17 by norm_num]
    · refine Or.inr ⟨Or.inr h, ?_⟩
      rw [h]
      have : ((NumericType.int64.maxValue.toNat : ℕ) : ℚ) = 9223372036854775807 := by decide
      rw [this]
      linarith
  obtain ⟨r, hr⟩ := STAmount.roundToNumericType_ok_of_fits rb.numericType mc .upward b hmcn hmc0 hfits
    ⟨by omega, by omega⟩
  refine ⟨r.operator_le rb.coverAvailable, ?_⟩
  unfold RawLoanBroker.hasMinimumCover minimumBrokerCover
  rw [hmc, ok_bind, hr]
  rfl

end XRPL.Model.Lending
