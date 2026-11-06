import XRPL.Properties.Lending.Loan.Common.PaymentFactor
import XRPL.Properties.Protocol.Common.TenthBips

/-! # How much interest a full payment charges

The interest of an early payoff is the interest accrued over at most one PaymentInterval plus the close
rate on the theoretical principal, so it is at most that principal times one plus the periodic rate. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

open private rn_nonneg from XRPL.Properties.Lending.Loan.Common.SetLawful

local notation "ε" => Number.nearestError

/-- A count of seconds converts to a `Number` of the same value. -/
private lemma Number.ofInt64_seconds (n : UInt32) : (Number.ofInt64 n.toInt64).toRat = n.toNat :=
  Number.ofInt64_count n

/-- The interest accrued since the last payment is at most one period of interest plus three roundings up,
while the close time is at most one PaymentInterval after the last payment. -/
lemma loanAccruedInterest_le_period (tpo rate : Number) (now start prev interval : UInt32) (a : Number)
    (htpo : tpo.isNormalized) (htpo0 : 0 ≤ tpo.toRat) (hrate : rate.isNormalized) (hr0 : 0 ≤ rate.toRat)
    (hdue : now.toNat ≤ (if prev < start then start else prev).toNat + interval.toNat)
    (h : loanAccruedInterest tpo rate now start prev interval = .ok a) :
    a.isNormalized ∧ 0 ≤ a.toRat ∧ a.toRat ≤ tpo.toRat * rate.toRat * (1 + ε) ^ 3 := by
  have he := Number.nearestError_pos
  have hbound : 0 ≤ tpo.toRat * rate.toRat * (1 + ε) ^ 3 := by positivity
  unfold loanAccruedInterest at h
  dsimp only at h
  generalize hL : (if prev < start then start else prev) = last at h hdue
  split at h
  · cases h; exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero], by rw [Number.toRat_zero]; exact hbound⟩
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · cases h; exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero], by rw [Number.toRat_zero]; exact hbound⟩
  rename_i hI
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  split at h
  · cases h; exact ⟨Number.zero_isNormalized, by rw [Number.toRat_zero], by rw [Number.toRat_zero]; exact hbound⟩
  rename_i hlate
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, hsc, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨-, rfl⟩ := UInt32.subChecked_eq_ok.mp hsc
  obtain ⟨ipi, hipi, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨num, hnum, h⟩ := bind_ok_peel _ _ _ h
  have hlt : last < now := by
    rcases UInt32.lt_or_le last now with h' | h'
    · exact h'
    · exact absurd (by simpa using h') hlate
  have hsecs : ((now - last).toNat : ℚ) = now.toNat - last.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hlt)]
    push_cast [UInt32.le_iff_toNat_le.mp (UInt32.le_of_lt hlt)]
    ring
  have hI1 : (1 : ℚ) ≤ interval.toNat := by
    have : interval.toNat ≠ 0 := fun h0 => hI (by simpa using UInt32.toNat_inj.mp (by simpa using h0))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hsI : ((now - last).toNat : ℚ) ≤ interval.toNat := by
    rw [hsecs]
    have : (now.toNat : ℚ) ≤ last.toNat + interval.toNat := by exact_mod_cast hdue
    linarith
  have hS := Number.ofInt64_isNormalized (now - last).toInt64
  have hSv := Number.ofInt64_seconds (now - last)
  have hIN := Number.ofInt64_isNormalized interval.toInt64
  have hIv := Number.ofInt64_seconds interval
  have hipiN := Number.operator_mul_isNormalized _ _ ipi _ htpo hrate hipi
  have hipi0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ htpo hrate hipi) (mul_nonneg htpo0 hr0)
  have hipile := (Number.mul_near _ _ _ htpo hrate hipi).le (mul_nonneg htpo0 hr0)
  have hnumN := Number.operator_mul_isNormalized _ _ num _ hipiN hS hnum
  have hnum0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hipiN hS hnum) (mul_nonneg hipi0 (by
    rw [hSv]; positivity))
  have hnumle := (Number.mul_near _ _ _ hipiN hS hnum).le (mul_nonneg hipi0 (by rw [hSv]; positivity))
  have hle := (Number.div_near _ _ _ hnumN hIN h).le (div_nonneg hnum0 (by rw [hIv]; positivity))
  rw [hSv] at hnumle
  rw [hIv] at hle
  refine ⟨Number.operator_div_isNormalized _ _ a _ hnumN hIN h,
    rn_nonneg (operator_div_rounded_to_nearest _ _ _ hnumN hIN h) (div_nonneg hnum0 (by rw [hIv]; positivity)), ?_⟩
  have hIpos : (0 : ℚ) < interval.toNat := by linarith
  calc a.toRat ≤ num.toRat / interval.toNat * (1 + ε) := hle
    _ ≤ ipi.toRat * (now - last).toNat * (1 + ε) / interval.toNat * (1 + ε) := by gcongr
    _ ≤ tpo.toRat * rate.toRat * (1 + ε) * (now - last).toNat * (1 + ε) / interval.toNat * (1 + ε) := by
        gcongr
    _ = tpo.toRat * rate.toRat * (1 + ε) ^ 3 * ((now - last).toNat / interval.toNat) := by ring
    _ ≤ tpo.toRat * rate.toRat * (1 + ε) ^ 3 * 1 := by
        gcongr
        rw [div_le_one hIpos]; exact hsI
    _ = tpo.toRat * rate.toRat * (1 + ε) ^ 3 := by ring

/-- A tenth-bips share of a value at least zero is at most the exact share times `(1 + ε)^2`. -/
lemma tenthBipsOfValue_le_share (x : Number) (bips : TenthBips32) (r : Number) (hx : x.isNormalized)
    (hx0 : 0 ≤ x.toRat) (h : tenthBipsOfValue x bips .to_nearest = .ok r) :
    r.isNormalized ∧ 0 ≤ r.toRat ∧ r.toRat ≤ x.toRat * (bips.toNat / 100000) * (1 + ε) ^ 2 := by
  obtain ⟨hrn, hrv⟩ := TenthBips32.toNumber_facts bips
  obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  have hU : (kTenthBipsPerUnity.toNat : ℚ) = 100000 := rfl
  have heq : tenthBipsOfValue x bips .to_nearest = (x.operator_mul bips.toNumber .to_nearest) >>=
      (fun p => p.operator_div kTenthBipsPerUnity.toNumber .to_nearest) := rfl
  rw [heq] at h
  obtain ⟨p, hp, h⟩ := bind_ok_peel _ _ _ h
  have hpn := Number.operator_mul_isNormalized _ _ _ _ hx hrn hp
  have hp0 := rn_nonneg (operator_mul_rounded_to_nearest _ _ _ hx hrn hp) (by rw [hrv]; positivity)
  have hple := (Number.mul_near _ _ _ hx hrn hp).le (by rw [hrv]; positivity)
  have hle := (Number.div_near _ _ _ hpn hun h).le (by rw [huv, hU]; positivity)
  rw [hrv] at hple
  rw [huv, hU] at hle
  refine ⟨Number.operator_div_isNormalized _ _ _ _ hpn hun h,
    rn_nonneg (operator_div_rounded_to_nearest _ _ _ hpn hun h) (by rw [huv, hU]; positivity), ?_⟩
  have he := Number.nearestError_pos
  calc r.toRat ≤ p.toRat / 100000 * (1 + ε) := hle
    _ ≤ x.toRat * bips.toNat * (1 + ε) / 100000 * (1 + ε) := by gcongr
    _ = x.toRat * (bips.toNat / 100000) * (1 + ε) ^ 2 := by ring

/-- The interest of a full payment at most one PaymentInterval after the last due date, with CloseInterestRate at
most 100%, is at most the theoretical principal times one plus the periodic rate, plus four roundings up. -/
lemma computeFullPaymentInterest_le_principal (tpo rate : Number) (now interval prev start : UInt32) (cr : TenthBips32)
    (fi : Number) (htpo : tpo.isNormalized) (htpo0 : 0 ≤ tpo.toRat) (hrate : rate.isNormalized)
    (hr0 : 0 ≤ rate.toRat) (hcr : cr.toNat ≤ 100000)
    (hdue : now.toNat ≤ (if prev < start then start else prev).toNat + interval.toNat)
    (h : computeFullPaymentInterest tpo rate now interval prev start cr = .ok fi) :
    fi.isNormalized ∧ 0 ≤ fi.toRat ∧ fi.toRat ≤ (tpo.toRat * rate.toRat + tpo.toRat) * (1 + ε) ^ 4 := by
  have he := Number.nearestError_pos
  unfold computeFullPaymentInterest at h
  obtain ⟨acc, hacc, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨haN, ha0, hale⟩ := loanAccruedInterest_le_period tpo rate now start prev interval acc htpo htpo0 hrate hr0
    hdue hacc
  have hpenb : ∃ pen : Number, pen.isNormalized ∧ 0 ≤ pen.toRat ∧ pen.toRat ≤ tpo.toRat * (1 + ε) ^ 2 ∧
      acc.operator_add pen .to_nearest = .ok fi := by
    dsimp only at h
    split at h
    · obtain ⟨pen, hpen, h⟩ := bind_ok_peel _ _ _ h
      cases hpen
      exact ⟨_, Number.zero_isNormalized, by rw [Number.toRat_zero], by rw [Number.toRat_zero]; positivity, h⟩
    · obtain ⟨pen, hpen, h⟩ := bind_ok_peel _ _ _ h
      obtain ⟨h1, h2, h3⟩ := tenthBipsOfValue_le_share tpo cr pen htpo htpo0 hpen
      refine ⟨pen, h1, h2, le_trans h3 ?_, h⟩
      have : (cr.toNat : ℚ) / 100000 ≤ 1 := by
        rw [div_le_one (by norm_num)]; exact_mod_cast hcr
      have : tpo.toRat * (cr.toNat / 100000) ≤ tpo.toRat := by nlinarith
      nlinarith [pow_pos (show (0 : ℚ) < 1 + ε by linarith) 2]
  obtain ⟨pen, hpN, hp0, hple, h⟩ := hpenb
  refine ⟨operator_add_isNormalized_to_nearest_sz _ _ _ haN hpN h,
    rn_nonneg (operator_add_rounded_to_nearest _ _ _ haN hpN h) (add_nonneg ha0 hp0), ?_⟩
  have hfle := (Number.add_near _ _ _ haN hpN h).le (add_nonneg ha0 hp0)
  have h1 : (1 + ε) ^ 2 ≤ (1 + ε) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  calc fi.toRat ≤ (acc.toRat + pen.toRat) * (1 + ε) := hfle
    _ ≤ (tpo.toRat * rate.toRat * (1 + ε) ^ 3 + tpo.toRat * (1 + ε) ^ 3) * (1 + ε) := by
        gcongr
        exact le_trans hple (by gcongr)
    _ = (tpo.toRat * rate.toRat + tpo.toRat) * (1 + ε) ^ 4 := by ring

end XRPL.Model.Lending
