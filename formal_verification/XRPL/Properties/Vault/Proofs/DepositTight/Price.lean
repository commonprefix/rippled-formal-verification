import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.Common.Underflow
import XRPL.Properties.Vault.Proofs.DepositAccuracy.Pricing
import XRPL.Properties.Vault.Proofs.WithdrawPricing.Core

/-! # Pricing facts of the deposit charge -/

namespace XRPL.Model.SingleAssetVault.DepTight

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault.DepAcc

/-- A 19-digit normalized mantissa that denotes a value of at most 16 significant digits ends in three
zeros: `a·10^X = s·10^Y` with `s < 10^16` forces `a = s·10^(Y-X)` with `Y-X ≥ 3`. -/
private lemma sig16_normalized_mod1000 (a s : ℕ) (X Y : ℤ)
    (ha_lo : 10 ^ 18 ≤ a) (ha_hi : a < 10 ^ 19) (hs : s < 10 ^ 16)
    (heq : (a : ℚ) * (10 : ℚ) ^ X = (s : ℚ) * (10 : ℚ) ^ Y) :
    a % 1000 = 0 := by
  have h10ne : (10 : ℚ) ≠ 0 := by norm_num
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h; swap; · exact h
    exfalso
    have hz : (a : ℚ) * (10 : ℚ) ^ X = 0 := by rw [heq, h0]; simp
    have hne : (10 : ℚ) ^ X ≠ 0 := by positivity
    have haq : (a : ℚ) = 0 := (mul_eq_zero.mp hz).resolve_right hne
    have hapos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (show 0 < a by omega)
    linarith
  have haeq : (s : ℚ) * (10 : ℚ) ^ (Y - X) = (a : ℚ) := by
    have key : (s : ℚ) * (10 : ℚ) ^ (Y - X) * (10 : ℚ) ^ X = (a : ℚ) * (10 : ℚ) ^ X := by
      rw [mul_assoc, ← zpow_add₀ h10ne, show (Y - X) + X = Y from by ring, ← heq]
    exact mul_right_cancel₀ (by positivity) key
  have h3 : (3 : ℤ) ≤ Y - X := by
    by_contra hlt
    push Not at hlt
    have hle2 : Y - X ≤ 2 := by omega
    have hpow : (10 : ℚ) ^ (Y - X) ≤ (10 : ℚ) ^ (2 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) hle2
    have hp2 : (10 : ℚ) ^ (2 : ℤ) = 100 := by norm_num
    have hsq : (s : ℚ) < 10 ^ 16 := by exact_mod_cast hs
    have haq : (10 : ℚ) ^ 18 ≤ (a : ℚ) := by exact_mod_cast ha_lo
    have hsnn : (0 : ℚ) ≤ (s : ℚ) := by positivity
    have hub : (a : ℚ) ≤ (s : ℚ) * 100 := by rw [← haeq]; nlinarith [hpow, hp2, hsnn]
    nlinarith [hub, hsq, haq]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Y - X = (n : ℤ) := ⟨(Y - X).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hnge : 3 ≤ n := by omega
  have haeq2 : a = s * 10 ^ n := by
    have hcast : (a : ℚ) = ((s * 10 ^ n : ℕ) : ℚ) := by
      rw [← haeq, hn, zpow_natCast]; push_cast; ring
    exact_mod_cast hcast
  have hdvd : (1000 : ℕ) ∣ a := by
    rw [haeq2, show (1000 : ℕ) = 10 ^ 3 from by norm_num]
    exact Dvd.dvd.mul_left (pow_dvd_pow 10 hnge) s
  omega

/-- `IOUAmount.normalize` is value-exact on a mantissa of at most 16 significant digits: the 19-digit
re-lift lands three or more zeros below the 16-digit window, so the re-round drops only zeros. -/
private lemma IOUAmount.normalize_sigdigits16 (M : UInt64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (s t : ℕ)
    (hMform : M.toNat = s * 10 ^ t) (hs : s < 10 ^ 16) (hMnz : M ≠ 0)
    (hfit : M.toNat < 2 ^ 63) (he_lo : -18 ≤ e) (he_hi : e ≤ 0)
    (hok : IOUAmount.normalize ⟨M.toInt64, e⟩ mode = .ok i) :
    i.toRat = (M.toNat : ℚ) * (10 : ℚ) ^ e := by
  have hmin : minExponent = -32768 := rfl
  have hmax : maxExponent = 32768 := rfl
  have hcmin : cMinOffset = -96 := rfl
  have hcmax : cMaxOffset = 80 := rfl
  have hMnz' : M.toNat ≠ 0 := fun h => hMnz (by rw [← UInt64.toNat_inj]; simpa using h)
  have hMtoInt : M.toInt64.toInt = (M.toNat : ℤ) := UInt64.toInt64_toInt_of_lt M hfit
  have hM19 : M.toNat < 10 ^ 19 := by omega
  have hne_min : M.toInt64 ≠ Int64.minValue := by
    intro h
    have h2 : M.toInt64.toInt = Int64.minValue.toInt := by rw [h]
    rw [hMtoInt, show Int64.minValue.toInt = (-9223372036854775808 : ℤ) from by decide] at h2
    omega
  obtain ⟨v, hfr, hvval, hvnorm⟩ := Number.from_rep_exact M.toInt64 e mode hne_min
    (by omega : minExponent + 18 ≤ e) (by omega : e ≤ maxExponent - 1)
  rw [hMtoInt] at hvval
  have hvpos : 0 < v.toRat := by rw [hvval]; positivity
  have hvm_ne : v.mantissa_ ≠ 0 := fun h => by
    rw [Number.toRat_eq_zero_of_mantissa_zero v h] at hvpos; exact lt_irrefl _ hvpos
  have hvneg : v.negative_ = false := by
    by_contra h
    rw [Bool.not_eq_false] at h
    linarith [Number.toRat_nonpos_of_negative v h, hvpos]
  obtain ⟨hvm_lo, hvm_hi⟩ := hvnorm.mantissaBounds_nat hvm_ne
  have hve_lo : minExponent ≤ v.exponent_ := by
    rcases hvnorm with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show v.mantissa_ = 0 by rw [h0]; rfl) hvm_ne
    · exact hlo
  have hve_hi : v.exponent_ ≤ maxExponent := by
    rcases hvnorm with h0 | ⟨_, _, _, _, hhi⟩
    · exact absurd (show v.mantissa_ = 0 by rw [h0]; rfl) hvm_ne
    · exact hhi
  have hvtoRat_form : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_
      = (s : ℚ) * (10 : ℚ) ^ ((t : ℤ) + e) := by
    have h1 : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ = v.toRat :=
      (Number.toRat_of_nonneg v hvneg).symm
    rw [h1, hvval, hMform]
    push_cast
    rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0), ← zpow_natCast (10:ℚ) t]
    ring
  have hmod : v.mantissa_.toNat % 1000 = 0 :=
    sig16_normalized_mod1000 v.mantissa_.toNat s v.exponent_ ((t : ℤ) + e)
      hvm_lo hvm_hi hs hvtoRat_form
  have hveq : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ = (M.toNat : ℚ) * (10:ℚ)^e := by
    rw [← Number.toRat_of_nonneg v hvneg]; exact hvval
  have hve_le0 : v.exponent_ ≤ 0 := by
    by_contra hgt
    push Not at hgt
    have hge1 : (1 : ℤ) ≤ v.exponent_ := hgt
    have hlhs : (10 : ℚ) ^ 19 ≤ (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ := by
      have hm18 : (10 : ℚ) ^ 18 ≤ (v.mantissa_.toNat : ℚ) := by exact_mod_cast hvm_lo
      have hexp : (10 : ℚ) ^ (1 : ℤ) ≤ (10 : ℚ) ^ v.exponent_ :=
        zpow_le_zpow_right₀ (by norm_num) hge1
      have h181 : (10 : ℚ) ^ 19 = (10 : ℚ) ^ 18 * (10 : ℚ) ^ (1 : ℤ) := by norm_num
      have hmnn : (0:ℚ) ≤ (v.mantissa_.toNat : ℚ) := by positivity
      have hpnn : (0:ℚ) < (10:ℚ)^(1:ℤ) := by positivity
      calc (10:ℚ)^19 = (10:ℚ)^18 * (10:ℚ)^(1:ℤ) := h181
        _ ≤ (v.mantissa_.toNat : ℚ) * (10:ℚ)^(1:ℤ) := by nlinarith [hm18, hpnn]
        _ ≤ (v.mantissa_.toNat : ℚ) * (10:ℚ)^v.exponent_ := by nlinarith [hexp, hmnn]
    have hrhs : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ < (10 : ℚ) ^ 19 := by
      rw [hveq]
      have hMlt : (M.toNat : ℚ) < (10:ℚ)^19 := by exact_mod_cast hM19
      have hele : (10:ℚ)^e ≤ (10:ℚ)^(0:ℤ) := zpow_le_zpow_right₀ (by norm_num) he_hi
      have he0 : (10:ℚ)^(0:ℤ) = 1 := by norm_num
      have hMnn : (0:ℚ) ≤ (M.toNat : ℚ) := by positivity
      have hepos : (0:ℚ) < (10:ℚ)^e := by positivity
      nlinarith [hMlt, hele, he0, hMnn, hepos]
    linarith
  have hve_ge : (-99 : ℤ) ≤ v.exponent_ := by
    by_contra hlt
    push Not at hlt
    have hle : v.exponent_ ≤ -100 := by omega
    have hlhs : (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ < (10 : ℚ) ^ (-81 : ℤ) := by
      have hmlt : (v.mantissa_.toNat : ℚ) < (10 : ℚ) ^ 19 := by exact_mod_cast hvm_hi
      have hexp : (10 : ℚ) ^ v.exponent_ ≤ (10 : ℚ) ^ (-100 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hle
      have hsplit : (10:ℚ)^(19:ℕ) * (10:ℚ)^(-100:ℤ) = (10:ℚ)^(-81:ℤ) := by
        rw [show ((10:ℚ)^(19:ℕ)) = (10:ℚ)^(19:ℤ) by norm_num,
            ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
        norm_num
      have hmnn : (0:ℚ) ≤ (v.mantissa_.toNat : ℚ) := by positivity
      have hp100 : (0:ℚ) < (10:ℚ)^(-100:ℤ) := by positivity
      calc (v.mantissa_.toNat : ℚ) * (10:ℚ)^v.exponent_
          ≤ (v.mantissa_.toNat : ℚ) * (10:ℚ)^(-100:ℤ) := by nlinarith [hexp, hmnn]
        _ < (10:ℚ)^(19:ℕ) * (10:ℚ)^(-100:ℤ) := by nlinarith [hmlt, hp100]
        _ = (10:ℚ)^(-81:ℤ) := hsplit
    have hrhs : (10 : ℚ) ^ (-81 : ℤ) ≤ (v.mantissa_.toNat : ℚ) * (10 : ℚ) ^ v.exponent_ := by
      rw [hveq]
      have hM1 : (1:ℚ) ≤ (M.toNat : ℚ) := by exact_mod_cast (show 1 ≤ M.toNat by omega)
      have hele : (10:ℚ)^(-18:ℤ) ≤ (10:ℚ)^e := zpow_le_zpow_right₀ (by norm_num) he_lo
      have hcmp : (10:ℚ)^(-81:ℤ) ≤ (10:ℚ)^(-18:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      have hepos : (0:ℚ) < (10:ℚ)^e := by positivity
      have hMnn : (0:ℚ) ≤ (M.toNat:ℚ) := by positivity
      nlinarith [hM1, hele, hcmp, hepos, hMnn]
    linarith
  have hntr := normalizeToRange_16_exact v mode hvm_lo hvm_hi hmod
    (by omega : minExponent ≤ v.exponent_ + 3) (by omega : v.exponent_ + 3 ≤ maxExponent)
  rw [hvneg] at hntr
  simp only [Bool.false_eq_true, if_false] at hntr
  have hfn : IOUAmount.fromNumber v mode
      = .ok ⟨(v.mantissa_ / 10 / 10 / 10).toInt64, v.exponent_ + 3⟩ := by
    unfold IOUAmount.fromNumber; rw [hntr]
  have hmant_ne : ¬ ((⟨M.toInt64, e⟩ : IOUAmount).mantissa_ == 0) = true := by
    show ¬ (M.toInt64 == 0) = true
    rw [beq_iff_eq]; intro h
    rw [h, show (0 : Int64).toInt = 0 from by decide] at hMtoInt
    omega
  unfold IOUAmount.normalize at hok
  rw [if_neg hmant_ne] at hok
  rw [show (⟨M.toInt64, e⟩ : IOUAmount).mantissa_ = M.toInt64 from rfl,
      show (⟨M.toInt64, e⟩ : IOUAmount).exponent_ = e from rfl, hfr] at hok
  simp only [] at hok
  rw [hfn] at hok
  simp only [] at hok
  rw [if_neg (by show ¬ (v.exponent_ + 3 > cMaxOffset); omega),
      if_neg (by show ¬ (v.exponent_ + 3 < cMinOffset); omega)] at hok
  have hieq : i = ⟨(v.mantissa_ / 10 / 10 / 10).toInt64, v.exponent_ + 3⟩ := (Except.ok.inj hok).symm
  rw [hieq, IOUAmount.toRat_eq]
  show ((v.mantissa_ / 10 / 10 / 10).toInt64.toInt : ℚ) * (10:ℚ)^(v.exponent_ + 3) = _
  have hdiv_lt : (v.mantissa_ / 10 / 10 / 10).toNat < 2 ^ 63 := by
    rw [m_div_thousand_toNat]; omega
  have hdiv_toInt : (v.mantissa_ / 10 / 10 / 10).toInt64.toInt
      = ((v.mantissa_.toNat / 1000 : ℕ) : ℤ) := by
    rw [UInt64.toInt64_toInt_of_lt _ hdiv_lt, m_div_thousand_toNat]
  rw [hdiv_toInt]
  have hdiv1000 : ((v.mantissa_.toNat / 1000 : ℕ) : ℚ) * 1000 = (v.mantissa_.toNat : ℚ) := by
    have hnat : v.mantissa_.toNat / 1000 * 1000 = v.mantissa_.toNat := Nat.div_mul_cancel (by omega)
    have := congrArg (Nat.cast (R := ℚ)) hnat
    push_cast at this ⊢; linarith
  have hexp3 : (10:ℚ)^(v.exponent_ + 3) = (10:ℚ)^v.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
  rw [hexp3]
  calc ((v.mantissa_.toNat / 1000 : ℕ) : ℚ) * ((10:ℚ)^v.exponent_ * 1000)
      = (((v.mantissa_.toNat / 1000 : ℕ) : ℚ) * 1000) * (10:ℚ)^v.exponent_ := by ring
    _ = (v.mantissa_.toNat : ℚ) * (10:ℚ)^v.exponent_ := by rw [hdiv1000]
    _ = (M.toNat : ℚ) * (10:ℚ)^e := hveq

/-- `STAmount.checked` on a `.fractional` type is value-exact on a mantissa of at most 16 significant
digits. -/
private lemma STAmount.checked_frac_sigdigits_exact (M : UInt64) (e : Int) (mode : rounding_mode)
    (c : STAmount) (s t : ℕ)
    (hMform : M.toNat = s * 10 ^ t) (hs : s < 10 ^ 16) (hMnz : M ≠ 0)
    (hfit : M.toNat < 2 ^ 63) (he_lo : -18 ≤ e) (he_hi : e ≤ 0)
    (hok : STAmount.checked .fractional M e false mode = .ok c) :
    c.toRat = (M.toNat : ℚ) * (10 : ℚ) ^ e := by
  have hMnz' : M.toNat ≠ 0 := fun h => hMnz (by rw [← UInt64.toNat_inj]; simpa using h)
  set s0 : STAmount := STAmount.unchecked .fractional M e false with hs0
  have h_int : ¬ s0.integral = true := by
    rw [hs0]; simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have hsd_eq : s0.signedDrops.toInt64 = M.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt_of_lt s0 (show s0.mValue.toNat < 2 ^ 63 from hfit),
        UInt64.toInt64_toInt_of_lt M hfit]
    show s0.signedDrops = (M.toNat : ℤ)
    simp [hs0, STAmount.signedDrops, STAmount.unchecked]
  have hiou : s0.iou mode = IOUAmount.normalize ⟨M.toInt64, e⟩ mode := by
    rw [STAmount.iou_of_lt mode h_int (show s0.mValue.toNat < 2 ^ 63 from hfit), hsd_eq]; rfl
  rw [STAmount.checked] at hok
  unfold STAmount.canonicalize at hok
  rw [if_neg h_int, hiou] at hok
  cases h_norm : IOUAmount.normalize ⟨M.toInt64, e⟩ mode with
  | error err => rw [h_norm] at hok; simp at hok
  | ok i =>
    rw [h_norm] at hok; simp only [] at hok
    have hres_eq : c = ⟨.fractional,
        (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64,
        i.exponent_, decide (i.signum < 0)⟩ := by
      rw [IOUAmount.absMant_toUInt64]; exact (Except.ok.inj hok).symm
    have hival : i.toRat = (M.toNat : ℚ) * (10 : ℚ) ^ e :=
      IOUAmount.normalize_sigdigits16 M e mode i s t hMform hs hMnz hfit he_lo he_hi h_norm
    have himne : i.mantissa_ ≠ 0 := by
      intro h0
      have h0r : i.toRat = 0 := by rw [IOUAmount.toRat_eq, h0]; simp
      rw [hival] at h0r
      have hpos : (0 : ℚ) < (M.toNat : ℚ) * (10 : ℚ) ^ e :=
        mul_pos (by exact_mod_cast (show 0 < M.toNat by omega)) (by positivity)
      linarith
    have hr16 : i.InRange16 :=
      (IOUAmount.normalize_InRange16_or_zero ⟨M.toInt64, e⟩ mode i h_norm).resolve_right himne
    rw [hres_eq, STAmount.iou_pack_toRat i hr16, hival]

/-- The floor of `A·10^P` has at most 16 significant digits when `A < 10^16`. For `P ≥ 0` it is
`A·10^P` with trailing zeros, for `P < 0` it is below `A`. -/
private lemma floor_nat_mul_zpow_sigform (A : ℕ) (P : ℤ) (hA : A < 10 ^ 16) :
    ∃ s t : ℕ, (⌊(A : ℚ) * (10 : ℚ) ^ P⌋).toNat = s * 10 ^ t ∧ s < 10 ^ 16 := by
  by_cases hP : 0 ≤ P
  · refine ⟨A, P.toNat, ?_, hA⟩
    have hPeq : (10 : ℚ) ^ P = (10 : ℚ) ^ P.toNat := by
      rw [← zpow_natCast (10 : ℚ) P.toNat, Int.toNat_of_nonneg hP]
    have hcast : (A : ℚ) * (10 : ℚ) ^ P = ((A * 10 ^ P.toNat : ℕ) : ℚ) := by
      rw [hPeq]; push_cast; ring
    rw [hcast, Int.floor_natCast, Int.toNat_natCast]
  · refine ⟨(⌊(A : ℚ) * (10 : ℚ) ^ P⌋).toNat, 0, by rw [pow_zero, mul_one], ?_⟩
    have hPlt : P ≤ 0 := le_of_lt (not_le.mp hP)
    have h10 : (10 : ℚ) ^ P ≤ 1 := by
      calc (10 : ℚ) ^ P ≤ (10 : ℚ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hPlt
        _ = 1 := by norm_num
    have hle : (A : ℚ) * (10 : ℚ) ^ P ≤ (A : ℚ) := by
      nlinarith [h10, (show (0 : ℚ) ≤ (A : ℚ) from by positivity)]
    have hfl : ⌊(A : ℚ) * (10 : ℚ) ^ P⌋ ≤ (A : ℤ) := by
      calc ⌊(A : ℚ) * (10 : ℚ) ^ P⌋ ≤ ⌊(A : ℚ)⌋ := Int.floor_le_floor hle
        _ = (A : ℤ) := Int.floor_natCast A
    omega

/-- On an empty vault the issued shares are the floor of the ideal share count, which is the exact
`amount · 10^scale`. -/
lemma empty_shares_floor (v : Vault) (amount shares : STAmount) (hc : amount.Canonical)
    (hpos : 0 < amount.toRat) (navN : Number) (hat : v.assetsTotal = .ok navN)
    (hmz : navN.mantissa_ = 0) (hok : assetsToSharesDeposit v amount = .ok shares)
    (hnz : shares.isZero = false) :
    v.idealSharesDepositAt navN.toRat amount.toRat = amount.toRat * (10 : ℚ) ^ (v.scale.toNat : ℤ) ∧
      0 < v.idealSharesDepositAt navN.toRat amount.toRat ∧
      shares.toRat = (⌊v.idealSharesDepositAt navN.toRat amount.toRat⌋ : ℚ) := by
  obtain ⟨n1, n2, hn1norm, hn1neg, hn1val, hn2, hn2norm, hn2den, hsh⟩ :=
    deposit_empty_chain_facts v (Vault.scale_toNat_le v) amount shares hc hpos navN hat hmz hok hnz
  have hideal : v.idealSharesDepositAt navN.toRat amount.toRat = n1.toRat := by
    unfold RawVault.idealSharesDepositAt
    rw [if_pos (Number.toRat_eq_zero_of_mantissa_zero navN hmz), hn1val, zpow_natCast]
  obtain ⟨hn2val, -⟩ := Number.truncate_floor n1 n2 hn1norm hn1neg hn2
  have hshval : shares.toRat = n2.toRat :=
    STAmount.ofNumber_integral_exact .int64 n2 .to_nearest shares (by decide) hn2norm hn2den hsh
  refine ⟨by rw [hideal, hn1val], by rw [hideal, hn1val]; positivity, by rw [hshval, hn2val, hideal]⟩

/-- On an empty vault the issued shares keep at most 16 significant digits: they are the floor of the
16-digit amount scaled by a power of ten. -/
private lemma empty_shares_sigform (v : Vault) (amount shares : STAmount)
    (hc : amount.Canonical) (hac : amount.IOUCanonical) (hpos : 0 < amount.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN) (hmz : navN.mantissa_ = 0)
    (hshnz : shares.isZero = false)
    (hshares : assetsToSharesDeposit v amount = .ok shares) :
    shares.mIsNegative = false ∧
      ∃ s t : ℕ, shares.mValue.toNat = s * 10 ^ t ∧ s < 10 ^ 16 := by
  have hshmv : shares.mValue ≠ 0 := ne_of_beq_false hshnz
  obtain ⟨hideal, hidpos, hshval⟩ :=
    empty_shares_floor v amount shares hc hpos navN hat hmz hshares hshnz
  have hideal' : v.idealSharesDepositAt navN.toRat amount.toRat
      = (amount.mValue.toNat : ℚ) * (10 : ℚ) ^ (amount.exponent + (v.scale.toNat : ℤ)) := by
    rw [hideal, STAmount.toRat_of_nonneg amount (STAmount.mIsNegative_false_of_pos amount hpos)]
    show (amount.mValue.toNat : ℚ) * 10 ^ amount.mOffset * 10 ^ (v.scale.toNat : ℤ)
      = (amount.mValue.toNat : ℚ) * 10 ^ (amount.mOffset + (v.scale.toNat : ℤ))
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
  have hshnn : 0 ≤ shares.toRat := by
    rw [hshval]; exact_mod_cast Int.floor_nonneg.mpr hidpos.le
  have hshpos : 0 < shares.toRat :=
    lt_of_le_of_ne hshnn (Ne.symm (STAmount.toRat_ne_zero shares hshmv))
  have hshneg : shares.mIsNegative = false := STAmount.mIsNegative_false_of_pos shares hshpos
  obtain ⟨hshc, -⟩ := assetsToSharesDeposit_int64_canonical v amount shares hshares
  have hshvaln : (shares.mValue.toNat : ℚ) = shares.toRat := by
    rw [STAmount.toRat_of_nonneg shares hshneg, hshc.offset_zero]; norm_num
  have hshint : (shares.mValue.toNat : ℤ)
      = ⌊(amount.mValue.toNat : ℚ) * (10 : ℚ) ^ (amount.exponent + (v.scale.toNat : ℤ))⌋ := by
    have hq : (shares.mValue.toNat : ℚ)
        = (⌊(amount.mValue.toNat : ℚ) * (10 : ℚ) ^ (amount.exponent + (v.scale.toNat : ℤ))⌋ : ℚ) := by
      rw [hshvaln, hshval, hideal']
    exact_mod_cast hq
  obtain ⟨s, t, hst, hslt⟩ :=
    floor_nat_mul_zpow_sigform amount.mValue.toNat (amount.exponent + (v.scale.toNat : ℤ)) hac.mant_hi
  exact ⟨hshneg, s, t, by rw [← hst]; omega, hslt⟩

/-- On a first deposit into an empty IOU vault the charge is the exact ideal `shares / 10^scale`: the
shares keep at most 16 significant digits, so the charge pack renormalizes them losslessly. -/
lemma empty_frac_charge_exact (v : Vault) (amount shares c : STAmount)
    (hintf : v.numericType.isIntegral = false)
    (navN : Number) (hat : v.assetsTotal = .ok navN) (hmz : navN.mantissa_ = 0)
    (hamtcanon : amount.Canonical) (hpos : 0 < amount.toRat)
    (hamtfrac : amount.mNumericType = .fractional)
    (hshares : assetsToSharesDeposit v amount = .ok shares)
    (hshnz : shares.isZero = false)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    c.toRat = v.idealChargeDeposit shares.toRat := by
  have hamtint : amount.integral = false := by
    unfold STAmount.integral; rw [hamtfrac]; decide
  have hac : amount.IOUCanonical := hamtcanon.2 hamtint
  obtain ⟨hshneg, s, t, hst, hslt⟩ :=
    empty_shares_sigform v amount shares hamtcanon hac hpos navN hat hmz hshnz hshares
  obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v amount shares hshares
  have hshmv : shares.mValue ≠ 0 := ne_of_beq_false (show (shares.mValue == 0) = false from hshnz)
  have hfit : shares.mValue.toNat < 2 ^ 63 := by
    have hr := hshc.in_range; rw [hshnt] at hr
    have hm : NumericType.int64.maxValue.toNat = 9223372036854775807 := by decide
    omega
  have hvfrac : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral hintf
  unfold sharesToAssetsDeposit at hsad
  obtain ⟨navN', hat', hsad⟩ := bind_ok_peel _ _ _ hsad
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  rw [if_pos hmz] at hsad
  obtain ⟨c', hcx, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hc' : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  have hexp0 : shares.exponent = 0 := hshc.offset_zero
  rw [hc', hvfrac, show shares.mantissa = shares.mValue from rfl, hexp0] at hcx
  have hcval : c.toRat = (shares.mValue.toNat : ℚ) * (10 : ℚ) ^ ((0 : ℤ) - (v.scale.toNat : ℤ)) := by
    apply STAmount.checked_frac_sigdigits_exact shares.mValue ((0 : ℤ) - (v.scale.toNat : ℤ))
      .to_nearest c s t hst hslt hshmv hfit
    · show (-18 : ℤ) ≤ (0 : ℤ) - (v.scale.toNat : ℤ); have h18 := Vault.scale_toNat_le v; omega
    · show (0 : ℤ) - (v.scale.toNat : ℤ) ≤ 0; omega
    · exact hcx
  rw [hcval]
  unfold RawVault.idealChargeDeposit
  have hA0 : v.toExact.assetsTotal = 0 := (Vault.assetsTotal_eq_zero_iff v navN hat).mp hmz
  rw [if_pos hA0]
  have hsheq : shares.toRat = (shares.mValue.toNat : ℚ) := by
    rw [STAmount.toRat_of_nonneg shares hshneg, hshc.offset_zero]; norm_num
  rw [hsheq, show (0 : ℤ) - (v.scale.toNat : ℤ) = -(v.scale.toNat : ℤ) from by ring,
      zpow_neg, zpow_natCast, div_eq_mul_inv]

private lemma charge_underflow_mul (nav s ST t : ℚ)
    (hs : 0 < s) (hnav : 0 < nav) (hST : 1 ≤ ST)
    (hmul : nav * s < t) :
    nav * s / ST < t := by
  have hSTpos : 0 < ST := by linarith
  have h1 : nav * s / ST ≤ nav * s := by
    rw [div_le_iff₀ hSTpos]; nlinarith [mul_pos hnav hs]
  linarith

private lemma charge_underflow_div (nav s ST P t : ℚ)
    (hs : 0 < s) (hnav : 0 < nav) (hSTpos : 0 < ST)
    (hmul : |P - nav * s| ≤ |nav * s| * (5 / (2 ^ 63 + 7)))
    (hdiv : |P / ST| < t) :
    nav * s / ST < 2 * t := by
  have hnavs : 0 < nav * s := mul_pos hnav hs
  rw [abs_of_pos hnavs] at hmul
  have hmb := abs_le.mp hmul
  have hPpos : 0 < P := by nlinarith [hmb.1, hnavs]
  have hPST : P / ST < t := by rw [abs_of_pos (div_pos hPpos hSTpos)] at hdiv; exact hdiv
  have hle2 : nav * s / ST ≤ 2 * (P / ST) := by
    rw [div_le_iff₀ hSTpos, show 2 * (P / ST) * ST = 2 * P from by
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hSTpos)]]
    linarith
  linarith

/-- On a nonempty vault the priced charge is the `to_nearest` pack of a `Number` `Q` that is within
`sharesε` of the ideal charge, or is zero with an ideal below the `Number` underflow. -/
lemma charge_nonempty (v : Vault) (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (navN : Number) (hat : v.assetsTotal = .ok navN) (hmz : navN.mantissa_ ≠ 0)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    ∃ Q : Number,
      STAmount.ofNumber v.numericType Q .to_nearest = .ok c ∧
      0 < v.idealChargeDepositAt navN.toRat shares.toRat ∧
      ((Q.mantissa_ ≠ 0 ∧ Q.isNormalized ∧ Q.negative_ = false ∧
        |Q.toRat - v.idealChargeDepositAt navN.toRat shares.toRat|
          ≤ v.idealChargeDepositAt navN.toRat shares.toRat * sharesε) ∨
      (Q.mantissa_ = 0 ∧ v.idealChargeDepositAt navN.toRat shares.toRat ≤ (10 : ℚ) ^ (-32700 : ℤ))) := by
  set nav : ℚ := navN.toRat
  set s : ℚ := shares.toRat
  set ST : ℚ := v.sharesTotal.toRat with hST_def
  have hnav_pos : 0 < nav := (Vault.assetsTotal_pos v navN hat hmz).2
  have hST_one : 1 ≤ ST := Vault.sharesTotal_one_le v navN hat hmz
  have hST_pos : 0 < ST := by linarith
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [← hST_def]; exact ne_of_gt hST_pos)
  have hideal : v.idealChargeDepositAt navN.toRat s = nav * s / ST := by
    unfold RawVault.idealChargeDepositAt
    rw [if_neg (ne_of_gt hnav_pos), RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  have hidpos : 0 < nav * s / ST := div_pos (mul_pos hnav_pos hshpos) hST_pos
  unfold sharesToAssetsDeposit at hsad
  obtain ⟨navN', hat', hsad⟩ := bind_ok_peel _ _ _ hsad
  rw [hat, Except.ok.injEq] at hat'
  subst hat'
  rw [if_neg hmz] at hsad
  obtain ⟨_, _, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨shN, hshN, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨P, hP, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨Q, hQ, hsad⟩ := bind_ok_peel _ _ _ hsad
  obtain ⟨c', hc, hlast⟩ := bind_ok_peel _ _ _ hsad
  have hceq : c' = c := Except.ok.inj (show Except.ok c' = .ok c from hlast)
  rw [hceq] at hc
  have hnavnorm : navN.isNormalized := (Vault.assetsTotal_ge_deployed v navN hat).1
  have hnavv : navN.toRat = nav := rfl
  obtain ⟨sn, hsn, hsnval, hsnnorm, _⟩ :=
    STAmount.toNumber_integral_exact shares .to_nearest hshc (by rw [hshnt]; decide)
  have hshNeq : sn = shN := by rw [hsn] at hshN; exact Except.ok.inj hshN
  rw [hshNeq] at hsnval hsnnorm
  have hshN_val : shN.toRat = s := by rw [hsnval]
  have hshN_pos : 0 < shN.toRat := by rw [hshN_val]; exact hshpos
  have hshNm : shN.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hshN_val]; exact ne_of_gt hshpos)
  refine ⟨Q, hc, by rw [hideal]; exact hidpos, ?_⟩
  by_cases hQm : Q.mantissa_ ≠ 0
  · left
    obtain ⟨hQnorm, hQpos, hb⟩ := WdPrice.pipe navN shN P Q v.sharesTotal hnavnorm hnav_pos.le hsnnorm
      hshN_pos.le v.wf.sharesTotal_norm hST_pos hP hQ hQm
    refine ⟨hQm, hQnorm, Number.negative_false_of_pos Q hQpos, ?_⟩
    rw [hshN_val] at hb
    rw [hideal]
    exact hb
  · right
    push Not at hQm
    refine ⟨hQm, ?_⟩
    rw [hideal]
    have hunit : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) = (10 : ℚ) ^ (-32750 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      norm_num [minExponent]
    have hu_pos : (0 : ℚ) < (10 : ℚ) ^ (-32750 : ℤ) := zpow_pos (by norm_num) _
    have h_le : 2 * (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-32700 : ℤ) := by
      rw [show (10 : ℚ) ^ (-32700 : ℤ) = (10 : ℚ) ^ (50 : ℤ) * (10 : ℚ) ^ (-32750 : ℤ) from by
        rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num]
      nlinarith [hu_pos, show (2 : ℚ) ≤ (10 : ℚ) ^ (50 : ℤ) from by norm_num]
    have hbound : nav * s / ST < 2 * (10 : ℚ) ^ (-32750 : ℤ) := by
      by_cases hPm0 : P.mantissa_ = 0
      · have hsmall := operator_mul_underflow_truth_small navN shN P .to_nearest
          hnavnorm hsnnorm hmz hshNm hP hPm0
        rw [abs_of_pos (mul_pos (by rw [hnavv]; exact hnav_pos) hshN_pos), hunit, hnavv,
          hshN_val] at hsmall
        have := charge_underflow_mul nav s ST _ hshpos hnav_pos hST_one hsmall
        linarith
      · have hsmall := operator_div_underflow_truth_small P v.sharesTotal Q .to_nearest
          (operator_mul_result_isNormalized navN shN P .to_nearest hnavnorm hsnnorm hmz
            hshNm hP hPm0)
          v.wf.sharesTotal_norm hPm0 hSTm hQ hQm
        rw [hunit] at hsmall
        have hmulbound := operator_mul_rounds_to_nearest navN shN P hnavnorm hsnnorm hP hPm0
        rw [hnavv, hshN_val] at hmulbound
        exact charge_underflow_div nav s ST P.toRat _ hshpos hnav_pos hST_pos hmulbound hsmall
    linarith [hbound, h_le]

end XRPL.Model.SingleAssetVault.DepTight
