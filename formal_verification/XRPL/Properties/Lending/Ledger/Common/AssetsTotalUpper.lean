import XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
import XRPL.Properties.Vault.Proofs.ExactUpdates.Grid
import XRPL.Properties.Lending.Loan.Common.PayFit
import XRPL.Properties.Lending.Ledger.Common.WithdrawHolder

/-! # AssetsTotal runs at most six tenths of a unit of the vault scale per transaction above its flows

On a vault that is not coarsened every transaction moves AssetsTotal by exactly its flow. On a coarsened vault a
deposit, a LoanSet and a LoanAccept are rejected by the Open-limit check, a payment never credits more than its
interest, a default and an impairment change are exact, and a withdrawal, a clawback or a pending delete rounds
AssetsAvailable' to 16 digits, at most six tenths of a unit of its scale above the exact sum. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault VaultWithAmounts WithdrawAmount VaultAmounts
  computeClawback_success_reduces)

open private Vault.cash_update_eq Loan.create_total_eq Loan.accept_total_eq Loan.changeImpairment_total_eq
  add_downward_ge_any from XRPL.Properties.Lending.Ledger.Common.AssetsTotalSteps
open private Number.add_exact_of_grid Vault.total_of_raw open_line_eq
  from XRPL.Properties.Lending.Ledger.Common.VaultScaleProofs
open private Vault.baseExponent_grid from XRPL.Properties.Lending.Ledger.Common.VaultGrid
open private LendingLedger.loanRead_eq Vault.deposit_total_eq Vault.withdraw_payout_units' Vault.clawback_payout_units'
  LendingTx.preflight_vaultClawback_canonical' AssetFlows.net_mk_zero
  from XRPL.Properties.Lending.Ledger.Common.AssetFlowSteps
open private Loan.changeImpairment from XRPL.Model.Lending.Loan.LoanManage

/-- **A cash update lands at most six tenths of a unit of its own scale above the exact sum.** An integral sum below
`2^63` lands exactly. An IOU sum is rounded to 19 digits and then to 16, within half a unit plus a tenth. -/
private lemma Vault.cash_update_le (v : Vault) (cash aa aa' : Number) (hasset : Vault.HoldsAsset v)
    (hv : Number.OnGrid v.baseExponent v.assetsAvailable) (hc : Number.OnGrid v.baseExponent cash)
    (h0 : 0 ≤ v.assetsAvailable.toRat + cash.toRat)
    (hint : v.numericType.isIntegral = true → v.assetsAvailable.toRat + cash.toRat < 2 ^ 63)
    (hs : v.assetsAvailable.operator_add cash .to_nearest = .ok aa)
    (hr : STAmount.roundToNumericType v.numericType aa .to_nearest = .ok aa') :
    aa'.toRat ≤ v.assetsAvailable.toRat + cash.toRat ∨ (v.numericType = .fractional ∧
      ∃ E : ℤ, -96 ≤ E ∧ E ≤ 80 ∧ (10 : ℚ) ^ (E + 15) ≤ aa'.toRat ∧
        aa'.toRat ≤ v.assetsAvailable.toRat + cash.toRat + 6 / 10 * 10 ^ E) := by
  have hmax := hasset.maxValue_le
  have haan := operator_add_isNormalized_to_nearest_sz _ _ _ hv.1 hc.1 hs
  have hsr := operator_add_rounded_to_nearest _ _ _ hv.1 hc.1 hs
  have haa0 : 0 ≤ aa.toRat := Number.RoundsToRepresentable.nonneg_of_nonneg aa _ hsr h0
  by_cases hint' : v.numericType.isIntegral = true
  · -- a whole-number sum below `2^63`, which the asset stores
    left
    obtain ⟨-, hsb⟩ := Vault.baseExponent_grid v
    have hb0 := v.baseExponent_bounds.2.2 hint'
    have hp : (0 : ℚ) < 10 ^ v.baseExponent := zpow_pos (by norm_num) _
    have hlt := hint hint'
    have hbe : (10 : ℚ) ^ v.baseExponent = 1 := by rw [hb0, zpow_zero]
    have haav : aa.toRat = v.assetsAvailable.toRat + cash.toRat :=
      Number.add_exact_of_grid hv hc (by rw [hbe]; linarith) (by rw [hbe]; linarith) hsb hs
    have hden : aa.toRat.den = 1 := by
      obtain ⟨-, a, ha⟩ := hv
      obtain ⟨-, c, hc'⟩ := hc
      rw [haav, ha, hc', hbe, mul_one, mul_one, ← Int.cast_add]
      exact Rat.den_intCast _
    have hrep := STAmount.isRounded_eq_false_of_integral_round _ aa aa' hint' haan haa0 hden hr
    rw [STAmount.roundToNumericType_of_isRounded_false _ _ _ haan hrep hr, haav]
  have hfr : v.numericType = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hint')
  unfold STAmount.roundToNumericType at hr
  cases hst : STAmount.ofNumber v.numericType aa .to_nearest with
  | error e => rw [hst] at hr; cases hr
  | ok st =>
    rw [hst] at hr
    simp only at hr
    obtain ⟨hstc, hstt⟩ := STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax hst
    obtain ⟨hav, -⟩ := hstc.toNumber_exact aa' hr
    have hst0 := STAmount.ofNumber_nonneg _ _ _ _ haan (Number.negative_false_of_nonneg _ haan haa0) hst
    by_cases hm : st.mValue = 0
    · left
      rw [hav, (STAmount.toRat_eq_zero_iff _).mpr hm]
      exact h0
    right
    refine ⟨hfr, ?_⟩
    have hE := STAmount.ofNumber_exactCanonical _ _ _ _ haan haa0 hst hm
    have hiou : st.IOUCanonical := by
      rcases hE with h | ⟨hic, -⟩
      · exact h
      · exact absurd (hstt ▸ hic.is_integral) hint'
    have hstpos : 0 < st.toRat :=
      lt_of_le_of_ne hst0 (fun h => hm ((STAmount.toRat_eq_zero_iff _).mp h.symm))
    obtain ⟨hlo, hhi⟩ := STAmount.IOUCanonical.toRat_bounds st hiou hstpos
    have hw := STAmount.ofNumber_to_nearest_within_half _ aa st haan haa0 hst hm
    obtain ⟨hw1, hw2⟩ := abs_le.mp hw
    have hE1 : (-96 : ℤ) ≤ st.exponent := hiou.exp_lo
    have hE1' : st.exponent ≤ 80 := hiou.exp_hi
    have hpE : (0 : ℚ) < 10 ^ st.exponent := zpow_pos (by norm_num) _
    have h16 : (10 : ℚ) ^ (st.exponent + 16) = 10 ^ st.exponent * 10 ^ 16 := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    have h17 : (10 : ℚ) ^ (st.exponent + 17) = 10 ^ st.exponent * 10 ^ 17 := by
      rw [zpow_add₀ (by norm_num)]; norm_num
    have hm1 : (10 : ℚ) ^ (st.exponent - 1) = 10 ^ st.exponent / 10 := by
      rw [zpow_sub₀ (by norm_num), zpow_one]
    refine ⟨st.exponent, hE1, hE1', by rw [hav]; exact hlo, ?_⟩
    rw [hav]
    -- the exact sum is below `10^(E + 17)`, or the 19-digit sum would be as well
    have hxlt : v.assetsAvailable.toRat + cash.toRat < 10 ^ (st.exponent + 17) := by
      by_contra hc'
      push Not at hc'
      obtain ⟨w, hwn, hwv⟩ := XRPL.Model.SingleAssetVault.Exact.exists_normalized_grid 1 (st.exponent + 17) le_rfl
        (by norm_num) (by unfold minExponent; omega) (by unfold maxExponent; omega)
      have hge := Number.RoundsToRepresentable.ge_of_ge_normalized aa _ hsr w hwn (by rw [hwv]; simpa using hc')
      rw [hwv] at hge
      push_cast at hge
      nlinarith
    -- the 19-digit sum is at most the next point of the `10^(E - 1)` grid
    by_cases hx0 : v.assetsAvailable.toRat + cash.toRat = 0
    · have hle := Number.RoundsToRepresentable.le_of_le_normalized aa _ hsr Number.zero (Or.inl rfl)
        (by rw [Number.toRat_zero, hx0])
      rw [Number.toRat_zero] at hle
      rw [hx0]
      nlinarith
    have hxpos : 0 < v.assetsAvailable.toRat + cash.toRat := lt_of_le_of_ne h0 (Ne.symm hx0)
    have hpm : (0 : ℚ) < 10 ^ (st.exponent - 1) := zpow_pos (by norm_num) _
    set K : ℤ := ⌈(v.assetsAvailable.toRat + cash.toRat) / 10 ^ (st.exponent - 1)⌉ with hK
    have hK1 : 1 ≤ K := by
      rw [hK, Int.one_le_ceil_iff]
      exact div_pos hxpos hpm
    have hKhi : K ≤ 10 ^ 18 := by
      rw [hK, Int.ceil_le]
      rw [div_le_iff₀ hpm, hm1]
      push_cast
      nlinarith
    have hKge : v.assetsAvailable.toRat + cash.toRat ≤ (K : ℚ) * 10 ^ (st.exponent - 1) := by
      have := Int.le_ceil ((v.assetsAvailable.toRat + cash.toRat) / 10 ^ (st.exponent - 1))
      rw [← hK, div_le_iff₀ hpm] at this
      exact this
    have hKlt : (K : ℚ) * 10 ^ (st.exponent - 1) < v.assetsAvailable.toRat + cash.toRat + 10 ^ (st.exponent - 1) := by
      have := Int.ceil_lt_add_one ((v.assetsAvailable.toRat + cash.toRat) / 10 ^ (st.exponent - 1))
      rw [← hK] at this
      calc (K : ℚ) * 10 ^ (st.exponent - 1)
          < ((v.assetsAvailable.toRat + cash.toRat) / 10 ^ (st.exponent - 1) + 1) * 10 ^ (st.exponent - 1) :=
            mul_lt_mul_of_pos_right this hpm
        _ = _ := by field_simp
    obtain ⟨w, hwn, hwv⟩ := XRPL.Model.SingleAssetVault.Exact.exists_normalized_grid K.toNat (st.exponent - 1)
      (by omega) (by omega) (by unfold minExponent; omega) (by unfold maxExponent; omega)
    have hKn : ((K.toNat : ℕ) : ℚ) = (K : ℚ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [hKn] at hwv
    have hle := Number.RoundsToRepresentable.le_of_le_normalized aa _ hsr w hwn (by rw [hwv]; exact hKge)
    rw [hwv, hm1] at hle
    rw [hm1] at hKlt
    linarith

/-- An integral AssetsAvailable the asset stores is within the asset's maximum. -/
private lemma Vault.cash_le_maxValue (v : Vault) (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hint : v.numericType.isIntegral = true) :
    v.assetsAvailable.toRat ≤ v.numericType.maxValue.toNat ∧ v.assetsAvailable.toRat < 2 ^ 63 := by
  have hrep := (STAmount.isRounded_eq_false_iff _ _ v.wf.assetsAvailable_norm v.exact.assetsAvailable_nonneg).mp hst
  rcases hrep with h0 | hrep
  · rw [h0]; exact ⟨Nat.cast_nonneg _, by norm_num⟩
  cases hnt : v.numericType with
  | integral mv mo ms msh =>
    rw [hnt] at hrep
    obtain ⟨-, k, hkm, hk, hkv⟩ := hrep
    have hk' : (k : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (show k ≤ 9223372036854775807 by omega)
    have hkm' : (k : ℚ) ≤ mv.toNat := by exact_mod_cast hkm
    rw [hkv]
    exact ⟨hkm', by linarith⟩
  | fractional => rw [hnt] at hint; cases hint

/-- **An AssetsAvailable of at least `10^(E + 15)` puts the vault scale at `E` or above.** AssetsTotal rounds the
sum down, never below a 19-digit value under it. -/
private lemma Vault.le_scale_of_cash (v : Vault) (E : ℤ) (hE : -96 ≤ E) (hE' : E ≤ 80)
    (hfr : v.numericType = .fractional)
    (hA : (10 : ℚ) ^ (E + 15) ≤ v.assetsAvailable.toRat) (t : Number) (e : ℤ) (ht : v.assetsTotal = .ok t)
    (he : numberExponent t v.baseExponent v.numericType = .ok e) : E ≤ e := by
  obtain ⟨w, hwn, hwv⟩ := XRPL.Model.SingleAssetVault.Exact.exists_normalized_grid 1 (E + 15) le_rfl (by norm_num)
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  rw [Nat.cast_one, one_mul] at hwv
  have hw0 : 0 < w.toRat := by rw [hwv]; positivity
  unfold RawVault.assetsTotal at ht
  have hAD0 : 0 ≤ v.assetsDeployed.toRat := v.exact.assetsDeployed_nonneg
  have hwt := add_downward_ge_any _ _ t w v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm ht hwn hw0
    (by rw [hwv]; linarith)
  have htm : t.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by linarith)
  have htn := operator_add_isNormalized _ _ t _ v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm ht htm
  rw [hfr] at he
  exact numberExponent_frac_of_le t _ e E htn hE (by rw [hwv] at hwt; exact hwt) he

/-- **A debit of whole base units, at most AssetsAvailable, lands at most six tenths of a unit of its scale too
high**, and leaves AssetsDeployed alone. -/
private lemma Vault.debit_total_le (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hasset : Vault.HoldsAsset v) (hv : Vault.OnBaseGrid v)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hc : assets.CanonicalOrZero) (hj : ∃ j : ℕ, assets.toRat = (j : ℚ) * (10 : ℚ) ^ v.baseExponent)
    (hle : assets.toRat ≤ v.assetsAvailable.toRat)
    (hadj : (v.adjustAssetsAndShares assets.operator_neg shares).run = .ok (.ok raw)) :
    raw.assetsDeployed.toRat = v.assetsDeployed.toRat ∧
      (raw.assetsAvailable.toRat ≤ v.assetsAvailable.toRat - assets.toRat ∨ (v.numericType = .fractional ∧
        ∃ E : ℤ, -96 ≤ E ∧ E ≤ 80 ∧ (10 : ℚ) ^ (E + 15) ≤ raw.assetsAvailable.toRat ∧
          raw.assetsAvailable.toRat ≤ v.assetsAvailable.toRat - assets.toRat + 6 / 10 * 10 ^ E)) := by
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, hrw⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hnv, hnn⟩ := hc.operator_neg.toNumber_exact assetsNum hnum
  rw [STAmount.operator_neg_toRat] at hnv
  obtain ⟨j, hj⟩ := hj
  have ha0 : 0 ≤ assets.toRat := by rw [hj]; positivity
  have hcash := Vault.cash_update_le v assetsNum s aa' hasset hv.1 ⟨hnn, -(j : ℤ), by rw [hnv, hj]; push_cast; ring⟩
    (by rw [hnv]; linarith) (fun hint => by rw [hnv]; linarith [(Vault.cash_le_maxValue v hst hint).2]) hs haa
  rw [hnv, ← sub_eq_add_neg] at hcash
  subst hrw
  exact ⟨rfl, hcash⟩

/-- A balance change that moves no cash and deploys nothing keeps the total exactly, on a vault whose asset stores
AssetsAvailable. -/
private lemma Vault.poolAdjust_zero_total_eq' (v v' : Vault) (c : PoolBalanceChange)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (hc : c.cash = Number.zero) (hd : c.deployed = Number.zero) (h : AssetPool.adjustBalances v c = .ok (.ok v')) :
    v'.assetsAvailable.toRat + v'.assetsDeployed.toRat = v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  obtain ⟨raw, hadj, hlaw⟩ := Vault.poolAdjust_ok_inv v c v' h
  obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv v c raw hadj
  obtain ⟨aa, haa, hround⟩ := hs.cash
  rw [hc, Number.operator_add_zero_right, Except.ok.injEq] at haa
  subst haa
  have h1 := STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm hst hround
  have h2 := hs.deployed
  rw [hd, Number.operator_add_zero_right, Except.ok.injEq] at h2
  rw [Vault.total_of_raw hlaw, h1, ← h2]

/-- A whole number of base units up to `10^16` of them is stored exactly by the asset. -/
private lemma Vault.isRounded_false_of_le_line (v : Vault) (hasset : Vault.HoldsAsset v) (x : Number)
    (hx : Number.OnGrid v.baseExponent x) (h0 : 0 ≤ x.toRat) (hle : x.toRat ≤ 10 ^ (16 + v.baseExponent)) :
    STAmount.isRounded v.numericType x = false := by
  rcases hle.lt_or_eq with hlt | heq
  · exact Vault.isRounded_false_of_grid' v hasset x hx h0 hlt
  rw [STAmount.isRounded_eq_false_iff _ x hx.1 h0, heq]
  right
  obtain ⟨hblo, hbhi, hbint⟩ := v.baseExponent_bounds
  rcases hasset with h | h | h <;> rw [h]
  · refine ⟨10 ^ 15, v.baseExponent + 1, by norm_num, by norm_num, by omega, by omega, ?_⟩
    rw [show (16 : ℤ) + v.baseExponent = (v.baseExponent + 1) + 15 by ring, zpow_add₀ (by norm_num)]
    push_cast; ring
  · have hb0 : v.baseExponent = 0 := hbint (by rw [h]; rfl)
    rw [hb0]
    exact ⟨by decide, 10 ^ 16, by decide, by norm_num, by norm_num⟩
  · have hb0 : v.baseExponent = 0 := hbint (by rw [h]; rfl)
    rw [hb0]
    exact ⟨by decide, 10 ^ 16, by decide, by norm_num, by norm_num⟩

/-- **A delete lands AssetsTotal at most six tenths of a unit of its scale too high**: a pending loan's
principal leaves AssetsDeployed exactly and returns to AssetsAvailable at 16 digits. Other deletes move no cash. -/
private lemma LendingLedger.delete_total_le (l : LendingLedger) (hr : l.Reachable) (i : Nat) (loan : Loan)
    (hat : l.LoanAt i loan)
    (hsupply : l.vault.numericType = NumericType.int64 →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 2 ^ 63)
    (r : LoanBrokerWithPool Vault) (h : (loan.delete l.vault).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ∨
      (l.vault.numericType = .fractional ∧ ∃ E : ℤ, -96 ≤ E ∧ E ≤ 80 ∧
        (10 : ℚ) ^ (E + 15) ≤ r.pool'.assetsAvailable.toRat ∧
        r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤
          l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + 6 / 10 * 10 ^ E) := by
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  have hst := hr.availableStored
  obtain ⟨hAAg, -, -⟩ := LendingLedger.base_grid_proof l hr hmax
  obtain ⟨-, hnt⟩ := hr.loanAt_scale hat
  by_cases hp : loan.isPending = true
  · obtain ⟨principal', raw, _, hround, hadj, hlaw, -, -⟩ := Loan.delete_pending_ok_inv loan l.vault r hp h
    obtain ⟨p, hpb, hpv, hpad, -⟩ := hr.loanAt_principal hat
    have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
    have hAD16 : l.vault.assetsDeployed.toRat ≤ 10 ^ 16 * (10 : ℚ) ^ l.vault.baseExponent := hr.debtInv.loss.deployed
    have hp0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
    have hAA0 : 0 ≤ l.vault.assetsAvailable.toRat := l.vault.exact.assetsAvailable_nonneg
    have hpg : Number.OnGrid l.vault.baseExponent loan.principalOutstanding :=
      ⟨loan.wf.principalOutstanding_norm, p, by rw [hpv]; push_cast; rfl⟩
    -- the asset stores the principal, which returns to AssetsAvailable
    have hpst := Vault.isRounded_false_of_le_line l.vault hasset _ hpg hp0 (by rw [open_line_eq]; linarith)
    rw [hnt] at hround
    have hpv' : principal'.toRat = loan.principalOutstanding.toRat :=
      STAmount.roundToNumericType_of_isRounded_false _ _ _ loan.wf.principalOutstanding_norm hpst hround
    have hpg' : Number.OnGrid l.vault.baseExponent principal' :=
      ⟨STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround, p, by rw [hpv', hpv]; push_cast; rfl⟩
    obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv l.vault _ raw hadj
    obtain ⟨aa, haa, hr'⟩ := hs.cash
    -- AssetsDeployed loses the principal exactly
    obtain ⟨w, hw, hwv⟩ := hr.deployed_fits hat
    have hd : raw.assetsDeployed.toRat = l.vault.assetsDeployed.toRat - loan.principalOutstanding.toRat := by
      have := Number.operator_add_exact_of_fits l.vault.wf.assetsDeployed_norm
        (Number.operator_neg_isNormalized _ loan.wf.principalOutstanding_norm) hs.deployed
        ⟨w, hw, by rw [hwv, Number.toRat_neg]; ring⟩
      rw [this, Number.toRat_neg]; ring
    have hint : l.vault.numericType.isIntegral = true →
        l.vault.assetsAvailable.toRat + principal'.toRat < 2 ^ 63 := by
      intro hint
      have hb0 := l.vault.baseExponent_bounds.2.2 hint
      rw [hb0, zpow_zero, mul_one] at hAD16
      rw [hpv']
      rcases hasset with hf | hn | hi
      · rw [hf] at hint; cases hint
      · have hmv := (Vault.cash_le_maxValue l.vault hst hint).1
        rw [hn, show NumericType.native.maxValue.toNat = 10 ^ 17 from rfl] at hmv
        push_cast at hmv
        linarith
      · linarith [hsupply hi]
    have hcash := Vault.cash_update_le l.vault principal' aa raw.assetsAvailable hasset hAAg hpg'
      (by rw [hpv']; linarith) hint haa hr'
    rw [hpv'] at hcash
    have hAA' : r.pool'.assetsAvailable = raw.assetsAvailable :=
      congrArg RawVault.assetsAvailable (RawVault.to_lawful_ok hlaw).1
    have hAD' : r.pool'.assetsDeployed = raw.assetsDeployed :=
      congrArg RawVault.assetsDeployed (RawVault.to_lawful_ok hlaw).1
    rw [hAA', hAD', hd]
    rcases hcash with hle | ⟨hfr, E, hE1, hE2, hE3, hE4⟩
    · left; linarith
    · right; exact ⟨hfr, E, hE1, hE2, hE3, by linarith⟩
  · simp only [Loan.delete, Bool.not_eq_true] at h hp
    rw [hp] at h
    unfold_ter at h
    walk_ok
    left
    exact le_refl _

/-- **A payment never raises AssetsTotal by more than its interest**, on any reachable ledger. -/
private lemma LendingLedger.pay_total_le (l l' : LendingLedger) (i : Nat) (pt : LoanPaymentType) (amount : Number)
    (hr : l.Reachable) (h : (l.apply (.loanPay i pt amount)).run = .ok (.ok l')) :
    l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat ≤
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + l.paidInterest i pt amount := by
  obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan rfl h
  obtain ⟨e, broker, loan, r, he, hb, hw, -, hpay, rfl⟩ := l.applyLoan_pay_inv u i pt amount hu
  obtain ⟨p, hp', -⟩ := Loan.pay_ok loan l.vault pt amount l.now r hpay
  have hip : l.paidInterest i pt amount = p.amounts.interestPaid.toRat := by
    simp only [LendingLedger.paidInterest, LendingLedger.loanRead_eq he hb hw, hp']
  have h53 := Loan.payment_assetsTotal_upper_bound_reachable_proof loan amount pt r l hr i ⟨e, broker, he, hb, hw⟩ p
    hp' hpay
  show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤ _
  have h53' : r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat -
      (l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + p.amounts.interestPaid.toRat) ≤ 0 := h53
  rw [hip]
  linarith

open XRPL.Model.SingleAssetVault in
/-- **A deposit succeeds only on a vault that is not coarsened**: the inflow check keeps AssetsTotal below the Open
limit plus a base unit. -/
private lemma Vault.deposit_not_coarsened (v : Vault) (amount : STAmount) (isDonation : Bool) (t : UInt32)
    (hpos : 0 < amount.toRat) (hc : amount.Canonical) (hty : amount.mNumericType = v.numericType)
    (hasset : Vault.HoldsAsset v) (r : VaultWithAmounts) (h : (v.deposit amount isDonation t hpos).run = .ok (.ok r)) :
    v.assetsAvailable.toRat + v.assetsDeployed.toRat < 10 ^ (16 + v.baseExponent) := by
  obtain ⟨ra, amounts, raw, hra, hcomp, hin, -⟩ := Vault.deposit_ok_reduces v amount isDonation t hpos r h
  have hmax := hasset.maxValue_le
  obtain ⟨hrac, hraty, -⟩ := Vault.roundedDepositAmount_form v amount ra hc hty hra
  obtain ⟨hcf, -, hc0⟩ := computeDeposit_assets_form v ra isDonation amounts hrac hraty hmax hcomp
  obtain ⟨amountNum, -, hex⟩ := Vault.checkOpenLimit_ok_inv v _ hin
  unfold XRPL.Model.SingleAssetVault.Vault.exceedsOpenLimit at hex
  obtain ⟨atot, hat, -⟩ := bind_ok_peel _ _ _ hex
  have hb := Vault.checkOpenLimit_bound v _ hcf hc0 atot hat hin
  by_contra hge
  push Not at hge
  obtain ⟨hblo, hbhi, -⟩ := v.baseExponent_bounds
  obtain ⟨w, hwn, hwv⟩ := XRPL.Model.SingleAssetVault.Exact.exists_normalized_grid 1 (16 + v.baseExponent) le_rfl
    (by norm_num) (by unfold minExponent; omega) (by unfold maxExponent; omega)
  rw [Nat.cast_one, one_mul] at hwv
  unfold RawVault.assetsTotal at hat
  have hwt := add_downward_ge_any _ _ atot w v.wf.assetsAvailable_norm v.wf.assetsDeployed_norm hat hwn
    (by rw [hwv]; positivity) (by rw [hwv]; exact hge)
  rw [hwv] at hwt
  have h1 : (10 : ℚ) ^ (16 + v.baseExponent) = 10 * 10 ^ (15 + v.baseExponent) := by
    rw [show (16 : ℤ) + v.baseExponent = 1 + (15 + v.baseExponent) by ring, zpow_add₀ (by norm_num)]; norm_num
  have h2 : (10 : ℚ) ^ v.baseExponent ≤ 10 ^ (15 + v.baseExponent) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith

/-- An impairment change moves no cash and deploys nothing, on a vault whose asset stores AssetsAvailable. -/
private lemma Loan.changeImpairment_total_eq' (loan : Loan) (v : Vault) (impaired : Bool) (r : LoanWithPool Vault)
    (hst : STAmount.isRounded v.numericType v.assetsAvailable = false)
    (h : (Loan.changeImpairment loan v impaired).run = .ok (.ok r)) :
    r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
      v.assetsAvailable.toRat + v.assetsDeployed.toRat := by
  simp only [Loan.changeImpairment] at h
  unfold_ter at h
  walk_ok
  all_goals exact Vault.poolAdjust_zero_total_eq' v _ _ hst rfl rfl ‹_›

/-- **A transaction lands AssetsTotal at most six tenths of a unit of the vault scale above its flow** on a reachable
ledger. The vault scale is the scale of AssetsTotal after the transaction. -/
lemma LendingLedger.flow_step_upper (l l' : LendingLedger) (tx : LendingTx) (hr : l.Reachable)
    (h : (l.apply tx).run = .ok (.ok l'))
    (hsupply : l.vault.numericType = NumericType.int64 → ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b →
      l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + b.coverAvailable.toRat < 2 ^ 63)
    (t : Number) (e : ℤ) (ht : l'.vault.assetsTotal = .ok t)
    (he : numberExponent t l'.vault.baseExponent l'.vault.numericType = .ok e) :
    l'.vault.toRawVault.toExact.assetsTotal ≤
      l.vault.toRawVault.toExact.assetsTotal + (l.flowOf tx).net + 6 / 10 * 10 ^ e := by
  have hpe : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
  show l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat ≤
    l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + _ + _
  by_cases hpay : ∃ i pt amount, tx = .loanPay i pt amount
  · obtain ⟨i, pt, amount, rfl⟩ := hpay
    have hle := LendingLedger.pay_total_le l l' i pt amount hr h
    show _ ≤ _ + ((0 : ℚ) - 0 - 0 + l.paidInterest i pt amount - 0) + _
    linarith
  by_cases hnc : l.NotCoarsened
  · have heq : l'.vault.assetsAvailable.toRat + l'.vault.assetsDeployed.toRat =
        l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat + (l.flowOf tx).net :=
      LendingLedger.flow_step l l' tx hr h hnc (fun hp => absurd hp hpay)
    linarith
  -- a coarsened vault
  have hasset := hr.holdsAsset
  have hmax := hasset.maxValue_le
  obtain ⟨hAAg, hADg, -, -, -, -⟩ := LendingLedger.base_grid_proof l hr hmax
  have hv : Vault.OnBaseGrid l.vault := ⟨hAAg, hADg⟩
  have hst := hr.availableStored
  obtain ⟨kA, hkA⟩ := hr.assetsAvailable_units hasset
  have hpre := (LendingLedger.apply_checked h).1
  have hnt' := LendingLedger.apply_numericType h
  have hAD0 : 0 ≤ l.vault.assetsDeployed.toRat := l.vault.exact.assetsDeployed_nonneg
  -- a cash rounding on a coarsened vault lands within one unit of the vault scale
  have hscale : ∀ E : ℤ, -96 ≤ E → E ≤ 80 → l.vault.numericType = .fractional →
      (10 : ℚ) ^ (E + 15) ≤ l'.vault.assetsAvailable.toRat → (10 : ℚ) ^ E ≤ 10 ^ e := fun E h1 h2 hfr hA =>
    zpow_le_zpow_right₀ (by norm_num) (Vault.le_scale_of_cash l'.vault E h1 h2 (by rw [hnt']; exact hfr) hA t e ht he)
  by_cases hvt : tx.isVault = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_vault hvt h
    have hvault : (l.commitVault u).vault = u.vault := by
      unfold LendingLedger.commitVault; split <;> simp [LendingLedger.setShares]
    rw [hvault] at hscale ⊢
    cases tx with
    | vaultDeposit hd amount isDonation =>
      obtain ⟨hc, hty⟩ := LendingTx.preflight_vaultDeposit' l hd amount isDonation hasset hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hpos
        unfold_ter at hu
        walk_ok
        have hdep : (l.vault.deposit amount isDonation l.now hpos).run = .ok (.ok _) := ‹_›
        have hS := Vault.deposit_not_coarsened _ _ _ _ _ hc hty hasset _ hdep
        exact absurd (show l.NotCoarsened by unfold LendingLedger.NotCoarsened; rw [← open_line_eq]; exact hS) hnc
      · cases hu
    | vaultWithdraw hd amount =>
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hpos
        unfold_ter at hu
        walk_ok
        have hwh : (l.vault.withdraw amount (l.isSoleShareholder hd) l.now hpos (some (l.sharesOf hd))).run =
          .ok (.ok _) := ‹_›
        have hw := (Vault.withdraw_holder_ok _ _ _ _ _ _ _ hwh).1
        obtain ⟨hc, hj, hle, raw, hadj, hraw⟩ := Vault.withdraw_payout_units' _ _ _ _ _ hst ⟨kA, hkA⟩ hmax _ hw
        obtain ⟨hADe, hcash⟩ := Vault.debit_total_le _ _ _ raw hasset hv hst hc hj hle hadj
        rw [show (_ : VaultWithAmounts).vault'.assetsAvailable = _ from congrArg RawVault.assetsAvailable hraw]
          at hscale
        rw [show (_ : VaultWithAmounts).vault'.assetsAvailable = _ from congrArg RawVault.assetsAvailable hraw,
          show (_ : VaultWithAmounts).vault'.assetsDeployed = _ from congrArg RawVault.assetsDeployed hraw, hADe]
        show _ ≤ _ + ((0 : ℚ) - l.withdrawalPayout hd amount - 0 + 0 - 0) + _
        simp only [LendingLedger.withdrawalPayout, dif_pos hpos, hwh]
        rcases hcash with hle' | ⟨hfr, E, hE1, hE2, hE3, hE4⟩
        · linarith
        · have := hscale E hE1 hE2 hfr hE3
          linarith
      · cases hu
    | vaultClawback hd assets =>
      have hca := LendingTx.preflight_vaultClawback_canonical' l hasset hd assets hpre
      simp only [LendingLedger.applyVault] at hu
      split at hu
      · rename_i hnn
        unfold_ter at hu
        walk_ok
        have hof : STAmount.ofNumber .int64 (l.sharesOf hd) .to_nearest = .ok _ := ‹_›
        have hcw : (l.vault.clawback assets _ (l.isSoleShareholder hd) hnn).run = .ok (.ok _) := ‹_›
        obtain ⟨hsn, hs0⟩ := hr.sharesNonneg.sharesOf hd
        have hhs := (STAmount.ofNumber_canonicalOrZero .int64 _ _ _ (fun _ => by decide) hof).1
        have hhs0 := STAmount.ofNumber_nonneg _ _ _ _ hsn (Number.negative_false_of_nonneg _ hsn hs0) hof
        obtain ⟨hc, hj, hle, raw, hadj, hraw⟩ :=
          Vault.clawback_payout_units' _ _ _ _ hnn hca ⟨hhs, hhs0⟩ hmax _ hcw
        obtain ⟨hADe, hcash⟩ := Vault.debit_total_le _ _ _ raw hasset hv hst hc hj hle hadj
        rw [show (_ : VaultWithAmounts).vault'.assetsAvailable = _ from congrArg RawVault.assetsAvailable hraw]
          at hscale
        rw [show (_ : VaultWithAmounts).vault'.assetsAvailable = _ from congrArg RawVault.assetsAvailable hraw,
          show (_ : VaultWithAmounts).vault'.assetsDeployed = _ from congrArg RawVault.assetsDeployed hraw, hADe]
        show _ ≤ _ + ((0 : ℚ) - 0 - l.clawedAssets hd assets + 0 - 0) + _
        simp only [LendingLedger.clawedAssets, dif_pos hnn, hof, hcw]
        rcases hcash with hle' | ⟨hfr, E, hE1, hE2, hE3, hE4⟩
        · linarith
        · have := hscale E hE1 hE2 hfr hE3
          linarith
      · cases hu
    | vaultBurnShares hd amount =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, hf⟩ := Vault.burnShares_frame _ _ _ ‹_›
      rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)]
      show _ ≤ _ + AssetFlows.net 0 + _
      rw [AssetFlows.net_zero]; linarith
    | vaultSet m b ub =>
      simp only [LendingLedger.applyVault] at hu
      unfold_ter at hu
      walk_ok
      obtain ⟨_, _, hf⟩ := Vault.update_frame _ _ _ _ _ ‹_›
      rw [(congrArg RawVault.assetsAvailable hf :), (congrArg RawVault.assetsDeployed hf :)]
      show _ ≤ _ + AssetFlows.net 0 + _
      rw [AssetFlows.net_zero]; linarith
    | _ => simp only [LendingTx.isVault] at hvt; cases hvt
  by_cases hb : tx.isBroker = true
  · obtain ⟨u, -, rfl⟩ := LendingLedger.apply_broker hb h
    have h0 : (l.flowOf tx).net = 0 := by
      cases tx <;> simp only [LendingTx.isBroker, Bool.false_eq_true] at hb <;> exact AssetFlows.net_zero
    show l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat ≤ _ + _ + _
    rw [h0]; linarith
  by_cases hl : tx.isLoan = true
  · obtain ⟨u, hu, rfl⟩ := LendingLedger.apply_loan hl h
    show u.vault.assetsAvailable.toRat + u.vault.assetsDeployed.toRat ≤ _
    cases tx with
    | loanSet i principal rates fees pi pt gp sd twoStep ao =>
      obtain ⟨hpn, hpos⟩ := LendingTx.preflight_loanSet_principal l i principal rates fees pi pt gp sd twoStep ao hpre
      simp only [LendingLedger.applyLoan] at hu
      obtain ⟨broker, r, hb', hc, hcr, rfl⟩ := l.applyLoanSet_inv _ _ _ _ _ _ _ _ hu
      have hst' := Loan.canCreate_exact _ _ _ _ _ _ _ hc principal (List.mem_cons_self ..)
      obtain ⟨hzone, -⟩ := Loan.create_inside_open_zone broker l.vault principal rates fees _ ao twoStep r hpn
        hpos hst' hcr
      have hp10 : (0 : ℚ) < 10 ^ l.vault.baseExponent := zpow_pos (by norm_num) _
      have h2 : (10 : ℚ) ^ (l.vault.baseExponent - 1) = 10 ^ l.vault.baseExponent / 10 := by
        rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
      rw [h2] at hzone
      push_cast at hzone
      exact absurd (show l.NotCoarsened by unfold LendingLedger.NotCoarsened; nlinarith) hnc
    | loanAccept i =>
      obtain ⟨e', broker, loan, r, he', hb', hw, -, hr', rfl⟩ := l.applyLoan_accept_inv u i hu
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤ _
      have hacc : r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
          l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat := by
        simp only [Loan.accept] at hr'
        unfold_ter at hr'
        walk_ok
        exact Vault.poolAdjust_zero_total_eq' l.vault _ _ hst rfl rfl ‹_›
      rw [hacc]
      show _ ≤ _ + AssetFlows.net 0 + _
      rw [AssetFlows.net_zero]; linarith
    | loanDelete i =>
      obtain ⟨e', broker, loan, r, he', hb', hw, -, hr', rfl⟩ := l.applyLoan_delete_inv u i hu
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤ _
      have hsup : l.vault.numericType = NumericType.int64 →
          l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat < 2 ^ 63 := fun hi => by
        have := hsupply hi _ broker hb'
        have : 0 ≤ broker.coverAvailable.toRat := broker.exact.coverAvailable_nonneg
        linarith
      have hdel := LendingLedger.delete_total_le l hr i loan ⟨e', broker, he', hb', hw⟩ hsup r hr'
      show _ ≤ _ + AssetFlows.net 0 + _
      rw [AssetFlows.net_zero]
      have hscale' := hscale
      simp only [LendingLedger.commitLoan] at hscale'
      rcases hdel with hle' | ⟨hfr, E, hE1, hE2, hE3, hE4⟩
      · linarith
      · have := hscale' E hE1 hE2 hfr hE3
        linarith
    | loanManage i action =>
      obtain ⟨e', broker, loan, r, he', hb', hw, -, hr', rfl⟩ := l.applyLoan_manage_inv u i action hu
      show r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat ≤ _
      cases action with
      | impair =>
        have himp : r.pool'.assetsAvailable.toRat + r.pool'.assetsDeployed.toRat =
            l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat := by
          simp only [Loan.manage, Loan.manageImpair] at hr'
          unfold_ter at hr'
          walk_ok
          exact Loan.changeImpairment_total_eq' loan l.vault true _ hst ‹_›
        rw [himp]
        show _ ≤ _ + AssetFlows.net 0 + _
        rw [AssetFlows.net_zero]; linarith
      | unimpair =>
        rw [Loan.changeImpairment_total_eq' loan _ false r hst hr']
        show _ ≤ _ + AssetFlows.net 0 + _
        rw [AssetFlows.net_zero]; linarith
      | default =>
        have hdef : ∃ r₀ : LoanWithAmounts Vault, (loan.manageDefault l.vault).run = .ok (.ok r₀) ∧
            r = r₀.toLoanWithPool := by
          simp only [Loan.manage] at hr'
          unfold_ter at hr'
          walk_ok
          exact ⟨_, ‹_›, rfl⟩
        obtain ⟨r₀, hok₀, rfl⟩ := hdef
        have hbr : loan.broker = broker := by
          have := Loan.withBroker_eq hw
          exact congrArg RawLoan.broker this
        have hsup : l.vault.numericType = NumericType.int64 →
            l.vault.assetsAvailable.toRat + loan.broker.coverAvailable.toRat < 2 ^ 63 := fun hi => by
          have := hsupply hi _ broker hb'
          rw [hbr]; linarith
        obtain ⟨htot, -⟩ := LendingLedger.manageDefault_vault_exact_proof l hr i loan ⟨e', broker, he', hb', hw⟩ r₀
          hok₀ hsup
        have htot' : r₀.pool'.assetsAvailable.toRat + r₀.pool'.assetsDeployed.toRat =
            l.vault.assetsAvailable.toRat + l.vault.assetsDeployed.toRat -
              (loan.principalOutstanding.toRat - r₀.amountToPool.toRat) := htot
        rw [show r₀.toLoanWithPool.pool' = r₀.pool' from rfl, htot']
        show _ ≤ _ + ((0 : ℚ) - 0 - 0 + 0 - l.defaultLoss i) + _
        obtain ⟨_, _, _, _, _, -, hdc, -⟩ := Loan.manageDefault_ok_parts loan l.vault r₀ hok₀
        simp only [LendingLedger.defaultLoss, LendingLedger.loanRead_eq he' hb' hw, hdc]
        linarith
    | loanPay i paymentType amount => exact absurd ⟨i, paymentType, amount, rfl⟩ hpay
    | _ => simp only [LendingLedger.applyLoan] at hu; cases hu
  have hc := (LendingLedger.apply_checked h).2
  cases tx <;> simp only [LendingTx.isVault, LendingTx.isBroker, LendingTx.isLoan, Bool.false_eq_true,
    not_false_eq_true, not_true_eq_false] at hvt hb hl
  · simp only [LendingLedger.applyChecked, LendingLedger.applyVaultDelete] at hc
    unfold_ter at hc
    walk_ok
    show _ ≤ _ + AssetFlows.net 0 + _
    rw [AssetFlows.net_zero]; linarith
  · simp only [LendingLedger.applyChecked] at hc
    cases hc
    show _ ≤ _ + AssetFlows.net 0 + _
    rw [AssetFlows.net_zero]; linarith

/-- **Proof body of `assetsTotal_upper_bound`.** Each transaction lands AssetsTotal at most six tenths of a unit of
the vault scale above its flow, and these add up along the run. -/
lemma LendingLedger.assetsTotal_upper_bound_proof (start l : LendingLedger) (txs : List LendingTx) (x : ℚ)
    (hr : start.Reachable) (hrun : start.ReachableFromIn txs l x) (E : ℤ)
    (hE : ∀ (pre : List LendingTx) (l₁ : LendingLedger) (x₁ : ℚ), pre <+: txs → start.ReachableFromIn pre l₁ x₁ →
      ∃ (t : Number) (e : ℤ), l₁.vault.assetsTotal = .ok t ∧
        numberExponent t l₁.vault.baseExponent l₁.vault.numericType = .ok e ∧ e ≤ E)
    (hsupply : ∀ (pre : List LendingTx) (l₁ : LendingLedger) (x₁ : ℚ), pre <+: txs →
      start.ReachableFromIn pre l₁ x₁ → l₁.vault.numericType = NumericType.int64 →
      ∀ (j : Nat) (b : LoanBroker), l₁.broker? j = some b →
        l₁.vault.assetsAvailable.toRat + l₁.vault.assetsDeployed.toRat + b.coverAvailable.toRat < 2 ^ 63) :
    l.vault.toRawVault.toExact.assetsTotal - (start.vault.toRawVault.toExact.assetsTotal +
      (start.flows txs).deposits - (start.flows txs).withdrawals - (start.flows txs).clawbacks +
      (start.flows txs).interestPaid - (start.flows txs).defaultLosses) ≤ 6 / 10 * txs.length * (10 : ℚ) ^ E := by
  suffices h : l.vault.toRawVault.toExact.assetsTotal ≤
      start.vault.toRawVault.toExact.assetsTotal + (start.flows txs).net + 6 / 10 * txs.length * (10 : ℚ) ^ E by
    unfold AssetFlows.net at h; linarith
  induction hrun with
  | refl => rw [show start.flows [] = 0 from rfl, AssetFlows.net_zero]; simp
  | @step txs₀ l₀ l₁ x₀ tx hprev hok ih =>
    have ih' := ih (fun pre l₂ x₂ hpre hr' => hE pre l₂ x₂ (hpre.trans (List.prefix_append _ _)) hr')
      (fun pre l₂ x₂ hpre hr' => hsupply pre l₂ x₂ (hpre.trans (List.prefix_append _ _)) hr')
    obtain ⟨t, e, ht, he, heE⟩ := hE (txs₀ ++ [tx]) l₁ _ (List.prefix_refl _) (.step tx hprev hok)
    have hstep := LendingLedger.flow_step_upper l₀ l₁ tx (hprev.reachable_of hr) hok
      (hsupply txs₀ l₀ x₀ (List.prefix_append _ _) hprev) t e ht he
    have hpow : (10 : ℚ) ^ e ≤ 10 ^ E := zpow_le_zpow_right₀ (by norm_num) heE
    rw [LendingLedger.flows_snoc hprev.reaches hok, AssetFlows.net_add, List.length_append, List.length_singleton]
    push_cast
    linarith

end XRPL.Model.Lending
