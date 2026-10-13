import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Defs

/-! # Witnesses for the tight `withdraw_sharesBurned` and `withdraw_payout` bounds

Each run's result is computed by the model and checked by `native_decide`.

* Truncation: 1 asset, `10¹⁵` shares, withdraw `1.999999999999999·10⁻¹⁵`: ideal
  `1.999999999999999` shares, burned `1`, short by `1 - 10⁻¹⁵`.
* Sharp share overshoot: `99999999999889682.7` assets, 1844674407370955163 shares, withdraw
  `5·10¹⁵`: both `.to_nearest` stages round up by almost half a step of the maxRep band, burning
  `92233720368649508` shares, `1.0841995·10⁻¹⁸` relatively above the ideal.
* Payout overshoot: int64, `10¹⁸ + 2` assets, `2·10¹⁸` shares, burn 1: worth
  `0.5 + 10⁻¹⁸`, paid `1`.
* Payout rounding shortfall: int64, `3·10¹⁸ - 2` assets, `2·10¹⁸` shares, burn 1: worth
  `1.5 - 10⁻¹⁸`, paid `1`.
* Payout clamp shortfall: `1999999.999999999499` assets, `10⁶` shares, burn 1: worth
  `1.999999999999999499`, priced `1.999999999999999`, floored onto the `10⁻⁹` grid of the
  post-withdrawal total to `1.999999999`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.WdTightWit

open XRPL.Model.Protocol

def rv (nt : NumericType) (a s : Number) : RawVault :=
  { assetsTotal := a, assetsAvailable := a, assetsReserved := Number.zero
  , assetsMaximum := none, numericType := nt, scale := 0
  , sharesTotal := s, lossUnrealized := Number.zero }

def vT : Vault := ⟨rv .fractional ⟨false, 1000000000000000000, -18⟩
  ⟨false, 1000000000000000000, -3⟩, by native_decide, by native_decide⟩
def aT : STAmount := STAmount.unchecked .fractional 1999999999999999 (-30) false
lemma aT_pos : 0 < aT.toRat := by native_decide
def rT : WithdrawResult :=
  (vT.withdraw (.vaultAssets aT) false aT_pos).toOption.getD (WithdrawResult.rejected vT .tecINTERNAL)

def vS : Vault := ⟨rv .fractional ⟨false, 9999999999988968270, -2⟩
  ⟨false, 1844674407370955163, 0⟩, by native_decide, by native_decide⟩
def aS : STAmount := STAmount.unchecked .fractional 5000000000000000 0 false
lemma aS_pos : 0 < aS.toRat := by native_decide
def rS : WithdrawResult :=
  (vS.withdraw (.vaultAssets aS) false aS_pos).toOption.getD (WithdrawResult.rejected vS .tecINTERNAL)

def wOne : STAmount := STAmount.unchecked .int64 1 0 false
lemma wOne_pos : 0 < (WithdrawAmount.vaultShares wOne).amount.toRat := by native_decide

def vU : Vault := ⟨rv .int64 ⟨false, 1000000000000000002, 0⟩
  ⟨false, 2000000000000000000, 0⟩, by native_decide, by native_decide⟩
def rU : WithdrawResult :=
  (vU.withdraw (.vaultShares wOne) false wOne_pos).toOption.getD (WithdrawResult.rejected vU .tecINTERNAL)
def sU : STAmount := STAmount.unchecked .int64 2000000000000000000 0 false

def vH : Vault := ⟨rv .int64 ⟨false, 2999999999999999998, 0⟩
  ⟨false, 2000000000000000000, 0⟩, by native_decide, by native_decide⟩
def rH : WithdrawResult :=
  (vH.withdraw (.vaultShares wOne) false wOne_pos).toOption.getD (WithdrawResult.rejected vH .tecINTERNAL)

def vC : Vault := ⟨rv .fractional ⟨false, 1999999999999999499, -12⟩
  ⟨false, 1000000000000000000, -12⟩, by native_decide, by native_decide⟩
def rC : WithdrawResult :=
  (vC.withdraw (.vaultShares wOne) false wOne_pos).toOption.getD (WithdrawResult.rejected vC .tecINTERNAL)
def sC : STAmount := STAmount.unchecked .int64 1000000 0 false

lemma wOne_canonical : wOne.Canonical :=
  ⟨fun _ => ⟨⟨rfl, rfl, by decide⟩, by decide⟩, fun h => absurd h (by decide)⟩

lemma frac_canonical (m : UInt64) (e : Int) (h1 : 10 ^ 15 ≤ m.toNat) (h2 : m.toNat < 10 ^ 16)
    (h3 : (-96 : ℤ) ≤ e) (h4 : e ≤ 80) :
    (STAmount.unchecked .fractional m e false).Canonical :=
  ⟨fun h => absurd h (by simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]),
    fun _ => ⟨rfl, h1, h2, h3, h4⟩⟩

end XRPL.Model.SingleAssetVault.WdTightWit

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol WdTightWit

/-- Truncation: a withdrawal by assets burns `1 - 10⁻¹⁵` of a share less than the ideal,
the one-share term of `withdraw_sharesBurned` less `10⁻¹⁴` beyond the relative error. -/
lemma Vault.withdraw_sharesBurned_witness :
    ∃ (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (hpos : 0 < assets.toRat)
      (r : WithdrawResult),
      assets.Canonical ∧ v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultAssets assets) waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * sharesε + (1 - 1 / 10 ^ 14) <
        v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat - r.sharesBurned.toRat :=
  ⟨vT, aT, false, aT_pos, rT, frac_canonical _ _ (by decide) (by decide) (by decide) (by decide),
    ⟨⟨false, 1000000000000000000, -18⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, by native_decide⟩

/-- Sharp share overshoot: the burned shares exceed the ideal by `1.0841995·10⁻¹⁸`
relatively, 98.56% of `sharesε`. -/
lemma Vault.withdraw_sharesBurned_sharp_witness :
    ∃ (v : Vault) (assets : STAmount) (waiveUnrealizedLoss : Bool) (hpos : 0 < assets.toRat)
      (r : WithdrawResult),
      assets.Canonical ∧ v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw (.vaultAssets assets) waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat * (10841995 / 10 ^ 25) <
        r.sharesBurned.toRat - v.idealSharesWithdraw waiveUnrealizedLoss assets.toRat :=
  ⟨vS, aS, false, aS_pos, rS, frac_canonical _ _ (by decide) (by decide) (by decide) (by decide),
    ⟨⟨false, 9999999999988968270, -2⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, by native_decide⟩

/-- Payout overshoot: the payout exceeds the burned shares' worth plus the relative error
by all but `10⁻¹⁵` of the half-unit term of `withdraw_payout`. -/
lemma Vault.withdraw_payout_overshoot_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (sharesTotalAmount : STAmount) (r : WithdrawResult),
      0 ≤ r.sharesBurned.toRat ∧ r.sharesBurned.Canonical ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * (1 + depositε) +
          (1 - 1 / 10 ^ 15) * (1 / 2 * (10 : ℚ) ^ r.assets'.exponent) < r.assets'.toRat := by
  have hb : rU.sharesBurned = wOne := by native_decide
  refine ⟨vU, .vaultShares wOne, false, wOne_pos, sU, rU, by rw [hb]; native_decide,
    by rw [hb]; exact wOne_canonical,
    ⟨⟨false, 1000000000000000002, 0⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Rounding shortfall: without the clamp the payout falls short of the burned shares'
worth by the relative error plus all but `10⁻¹⁵` of the half-unit term. -/
lemma Vault.withdraw_payout_round_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (sharesTotalAmount : STAmount) (r : WithdrawResult),
      0 ≤ r.sharesBurned.toRat ∧ r.sharesBurned.Canonical ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
        v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
            (1 - 1 / 10 ^ 15) * max (1 / 2 * (10 : ℚ) ^ r.assets'.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assets'.exponent) <
          v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat := by
  have hb : rH.sharesBurned = wOne := by native_decide
  refine ⟨vH, .vaultShares wOne, false, wOne_pos, sU, rH, by rw [hb]; native_decide,
    by rw [hb]; exact wOne_canonical,
    ⟨⟨false, 2999999999999999998, 0⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, by native_decide, by native_decide,
    STAmount.unchecked .int64 2999999999999999997 0 false, by native_decide, by native_decide⟩

/-- Clamp shortfall: the payout floored onto the post-withdrawal grid falls short of the
burned shares' worth by the relative error plus all but `10⁻⁷` of the grid term. -/
lemma Vault.withdraw_payout_clamp_witness :
    ∃ (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
      (hpos : 0 < amount.amount.toRat) (sharesTotalAmount : STAmount) (r : WithdrawResult),
      0 ≤ r.sharesBurned.toRat ∧ r.sharesBurned.Canonical ∧
      v.WithdrawNavExact waiveUnrealizedLoss ∧
      v.withdraw amount waiveUnrealizedLoss hpos = .ok r ∧ r.error = none ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r.sharesBurned.operator_eq sharesTotalAmount = false ∧
      ∃ atr' : STAmount,
        STAmount.ofNumber v.numericType r.vault'.assetsTotal .to_nearest = .ok atr' ∧
        v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat * depositε +
            (1 - 1 / 10 ^ 7) * max (1 / 2 * (10 : ℚ) ^ r.assets'.exponent)
              ((10 : ℚ) ^ atr'.exponent - 1 / 2 * (10 : ℚ) ^ r.assets'.exponent) <
          v.idealAssetsWithdraw waiveUnrealizedLoss r.sharesBurned.toRat - r.assets'.toRat := by
  have hb : rC.sharesBurned = wOne := by native_decide
  refine ⟨vC, .vaultShares wOne, false, wOne_pos, sC, rC, by rw [hb]; native_decide,
    by rw [hb]; exact wOne_canonical,
    ⟨⟨false, 1999999999999999499, -12⟩, by native_decide, by native_decide⟩,
    by native_decide, by native_decide, by native_decide, by native_decide,
    STAmount.unchecked .fractional 1999998000000000 (-9) false, by native_decide,
    by native_decide⟩

end XRPL.Model.SingleAssetVault
