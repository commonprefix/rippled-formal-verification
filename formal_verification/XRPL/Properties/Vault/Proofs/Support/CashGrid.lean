import XRPL.Properties.Lending.Common.GridRounding
import XRPL.Properties.Lending.Loan.Common.PayUnits

/-! # Cash updates keep AssetsAvailable stored exactly and on the base grid

AssetsAvailable is a whole number of base units, so a cash update by a whole number of base units, rounded to the
asset, writes one again, and the asset stores it exactly. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol XRPL.Model.Lending

/-- AssetsAvailable is a normalized whole number of base units. -/
lemma Vault.assetsAvailable_onGrid (v : Vault) : Number.OnGrid v.baseExponent v.assetsAvailable :=
  ⟨v.wf.assetsAvailable_norm, v.exact.assetsAvailable_onGrid⟩

/-- The operator form of the grid clause of `RawVault.Valid`, from a nonnegative whole number of base units. -/
lemma Vault.onGrid_clause (v : Vault) (x : Number) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hk : ∃ k : ℤ, x.toRat = k * 10 ^ v.baseExponent) :
    x = Number.zero ∨ x.mantissa_.toNat % 10 ^ (v.numericType.baseExponent v.scale - x.exponent_).toNat = 0 :=
  Or.inr ((Number.mod_grid_iff _ _ (Number.negative_false_of_nonneg _ hx h0)).mpr hk)

/-- Rounding AssetsAvailable to the asset keeps it, so the result is stored exactly and on the base grid. -/
lemma Vault.round_cash_valid (v : Vault) (aa' : Number)
    (h : STAmount.roundToNumericType v.numericType v.assetsAvailable .to_nearest = .ok aa') :
    STAmount.isRounded v.numericType aa' = false ∧ ∃ k : ℤ, aa'.toRat = k * 10 ^ v.baseExponent := by
  have hv := STAmount.roundToNumericType_of_isRounded_false _ _ _ v.wf.assetsAvailable_norm
    v.valid.assetsAvailable_representable h
  have heq : aa' = v.assetsAvailable :=
    (STAmount.roundToNumericType_isNormalized _ _ _ _ _ h).toRat_inj v.wf.assetsAvailable_norm hv
  rw [heq]
  exact ⟨v.valid.assetsAvailable_representable, v.exact.assetsAvailable_onGrid⟩

/-- A clamped amount of the asset is a whole number of base units. -/
lemma Vault.clamp_grid (v : Vault) (A : Number) (delta result : STAmount) (hd : delta.CanonicalOrZero)
    (h : clampToSumExponent A delta v.baseExponent = .ok result) :
    ∃ k : ℤ, result.toRat = (k : ℚ) * 10 ^ v.baseExponent := by
  obtain ⟨k, hk⟩ := clampToSumExponent_units A delta result v.baseExponent hd v.baseExponent_range.1
    v.baseExponent_range.2 (fun _ => v.baseExponent_bounds.2.1) h
  exact ⟨k, by rw [hk]; push_cast; rfl⟩

/-- A balance update by a whole number of base units of cash writes AssetsAvailable stored exactly and on the base
grid. -/
lemma Vault.adjustBalances_cash_valid (v : Vault) (c : PoolBalanceChange) (raw : RawVault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hc : Number.OnGrid v.baseExponent c.cash) (h : (v.adjustBalances c).run = .ok (.ok raw))
    (hnn : 0 ≤ raw.assetsAvailable.toRat) :
    STAmount.isRounded v.numericType raw.assetsAvailable = false ∧
      ∃ k : ℤ, raw.assetsAvailable.toRat = k * 10 ^ v.baseExponent := by
  obtain ⟨hs, -⟩ := Vault.adjustBalances_ok_inv v c raw h
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  obtain ⟨aa, haa, hround⟩ := hs.cash
  exact ⟨STAmount.isRounded_eq_false_of_rounded _ _ _ hmax hround hnn,
    (STAmount.roundToNumericType_onGrid_none _ _ _ _ _ (Number.OnGrid.add (Vault.assetsAvailable_onGrid v) hc hsr haa)
      (by omega) (fun hi => v.baseExponent_bounds.2.2 hi) hround).2⟩

/-- A cash update by a whole number of base units writes AssetsAvailable stored exactly and on the base grid. -/
lemma Vault.adjustAssetsAndShares_cash_valid (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hc : assets.CanonicalOrZero) (hk : ∃ k : ℤ, assets.toRat = k * 10 ^ v.baseExponent)
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.ok raw)) (hnn : 0 ≤ raw.assetsAvailable.toRat) :
    STAmount.isRounded v.numericType raw.assetsAvailable = false ∧
      ∃ k : ℤ, raw.assetsAvailable.toRat = k * 10 ^ v.baseExponent := by
  obtain ⟨assetsNum, _, s, aa', _, hnum, -, -, hs, haa, rfl⟩ := Vault.adjustAssetsAndShares_ok_reduces v _ _ raw h
  obtain ⟨hnv, hnorm⟩ := hc.toNumber_exact assetsNum hnum
  obtain ⟨k, hk⟩ := hk
  obtain ⟨hb, hsr⟩ := Vault.baseExponent_grid v
  exact ⟨STAmount.isRounded_eq_false_of_rounded _ _ _ hmax haa hnn,
    (STAmount.roundToNumericType_onGrid_none _ _ _ _ _
      (Number.OnGrid.add (Vault.assetsAvailable_onGrid v) ⟨hnorm, k, by rw [hnv, hk]⟩ hsr hs) (by omega)
      (fun hi => v.baseExponent_bounds.2.2 hi) haa).2⟩

end XRPL.Model.SingleAssetVault
