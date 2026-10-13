import XRPL.Properties.Vault.Common.VaultDecidable
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Counterexamples for the statements in `Unprovable.lean`

* A reachable off-grid vault: create a fractional scale-15 vault, deposit
  `1.234567890123456`, then deposit `100`. The second charge `99.99999999999994` is
  clamped to the post-deposit grid, but the sum keeps the old total's `10⁻¹⁵` digit, so
  the stored total `101.234567890123396` needs 18 significant digits.
* A lawful int64 vault holding `9223372036854775806` with `3` shares: redeeming all three
  shares prices one unit above `assetsAvailable`, so the funds guard rejects the full
  exit with `tecINSUFFICIENT_FUNDS`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.SingleAssetVault.CatHI

open XRPL.Model.Protocol

lemma hmax_norm_none : ∀ m ∈ (none : Option Number), m.isNormalized := by simp
lemma hmax_pos_none : ∀ m ∈ (none : Option Number), 0 < m.toRat := by simp
lemma hscale_int_frac : NumericType.fractional.isIntegral = true → (15 : UInt8) = 0 := by
  intro h; exact absurd h (by decide)
lemma hscale_le_15 : (15 : UInt8).toNat ≤ 18 := by decide

/-- The freshly created fractional scale-15 vault. -/
def rv0 : Vault :=
  Vault.create_lawful .fractional 15 none hmax_norm_none hmax_pos_none hscale_int_frac hscale_le_15

/-- The first deposit, `1.234567890123456`. -/
def ra1 : STAmount := STAmount.unchecked .fractional 1234567890123456 (-15) false

lemma ra1_pos : 0 < ra1.toRat := by native_decide

lemma ra1_canonical : ra1.Canonical :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, by decide, by decide, by decide, by decide⟩⟩

def rr1 : DepositResult :=
  (rv0.deposit ra1 false ra1_pos).toOption.getD (DepositResult.rejected rv0 .tecINTERNAL)

/-- The second deposit, `100`. -/
def ra2 : STAmount := STAmount.unchecked .fractional 1000000000000000 (-13) false

lemma ra2_pos : 0 < ra2.toRat := by native_decide

lemma ra2_canonical : ra2.Canonical :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, by decide, by decide, by decide, by decide⟩⟩

def rr2 : DepositResult :=
  (rr1.vault'.deposit ra2 false ra2_pos).toOption.getD
    (DepositResult.rejected rr1.vault' .tecINTERNAL)

/-- An int64 vault holding `9223372036854775806`, all of it available, with `3` shares. -/
def ce : RawVault :=
  { assetsTotal := ⟨false, 9223372036854775806, 0⟩
  , assetsAvailable := ⟨false, 9223372036854775806, 0⟩
  , assetsReserved := Number.zero, assetsMaximum := none
  , numericType := .int64, scale := 0
  , sharesTotal := ⟨false, 3000000000000000000, -18⟩
  , lossUnrealized := Number.zero }

def ceL : Vault := ⟨ce, by native_decide, by native_decide⟩

/-- The share total as an amount, computed by the model. -/
def ceShares : STAmount :=
  (STAmount.ofNumber .int64 ceL.sharesTotal .to_nearest).toOption.getD (STAmount.zero .int64)

lemma ceShares_pos : 0 < ceShares.toRat := by native_decide

/-- The full redemption's result, computed by the model. -/
def ceR : WithdrawResult :=
  (ceL.withdraw (.vaultShares ceShares) false ceShares_pos).toOption.getD
    (WithdrawResult.rejected ceL .tecINTERNAL)

end XRPL.Model.SingleAssetVault.CatHI

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol CatHI

set_option maxRecDepth 10000

lemma Vault.reachable_offgrid_witness : ∃ v : Vault, Vault.Reachable v ∧ v.assetsRounded := by
  have h0 : Vault.Reachable rv0 := Vault.Reachable.create _ _ _ _ _ _ _
  have h1 : Vault.Reachable rr1.vault' :=
    Vault.Reachable.deposit rv0 ra1 false rr1 h0 ra1_pos (by native_decide) ra1_canonical
      (by native_decide)
  have h2 : Vault.Reachable rr2.vault' :=
    Vault.Reachable.deposit rr1.vault' ra2 false rr2 h1 ra2_pos (by native_decide) ra2_canonical
      (by native_decide)
  exact ⟨rr2.vault', h2, by unfold Vault.assetsRounded; native_decide⟩

lemma Vault.full_exit_rejected_witness :
    ∃ (v : Vault) (sharesTotalAmount : STAmount) (hpos : 0 < sharesTotalAmount.toRat)
      (r : WithdrawResult),
      v.toExact.assetsTotal = v.toExact.assetsAvailable ∧
      STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      v.withdraw (.vaultShares sharesTotalAmount) false hpos = .ok r ∧
      r.error = some .tecINSUFFICIENT_FUNDS :=
  ⟨ceL, ceShares, ceShares_pos, ceR, rfl, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.SingleAssetVault
