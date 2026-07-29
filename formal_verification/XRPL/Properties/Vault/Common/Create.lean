import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultCreate
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas

/-! # `Vault.create` lawfulness proof

The proof backing the `Vault.create_lawful` headline. A freshly created vault has
every `Number` field at `Number.zero`, so `WF` follows from `Number.zero` being
normalized and the two scale hypotheses, and every `Valid` clause is arithmetic
on zeros (the `assetsMaximum` clauses use the creation positivity hypothesis). -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

theorem Vault.create_lawful_proof (nt : NumericType) (scale : UInt8)
    (assetsMaximum : Option Number)
    (hmax_norm : ∀ m ∈ assetsMaximum, m.isNormalized)
    (hmax_pos : ∀ m ∈ assetsMaximum, 0 < m.toRat)
    (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) :
    (Vault.create nt scale assetsMaximum).Lawful := by
  have hz : Number.zero.isNormalized := Or.inl rfl
  have hAT : (Vault.create nt scale assetsMaximum).toExact.assetsTotal = 0 := by
    simp only [Vault.toExact, Vault.create, Number.toRat_zero]
  have hAV : (Vault.create nt scale assetsMaximum).toExact.assetsAvailable = 0 := by
    simp only [Vault.toExact, Vault.create, Number.toRat_zero]
  have hST : (Vault.create nt scale assetsMaximum).toExact.sharesTotal = 0 := by
    simp only [Vault.toExact, Vault.create, Number.toRat_zero, Rat.num_zero, Int.toNat_zero]
  have hLU : (Vault.create nt scale assetsMaximum).toExact.lossUnrealized = 0 := by
    simp only [Vault.toExact, Vault.create, Number.toRat_zero]
  have hAM : (Vault.create nt scale assetsMaximum).toExact.assetsMaximum
      = assetsMaximum.map Number.toRat := rfl
  refine ⟨⟨hz, hz, ?_, hz, hz, ?_, ?_, hscale_int, hscale_le⟩, ?_⟩
  · intro m hm; exact hmax_norm m hm
  · simp only [Vault.create, Number.toRat_zero, le_refl]
  · simp only [Vault.create, Number.toRat_zero]; rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAT]
    · rw [hAV]
    · rw [hAV, hAT]
    · rw [hAM]; intro m hm; rw [Option.mem_map] at hm
      obtain ⟨n, hn, rfl⟩ := hm; exact hmax_pos n hn
    · rw [hST, hAT, hAV]; intro _; exact ⟨rfl, rfl⟩
    · rw [hAM, hAT]; intro m hm; rw [Option.mem_map] at hm
      obtain ⟨n, hn, rfl⟩ := hm; exact le_of_lt (hmax_pos n hn)
    · rw [hLU]
    · rw [hLU, hAT, hAV]; norm_num
    · rw [hAT, hLU]; norm_num

end XRPL.Model.SingleAssetVault
