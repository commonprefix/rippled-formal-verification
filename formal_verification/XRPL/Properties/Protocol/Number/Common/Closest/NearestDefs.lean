import XRPL.Properties.Protocol.Number.Common.Rounding.Guard
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.Basic

/-! # Rounding to the nearest Number -/

namespace XRPL.Model.Protocol

/-- `result` is a Number nearest to `truth`: no normalized Number lies strictly closer. -/
def Number.RoundsToNearest (result : Number) (truth : ℚ) : Prop :=
  ∀ m : Number, m.isNormalized → |result.toRat - truth| ≤ |m.toRat - truth|

/-- The guard rounds the dropped fraction `f` to nearest the way exact rounding would. It is empty exactly when
`f = 0`, rounds up exactly when `f > 1/2` and reports a tie exactly when `f = 1/2`. -/
def Guard.RoundsLike (g : Guard) (f : ℚ) : Prop :=
  (g.empty = true ↔ f = 0) ∧ (g.round .to_nearest = 1 ↔ 1 / 2 < f) ∧ (g.round .to_nearest = 0 ↔ f = 1 / 2)

/-- A guard that holds the exact dropped fraction rounds it like exact rounding. -/
lemma Guard.roundsLike_of_represents {g : Guard} {f : ℚ} (hg : represents g f) : g.RoundsLike f := by
  by_cases he : g.empty = true
  · have hf0 : f = 0 := represents_empty_eq_zero he hg
    have hr : g.round .to_nearest = -2 := by unfold Guard.round; rw [if_pos he]
    unfold Guard.RoundsLike
    rw [hf0, hr]
    exact ⟨⟨fun _ => rfl, fun _ => he⟩, ⟨fun h => absurd h (by decide), fun h => by norm_num at h⟩,
      ⟨fun h => absurd h (by decide), fun h => by norm_num at h⟩⟩
  · have hc := round_correct he hg
    have hf_pos : 0 < f := by
      obtain ⟨x, hx_nn, _, hf, hxbit, _⟩ := hg
      have h16 : (0 : ℚ) < 10 ^ 16 := by positivity
      have hne : g.digits_ ≠ 0 ∨ g.xbit_ = true := by
        by_contra h
        push Not at h
        apply he
        unfold Guard.empty Guard.unrecoverable
        simp [h.1, h.2]
      rcases hne with hd | hx
      · have hdec : (0 : ℚ) < decimalValue g.digits_ := by exact_mod_cast decimalValue_pos_of_ne_zero _ hd
        rw [hf]
        exact add_pos_of_pos_of_nonneg (div_pos hdec h16) hx_nn
      · rw [hf]
        exact add_pos_of_nonneg_of_pos (div_nonneg (Nat.cast_nonneg _) h16.le) (hxbit.mp hx)
    exact ⟨⟨fun h => absurd h he, fun h => absurd h hf_pos.ne'⟩, hc.1, hc.2.2⟩

end XRPL.Model.Protocol
