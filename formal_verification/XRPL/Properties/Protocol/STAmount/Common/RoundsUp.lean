import XRPL.Properties.Protocol.Number.Common.Closest.NearestDefs
import XRPL.Properties.Protocol.Number.Common.Rounding.SuccessCondition

/-! # When a rounding step adds one

Every rounding in the model keeps some digits `q`, drops a fraction `f` and then adds one to `q` or not.
`RoundsUp` says when it adds one, and `Guard.round_bool_iff` shows the guard decides exactly that. -/

namespace XRPL.Model.Protocol

/-- Rounding in the mode adds one to the kept digits `q`, given the sign and the dropped fraction `f`. -/
def RoundsUp (mode : rounding_mode) (neg : Bool) (q : ℤ) (f : ℚ) : Prop :=
  match mode with
  | .to_nearest => 1 / 2 < f ∨ (f = 1 / 2 ∧ q % 2 = 1)
  | .towards_zero => False
  | .downward => neg = true ∧ 0 < f
  | .upward => neg = false ∧ 0 < f

/-- Nothing is added when no fraction was dropped. -/
lemma not_roundsUp_zero (mode : rounding_mode) (neg : Bool) (q : ℤ) : ¬ RoundsUp mode neg q 0 := by
  cases mode <;> simp [RoundsUp]

/-- In `to_nearest` and `towards_zero` the sign does not change whether one is added. -/
lemma roundsUp_sign_irrelevant (mode : rounding_mode) (neg neg' : Bool) (q : ℤ) (f : ℚ)
    (hmode : mode = .to_nearest ∨ mode = .towards_zero) : RoundsUp mode neg q f ↔ RoundsUp mode neg' q f := by
  rcases hmode with rfl | rfl <;> exact Iff.rfl

/-- The guard adds one exactly when `RoundsUp` holds for the fraction it holds. -/
lemma Guard.round_bool_iff {g : Guard} {f : ℚ} (hg : represents g f) (mode : rounding_mode) (odd : Bool)
    (q : ℤ) (hodd : odd = true ↔ q % 2 = 1) :
    (g.round mode == 1 || (g.round mode == 0 && odd)) = true ↔ RoundsUp mode g.sbit_ q f := by
  cases mode with
  | to_nearest =>
    obtain ⟨-, h1, h0⟩ := Guard.roundsLike_of_represents hg
    rw [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, h1, h0, hodd]
    rfl
  | towards_zero =>
    have hr := Guard.round_directed_eq g .towards_zero (by decide)
    dsimp only at hr
    rw [hr]
    show _ ↔ False
    split_ifs <;> simp
  | downward =>
    have h1 := Guard.round_downward_eq_one_iff hg
    have h0 : (g.round .downward == 0) = false := by
      rw [Guard.round_directed_eq g .downward (by decide)]
      dsimp only
      split_ifs <;> rfl
    rw [h0, Bool.false_and, Bool.or_false, h1]
    rfl
  | upward =>
    have h1 := Guard.round_upward_eq_one_iff hg
    have h0 : (g.round .upward == 0) = false := by
      rw [Guard.round_directed_eq g .upward (by decide)]
      dsimp only
      split_ifs <;> rfl
    rw [h0, Bool.false_and, Bool.or_false, h1]
    rfl

/-- The odd test on a `UInt64` mantissa. -/
lemma UInt64.mod_two_beq_one_iff (m : UInt64) : (m % 2 == 1) = true ↔ (m.toNat : ℤ) % 2 = 1 := by
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mod]
  show m.toNat % 2 = 1 ↔ _
  omega

/-- The odd test on an `Int64` that is not negative. -/
lemma Int64.mod_two_beq_one_iff (d : Int64) (h0 : 0 ≤ d.toInt) : (d % 2 == 1) = true ↔ d.toInt % 2 = 1 := by
  rw [beq_iff_eq, ← Int64.toInt_inj, Int64.toInt_mod, Int.tmod_eq_emod_of_nonneg h0]
  rfl

end XRPL.Model.Protocol
