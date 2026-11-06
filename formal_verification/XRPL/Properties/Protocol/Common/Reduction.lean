/-! # Stepping through `Except` pipelines

The `Except` identities the exit proofs use to step through a `do` block, one
bind at a time. All of them hold by definition. -/

namespace XRPL.Model.Protocol

/-- A successful step passes its value to the rest of the block. -/
theorem ok_bind {ε α β} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- A thrown error skips the rest of the block. -/
theorem err_bind {ε α β} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- `return x` in an `Except` block is `.ok x`. -/
theorem pure_eq {ε α} (a : α) : (pure a : Except ε α) = .ok a := rfl

/-- `.pure x` in an `Except` block is `.ok x`. -/
theorem except_pure_eq {ε α} (a : α) : (Except.pure a : Except ε α) = .ok a := rfl

/-- `throw e` in an `Except` block is `.error e`. -/
theorem throw_eq {ε α} (e : ε) : (throw e : Except ε α) = .error e := rfl

/-- A `try` around a successful step never runs the `catch` handler. -/
theorem tryCatch_ok {ε α} (a : α) (h : ε → Except ε α) :
    (tryCatch (Except.ok a : Except ε α) h) = .ok a := rfl

/-- A `try` around a thrown error runs the `catch` handler on it. -/
theorem tryCatch_error {ε α} (e : ε) (h : ε → Except ε α) :
    (tryCatch (Except.error e) h) = h e := rfl

/-- Peel one bind off a successful block: the first step succeeded, and the rest
of the block reached the same result. -/
theorem bind_ok_peel {ε α β} (x : Except ε α) (f : α → Except ε β) (r : β)
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => rw [hx, err_bind] at h; exact absurd h (by simp)
  | ok a => rw [hx, ok_bind] at h; exact ⟨a, rfl, h⟩

/-- A block fails with `e` only when its first step or the rest of it does. -/
theorem bind_ne_error {ε α β} {x : Except ε α} {f : α → Except ε β} {e : ε} (hx : x ≠ .error e)
    (hf : ∀ a, f a ≠ .error e) : (x >>= f) ≠ .error e := by
  cases x with
  | error e' =>
    rw [err_bind]
    intro h
    exact hx (by cases h; rfl)
  | ok a => rw [ok_bind]; exact hf a

/-- An `if` fails with `e` only when one of its branches does. -/
theorem ite_ne_error {ε α} {c : Prop} [Decidable c] {a b : Except ε α} {e : ε} (ha : a ≠ .error e)
    (hb : b ≠ .error e) : (if c then a else b) ≠ .error e := by
  split
  · exact ha
  · exact hb

end XRPL.Model.Protocol
