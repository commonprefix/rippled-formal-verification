import XRPL.Properties.Lending.Ledger.Common.AssetFlowDefs

/-! # Sums over a sequence of transactions

`l.runSum f txs` adds up `f l₀ tx` over the transactions `txs` applied in order from `l`, each read on the ledger
`l₀` it runs on. A ledger quantity that every step moves by `f` ends at its start value plus that sum. -/

namespace XRPL.Model.Lending

/-- The sum of `f` over the transactions `txs` applied in order from `l`. Once one fails, the ones after it add
nothing. -/
def LendingLedger.runSum (f : LendingLedger → LendingTx → ℚ) (l : LendingLedger) : List LendingTx → ℚ
  | [] => 0
  | tx :: txs =>
    f l tx +
      match (l.apply tx).run with
      | .ok (.ok l') => l'.runSum f txs
      | _ => 0

/-- A sum over a sequence grows by each step's amount. -/
lemma LendingLedger.runSum_snoc {f : LendingLedger → LendingTx → ℚ} {start l l' : LendingLedger}
    {txs : List LendingTx} {tx : LendingTx}
    (h : LendingLedger.Reaches start txs l) (hok : (l.apply tx).run = .ok (.ok l')) :
    start.runSum f (txs ++ [tx]) = start.runSum f txs + f l tx := by
  induction txs generalizing start with
  | nil =>
    obtain rfl := h.nil_inv
    simp only [List.nil_append, LendingLedger.runSum, hok, add_zero]
    ring
  | cons t ts ih =>
    obtain ⟨l₁, h₁, hr₁⟩ := LendingLedger.Reaches.cons_inv h
    simp only [List.cons_append, LendingLedger.runSum, h₁]
    rw [ih hr₁]
    ring

/-- The sum of a difference is the difference of the sums. -/
lemma LendingLedger.runSum_sub (f g : LendingLedger → LendingTx → ℚ) (l : LendingLedger) (txs : List LendingTx) :
    l.runSum (fun l₀ tx => f l₀ tx - g l₀ tx) txs = l.runSum f txs - l.runSum g txs := by
  induction txs generalizing l with
  | nil => simp [LendingLedger.runSum]
  | cons tx txs ih =>
    simp only [LendingLedger.runSum]
    split
    · rw [ih]; ring
    · ring

/-- The sum of two amounts is the sum of their sums. -/
lemma LendingLedger.runSum_add (f g : LendingLedger → LendingTx → ℚ) (l : LendingLedger) (txs : List LendingTx) :
    l.runSum (fun l₀ tx => f l₀ tx + g l₀ tx) txs = l.runSum f txs + l.runSum g txs := by
  induction txs generalizing l with
  | nil => simp [LendingLedger.runSum]
  | cons tx txs ih =>
    simp only [LendingLedger.runSum]
    split
    · rw [ih]; ring
    · ring

/-- Two amounts that agree on every successful step of a sequence have the same sum. -/
lemma LendingLedger.runSum_congr {f g : LendingLedger → LendingTx → ℚ} {start l : LendingLedger}
    {txs : List LendingTx} (hrun : LendingLedger.Reaches start txs l)
    (hfg : ∀ (pre : List LendingTx) (l₁ : LendingLedger) (tx : LendingTx) (l₂ : LendingLedger),
      pre ++ [tx] <+: txs → LendingLedger.Reaches start pre l₁ → (l₁.apply tx).run = .ok (.ok l₂) →
      f l₁ tx = g l₁ tx) :
    start.runSum f txs = start.runSum g txs := by
  induction hrun with
  | refl => rfl
  | @step txs₀ l₀ l₁ tx hprev hok ih =>
    rw [LendingLedger.runSum_snoc hprev hok, LendingLedger.runSum_snoc hprev hok,
      ih (fun pre l₂ t l₃ hp hr ha => hfg pre l₂ t l₃ (hp.trans (List.prefix_append _ _)) hr ha),
      hfg txs₀ l₀ tx l₁ (List.prefix_refl _) hprev hok]

/-- Every ledger a sequence passes through from a reachable ledger is reachable. -/
lemma LendingLedger.Reaches.reachable {start l : LendingLedger} {txs : List LendingTx} (hr : start.Reachable)
    (hrun : LendingLedger.Reaches start txs l) : l.Reachable := by
  induction hrun with
  | refl => exact hr
  | step tx _ hok ih => exact ih.apply hok

/-- A ledger quantity `F` that each step moves by `d` ends at its start value plus the sum of `d`. `P` - the steps
on which the step identity holds, checked on every step of the sequence -/
lemma LendingLedger.Reaches.runSum_eq {F : LendingLedger → ℚ} {d : LendingLedger → LendingTx → ℚ}
    {P : LendingLedger → LendingTx → LendingLedger → Prop} {start l : LendingLedger} {txs : List LendingTx}
    (hstep : ∀ (l₁ : LendingLedger) (tx : LendingTx) (l₂ : LendingLedger), l₁.Reachable →
      (l₁.apply tx).run = .ok (.ok l₂) → P l₁ tx l₂ → F l₂ = F l₁ + d l₁ tx)
    (hr : start.Reachable) (hrun : LendingLedger.Reaches start txs l)
    (hP : ∀ (pre : List LendingTx) (l₁ : LendingLedger) (tx : LendingTx) (l₂ : LendingLedger),
      pre ++ [tx] <+: txs → LendingLedger.Reaches start pre l₁ → (l₁.apply tx).run = .ok (.ok l₂) →
      P l₁ tx l₂) :
    F l = F start + start.runSum d txs := by
  induction hrun with
  | refl => simp [LendingLedger.runSum]
  | @step txs₀ l₀ l₁ tx hprev hok ih =>
    rw [LendingLedger.runSum_snoc hprev hok,
      hstep l₀ tx l₁ (hprev.reachable hr) hok (hP txs₀ l₀ tx l₁ (List.prefix_refl _) hprev hok),
      ih (fun pre l₂ t l₃ hp hr' ha => hP pre l₂ t l₃ (hp.trans (List.prefix_append _ _)) hr' ha)]
    ring

end XRPL.Model.Lending
