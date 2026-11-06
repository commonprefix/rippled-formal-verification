import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Protocol.Common.Reduction

/-! # Reading `roundedDepositAmount`

`roundedDepositAmount` in closed form once the vault total and the clamp are known, and the facts a successful
rounding gives back. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Clean `if`-form of `roundedDepositAmount` when the vault total and its clamp succeed. -/
lemma roundedDepositAmount_ok (v : Vault) (amountDeposit ra' : STAmount) (assetsTotal : Number)
    (ht : v.assetsTotal = .ok assetsTotal)
    (hr : clampToSumExponent assetsTotal amountDeposit v.baseExponent = .ok ra') :
    (v.roundedDepositAmount amountDeposit).run =
      (if ra'.isZero then .ok (.error .tecPRECISION_LOSS) else .ok (.ok ra')) := by
  simp only [Vault.roundedDepositAmount, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.pure,
    ExceptT.bindCont, bind, pure, Except.bind, Except.pure, Except.map, Functor.map, throw, throwThe,
    MonadExceptOf.throw, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, ht, hr]
  split <;> rfl

/-- `roundedDepositAmount` propagates a `clampToSumExponent` error. -/
private lemma roundedDepositAmount_err (v : Vault) (amountDeposit : STAmount) (assetsTotal : Number) (e : Error)
    (ht : v.assetsTotal = .ok assetsTotal)
    (hr : clampToSumExponent assetsTotal amountDeposit v.baseExponent = .error e) :
    (v.roundedDepositAmount amountDeposit).run = .error e := by
  simp only [Vault.roundedDepositAmount, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont,
    bind, Except.bind, Except.map, Functor.map, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, ht, hr]

/-- A successful rounding means clamping to the vault total produced exactly that nonzero amount. -/
lemma roundedDepositAmount_rounded (v : Vault) (amountDeposit ra : STAmount)
    (h : (v.roundedDepositAmount amountDeposit).run = .ok (.ok ra)) :
    ∃ assetsTotal, v.assetsTotal = .ok assetsTotal ∧
      clampToSumExponent assetsTotal amountDeposit v.baseExponent = .ok ra ∧ ra.isZero = false := by
  cases ht : v.assetsTotal with
  | error e =>
    simp only [Vault.roundedDepositAmount, ExceptT.run, ExceptT.bind, ExceptT.mk, ExceptT.lift,
      bind, Except.bind, Except.map, Functor.map, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
      ht] at h
    exact absurd h (by simp)
  | ok assetsTotal =>
    cases hr : clampToSumExponent assetsTotal amountDeposit v.baseExponent with
    | error e =>
      rw [roundedDepositAmount_err v amountDeposit assetsTotal e ht hr] at h; exact absurd h (by simp)
    | ok ra' =>
      rw [roundedDepositAmount_ok v amountDeposit ra' assetsTotal ht hr] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hz
        rw [Except.ok.injEq, Except.ok.injEq] at h
        subst h
        exact ⟨assetsTotal, rfl, hr, by simpa using hz⟩

end XRPL.Model.SingleAssetVault
