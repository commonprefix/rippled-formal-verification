import XRPL.Properties.Vault.Proofs.Reachable
import XRPL.Properties.Vault.Proofs.DepositExits
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent

/-! # Exponent of an integral amount -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- An integral `numberExponent` is never above the larger of the given exponent and zero: an
integral amount is stored at offset zero. -/
lemma numberExponent_integral_le (n : Number) (exponent : Int) (nt : NumericType) (e : Int)
    (hnt : nt.isIntegral = true) (hok : numberExponent n exponent nt = .ok e) : e ≤ max exponent 0 := by
  unfold numberExponent at hok
  by_cases hz : n.operator_eq Number.zero = true
  · simp only [hz, if_true, pure, Except.pure, Except.ok.injEq] at hok
    omega
  simp only [hz, Bool.false_eq_true, if_false] at hok
  cases ha : STAmount.ofNumber nt n .downward with
  | error err => rw [ha] at hok; simp [bind, Except.bind, pure, Except.pure] at hok
  | ok a =>
    rw [ha] at hok
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hok
    have hoff : a.mOffset = 0 := (STAmount.ofNumber_integral_canonical nt n .downward a hnt ha).1.offset_zero
    have hmax : max exponent a.exponent = e := hok
    rw [show a.exponent = 0 from hoff] at hmax
    omega

end XRPL.Model.SingleAssetVault
