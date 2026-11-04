import XRPL.Properties.Lending.Loan.Common.PayUnits

/-! # The LossUnrealized a payment of an impaired loan books -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

open private Loan.settlePayment from XRPL.Model.Lending.Loan.LoanPay

variable (loan : Loan) (v : Vault) (amount : Number) (now : UInt32) (paymentType : LoanPaymentType)
  (r : LoanWithAmounts Vault)

/-- A payment of an impaired loan books LossUnrealized − PrincipalOutstanding as the new LossUnrealized. -/
lemma Loan.payment_unimpairs_sum (himp : loan.isImpaired = true)
    (hok : (loan.pay v paymentType amount now).run = .ok (.ok r)) :
    v.lossUnrealized.operator_add loan.principalOutstanding.operator_neg .to_nearest = .ok r.pool'.lossUnrealized := by
  obtain ⟨p, hp, hs⟩ := Loan.pay_ok loan v paymentType amount now r hok
  obtain ⟨-, hu, -, -, -⟩ := Loan.payInstalments_ok loan v paymentType amount now p hp
  rw [Loan.unimpairIfImpaired_impaired loan v himp] at hu
  have hadj1 : AssetPool.adjustBalances v { loss := loan.principalOutstanding.operator_neg } = .ok (.ok p.pool) := by
    split at hu
    · cases hu
    · cases hu
    · rename_i v1 hv1
      obtain rfl : v1 = p.pool := by injection hu with hu; injection hu with hu; injection hu
      exact hv1
  have hl1 := (Vault.poolAdjust_sums v p.pool _ hadj1).1.loss
  obtain ⟨_, _, _, _, _, raw, _, -, hadj2, hv2, -, -, -, -⟩ := UnsettledPayment.settle_ok p r hs
  have hpool2 := Vault.poolAdjust_ok p.pool _ raw r.pool' hadj2 hv2
  have hl2 := (Vault.poolAdjust_sums p.pool r.pool' _ hpool2).1.loss
  simp only [UnsettledPayment.change, Number.operator_add_zero_right] at hl2
  obtain h2 := Except.ok.inj hl2
  rw [← h2]
  exact hl1

end XRPL.Model.Lending
