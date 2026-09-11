import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

structure BrokerVault where
  vault : Vault
  broker : LoanBroker

structure LoanVault where
  loan : Loan
  vault : Vault

structure LendingState where
  vault : Vault
  broker : LoanBroker
  loan : Loan

-- The result of a lending operation (the new ledger state, or the TER that rejected it)
inductive LoanResult (α : Type) where
  | ok (state : α)
  | rejected (ter : TER)

end XRPL.Model.Lending
