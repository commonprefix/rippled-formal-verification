import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.Create
import XRPL.Properties.Vault.Common.Unchanged
import XRPL.Properties.Vault.Common.LawfulSupport
import XRPL.Properties.Vault.Common.Preservation
import XRPL.Properties.Vault.VaultBurn
import XRPL.Model.Vault.VaultCreate
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultDelete
import XRPL.Model.Vault.VaultSet

/-! # Every vault operation preserves lawfulness

In each preservation theorem `hok` states the operation ran without a throw. The
result may still carry a TER, and a rejected operation returns the starting vault
unchanged.

The three mutating operations additionally hypothesize the reachability
invariants of the vault-only model (`lossUnrealized = 0`, and record-level
`assetsAvailable = assetsTotal`: every vault operation writes both asset fields
with the identical update, and lending is out of scope). Canonical-storage and sign facts are hypothesized only on the
user-supplied inputs (`amount.Canonical` and nonnegativity for a deposit,
`assets.Canonical` for a clawback, the burned-share shape for a withdrawal); the
corresponding facts about the amounts the run computes are derived. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

theorem Vault.create_lawful (nt : NumericType) (scale : UInt8)
    (assetsMaximum : Option Number)
    (hmax_norm : ∀ m ∈ assetsMaximum, m.isNormalized) -- If assetsMaximum is present, it is normalized
    (hmax_pos : ∀ m ∈ assetsMaximum, 0 < m.toRat) -- If assetsMaximum is present, it is positive
    (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) : -- If vault holds an integral type, scale must be 0, otherwise it has to be <= 18
    (Vault.create nt scale assetsMaximum).Lawful :=
  Vault.create_lawful_proof nt scale assetsMaximum hmax_norm hmax_pos hscale_int hscale_le

variable (v : Vault)

theorem Vault.deposit_lawful (amount : STAmount) (isDonation : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    -- no unrealized loss: with lossUnrealized equal to the stored gap exactly,
    -- the two independent additions can shrink the gap and break Valid, so
    -- preservation only holds on the zero-loss state
    (hL : v.toExact.lossUnrealized = 0)
    -- vault-only operations keep both asset fields identical (no lending)
    (hAV : v.assetsAvailable = v.assetsTotal)
    -- the deposit amount is a stored-canonical, nonnegative user input
    (hcanon : amount.Canonical)
    (hnn : 0 ≤ amount.toRat)
    (r : DepositResult) (hok : v.deposit amount isDonation = .ok r)
    -- the new share total fits the share domain (int64)
    (hSsz : (v.toExact.sharesTotal : ℚ) + r.sharesIssued.toRat ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful :=
  Vault.deposit_lawful_proof v amount isDonation hv hL hAV hcanon hnn r hok hSsz

theorem Vault.withdraw_lawful (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    (hv : v.Lawful) -- the starting vault is lawful
    -- no unrealized loss: with lossUnrealized equal to the stored gap exactly,
    -- the two independent additions can shrink the gap and break Valid, so
    -- preservation only holds on the zero-loss state
    (hL : v.toExact.lossUnrealized = 0)
    -- vault-only operations keep both asset fields identical (no lending)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (r : WithdrawResult) (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    -- the burned shares are a canonical nonnegative int64 amount (the raw user
    -- input in the by-shares branch)
    (hSc : r.sharesBurned.IntegralCanonical)
    (hSnt : r.sharesBurned.mNumericType = .int64)
    (hSnn : r.sharesBurned.negative = false)
    -- a holder cannot burn more shares than exist
    (hsle : r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ))
    -- the share total fits the share domain (int64)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful :=
  Vault.withdraw_lawful_proof v amount waiveUnrealizedLoss hv hL hAV r hok
    hSc hSnt hSnn hsle hfit

theorem Vault.clawback_lawful (assets holderShares : STAmount)
    (hv : v.Lawful) -- the starting vault is lawful
    -- no unrealized loss: with lossUnrealized equal to the stored gap exactly,
    -- the two independent additions can shrink the gap and break Valid, so
    -- preservation only holds on the zero-loss state
    (hL : v.toExact.lossUnrealized = 0)
    -- vault-only operations keep both asset fields identical (no lending)
    (hAV : v.assetsAvailable = v.assetsTotal)
    -- the clawback amount is a stored-canonical user input
    (hcanon : assets.Canonical)
    (r : ClawbackResult)
    -- the holder balance passed to the run is a stored integral MPT amount,
    -- value exact and nonnegative (it carries the zero-amount claw all arm)
    (hSic : holderShares.IntegralCanonical) (hSc : holderShares.Canonical)
    (hSnn : holderShares.negative = false)
    (hok : v.clawback assets holderShares = .ok r)
    -- the destroyed shares stay strictly below the share total (a full clawback
    -- can leave asset dust with zero shares outstanding, which
    -- `Valid.empty_shares` forbids)
    (hslt : r.sharesDestroyed.toRat < (v.toExact.sharesTotal : ℚ))
    -- the share total fits the share domain (int64)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) :
    r.vault'.Lawful :=
  Vault.clawback_lawful_proof v assets holderShares hv hL hAV hcanon r hSic hSc hSnn hok hslt hfit

theorem Vault.burnShares_lawful (sharesDestroyed sharesTotalAmount : STAmount) (v' : Vault)
    (hv : v.Lawful) -- the starting vault is lawful
    (hcan : v.canBurnShares = .ok (.assets sharesTotalAmount)) -- the burn permission guard passed
    (hcanon : sharesDestroyed.IntegralCanonical) -- stored as a plain integral amount
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat) -- a holder cannot burn more than exists
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1) -- the share total fits int64
    (hok : v.burnShares sharesDestroyed = .ok v') :
    v'.Lawful :=
  Vault.burnShares_lawful_proof v sharesDestroyed sharesTotalAmount v' hv hcan hcanon hnn
    hle hfit hok

end XRPL.Model.SingleAssetVault
