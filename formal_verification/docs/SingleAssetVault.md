# Formal Verification of Single Asset Vault

## Modeling Philosophy

When modeling the Single Asset Vault in Lean 4, the goal was to capture the feature's core business logic and to clearly separate its essential concerns from peripheral implementation details.

The core business logic of the vault is to accept deposits of an asset, issue proportional vault shares, and allow share-holders to redeem their shares for the corresponding portion of the vault's assets. Additionally, the vault needs to support issuer-initiated clawback of the asset that it holds, as well as the ability to burn shares.

We have, in large part, considered every other concern peripheral to the vault. This includes, but is not limited to:

- the properties of the depositors and withdrawers, such as what their accounts look like or whether they are permitted to interact with the assets,
- the properties of the asset in the vault, such as who the issuer is, or whether it is frozen,
- how the asset is stored, the mechanisms of delivering value from accounts to assets and vice versa, or how users interact with the ledger,
- propagation of errors back to the transactor,
- the consensus mechanisms of XRPL, which transactions need to interact with the Vault, or even which other protocols will interact with the Vault.

The main objective when modeling was to establish a clear contract for the Vault, such that any consumer of it can abstract away reading and writing from storage, permissions, transaction parsing, or any other concern, and work against a simple, easy Vault API.
If tomorrow a new KYC feature is added to the ledger, or the Permissioned Domains are completely refactored, or freezing features are abstracted into a single module, the Vault API should not change.

While our Lean 4 design departs somewhat from the structure established in `xrpld`, we have kept exactly the same behavior, so that the Lean 4 Vault could be thought of as a drop-in replacement for the `xrpld` implementation.

## Modeling Challenges

During modeling and proving the Vault, we encountered several challenges when trying to keep the separation clear.

### Number and STAmount

XRPL, as well as the Vault, depends heavily on the `Number` and `STAmount` types, as well as on concrete asset implementations for IOU, MPT and XRP.
In principle, there is no reason why the Vault could not be extended to support any number representation. For example, outstanding shares could be represented using ℕ. We could have designed it abstractly to accept the number representation as input and output, but we found that to be overengineering at this point, which would have made both the model and the proofs much harder to read.
Using `STAmount` as input, and primarily `Number` as output, we have embedded their rounding rules and precision behaviors as part of the Vault's API.

This presents a challenge. The way the `xrpld` code is currently structured is to:

1. call Vault helpers that calculate the exchange rate and round it,
2. use the calculated values in `accountSend` to send the assets between the Vault's pseudoaccount and the holder's account,
3. use `associateAsset`, which both associates the asset and rounds it.

Since the Vault's concerns end at the first step, we could not assume that `accountSend` and `associateAsset` would not round the output of the Vault, essentially changing its output and potentially modifying `assetsTotal`, `assetsAvailable` and the pseudoaccount by different values.

We have attempted to provide the guarantee that any output of the Vault is exactly representable in `STAmount`, so that `accountSend` and `associateAsset` would not further round the output.
This guarantee now holds on reachable vaults. Every amount the vault records is exactly representable, so `associateAsset` changes nothing (`Vault.Reachable.associateAsset_noop`), and a deposit, withdrawal or clawback stores its new `assetsAvailable` exactly (`Vault.{deposit,withdraw,clawback}_associateAsset_noop`).

### Asset Type

In an ideal world, the Single Asset Vault would only need to know the mathematical properties of the asset that it holds.
This could be a floating-point decimal number, an unsigned integer, or `ℝ`. We have branded this `NumericType`, to point out the difference between an asset and its representation.

When it comes to XRPL, there are, broadly speaking, two types of assets: integral (representing XRP and MPT) and floating-point (IOUs). Our initial aim was to represent only those two types.
However, a lot of the arithmetic flows like `STAmount -> Number -> STAmount`, and casting a `Number` to an `STAmount` requires knowledge of not only whether the number is integral, but also the maximum value that it can store. If we lost that information, we would stop storing the final result the same way `xrpld` does, and we would potentially lose precision.
This might be a solvable problem, but for now we are still keeping the information about MPT vs XRP.

Due to this philosophy, we have decided not to care about the asset type in some other situations; for example, we have not modeled the check for whether we can hold the asset (the `tecWRONG_ASSET` preclaim check).
A natural model would be to have a function such as `Vault.canHoldAsset`, but we leave this compatibility check to the caller.

### Propagation of Errors

Every transaction returns either a success or an error. Currently, the codebase is structured so that errors returned by a helper are usually propagated back to the transactor.
To preserve this behavior, we had to tightly couple the Vault to the error codes.
In one solution, the Vault could return its own error representation, but defining this would clutter the API with its own set of error codes. An alternative would be to completely eliminate early returns from the Vault codebase, which would be ideal, but would still require a wrapper around the code that somehow translates the different conditions into errors. We have opted to keep early returns in the Vault implementation for simplicity and rely on the calling function to propagate the error.

### Holder Balances

Another important boundary we set is that the Vault does not know how many shares each holder has. Imagine a real-world scenario: a vault is an office with a teller. You come to the teller and ask to deposit some money, and the teller gives you a receipt for your number of shares. A few days later, you come back and give the teller your share certificate. The teller trusts the certificate and does not check it against their own ledger. They will only raise an eyebrow if you try to redeem more shares than the vault actually issued.

A clawback with a zero amount and a share burn act on the holder's whole balance, so for those the caller passes the holder's share balance in.

## Model

With all of that being said, the Single Asset Vault in Lean 4 still resembles the C++ implementation. The code is in the [Vault directory](../XRPL/Model/Vault).

`Vault.lean` holds the structure that describes the Vault state. This state is expected to be loaded by the caller.

```lean4
structure RawVault where
  assetsAvailable : Number
  assetsDeployed : Number
  assetsReserved : Number
  assetsMaximum : Option Number
  numericType : NumericType
  scale : UInt8
  sharesTotal : Number
  lossUnrealized : Number
  yieldUnrealized : Number
  schedule : Option VaultSchedule
  earlyExitFeeRate : Option TenthBips32
  ownerCanBlockDeposit : Bool
  depositBlocked : Bool
```

There are two types of functions that are implemented over `Vault`:

- Checks and helpers, such as `Vault.canVaultDelete` or `Vault.roundedDepositAmount` (which the `VaultDeposit` preclaim should use to obtain the rounded amount and check whether it will cause a precision loss). These functions are mostly used in preclaim checks, where verifying input against the state of the Vault is needed.
- Calculations, such as `Vault.deposit` or `Vault.withdraw`, which take the current `Vault` state and the intended input (such as the deposit amount), and return either an error, or a success with the new `Vault` state and potentially a delta of changes to key values.

Functions over the `Vault` structure should be considered public API, while free functions are private API. We have not used visibility modifiers, as we need universally public functions for theorems and proofs.

One notable discrepancy from `xrpld` is that we have split clawback functionality into clawback of assets and burning of shares, seeing them as separate concerns.

Also, we have modeled Vault creation. While this is in principle only a storage concern, it made it easier to reason about what the empty Vault looks like in theorems and proofs.

## Lawful Model

A **lawful** Vault is a `RawVault` that is both well-formed (`RawVault.WF`) and valid (`RawVault.Valid`). Both are in `Vault.lean`, and `Vault` extends `RawVault` with their proofs:

```lean4
structure RawVault.WF (rv : RawVault) : Prop where
  assetsAvailable_norm : rv.assetsAvailable.isNormalized
  assetsDeployed_norm : rv.assetsDeployed.isNormalized
  assetsReserved_norm : rv.assetsReserved.isNormalized
  assetsMaximum_norm : ∀ m ∈ rv.assetsMaximum, m.isNormalized
  sharesTotal_norm : rv.sharesTotal.isNormalized
  lossUnrealized_norm : rv.lossUnrealized.isNormalized
  yieldUnrealized_norm : rv.yieldUnrealized.isNormalized
  sharesTotal_nonneg : 0 ≤ rv.sharesTotal.toRat
  sharesTotal_int : rv.sharesTotal.toRat.den = 1
  scale_integral : rv.numericType.isIntegral = true → rv.scale = 0
  scale_le : rv.scale ≤ vaultMaximumIOUScale

structure RawVault.Valid (rv : RawVault) : Prop where
  assetsAvailable_nonneg : Number.zero.operator_le rv.assetsAvailable = true
  assetsDeployed_nonneg : Number.zero.operator_le rv.assetsDeployed = true
  assetsReserved_nonneg : Number.zero.operator_le rv.assetsReserved = true
  lossUnrealized_nonneg : Number.zero.operator_le rv.lossUnrealized = true
  yieldUnrealized_nonneg : Number.zero.operator_le rv.yieldUnrealized = true
  assetsMaximum_pos : ∀ m ∈ rv.assetsMaximum, Number.zero.operator_lt m = true
  empty_shares : rv.sharesTotal = Number.zero →
    rv.assetsAvailable = Number.zero ∧ rv.assetsDeployed = Number.zero
  lossUnrealized_le : rv.lossUnrealized.operator_le rv.assetsDeployed = true
  assetsDeployed_representable : STAmount.isRounded rv.numericType rv.assetsDeployed = false
  assetsReserved_le : rv.assetsReserved.operator_le rv.assetsDeployed = true
  sharesTotal_representable : STAmount.isRounded .int64 rv.sharesTotal = false
  depositBlocked_owner : rv.depositBlocked = true → rv.ownerCanBlockDeposit = true
  schedule_gap : ∀ s ∈ rv.schedule, s.hasValidGap = true
  earlyExitFeeRate_closedEnded : rv.earlyExitFeeRate.isSome = true → rv.schedule.isSome = true
  earlyExitFeeRate_le : ∀ r ∈ rv.earlyExitFeeRate, r ≤ maxEarlyExitFeeRate
  assetsAvailable_representable : STAmount.isRounded rv.numericType rv.assetsAvailable = false
  assetsAvailable_onGrid : rv.assetsAvailable = Number.zero ∨ rv.assetsAvailable.mantissa_.toNat %
    10 ^ (rv.numericType.baseExponent rv.scale - rv.assetsAvailable.exponent_).toNat = 0

structure Vault extends RawVault where
  wf : toRawVault.WF
  valid : toRawVault.Valid
```

`RawVault.Valid` is stated with the modeled `Number` operators, so the model can check it. `RawVault.to_lawful` runs the check and returns a `Vault`, or `notLawful`.
The [Vault properties](../XRPL/Properties/Vault) restate it in exact rationals (`RawVault.Exact.Valid` in `Defs.lean`) and prove that both agree on a well-formed record (`RawVault.valid_iff_exact`).

`Vault.Reachable` holds for every vault reachable from creation by vault transactions. Each operation carries a `Vault` to a `Vault`, so every reachable state is lawful by construction (`Vault.Reachable.lawful`).

The reason we have separated the lawfulness of the Vault from the `RawVault` structure (which may hold even an unlawful vault) is twofold:

1. to allow us to reason about an unlawful Vault as well,
2. to make it easier to change the rules of the Vault without changing the code that uses it.

For example, a new amendment may change what a lawful vault is, but it does not have to change the underlying representation of it.

## Theorems

We prove theorems for each of the operations:

- Burn
- Clawback
- Create
- Delete
- Deposit
- Set
- Withdraw

We provide two types of theorems:

- Vault theorems, which characterize the arithmetic of each operation, and what holds over any sequence of operations from a reachable vault.
- Return theorems, which characterize the exits and the error codes of each operation.

Theorems suffixed `_attained` are witnesses: each is a concrete run. A witness either shows that a bound is reached, or shows that the expected behavior fails without the theorem's hypothesis.

The theorems over `Vault.Reachable` cover vaults changed by vault transactions only. On such a vault `assetsDeployed`, `assetsReserved`, `lossUnrealized` and `yieldUnrealized` stay 0 (`Vault.Reachable.vault_fields`). Vaults changed by the lending protocol are covered by the [lending theorems](../XRPL/Properties/Lending).

The tables list the Single Asset Vault theorems of the final report. The status "Proven that functionality is wrong" means that the theorem states the expected behavior under a hypothesis that excludes a reported bug, and its witness shows the bug. The note names the bug.

### Vault Theorems

| File                  | Theorem                                           | Description                                                                                                                                                        | Status                             |
| --------------------- | ------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ---------------------------------- |
| `Reachable.lean`      | `Vault.Reachable.lawful`                          | Every vault reachable by vault transactions is lawful                                                                                                              | Proven                             |
|                       | `Vault.Reachable.vault_fields`                    | Every reachable vault ->                                                                                                                                           | Proven                             |
|                       |                                                   | AssetsDeployed = AssetsReserved = LossUnrealized = YieldUnrealized = 0                                                                                             |                                    |
|                       |                                                   | AssetsTotal = AssetsAvailable                                                                                                                                      |                                    |
|                       |                                                   | AssetsAvailable ≤ the Open limit (9·10^15 base units)                                                                                                              |                                    |
|                       |                                                   | SharesTotal ≤ AssetsAvailable in base units                                                                                                                        |                                    |
|                       | `Vault.vault_updates_exact`                       | Vault transaction ->                                                                                                                                               | Proven                             |
|                       |                                                   | deposit: AssetsAvailable' − AssetsAvailable = assetsDeposited and SharesTotal' − SharesTotal = sharesCreated                                                       |                                    |
|                       |                                                   | withdrawal: AssetsAvailable − AssetsAvailable' = assetsWithdrawn and SharesTotal − SharesTotal' = sharesRedeemed                                                   |                                    |
|                       |                                                   | clawback: AssetsAvailable − AssetsAvailable' = assetsRecovered and SharesTotal − SharesTotal' = sharesDestroyed                                                    |                                    |
|                       |                                                   | deposit never decreases AssetsAvailable, withdrawal and clawback never increase it                                                                                 |                                    |
| `VaultWithdraw.lean`  | `Vault.lawful_totals`                             | Every lawful vault ->                                                                                                                                              | Proven                             |
|                       |                                                   | insolvent ⟺ AssetsTotal = 0 and SharesTotal > 0                                                                                                                    |                                    |
|                       |                                                   | AssetsTotal = ⌊AssetsAvailable + AssetsDeployed⌋                                                                                                                   |                                    |
|                       |                                                   | netAssetValue = ⌊AssetsTotal − LossUnrealized⌉ unless the loss is waived                                                                                           |                                    |
|                       | `Vault.withdraw_sharesRedeemed`                   | Withdrawal on any lawful vault ->                                                                                                                                  | Proven that functionality is wrong |
|                       |                                                   | by shares, sharesRedeemed = the requested shares                                                                                                                   | Bug: FV_M2_20.                     |
|                       |                                                   | by assets, sharesRedeemed = ⌊idealShares⌋ > 0                                                                                                                      |                                    |
|                       |                                                   | where idealShares = SharesTotal × amount / netAssetValue                                                                                                           |                                    |
|                       | + `_truncation_attained`                          | witness: a run where sharesRedeemed < ⌊idealShares⌋                                                                                                                |                                    |
|                       | + `_relative_attained`                            | witness: a run where sharesRedeemed > ⌊idealShares⌋                                                                                                                |                                    |
|                       | `Vault.withdraw_payout`                           | Withdrawal with sharesRedeemed < SharesTotal ->                                                                                                                    | Proven that functionality is wrong |
|                       |                                                   | assetsWithdrawn = ⌊sharesWorth × (1 − feeRate)⌋ in whole base units                                                                                                | Bug: FV_M2_3.                      |
|                       |                                                   | a larger sharesRedeemed at the same time never lowers assetsWithdrawn                                                                                              |                                    |
|                       |                                                   | where feeRate = EarlyExitFeeRate in the investment phase, otherwise 0                                                                                              |                                    |
|                       |                                                   | and sharesWorth = netAssetValue × sharesRedeemed / SharesTotal                                                                                                     |                                    |
|                       | + `_worth_attained`                               | witness: a run with feeRate = 0 where assetsWithdrawn > sharesWorth                                                                                                |                                    |
| `AssociateAsset.lean` | `Vault.Reachable.associateAsset_noop`             | On a reachable vault -> all Numbers that are passed to associateAsset are exactly representable and calling associateAsset on them is a no-op in terms of rounding | Proven                             |
|                       | `Vault.deposit_associateAsset_noop`               | Deposit, withdrawal or clawback ->                                                                                                                                 | Proven                             |
|                       | `Vault.withdraw_associateAsset_noop`              | AssetsAvailable' is stored exactly                                                                                                                                 |                                    |
|                       | `Vault.clawback_associateAsset_noop`              | AssetsDeployed, AssetsReserved, LossUnrealized, YieldUnrealized and AssetsMaximum unchanged                                                                        |                                    |
| `VaultCreate.lean`    | `Vault.create_success`                            | Vault creation with fields that pass the lawfulness check ->                                                                                                       | Proven                             |
|                       |                                                   | it succeeds                                                                                                                                                        |                                    |
|                       |                                                   | AssetsAvailable = AssetsDeployed = AssetsReserved = SharesTotal = LossUnrealized = YieldUnrealized = 0                                                             |                                    |
|                       |                                                   | an AssetsMaximum that passes the checks is stored exactly                                                                                                          |                                    |
| `VaultSet.lean`       | `Vault.update_success`                            | Vault update with a new AssetsMaximum and deposit flags that pass the lawfulness check ->                                                                          | Proven                             |
|                       |                                                   | it succeeds and only AssetsMaximum and the deposit block change                                                                                                    |                                    |
|                       |                                                   | an AssetsMaximum that passes the checks is stored exactly                                                                                                          |                                    |
|                       |                                                   | with no new AssetsMaximum and no deposit flag, nothing changes                                                                                                     |                                    |
| `VaultDeposit.lean`   | `Vault.deposit_sharesCreated`                     | Deposit on any lawful vault ->                                                                                                                                     | Proven that functionality is wrong |
|                       |                                                   | roundedAmount = ⌊amount⌋ at the scale of AssetsTotal + amount, and ≠ 0                                                                                             | Bug: FV_M2_20.                     |
|                       |                                                   | a larger roundedAmount never lowers sharesCreated                                                                                                                  |                                    |
|                       |                                                   | sharesCreated = ⌊idealShares⌋                                                                                                                                      |                                    |
|                       |                                                   | where idealShares = SharesTotal × roundedAmount / AssetsTotal, or roundedAmount × 10^Scale on an empty vault                                                       |                                    |
|                       | + `_shortfall_attained`                           | witness: a run where sharesCreated < ⌊idealShares⌋                                                                                                                 |                                    |
|                       | + `_overshoot_attained`                           | witness: a run where sharesCreated > ⌊idealShares⌋                                                                                                                 |                                    |
|                       | `Vault.deposit_charge`                            | Deposit on any lawful vault ->                                                                                                                                     | Proven that functionality is wrong |
|                       |                                                   | assetsDeposited ≤ amount                                                                                                                                           | Bug: FV_M2_3.                      |
|                       |                                                   | assetsDeposited = ⌈sharesWorth⌉                                                                                                                                    |                                    |
|                       |                                                   | where sharesWorth = AssetsTotal × sharesCreated / SharesTotal, or sharesCreated / 10^Scale on an empty vault                                                       |                                    |
|                       | + `_undercharge_frac_attained`                    | witness: a run on an IOU where the charge rounded down to the vault scale gives assetsDeposited < sharesWorth                                                      |                                    |
|                       | + `_undercharge_integral_attained`                | witness: a run on XRP or MPT where the price rounded to nearest gives assetsDeposited < sharesWorth                                                                |                                    |
|                       | `Vault.deposit_donation`                          | Donation ->                                                                                                                                                        | Proven                             |
|                       |                                                   | assetsDeposited = roundedAmount                                                                                                                                    |                                    |
|                       |                                                   | sharesCreated = 0                                                                                                                                                  |                                    |
| `CanEmpty.lean`       | `Vault.Reachable.canEmpty`                        | Every reachable vault ->                                                                                                                                           | Proven                             |
|                       |                                                   | it can be emptied                                                                                                                                                  | With loans: FV_M2_9, FV_M4_37.     |
|                       |                                                   | outside the investment phase or with an EarlyExitFeeRate, a full withdrawal by shares succeeds                                                                     |                                    |
|                       |                                                   | a full withdrawal has assetsWithdrawn = AssetsAvailable                                                                                                            |                                    |
|                       |                                                   | any withdrawal from it:                                                                                                                                            |                                    |
|                       |                                                   | by shares ≤ SharesTotal, it never fails for lack of AssetsAvailable                                                                                                |                                    |
|                       |                                                   | sharesRedeemed = SharesTotal ⟺ AssetsAvailable' = SharesTotal' = 0 and no other field changes                                                                      |                                    |
| `VaultClawback.lean`  | `Vault.clawback_sharesDestroyed`                  | Clawback on any lawful vault, with amount ≠ 0 ->                                                                                                                   | Proven that functionality is wrong |
|                       |                                                   | sharesDestroyed = ⌊idealShares⌋                                                                                                                                    | Bug: FV_M2_20.                     |
|                       |                                                   | where idealShares = SharesTotal × amount / netAssetValue                                                                                                           |                                    |
|                       |                                                   | or SharesTotal × AssetsAvailable / netAssetValue when amount is priced above AssetsAvailable                                                                       |                                    |
|                       | + `_truncation_attained`                          | witness: a run where sharesDestroyed < ⌊idealShares⌋                                                                                                               |                                    |
|                       | + `_relative_attained`                            | witness: a run where sharesDestroyed > ⌊idealShares⌋                                                                                                               |                                    |
|                       | `Vault.clawback_zero_all_shares`                  | Clawback on any lawful vault, with amount = 0 ->                                                                                                                   | Proven that functionality is wrong |
|                       |                                                   | sharesDestroyed = the holder's whole balance ≠ 0                                                                                                                   | Bug: FV_M2_3.                      |
|                       |                                                   | assetsRecovered − sharesWorth ≤ 0                                                                                                                                  |                                    |
|                       |                                                   | where sharesWorth = netAssetValue × sharesDestroyed / SharesTotal                                                                                                  |                                    |
|                       | + `_attained`                                     | witness: a run where assetsRecovered > sharesWorth                                                                                                                 |                                    |
|                       | `Vault.clawback_assetsRecovered`                  | Clawback with amount ≠ 0 ->                                                                                                                                        | Proven that functionality is wrong |
|                       |                                                   | assetsRecovered ≤ AssetsAvailable                                                                                                                                  | Bug: FV_M2_3.                      |
|                       |                                                   | assetsRecovered − sharesWorth ≤ 0                                                                                                                                  |                                    |
|                       |                                                   | sharesWorth − assetsRecovered < 1 base unit                                                                                                                        |                                    |
|                       |                                                   | where sharesWorth = netAssetValue × sharesDestroyed / SharesTotal                                                                                                  |                                    |
|                       | + `_overshoot_attained`                           | witness: a run where assetsRecovered > sharesWorth                                                                                                                 |                                    |
| `VaultBurn.lean`      | `Vault.burnShares_sharesTotal_exact`              | Burn -> SharesTotal' = SharesTotal − sharesDestroyed                                                                                                               | Proven                             |
| `Dilution.lean`       | `Vault.no_dilution`                               | Vault transaction ->                                                                                                                                               | Proven that functionality is wrong |
|                       |                                                   | deposit: shareValue' − shareValue ≥ 0                                                                                                                              | Bug: FV_M2_3.                      |
|                       |                                                   | donation: shareValue' − shareValue > 0                                                                                                                             |                                    |
|                       |                                                   | withdrawal: shareValue' − shareValue ≥ 0                                                                                                                           |                                    |
|                       |                                                   | clawback, also with amount = 0: shareValue' − shareValue ≥ 0                                                                                                       |                                    |
|                       |                                                   | where shareValue = (AssetsTotal − LossUnrealized) / SharesTotal                                                                                                    |                                    |
|                       | + `_deposit_grid_attained`                        | witness: a deposit on an IOU where ⌊sharesWorth⌋ lowers shareValue                                                                                                 |                                    |
|                       | + `_deposit_integral_attained`                    | witness: a deposit on XRP or MPT where a price rounded to nearest lowers shareValue                                                                                |                                    |
|                       | + `_withdraw_half_ulp_attained`                   | witness: a withdrawal where a price rounded to nearest lowers shareValue                                                                                           |                                    |
|                       | + `_clawback_half_ulp_attained`                   | witness: a clawback where a price rounded to nearest lowers shareValue                                                                                             |                                    |
|                       | + `_clawback_zero_half_ulp_attained`              | witness: a clawback with amount = 0 where a price rounded to nearest lowers shareValue                                                                             |                                    |
|                       | `Vault.ReachableFromIn.no_dilution`               | Over any sequence of transactions from a reachable vault, while SharesTotal > 0 -> shareValue' − shareValue ≥ 0                                                    | Proven that functionality is wrong |
|                       |                                                   | where shareValue = (AssetsTotal − LossUnrealized) / SharesTotal                                                                                                    | Bug: FV_M2_3.                      |
|                       | `Vault.ReachableFromIn.dilution_attained`         | witness: a sequence where two withdrawals lower shareValue                                                                                                         |                                    |
|                       | `Vault.ReachableFromIn.dilution_deposit_attained` | witness: a sequence of 100 deposits on an IOU, each charge rounded down to the vault scale, that lowers shareValue                                                 |                                    |
| `Accounting.lean`     | `Vault.Reachable.accounting`                      | Over any sequence of transactions from a reachable vault ->                                                                                                        | Proven                             |
|                       |                                                   | AssetsTotal' = AssetsTotal + Σ deposits − Σ withdrawals − Σ clawbacks                                                                                              |                                    |
|                       |                                                   | AssetsAvailable' = AssetsAvailable + Σ deposits − Σ withdrawals − Σ clawbacks                                                                                      |                                    |
|                       |                                                   | SharesTotal' = SharesTotal + Σ sharesCreated − Σ sharesRedeemed − Σ sharesDestroyed                                                                                |                                    |
|                       |                                                   | from a new vault:                                                                                                                                                  |                                    |
|                       |                                                   | AssetsTotal' = AssetsAvailable' = Σ deposits − Σ withdrawals − Σ clawbacks                                                                                         |                                    |
|                       |                                                   | SharesTotal' = Σ sharesCreated − Σ sharesRedeemed − Σ sharesDestroyed                                                                                              |                                    |
| `Roundtrip.lean`      | `Vault.deposit_withdraw_roundtrip`                | Deposit then a withdrawal of its sharesCreated at the same time ->                                                                                                 | Proven                             |
|                       |                                                   | assetsWithdrawn − assetsDeposited ≤ 0                                                                                                                              |                                    |
|                       |                                                   | assetsDeposited − assetsWithdrawn ≤ 1 base unit                                                                                                                    |                                    |
|                       | + `_loss_attained`                                | witness: a run where assetsDeposited − assetsWithdrawn = 1 base unit                                                                                               |                                    |
|                       | + `_gain_attained`                                | witness: a run where assetsWithdrawn = assetsDeposited                                                                                                             |                                    |
|                       | `Vault.deposits_withdraw_roundtrip_attained`      | n deposits by one depositor, then a withdrawal of all their sharesCreated, at the same time ->                                                                     | Proven that functionality is wrong |
|                       |                                                   | assetsWithdrawn − Σ assetsDeposited ≤ 0                                                                                                                            | Bug: FV_M2_3.                      |
|                       |                                                   | witness: a run of 100 deposits on an IOU, each charge rounded down to the vault scale, where assetsWithdrawn − Σ assetsDeposited = 0.83                            |                                    |
| `Isolation.lean`      | `Vault.Reachable.isolation`                       | Vault transaction by another holder or the owner, at the same time ->                                                                                              | Proven that functionality is wrong |
|                       |                                                   | a withdrawal by shares that would have succeeded still succeeds                                                                                                    | Bug: FV_M2_3.                      |
|                       |                                                   | where feeRate = EarlyExitFeeRate in the investment phase, otherwise 0                                                                                              |                                    |
|                       | + `_clawback_attained`                            | witness: a run with feeRate = 75% where a clawback of shares not worth whole base units makes the withdrawal fail                                                  |                                    |
|                       | + `_clawback_tie_attained`                        | witness: a run with feeRate = 99.989% where a clawback makes a withdrawal of shares not worth whole base units fail                                                |                                    |
| `Phases.lean`         | `Vault.investment_shares_fixed`                   | Investment ->                                                                                                                                                      | Proven                             |
|                       |                                                   | SharesTotal changes only through a withdrawal from a vault with an EarlyExitFeeRate (even 0), a clawback, or burning the shares of an insolvent vault              |                                    |
| `ExitOrder.lean`      | `Vault.redemption_exit_order`                     | Redemption, A and B withdraw all their shares ->                                                                                                                   | Proven that functionality is wrong |
|                       |                                                   | payoutFirst − payoutSecond ≤ 0                                                                                                                                     | Bug: FV_M2_3.                      |
|                       |                                                   | payoutSecond − payoutFirst ≤ 1 base unit                                                                                                                           |                                    |
|                       |                                                   | where payoutFirst = A's assetsWithdrawn when A goes first                                                                                                          |                                    |
|                       |                                                   | payoutSecond = A's assetsWithdrawn when B goes first                                                                                                               |                                    |
|                       | + `_upper_bound_attained`                         | witness: a run where payoutFirst − payoutSecond = 1 base unit                                                                                                      |                                    |
|                       | + `_lower_bound_attained`                         | witness: a run where payoutSecond − payoutFirst = 2 base units                                                                                                     |                                    |
|                       | `Vault.redemption_exit_order_lower_bound_final`   | Redemption, A and B are the only holders and withdraw all their shares ->                                                                                          | Proven                             |
|                       |                                                   | payoutSecond − payoutFirst ≤ 1 base unit                                                                                                                           |                                    |
|                       |                                                   | where payoutFirst = A's assetsWithdrawn when A goes first                                                                                                          |                                    |
|                       |                                                   | payoutSecond = A's assetsWithdrawn when B goes first                                                                                                               |                                    |
|                       | + `_attained`                                     | witness: a run where payoutSecond − payoutFirst = 1 base unit                                                                                                      |                                    |

### Return Theorems

| File                       | Theorem                              | Exit condition                                                                                                                                               | Status                                                        |
| -------------------------- | ------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------- |
| `VaultCreate.lean`         | `Vault.canCreate_exits`              | When a schedule's subscription or redemption date has passed -> tecEXPIRED                                                                                   | Proven                                                        |
|                            |                                      | When AssetsMaximum isn't a whole number of base units or the asset can't store it exactly -> tecPRECISION_LOSS                                               |                                                               |
|                            |                                      | Otherwise -> success                                                                                                                                         |                                                               |
|                            | `Vault.canCreate_error_codes`        | Error codes: success, tecEXPIRED or tecPRECISION_LOSS                                                                                                        | Proven                                                        |
|                            | `Vault.create_not_lawful`            | When the vault holds an IOU and Scale > 10 -> notLawful                                                                                                      | Proven                                                        |
|                            |                                      | When AssetsMaximum ≠ 0 isn't normalized or isn't > 0 -> notLawful                                                                                            |                                                               |
|                            |                                      | When the schedule's investment period is too short or too long -> notLawful                                                                                  |                                                               |
|                            |                                      | When the vault has a schedule and EarlyExitFeeRate > 100% -> notLawful                                                                                       |                                                               |
| `VaultSet.lean`            | `Vault.canVaultUpdate_exits`         | When the new AssetsMaximum isn't a whole number of base units or the asset can't store it exactly -> tecPRECISION_LOSS                                       | Proven                                                        |
|                            |                                      | When blocking or unblocking deposits on a vault created without that permission -> tecNO_PERMISSION                                                          |                                                               |
|                            |                                      | When the new AssetsMaximum ≠ 0 and < AssetsTotal -> tecLIMIT_EXCEEDED                                                                                        |                                                               |
|                            | `Vault.canVaultUpdate_error_codes`   | Error codes: success, tecPRECISION_LOSS, tecNO_PERMISSION or tecLIMIT_EXCEEDED                                                                               | Proven                                                        |
|                            | `Vault.canVaultUpdate_lawful_iff`    | success ⟺                                                                                                                                                    | Proven                                                        |
|                            |                                      | the new AssetsMaximum is a whole number of base units that the asset stores exactly                                                                          |                                                               |
|                            |                                      | the deposit flags are permitted                                                                                                                              |                                                               |
|                            |                                      | the new AssetsMaximum is 0 or ≥ AssetsTotal                                                                                                                  |                                                               |
|                            | `Vault.update_not_lawful`            | When the new AssetsMaximum ≠ 0 isn't normalized or isn't > 0 -> notLawful                                                                                    | Proven                                                        |
|                            |                                      | When blocking deposits on a vault created without that permission -> notLawful                                                                               |                                                               |
| `VaultDepositReturn.lean`  | `Vault.deposit_exits`                | When a deposit comes in the investment or redemption phase -> tecEXPIRED                                                                                     | Proven                                                        |
|                            |                                      | When a donation comes and SharesTotal = 0 -> tecNO_PERMISSION                                                                                                |                                                               |
|                            |                                      | When a deposit comes and the vault is insolvent -> tecLOCKED                                                                                                 |                                                               |
|                            |                                      | When the vault owner blocked deposits -> tecLOCKED                                                                                                           |                                                               |
|                            |                                      | When roundedAmount = 0 -> tecPRECISION_LOSS                                                                                                                  |                                                               |
|                            |                                      | When a deposit comes and sharesCreated = 0 -> tecPRECISION_LOSS                                                                                              |                                                               |
|                            |                                      | When the priced assets > roundedAmount -> tecINTERNAL                                                                                                        |                                                               |
|                            |                                      | When ⌊assetsDeposited⌋ = 0 at the scale of AssetsTotal + assetsDeposited, for an IOU -> tecPRECISION_LOSS                                                    |                                                               |
|                            |                                      | When pricing overflows -> tecPATH_DRY                                                                                                                        |                                                               |
|                            |                                      | When AssetsTotal + assetsDeposited leaves the initial vault scale or passes the Open limit -> tecLIMIT_EXCEEDED                                              |                                                               |
|                            |                                      | When AssetsMaximum ≠ 0 and AssetsTotal' > AssetsMaximum -> tecLIMIT_EXCEEDED                                                                                 |                                                               |
|                            |                                      | When SharesTotal + sharesCreated > 2^63 − 1 -> tecPATH_DRY                                                                                                   |                                                               |
|                            |                                      | All checks pass -> updated vault, which is lawful                                                                                                            |                                                               |
|                            | `Vault.deposit_error_codes`          | The only deposit rejections are tecEXPIRED, tecNO_PERMISSION, tecLOCKED, tecPRECISION_LOSS, tecINTERNAL, tecPATH_DRY or tecLIMIT_EXCEEDED                    | Proven                                                        |
| `VaultWithdrawReturn.lean` | `Vault.withdraw_exits`               | When a withdrawal comes in the investment phase and the vault has no EarlyExitFeeRate -> tecTOO_SOON                                                         | Proven                                                        |
|                            |                                      | When sharesRedeemed = 0 -> tecPRECISION_LOSS                                                                                                                 |                                                               |
|                            |                                      | When pricing overflows -> tecPATH_DRY                                                                                                                        |                                                               |
|                            |                                      | When sharesRedeemed = SharesTotal and AssetsDeployed ≠ 0 -> tecHAS_OBLIGATIONS                                                                               |                                                               |
|                            |                                      | When withdrawing by shares, price = 0 and netAssetValue ≠ 0 -> tecPRECISION_LOSS                                                                             |                                                               |
|                            |                                      | When the price is too small to change the stored AssetsAvailable -> tecPRECISION_LOSS, or tecPATH_DRY on overflow                                            |                                                               |
|                            |                                      | When feeRate = 0 and price > AssetsAvailable -> tecINSUFFICIENT_FUNDS                                                                                        |                                                               |
|                            |                                      | When sharesRedeemed < SharesTotal, feeRate < 100% and the fee leaves nothing to pay or ⌊payout⌋ = 0 at the scale of AssetsAvailable' -> tecPRECISION_LOSS    |                                                               |
|                            |                                      | When the payout after the fee > AssetsAvailable -> tecINSUFFICIENT_FUNDS                                                                                     |                                                               |
|                            |                                      | When sharesRedeemed = SharesTotal and price > AssetsAvailable -> tecINSUFFICIENT_FUNDS                                                                       |                                                               |
|                            |                                      | All checks pass and sharesRedeemed < SharesTotal -> updated vault, which is lawful                                                                           |                                                               |
|                            |                                      | All checks pass and sharesRedeemed = SharesTotal -> assetsWithdrawn = AssetsAvailable, AssetsAvailable' = SharesTotal' = 0, and the updated vault is lawful  |                                                               |
|                            | `Vault.withdraw_error_codes`         | The only withdrawal rejections are tecTOO_SOON, tecPRECISION_LOSS, tecPATH_DRY, tecHAS_OBLIGATIONS or tecINSUFFICIENT_FUNDS                                  | Proven that functionality is wrong                            |
|                            | + `_attained`                        | witness: an XRP withdrawal of shares worth more than 10^17 drops that returns an error, not a result code                                                    | Bug: FV_M2_25.                                                |
| `VaultClawbackReturn.lean` | `Vault.clawback_exits`               | When the vault holds XRP -> tecNO_PERMISSION                                                                                                                 | Proven                                                        |
|                            |                                      | When pricing overflows -> tecPATH_DRY                                                                                                                        |                                                               |
|                            |                                      | When the capped assetsRecovered is still above AssetsAvailable -> tecINTERNAL                                                                                |                                                               |
|                            |                                      | When sharesDestroyed = SharesTotal and AssetsDeployed ≠ 0 -> tecHAS_OBLIGATIONS                                                                              |                                                               |
|                            |                                      | When assetsRecovered ≠ 0 and ⌊assetsRecovered⌋ = 0 at the scale of AssetsAvailable' -> tecPRECISION_LOSS                                                     |                                                               |
|                            |                                      | When sharesDestroyed = 0 -> tecPRECISION_LOSS                                                                                                                |                                                               |
|                            |                                      | When assetsRecovered is too small to change the stored AssetsAvailable -> tecPRECISION_LOSS, or tecPATH_DRY on overflow                                      |                                                               |
|                            |                                      | All checks pass and sharesDestroyed < SharesTotal -> updated vault, which is lawful                                                                          |                                                               |
|                            |                                      | All checks pass and sharesDestroyed = SharesTotal -> assetsRecovered = AssetsAvailable, AssetsAvailable' = SharesTotal' = 0, and the updated vault is lawful |                                                               |
|                            | `Vault.clawback_error_codes`         | The only clawback rejections are tecNO_PERMISSION, tecINTERNAL, tecHAS_OBLIGATIONS, tecPRECISION_LOSS, tecPATH_DRY or tecINSUFFICIENT_FUNDS                  | Proven                                                        |
| `NoInternalErrors.lean`    | `Vault.Reachable.no_internal_errors` | Vault transaction ->                                                                                                                                         | Proven that functionality is wrong                            |
|                            |                                      | deposit: no tecINTERNAL and no tecPATH_DRY                                                                                                                   | Bugs: FV_M2_22, FV_M2_23. Withdrawal and clawback: by design. |
|                            |                                      | withdrawal: no tecINTERNAL and no tecPATH_DRY                                                                                                                |                                                               |
|                            |                                      | clawback: no tecINTERNAL and no tecPATH_DRY                                                                                                                  |                                                               |
|                            | + `_deposit_attained`                | witness: a run where an MPT deposit above the Open limit returns tecINTERNAL                                                                                 |                                                               |
|                            | + `_deposit_path_dry_attained`       | witness: a run where a deposit above the Open limit returns tecPATH_DRY                                                                                      |                                                               |
|                            | + `_withdraw_path_dry_attained`      | witness: a run where a withdrawal above the Open limit returns tecPATH_DRY                                                                                   |                                                               |
|                            | + `_clawback_path_dry_attained`      | witness: a run where a clawback above the Open limit returns tecPATH_DRY                                                                                     |                                                               |
| `VaultBurnReturn.lean`     | `Vault.canBurnShares_exits`          | When the vault isn't insolvent -> tecNO_PERMISSION                                                                                                           | Proven                                                        |
|                            |                                      | When amount ≠ 0 and amount ≠ the holder's whole balance -> tecLIMIT_EXCEEDED                                                                                 |                                                               |
|                            |                                      | Otherwise -> returns SharesTotal                                                                                                                             |                                                               |
|                            | `Vault.canBurnShares_error_codes`    | Error codes: success, tecNO_PERMISSION or tecLIMIT_EXCEEDED                                                                                                  | Proven                                                        |
|                            | `Vault.burnShares_exits`             | When sharesDestroyed = 0 -> tecPRECISION_LOSS                                                                                                                | Proven                                                        |
|                            |                                      | All checks pass -> updated vault                                                                                                                             |                                                               |
|                            | `Vault.burnShares_error_codes`       | The only burn rejection is tecPRECISION_LOSS                                                                                                                 | Proven                                                        |
| `VaultDelete.lean`         | `Vault.canVaultDelete_exits`         | When AssetsAvailable ≠ 0, AssetsDeployed ≠ 0 or SharesTotal ≠ 0 -> tecHAS_OBLIGATIONS                                                                        | Proven                                                        |
|                            |                                      | Otherwise -> success                                                                                                                                         |                                                               |
|                            | `Vault.canVaultDelete_error_codes`   | Error codes: success or tecHAS_OBLIGATIONS                                                                                                                   | Proven                                                        |
|                            | `Vault.canVaultDelete_lawful_iff`    | success ⟺                                                                                                                                                    | Proven                                                        |
|                            |                                      | AssetsTotal = 0                                                                                                                                              |                                                               |
|                            |                                      | SharesTotal = 0                                                                                                                                              |                                                               |
