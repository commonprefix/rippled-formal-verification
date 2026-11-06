# rfv-ffi: model vs C++ gap fixes

2026-11-06

Gaps between the Lean model and the C++ found by the rfv-ffi differential tests, fixed one at a time. Known C++ bugs (FV_M2_*) are out of scope.

## Gap 1: clawback burns more shares than the holder owns

**Side:** model.

**Gap:** clawing back more than a holder's shares are worth (amount > 0, other holders present). C++ fails with `tecINSUFFICIENT_FUNDS`. The model succeeds and burns other holders' value.

**Why we missed it:** C++ has no explicit check. The rejection happens inside `accountSend`, when the shares move from the holder to the vault (`VaultClawback.cpp` doApply). The model has no per-holder balances, so nothing caught it.

**Fix:** `Vault.clawback` rejects with `tecINSUFFICIENT_FUNDS` when the shares to burn exceed `holderShares`, after the dust check, as in C++ (`VaultClawback.lean`). Compares the two `STAmount`s directly, like C++'s integer compare in `directSendNoFeeMPT` (`TokenHelpers.cpp`).

**Side cleanup (withdraw):** `Vault.withdraw` took `holderShares` as a `Number` (added in #52) and compared after a `toNumber` conversion. Now `Option STAmount`, compared with `STAmount.operator_lt`, as C++ does (`VaultWithdraw.cpp:432`). FFI export and C++ callers updated. No behaviour change: int64 shares convert to `Number` exactly.

**Test:** `testHolderValueSweep` re-enabled in `LeanVaultClawback_test.cpp`. Repro: `gapClawbackOverHolderValue` in `LeanCuspScratch_test.cpp`.

**Status:** fix applied, Lean builds; FFI run pending.

## Gap 2: LoanSet accepts an origination fee above the principal

**Side:** model.

**Gap:** fee > principal. C++ preflight returns `temINVALID` (`LoanSet.cpp:881`, `validNumericRange(fee, principal)`). The model creates the loan.

**Why we missed it:** preflight check; the model starts after preflight. Other LoanSet ranges became lawfulness clauses, but this one can't use a stored field: the loan only stores `principalOutstanding`, which falls with repayment.

**Impact:** low. The model doesn't track the payout to the borrower (`principal - fee`), so no model total is wrong. But it reaches loans C++ never creates, and `fee ≤ principal` can't be used in proofs.

**Test:** `testOriginationFeeSweep` disabled in `LeanLoanSet_test.cpp` (23 of 62 rows disagree, IOU and MPT). Repro: `gapLoanOriginationFee` in `LeanCuspScratch_test.cpp`.

**Fix options (undecided):**

| | A: lawfulness clause | B: hypothesis on `Loan.create` |
| --- | --- | --- |
| Change | New model field `principalRequested` + clause `fee ≤ principalRequested` | `(_hfee : fees.originationFee ≤ principal)`, FFI returns `badInput` |
| Pro | Same as the other LoanSet ranges; every lawful loan carries the fact for proofs | Small; no new state; same pattern as vault `_hpos` |
| Con | Field not on the C++ SLE (carried by tests, like `paymentTotal`); `Valid` and proofs that build loans grow | Fact lost after creation; later proofs (e.g. LoanAccept pays `principal - fee`) can't use it |
| Harness | C++ `tem` ↔ model `notLawful` | C++ `tem` ↔ model `badInput` |

**Status:** open.

## Gap 3: XRP vault created with an AssetsMaximum above 1e17 drops

**Side:** model.

**Gap:** a cap that no amount of the asset can hold (XRP above 1e17 drops). C++ preflight returns `temMALFORMED` (`VaultCreate.cpp:95`, `isRepresentable`, fixCleanup3_5_0). The model's `canCreate` returns `tecPRECISION_LOSS`, but `create` still builds a lawful vault with that cap.

**Why we missed it:** preflight check, newer amendment. VaultSet does the same check in preclaim (`tecPRECISION_LOSS`), which the model already matched, so only create showed it.

**Impact:** low. No total can reach the cap, so no deposit verdict changes. But lawful model vaults could hold a cap C++ cannot store.

**Fix:** new lawfulness clause `assetsMaximum_representable` in `RawVault.Valid` (`Vault.lean`): the cap must fit the asset's amount type. `Vault.create` now returns `notLawful`, which the harness matches with C++ `tem`. Also covers `Vault.update`.

**Test:** `testXrpMaximumSweep` re-enabled in `LeanVaultCreate_test.cpp`. New cases in `LeanVault_test.cpp`: 17-digit IOU cap and XRP cap 1e17+1 not lawful, XRP cap 1e17 lawful. Repro: `gapCreateXrpMaximum` in `LeanCuspScratch_test.cpp`.

**Status:** fix applied, Lean builds; FFI run pending. Proofs under `Properties/Vault` that build `RawVault.Valid` need the new clause (they look stale already).

## Gap 4: deposit past the share cap (2^63 - 1 shares)

**Side:** model.

**Gap:** a deposit whose shares push the outstanding total past 2^63 - 1. C++ returns `tecPATH_DRY`. The model:

- at exactly 2^63: succeeds, but the `Number` sum rounds the total down to 2^63 - 1, so one minted share is missing from `sharesTotal`;
- above 2^63: the total rounds up and is not representable, so the model raises `notLawful` instead of returning a TER.

**Why we missed it:** C++ has no check in `VaultDeposit`. It fails inside `accountSend` when the vault (the share issuer) sends the new shares: `isMPTOverflow` in `directSendNoLimitMPT` (`TokenHelpers.cpp`). The model adds share totals as a `Number`, which rounds silently past 2^63 - 1.

**Impact:** low to medium. Needs about 2^63 shares outstanding (a very cheap share price, e.g. after large losses). When hit, a lawful model state undercounts shares.

**Fix:** `Vault.deposit` returns `tecPATH_DRY` when `sharesTotal + shares > 2^63 - 1`, compared exactly (rationals), after the cap check and before `to_lawful`, as in C++ (`VaultDeposit.lean`). Checked with `#eval`: 2^63 - 1 succeeds, 2^63 and above return `tecPATH_DRY`.

**Test:** `testShareMintCapSweep` re-enabled in `LeanVaultDeposit_test.cpp` (its old comment wrongly said the pre-state was not lawful; it is the post-state).

**Status:** fix applied, Lean builds; FFI run pending.

## Gap 5: Number addition at the top exponent (32768)

**Side:** model (outdated port).

**Gap:** same-sign add whose mantissa sum is just above kMaxRepUp at exponent 32768. C++ throws "Number::normalize 1.5". The model rounds down and returns `9223372036854775810e32768` (to_nearest, towards_zero, downward; upward errors on both sides).

**Why:** the model's same-sign branch (`Number.lean`, `Number.operator_add`) uses the pre-#7369 shape: drop a digit, then `doRoundUp` (error `.overflow`, "addition overflow"), with the #7389 limit `maxRepUp`. C++ changed it in #7369 (2026-07-10): under `Enabled330` the raw sum goes to `doNormalize`, which throws at the top exponent before dropping a digit. The old shape is still in C++, but only for `cuspRoundingFix < Enabled330`. The model's subtraction branch already follows #7389; addition was not updated.

**Impact:** very low. Only values near 9.2e32786; no ledger amount gets close (`STAmount` exponents end at 80). Only `Number`-level statements (when addition fails) are off at this edge.

**Test:** `testSumOverflowSweep` disabled in `LeanNumber_test.cpp`. Cases in `NumberSweepCases.h` (`kSumOverflowCusps`).

**Possible actions (undecided):**

| | Action | Cost |
| --- | --- | --- |
| 1 | Leave as a known divergence; update the disabled test's comment | None |
| 2 | Guard: error `normalize1` / `normalize1_5` when the drop happens at `xe ≥ maxExponent` | Small code change; proofs that unfold `operator_add` gain an error case |
| 3 | Port #7369: pass the 128-bit sum to `doNormalize128`, as subtraction does | Matches C++ structure; reworks the ~10 `Add/Common/*` proofs and `Totality.lean` |

**Status:** open, nothing changed.

## Not a gap: `LeanIOUAmount_test` without the `NumberSO` guard

**Finding:** the suite had a commented-out `NumberSO const so{true};` with "TODO: add back when fixes merged". `NumberSO` no longer exists: #5962 (2026-06-10, retire fixUniversalNumber) removed the switchover and made the `Number`-based `IOUAmount` path the only one. The model follows that path, so the suite already tests the right behaviour. The TODO came with the copy from `lending-protocol-fv`, which predated #5962.

**Action:** replaced the stale lines with a one-line note (`LeanIOUAmount_test.cpp`).

## Gap 13: Scale on an XRP or MPT vault at create

**Side:** model (preflight not modelled).

**Gap:** a `Scale` field on an XRP or MPT vault (any value, even 0). C++ preflight returns `temMALFORMED` (`VaultCreate.cpp:112`). The model's `Vault.create` sets the scale to 0 and creates the vault.

**Why:** the model copies C++ doApply, which also forces the scale to 0 for integral assets (`VaultCreate.cpp:250`). Only the preflight rejection is missing. It can't be a lawfulness clause: the stored scale is 0 on both sides, the bad data is in the transaction.

**Impact:** none on state. Both sides store scale 0, so no unreal vault. Only the verdict for a malformed transaction differs.

**Test:** known and accepted. `LeanVaultCreate_test.cpp` runs XRP and MPT with scale 3 as `outsideModel` (C++ `tem`, model normalizes). No case for `Scale = 0`.

**Possible actions (undecided):**

| | Action | Effect |
| --- | --- | --- |
| 1 | Leave as is; add a `Scale = 0` case | Model stays a copy of doApply |
| 2 | Hypothesis on `Vault.create`, FFI returns `badInput` (gap 2 option B pattern) | Model rejects what C++ rejects; `outsideModel` goes away |
| 3 | `Vault.create` returns `notLawful` for a scale on an integral asset | Fits the harness rule, but the error is misleading (bad input, not bad state) |

**Status:** open, nothing changed.

## Gap 14: EarlyExitFeeRate on an open-ended vault at create

**Side:** model.

**Gap:** an open-ended vault created with an early-exit fee rate (even 0). C++ preflight returns `temMALFORMED` (`VaultCreate.cpp:143`). The model dropped the rate and created the vault.

**Why we missed it:** `Vault.create` copied doApply, which only stores the rate on a closed-ended vault. The vault invariant already had the rule (`earlyExitFeeRate_closedEnded`), but `create` dropped the rate before the check could see it. No test created an open-ended vault with a fee.

**Impact:** none on state. Only the verdict for a malformed transaction differed.

**Fix:** removed the filter in `Vault.create` (`VaultCreate.lean`). The rate now reaches `to_lawful`, which returns `notLawful` through the existing clause, matched with C++ `tem` by the harness. Same handling as the 100% fee cap.

**Test:** new cases in `LeanVaultCreate_test.cpp`: open-ended IOU vault with a 5% fee and with a 0 fee, both `temMALFORMED`.

**Status:** fix applied, Lean builds; FFI run pending.

## Gap 15: VaultSet with a negative cap, or with both block flags

**Side:** model (preflight not modelled).

**Gap:** two C++ preflight checks in `VaultSet.cpp`, checked in the model with `#eval`:

| Input | Model `canVaultUpdate` | Model `update` | C++ |
| --- | --- | --- | --- |
| cap below 0 | `tecLIMIT_EXCEEDED` | `notLawful` (`assetsMaximum_pos`) | `temMALFORMED` (L73) |
| both flags, owner can block | `tesSUCCESS` | lawful, deposits blocked | `temINVALID_FLAG` (L88) |
| both flags, owner can't block | `tecNO_PERMISSION` | — | `temINVALID_FLAG` |

With both flags, C++ doApply would set then clear the flag (unblock wins); the model's `update` lets block win, so it also differs from doApply on that input.

**Why we missed it:** preflight checks. The set harness (`checkSet`) compares TERs directly, with no `tem` ↔ `notLawful` rule like create's. No test sets a negative cap or both flags.

**Impact:** none on reachable state. The model cannot store a negative cap; preflight always stops both flags. Only the verdict differs.

**Possible actions (undecided):**

| | Action | Effect |
| --- | --- | --- |
| a | Negative cap: give `checkSet` the create rule (C++ `tem` ⇒ model `update` is `notLawful`) and add a sweep around a cap of 0 | Test-only; the model already rejects it |
| b1 | Both flags: document only | — |
| b2 | Both flags: `update` lets unblock win, as doApply does | One line; `update` matches doApply, verdict still differs |
| b3 | Both flags: hypothesis + `badInput` (gap 2 option B pattern) | Model rejects what C++ rejects |

**Status:** open, nothing changed.

## Gap 16: XRP or MPT withdraw by shares with an out-of-range payout

**Side:** C++ (robustness). Model is fine.

**Gap:** a by-shares withdraw whose payout does not fit the asset (XRP above 1e17 drops, MPT above 2^63 - 1). C++ assigns the `Number` result to an `STAmount` (`VaultHelpers.cpp:764`), whose `canonicalize` throws `std::runtime_error` ("amount out of range", `STAmount.cpp:879`). VaultWithdraw only catches `std::overflow_error`, so the transaction ends in `tefEXCEPTION`. The model returns an `outOfRange` error.

**Impact:** model none. C++: a malformed request ends in `tefEXCEPTION` (not applied, no fee) instead of a `tec`. Not reachable with real funds (the holder does not own those shares), and the throw comes before the holder-balance check.

**Test:** `sweepPayoutRange` in `LeanVaultWithdraw_test.cpp` runs and passes, counting both as "reject".

**Possible actions (undecided):** report to C++ (catch the range error or check representability, return a `tec`). After a C++ fix, map the model's `outOfRange` to the same `tec` and compare TERs.

**Status:** open, nothing changed.

## Gap 17: MPT multiply follows the MPTokensV2 path

**Side:** model, by design.

**Gap:** `STAmount.mulRoundImpl` (`STAmount.lean`) always uses `Number` for an MPT result. C++ does that only under MPTokensV2 (`STAmount.cpp:1559`, not supported, off by default); otherwise it uses the legacy path, which throws on intermediate overflow. Divide has no gap: C++ also takes the `Number` path under `fixCleanup3_5_0`.

**Impact:** none on vault or lending. No model transaction calls `STAmount.mulRound`; only its FFI export and `LeanSTAmount` use it. In C++, only `OfferCreate` (DEX) calls it.

**Why:** recorded decision (2026-10-21, handoff section 5): keep the model on the V2 path and run `LeanSTAmount` under supported amendments plus MPTokensV2 (6024 failures to 0). The model has a comment saying so.

**Test:** `LeanSTAmount_test` under MPTokensV2, passing. Nothing compares the multiply under default rules.

**Possible actions:** keep as decided; recheck if MPTokensV2 changes before it ships. Model the legacy path only if a modelled transaction ever uses `mulRound`.

**Status:** known, by design.
