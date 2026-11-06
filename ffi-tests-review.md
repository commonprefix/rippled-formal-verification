# Review: `wip: sav ffi tests` (8d3bda290, ms4-ffi)

Reviewed from the commit only (`git show`), against the model at the same commit
(`formal_verification/XRPL/Model/Vault/*`) and the C++ transactors at the same commit.
The working tree was not used.

## Verdict

The port is sound. Every FFI export matches the model signature and the `TerExcept`
decoding (outer `Error`, inner `TER`) is right, the SLE-to-model field mapping is right,
and every recalibrated expectation I recomputed by hand agrees with the model. The problems
are latent divergences and coverage holes for the new model branches, not wrong results.

## Findings

### 1. Loss waiver is not derived from sole-shareholdership (medium, latent divergence)

C++ `VaultClawback::assetsToClawback` (fix340) waives the unrealized loss when the holder
is the sole shareholder, and `VaultWithdraw` does the same (fixCleanup3_2_0) for the
withdrawer. The harness never computes this:

- `leanVaultClawback(state, amount, holderShares)` always sends `waiveUnrealizedLoss = false`
  (`VaultClawbackFFI.h`), and no clawback test passes anything else.
- `compareWithdraw` defaults it to `false`; only `testWithdrawWaiveLoss` and
  `testWithdrawFinalWithLoss` pass `true` by hand.

Every current case has `lossUnrealized == 0`, so the two NAVs coincide and nothing fails.
The first staged clawback (or withdraw) with a loss and a sole holder will diverge silently,
and for an amount-0 clawback the model would burn `holderShares` where C++ burns
`sfOutstandingAmount`. Compute `holderShares == outstanding` in the harness and pass it on
both paths instead of hand-setting it per test.

### 2. `Vault.create` accepts a `scale` for XRP/MPT; C++ preflight rejects it (medium, untested gap)

`VaultCreate::preflight` returns `temMALFORMED` when `sfScale` is present on a native or MPT
asset. The model's `Vault.create` zeroes the scale and returns a lawful vault. The create
harness asserts "preflight `tem` implies model `notLawful`", which this input breaks, and no
case exercises it. Either add the case and reject it in the model or FFI, or narrow the
comment. Also untested on create: `AssetsMaximum = 0` (C++ stores nothing, model filters to
`none`) and a negative maximum (`tem`, model `notLawful` via `assetsMaximum_pos`).

### 3. New model branches without a differential test (medium, coverage)

- Deposit `tecEXPIRED` in the investment or redemption phase; deposit `tecLOCKED` via
  `depositBlocked`.
- Withdraw `tecTOO_SOON` (investment phase, no fee rate); the early-exit-fee payout
  (investment phase with a rate, including the 100% rate that zeroes the payout and the
  `tecPRECISION_LOSS` when the fee eats it).
- VaultSet `tfVaultDepositBlock` / `tfVaultDepositUnblock`: neither the `tecNO_PERMISSION`
  branch nor the `lsfVaultDepositBlocked` state change. `lean_vault_update` is exported but
  has no C++ caller, so the Set suite never compares post-state.
- `yieldUnrealized` in the open-limit capacity (`exceedsOpenLimit` adds it; it is never
  nonzero in a test). `assetsReserved` and `yieldUnrealized` are read back but never compared
  after a transaction.
- `LeanVault_test` has no `sharesTotal_representable` case (shares above `INT64_MAX`).

### 4. Post-state is read after `env.close()` in two comparators (low, fragility)

`compareWithdraw` was changed to read the C++ state before closing because a close discards
staged open-ledger edits. `compareClawbackAsset` and `compareVaultDeposit` still read after
the close. It is safe today only because no staged clawback or deposit case expects
`tesSUCCESS`; the next one would compare the model against the replayed, unstaged ledger.
Make all three read before the close.

### 5. `VaultFFI::read()` turns a failed derived total into 0 (low)

`assetsTotal = total.value ? total.value->read() : Number{}` maps a model overflow in
`assetsAvailable + assetsDeployed` to a total of 0, which can produce a misleading pass or
failure. `readVaultState` throws for a missing vault; do the same here, or carry an optional.

### 6. Stale comments and names (low)

- `runTests` still lists `testWithdrawDrainsVault`, `testWithdrawAppliedDelta`,
  `testClawbackAppliedDelta` under "Known discrepancies, each fails until the C++ code is
  fixed", while their bodies say both sides agree and they pass.
- The testcase names "withdraw/clawback moves the vault totals by a different amount than paid
  out/recovered" and the `runTests` comments "totals move by more than paid out (both)"
  contradict the function comments "move by exactly what the holder receives".
- `testDepositOvercredit` says "+5 would need 17 digits"; the rejection is the open limit
  (9e5 at scale 10, seed 899999.9999999999 + 5 > 9e5). Same TER, wrong explanation.
- FV_M2_16 is now only reachable from a staged state past the open limit, so it documents
  an unreachable state and is no longer a finding; fine as a model check, say so.

## Verified correct

- All eight Lean exports match the model (`deposit`/`withdraw` take `parentCloseTime`,
  `clawback` takes `waiveUnrealizedLoss`, `canBurnShares` takes `amount holderShares`,
  `canVaultUpdate` takes the two flags, `canCreate`/`create` take the schedule as two
  options). `TenthBips32` is an `abbrev` of `UInt32`, so the `Option UInt32` boundary is exact.
- `initialize_XRPL_XRPL_FFI_FFI(uint8_t builtin)` matches the Lean 4.30 generated C
  (`.lake/build/ir/XRPL/FFI/FFI.c`).
- `readTerCode` / `TerExceptFFI` decode `Except Error Int32` and `Except Error (Except TER α)`
  with the right tags; `LeanError` ordinals match `Protocol.Error`.
- SLE mapping: `getAssetsTotal` (available + deployed), `sfAssetsDeployed`, `sfAssetsReserved`
  (SoeDefault), `sfYieldUnrealized`, optional `sfSubscriptionDate`/`sfRedemptionDate`,
  `sfEarlyExitFeeRate` stored as submitted including zero and absent otherwise (model:
  `earlyExitFeeRate'`), `lsfVaultOwnerCanBlockDeposit`, `lsfVaultDepositBlocked`.
  `parentCloseTime(env)` is the clock `getVaultPhase` reads.
- Check ordering matches C++ in all five transactors: deposit (EXPIRED, NO_PERMISSION, LOCKED,
  LOCKED, PRECISION_LOSS, INTERNAL, PATH_DRY, open limit, LIMIT_EXCEEDED); withdraw (TOO_SOON,
  PRECISION_LOSS, HAS_OBLIGATIONS, by-shares zero, dust, INSUFFICIENT_FUNDS, fee block, final
  clamp); clawback (clamp to available, HAS_OBLIGATIONS, outflow clamp, PRECISION_LOSS on zero
  shares, dust); set (grid, NO_PERMISSION, LIMIT_EXCEEDED); delete (available, total, shares).
  The C++ holder share-balance check before the fee block is outside the model; no current
  case redeems more shares than the holder has.
- Recomputed expectations: IOU 9e9 + 1e-6, MPT 9e15 - 1 + 2 and XRP 9e15 + 1 drops hit
  `tecLIMIT_EXCEEDED` through `exceedsOpenLimit`; the staged FV_M2_15 withdraw (6e-6 from
  1.2345678901234560e10) converts to 6 shares, passes the dust check, and the clamp to the
  1e-5 grid floors it to 0, hence `tecPRECISION_LOSS`; FV_M2_13 and the `(iouMax, 1e50, 1, 1)`
  case are final withdrawals with `assetsDeployed != 0`, hence `tecHAS_OBLIGATIONS`; the
  `(1000, 100, 1e9, 5e8)` case asks 500 from 100 available; the drain case pays 1e17 and
  leaves a lawful insolvent vault on both sides.
- `stageVaultHolding` negates the balance when the pseudo-account is the high account, the
  trust-line convention. `updateVaultState` and `stageSoleHolderVault` keep the `sfAssetsTotal`
  cache equal to available + deployed, which the owner-burn preclaim still reads directly.
- `LeanVault_test` clause coverage is correct for the new invariant (cap no longer a vault
  invariant; loss ≤ deployed; reserved ≤ deployed; 17-digit deployed not representable;
  schedule gap bounds; fee only on closed-ended, ≤ 100%).

---

# Review: `feat: vault open/closed ended ffi tests` (3966fbba5, ms4-ffi)

One new file, `src/test/formal_verification/tx/vault/LeanVaultClosedEnded_test.cpp` (471 lines),
reviewed from the commit against the model and C++ at the same commit. I did not build or run it.

## Verdict

Correct and well targeted. It closes the main coverage hole from the previous review (deposit
`tecEXPIRED`, withdraw `tecTOO_SOON`, the early-exit fee including the 100% rate and the two
fee-eats-payout paths). Every expected TER and payout I recomputed agrees with both the model and
the C++ (see "Verified" below). What remains are boundary and branch gaps and one misleading helper.

## Findings

### 1. No phase-boundary case (medium, coverage)

The phase is derived with `>` on the subscription date and `>=` on the redemption date on both
sides (C++ `hasExpired(..., Exclusive)` vs default Inclusive; model `Vault.phase`). All cases sit
600 s or 1e6 s away from the boundary, so the one place the two encodings could disagree is never
exercised. Add cases closed at exactly `subscriptionDate` (still Subscription: deposit succeeds,
withdraw without a fee succeeds) and exactly `redemptionDate` (Redemption: withdraw without a fee
succeeds, deposit `tecEXPIRED`). Assert `parentCloseTime(env)` equals the date first, since the
close time may be rounded to the ledger resolution.

### 2. The fee-dependent `tecINSUFFICIENT_FUNDS` branch is untested (medium, coverage)

With a zero rate, C++ and the model reject when the pre-fee amount exceeds `assetsAvailable`.
With a nonzero rate both skip that check and compare the post-fee payout instead, so a withdrawal
whose gross exceeds the available balance but whose net does not succeeds. This needs
`assetsAvailable < assetsTotal` (stage deployed assets with `updateVaultState`): the same request
should give `tecINSUFFICIENT_FUNDS` at rate 0 and `tesSUCCESS` at 50%. Also untested: a by-shares
withdrawal under a fee (the model's by-shares zero-payout check runs before the fee block), and a
fee that is inexact at 16 digits (a 16-digit amount at scale 10 with a two-digit rate), which is
where the C++ `Upward` fee / `Downward` subtraction pair and the model's `.upward` / `.downward`
could drift.

### 3. `leanTer` maps every model error to `tefEXCEPTION` (low, misleading)

`leanTer` returns `tefEXCEPTION` for any `leanError`, with the comment "a model raise surfaces as
tefEXCEPTION, matching the C++ transactor". A `notLawful` means the model's post-state violates
the invariant and a `badInput` means the preflight precondition failed; neither corresponds to a
thrown C++ exception, and `expectLawful` already asserts `notLawful` away just before. The mapping
is only reached after that assertion has failed, so it is harmless, but the comment claims an
equivalence that does not exist. Prefer the pattern of the other suites: `error.value_or(tesSUCCESS)`
plus an explicit `BEAST_EXPECTS(!leanError)`.

### 4. Small things (low)

- `compareDeposit` and `compareWithdraw` read the C++ post-state after `env.close()`. Nothing is
  staged in this suite so it is safe, but it is the same fragility as in the other suites; if
  finding 2 is added with staging, read before the close.
- `expectSameVault` compares total, available, shares and loss only; `assetsDeployed`,
  `yieldUnrealized` and `assetsReserved` are unchecked (all zero here). Fine for now.
- `holderShares` duplicates `fetchHolderShares` in the clawback suite; move one to
  `VaultTestHelpers.h`.
- The sole shareholder is the withdrawer and clawback target in every case, so C++ waives the
  loss while the harness passes `false`; harmless with zero loss (see finding 1 of the previous
  review).

## Verified

- Phase gates: deposit `tecEXPIRED` in Investment and Redemption, donation exempt in all four
  phases; withdraw `tecTOO_SOON` only in Investment without `sfEarlyExitFeeRate`; a zero rate
  stored as present opens Investment (C++ `isFieldPresent`, model `earlyExitFeeRate.isNone`).
- Fee arithmetic: 400 at 5% in Investment pays 380 and burns the shares for 400 on both sides;
  5% in Subscription and Redemption pays 400 (`earlyExitFeeRateAt` is 0 outside Investment);
  100% zeroes the payout and succeeds; a final withdrawal (all shares) skips the fee block and
  pays 1000.
- Fee-eats-payout: one drop at 50% gives a 0.5-drop payout that rounds `Downward` to zero, hence
  `tecPRECISION_LOSS` on both sides. One IOU grid unit (1e-6) at 50% gives a 5e-7 payout that
  the outflow clamp floors to zero on the 1e-6 base grid (`clampToSumExponent` with
  `postSumExponent` = max(-6, -7)), hence `tecPRECISION_LOSS` on both sides.
- Clawback, set and delete have no phase logic in C++ or the model; the three closed-ended cases
  are correct (issuer clawback needs `asfAllowTrustLineClawback`, set before the trust lines).
- Fixture: `createClosedEnded` and `closePastSubscription` give both sides the same
  `parentCloseTime`, so even if close times are rounded the TER comparison stays valid.

---

# Resolution check (working tree after both reviews, 2026-10-20)

Ran the eight vault FFI suites on the rebuilt `build/xrpld` (binary newer than every changed
source): 8 suites, 203 cases, 7666 checks, 0 failures (19.6 s).

## Review 1

| # | Finding | Status |
|---|---|---|
| 1 | Waiver from sole-shareholdership | Fixed: `holderOwnsAllShares` mirrors C++ `isSoleShareholder` (false at zero outstanding) and feeds every comparator and direct clawback/withdraw call, except `testSharesToAssets` (`LeanVaultWithdraw_test.cpp:244`), which still omits it. Harmless there (sole holder, zero loss), but inconsistent. |
| 2 | Create: scale on XRP/MPT, zero/negative maximum | Fixed as documented gaps: `outsideModel` flag asserts the model normalizes an integral-asset scale; zero and negative maximum cases added and passing. |
| 3 | Coverage of new branches | Fixed: blocked-deposit `tecLOCKED`, Set block/unblock with `leanVaultUpdate` and state compare, yield in the open-limit capacity (two staged MPT cases at 9e15-10 with yield 10 and 9), shares above INT64_MAX. |
| 4 | Read before close | Fixed in deposit, clawback, Set and closed-ended comparators. |
| 5 | Derived total error swallowed | Fixed: `VaultFFI::read` throws. |
| 6 | Stale comments | Fixed in Deposit and Withdraw. **Not fixed in Clawback**: `runTests` still says "Known discrepancies, each fails until the C++ code is fixed" over four passing tests, and `testClawbackAppliedDelta` is still named "moves the vault total by a different amount than recovered" while its body says it moves by exactly the recovery. |

## Review 2

| # | Finding | Status |
|---|---|---|
| 1 | Phase boundaries | Fixed: dates aligned to the close-time resolution, `closeExactlyAt` asserts the parent close time; deposit and withdraw cases at exactly the subscription date (still Subscription) and the redemption date (already Redemption) pass. `Env::close` adds resolution-1 s, so `at - resolution + 1 s` lands on `at`. |
| 2 | Fee-dependent insufficient funds, by-shares, inexact fee | Fixed: staged 390 available of 1000, 400 by assets fails at rate 0 and pays 380 at 5%; 4e8 shares at 5% pay 380; 16-digit amount at 3.333% agrees on both sides. |
| 3 | `leanTer` maps model errors to `tefEXCEPTION` | Fixed: explicit `leanError` expectations, TER from `error.value_or(tesSUCCESS)`. |
| 4 | Small things | Fixed: `fetchHolderShares` shared in `VaultTestHelpers.h`; `expectSameVault` compares deployed, reserved and yield; reads before close. |

## Remaining

- Clawback `runTests` block and the applied-delta testcase name (review 1, finding 6).
- `testSharesToAssets` passes no waiver (review 1, finding 1), cosmetic today.

---

# Review: LoanBroker and Loan FFI tests (working tree, 2026-10-21)

Scope: `formal_verification/XRPL/FFI/Lending/{LoanBroker,Loan}.lean`, `ffi/lending/{LoanBrokerFFI,LoanFFI}.h`,
`tx/lending/LendingTestHelpers.h` and the six suites `LeanLoanBroker`, `LeanLoanBrokerCover`, `LeanLoan`,
`LeanLoanSet`, `LeanLoanPay`, `LeanLoanManage`; the `LeanSTAmount` rules guard; the vault-suite follow-ups.
Checked against the lending model (`Model/Lending/**`) and the C++ transactors in the same tree.

Run on the current `build/xrpld` (newer than every source): 18 suites, 411 cases, 3,968,985 checks, 0 failures
(41 s). The two leftovers of the previous reviews are closed (clawback headers and names reworded, every
withdraw/clawback model call passes `holderOwnsAllShares`).

## Verdict

The port is faithful. Every export matches the model signature, the ledger-to-model mapping is right
(`loanCount` is the broker's `sfOwnerCount`, which is also the C++ delete gate; `sfPaymentTotal` is carried by
the test; the four loan flags map to `lsfLoan*`), the preclaim/doApply split (`modelVerdict`) follows the C++
division, and the TER orderings agree arm for arm (see "Verified"). One model-level clock defect is masked by
the fixtures and should be fixed before boundary cases are added.

## Findings

### 1. `Loan.canCreate` uses one clock where C++ uses two (medium, model)

C++ `LoanSet` reads the open ledger's `header().closeTime` for exactly one thing, the one-step loan's start date
(`getStartDate`). Everything else is on the parent close time: the two-step expiry (`hasExpired(view, StartDate)`)
and the vault phase inside `checkVaultAcceptsLoan` (`getVaultPhase` → `parentCloseTime`). The model's
`Loan.canCreate` takes a single `ledgerCloseTime` and uses it for all three (`LoanSchedule.build`, the
`twoStep && hasExpired` test, and `canFundLoan`'s `AssetPool.phase`). The harness passes `ledgerCloseTime(env)`,
so the model evaluates expiry and phase at the header close time, which differs from the parent close time by up
to a close-time resolution in a test `Env`. Every current case sits hundreds of seconds from a boundary, so
nothing fails. A two-step proposal whose start date falls between the two clocks, or a vault whose subscription
date does, would give `tesSUCCESS` on one side and `tecEXPIRED`/`tecTOO_SOON` on the other.

Fix in the model: give `Loan.canCreate` (and the FFI export) both `parentCloseTime` and `ledgerCloseTime`; use
the first for expiry and phase, the second only in `LoanSchedule.build`. Then add the boundary cases the
closed-ended vault suite already has (start date exactly at the parent close time; subscription date exactly at
the parent close time). `Loan.canAccept`'s parameter is also named `ledgerCloseTime` although its C++
counterparts (`hasExpired`, `getVaultPhase`) are on the parent close time; the harness passes
`parentCloseTime(env)` there, which is right, so only the name is wrong.

### 2. Loan configuration fields are copied, never compared (low, harness)

`LoanFFI::read(like)` copies rates, fees, schedule and `startDate` from the test's template because the model
never changes them, and `expectLoanMatches` compares only the accounting fields. On a LoanSet success the C++
SLE's `sfStartDate`, `sfPaymentInterval`, `sfGracePeriod` and the rates/fees are read by `readLoanState` but
not checked against the template, so a default drift (grace period, interval) or a wrong start-date clock would
only show up indirectly through `nextPaymentDueDate`. Add the comparison in `compareLoanSet`; it is one block.

### 3. The `LeanSTAmount` guard commits the model to an unsupported amendment (info, decision to record)

The suite now runs under every supported amendment plus `MPTokensV2`, because the model's int64 multiply follows
the V2 `Number` path. The transaction suites run under the default rules without it. For the MPT vault and loan
cases both sides agree, so the paths coincide on those values, but they differ exactly where C++ throws on an
intermediate overflow (the model returns a value). That is the one place an MPT transaction case could diverge
in the vault/loan suites; the coverage report's unhit overflow arms are consistent with it never being reached.
The handoff records the decision (section 5); the model's `STAmount.mulRound` should carry a one-line note too.

### 4. Out-of-model C++ conditions the fixtures avoid (info)

LoanPay sends the fee to the owner only if the cover meets its minimum **and** the owner is neither deep-frozen
nor unauthorized (`sendBrokerFeeToOwner`); LoanPay's preclaim rejects a borrower without funds
(`tecINSUFFICIENT_FUNDS`); LoanManage and LoanDelete check the submitter. The model has none of these (account
state), and no fixture triggers them. Fine as long as nobody reads "the model covers LoanPay" as covering them.

### 5. Nits (low)

- `paymentTypeOf`/`manageActionOf` map an unknown tag to `regular`/`impair` silently; the C++ enums are closed
  so it cannot happen today.
- `LeanLoanBroker_test::runCreate` reads the broker after `env.close()`; nothing is staged, fine.
- `BrokerFixture.redemptionDate` is recomputed as `subscriptionDate + investmentWindow`; equal to what
  `createClosedEnded` wrote, but reading it back from the SLE would be safer.

## Verified

- Exports: `lean_loan_broker_build` / `lean_loan_build` cover every raw field (`TenthBips16` is `UInt16`,
  `loanScale` crosses as `Int32`); the per-transaction exports match `canCreate/create/canUpdate/update`,
  `canCover{Deposit,Withdraw,Clawback}/cover*`, `canDelete/roundedCoverAvailable`, `canCreate/create`
  (`twoStep` → `pending`), `canAccept/accept`, `canPay/{regular,late,full,overpayment}Payment`,
  `canManage/manage{Impair,Unimpair,Default}`, `canDelete/delete`; `withZeroAmounts` gives accept, impair and
  unimpair the `LoanWithAmounts` shape; `TerExcept` decoding reuses the vault pattern.
- LoanSet doApply order is identical on both sides: `tecINSUFFICIENT_FUNDS` (available < principal),
  properties, the Legacy-only vault-maximum arm (a no-op under fixed precision, correctly absent from the model),
  `tecPRECISION_LOSS` at the loan scale, the four amortization guards, `tecINTERNAL` sanity, the open-limit
  `tecLIMIT_EXCEEDED`, the debt-maximum `tecLIMIT_EXCEEDED`, the cover `tecINSUFFICIENT_FUNDS`. Preclaim's
  precision check is representability on both sides (`STAmount{asset, v} != v` vs `!isRounded`).
- `canFundLoan` = `checkVaultAcceptsLoan`: phases, the `finalPayment + 60 > redemptionDate` buffer with the
  same strict comparison, and the coarsened-scale `tecLIMIT_EXCEEDED`.
- LoanAccept: the Legacy-only vault-maximum arm is absent from the model as it should be; the fixed-precision
  open-limit arm is present; `testAcceptPastOpenLimit` stages the yield so it fires.
- LoanManage: default's `tecTOO_SOON` uses the exclusive comparison under fixCleanup3_4_0, the model's
  `now > gracePeriodEnd`; the pre-fix340 due-date rewrites on impair/unimpair are gated off, so the model's
  flag-only `changeImpairment` is right. `defaultCoveredAmount` mirrors the C++ (min of liquidation amount,
  default amount and cover, truncated, then floor-summed into the vault).
- LoanPay: fee-into-cover floors the sum (`creditToPosteriorBrokerCoverScale` vs `sumRoundAndSubtract`); the
  `amountToBroker` check (cover delta plus owner balance delta) covers both destinations;
  `testFeeIntoCover` reaches the cover branch by draining it through a 100% liquidation default.
- Cover transactions: deposit (`roundedCoverAmount` dust, then base-exponent and open-limit
  `tecLIMIT_EXCEEDED`), withdraw (dust, available, minimum cover) and clawback (`maxClaw ≤ 0` →
  `tecINSUFFICIENT_FUNDS`, clamp, dust) match the C++ preclaims; the amount-absent and amount-zero clawbacks
  both claw the excess.
- LoanBrokerSet preflight ranges (fee ≤ 10%, cover rates ≤ 100%, debt maximum in `[0, 2^63-1]`, rates coupled)
  equal the model's lawfulness clauses; no ordering between the two cover rates on either side.
- Coverage report: three "unreachable" classifications spot-checked (VaultClawback L39, LoanAccept L19/L20,
  LoanSet L44) and they hold.

---

# Resolution check: lending review (working tree, 2026-10-21 evening)

Ran the six lending suites on the rebuilt `build/xrpld` (newer than every changed source): 147 cases, 10,317
checks, 0 failures.

| # | Finding | Status |
|---|---|---|
| 1 | One clock in `Loan.canCreate` | Fixed in the model: `Loan.canCreate` and `canFundLoan` take `parentCloseTime` for expiry and phase, `LoanSchedule.build` keeps `ledgerCloseTime` for the one-step start date; `Loan.canAccept` renamed to `parentCloseTime`. The FFI export and `leanCanLoanCreate` take both clocks; the harness passes `ledgerCloseTime(env)` and `parentCloseTime(env)`. Five boundary cases added and passing: a two-step proposal starting exactly at the parent close time (`tecEXPIRED`) and one second after it (`tesSUCCESS`), which discriminate the two clocks; LoanSet exactly at the subscription date (`tecTOO_SOON`) and at the redemption date (`tecEXPIRED`); LoanAccept exactly at the start date (`tecEXPIRED`). `setUpBrokerVault` now aligns the schedule dates to the close-time resolution so the exact closes land. |
| 2 | Configuration fields not compared | Fixed: `expectLoanMatches` compares the five rates, the four fees, the interval, the grace period and the start date against the ledger. |
| 3 | MPTokensV2 note at the multiply | Fixed: the comment on `STAmount.mulRoundImpl` names the amendment. |
| 4 | Out-of-model conditions | Informational, nothing to do. |
| 5 | Nits | Not addressed, none required. |

## New nit

`closeExactlyAt` and the date alignment now exist twice: as `closeExactlyAt`/`alignedTime` in
`LendingTestHelpers.h` and as a member plus an `alignUp` lambda in `LeanVaultClosedEnded_test.cpp`. Since the
lending helper already includes the vault helper, move the two functions to `VaultTestHelpers.h` and drop the
copies in the closed-ended suite. Low.

---

# Final review (working tree over fccb9e877, 2026-10-22)

Run on the current `build/xrpld` (newer than every source): 18 suites, 416 cases, 3,969,632 checks, 0 failures.

- The lending clock fix, the configuration-field comparison, the multiply note and the helper dedup
  (`timeCount`/`alignedTime`/`closeExactlyAt` now in `VaultTestHelpers.h`, used by both closed-ended fixtures)
  are the only changes over the commit; all reviewed and correct.
- `clang-format --dry-run -Werror` is clean on every committed and modified test file.
- No proof module under `XRPL/Properties` references `Loan.canCreate` / `Loan.canAccept`, so the signature change
  breaks nothing outside the model and the FFI.
- The commit contains no tool state or reports. Three `.omc/` directories now sit in the tree (`.omc`,
  `formal_verification/XRPL/.omc`, `src/test/formal_verification/tx/.omc`): keep them out of the next commit
  (a global git exclude for `.omc/` is the simplest).
- The six disabled cases in the vault suites (FV_M2_7, FV_M2_8_c, FV_M2_9, FV_M2_15_b, FV_M2_18, FV_M2_19_b) are
  the open C++ discrepancies, each labeled; nothing else is commented out, no debug output remains.
- Doc nit: `ffi-tests-handoff.md` still opens with "LoanBroker/Loan tests (to do)" and "Status (2026-10-20)"
  while its body records both as done on 2026-10-21.

Nothing blocks a commit of the working tree.
