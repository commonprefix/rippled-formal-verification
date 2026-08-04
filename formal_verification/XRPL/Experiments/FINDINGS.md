# Vault precision: measured results

```
lake exe depositprecision sites fuzz odd seq headroom   # deposit: attribution + drift
lake exe depositprecision single   200000               # deposit: single-execution error
lake exe depositprecision wseq wsites                   # withdraw by shares: drift + attribution
lake exe depositprecision wsingle  200000               # withdraw by shares: single-execution
lake exe depositprecision waseq wasites                 # withdraw by ASSETS: drift + attribution
lake exe depositprecision wasingle 200000               # withdraw by ASSETS: single-execution
lake exe depositprecision worst    20000                # directed worst-case NAV search
lake exe depositprecision span                          # mixed magnitudes vs buffer width
```

Instrumented duplicates of `Vault.deposit` and `Vault.withdraw` (IOU only; both the
by-shares and by-assets withdraw paths) on the real `Number` (19-digit mantissa) and `STAmount` (16-digit mantissa).
`precision : Nat` (0–8) added to the vault; `assetsTotal` round-trips through `STAmount`
and is rounded onto the `10^-precision` grid after every operation. Every rounding site
reports the exact rational it should have produced next to what it stored.

Configurations: (1) baseline, (2) Kahan on the stored total, (3) + NAV reads
`assetsTotal + buffer`, (4) 2 + mul/div residual carrying, (5) all.

**Sample size: 200 000 independent single operations per config per scenario — 8 M
deposits, 8 M by-shares withdraws, 8 M by-assets withdraws.** Results are stable to 4 significant figures from N = 2 000
upward, so 200 000 is well past convergence.

## 1. Single-execution error — the headline

Each sample is one operation on a fresh vault, so nothing accumulates. Absolute figures
are in **units of the asset**, because at 100B a small `precision` makes one ulp real
money.

The measured quantity is **conservation error**: the books (`assetsTotal + buffer`) against
the exact sum of what actually moved on the trust line. It is *not* "total loss in the
operation" — several other error axes stay non-zero even when this one is exactly zero.
See §1a.

### Deposit — conservation error

| scenario | ulp | lossy rate | baseline max | baseline mean | cfg 2–5 |
|---|---|---|---|---|---|
| 100B `p=0` | 1 | 50 % | **0.667** | **0.333** | **0** |
| 100B `p=2` | 0.01 | 67 % | 6.67e-3 | 3.34e-3 | **0** |
| 100B `p=4` (cap) | 1e-4 | 67 % | 3.33e-5 | 2.23e-5 | **0** |
| 123B `p=4` odd shares | 1e-4 | **100 %** | 3.61e-5 | 2.28e-5 | **0** |
| 10M `p=8` | 1e-8 | 70 % | 3.33e-9 | 2.34e-9 | **0** |
| 12M `p=8` odd shares | 1e-8 | **100 %** | 4.67e-9 | 2.74e-9 | **0** |

### Withdraw — conservation error

| scenario | ulp | lossy rate | baseline max | baseline mean | cfg 2–5 |
|---|---|---|---|---|---|
| 100B `p=0` | 1 | 67 % | **0.667** | **0.333** | **0** |
| 100B `p=2` | 0.01 | 67 % | 6.67e-3 | 3.34e-3 | **0** |
| 100B `p=4` (cap) | 1e-4 | 67 % | 7.00e-5 | 3.61e-5 | **0** |
| 123B `p=4` odd shares | 1e-4 | 91 % | 9.00e-5 | 3.74e-5 | **0** |
| 10M `p=8` | 1e-8 | 67 % | 7.00e-9 | 3.61e-9 | **0** |
| 12M `p=8` odd shares | 1e-8 | 91 % | 9.00e-9 | 3.68e-9 | **0** |

### Worst case, from directed search

The maxima above are *sampled* with `sharesTotal = 1.5 × assetsTotal`, i.e. NAV = 2/3. That
quantises the sub-ulp residue in thirds and caps the observed error at 1/3 ulp — an artifact
of the seed, not a bound. Sweeping `sharesTotal` over large primes (`worst` part) gives the
real limits, and they split by regime:

| `assetsTotal` position | grid-down step | baseline worst | cfg 2 primary lag |
|---|---|---|---|
| **at** the 16-digit limit | inert — the 16-digit store already lands on the grid | **0.500 ulp** | 0.999 ulp |
| **below** it, spare mantissa digits | live, drops up to a full ulp | **0.970 ulp** | 0.970 ulp |

So a single operation without compensation loses up to **½ ulp** when `assetsTotal` uses all
16 digits, and up to **1 ulp** when it has mantissa headroom. Conservation with compensation
is 0 in both regimes; the primary field lags by nearly a full ulp in both.

With an IOU worth $1, one ulp is `$10^-p` and capacity is `10^(16-p)`, so choosing `p` as
large as capacity allows puts the worst single-operation conservation loss at roughly
**one part in 10^15 of the vault size** — $0.0001 for a $100B vault at `p=4`, and $1.00 at
`p=0`.

Three things fall out:

**Withdraw is worse per operation than deposit.** On identical scenarios: 0.700 ulp against
0.333 at 100B `p=4`, mean ≈0.36 against ≈0.22. Both roundings on the withdraw path move the
stored total the same way (payout `.downward`, then the total *decreases*), whereas deposit's
`.upward` charge partly opposes the increase — though I have not isolated that mechanism
against the regime split above.

**A non-terminating NAV makes every single operation lossy.** With round `sharesTotal`
the lossy rate is 50–70 %; with odd shares it is 91–100 %. There is no "usually exact"
regime to rely on.

**Compensation zeroes the conservation error, in all 16 M samples.** Exactly 0 —
`0/200000` non-zero — for every Kahan configuration, on both paths, at every scenario
above. Two scope limits on that zero: these scenarios all use a **single deposit
magnitude** (one fixed `amtExpo`), and under mixed magnitudes the compensation itself
loses digits (§4b); and conservation is only one of several error axes (§1a).

## 1a. A single operation is not lossless, even with compensation

Conservation being zero means *the books match what moved*. It does not mean the operation
was exact. Measured worst case for a **single** operation, `p=4` at 100B unless noted:

| axis | worst, with Kahan | does Kahan help? |
|---|---|---|
| conservation (books vs what moved) | **0** | **yes — this is the win** |
| `assetsTotal` alone, i.e. what NAV reads in cfg 2/4 | **0.67–0.999 ulp** behind truth | no, by design — the value sits in the buffer |
| buffer is sub-ulp, so not transferable | up to **1 ulp booked but unpayable** | inherent to the approach |
| deposit price (`chargeStore`, `.upward`) | 6.7e-11; 6.7e-9 on 1e7–1e8 deposits | **no** — identical in all 5 configs |
| withdraw payout (`wStore`, `.downward`) | 6.67e-6; 9.99e-6 on the odd seed | **no** — identical in all 5 configs |
| by-assets request fidelity (§1b) | **½ × NAV** — e.g. $5 at NAV 10 | **no** |
| input alignment (`inputRound`) | up to 1 ulp | intentional; depositor keeps it |
| share truncation (`sharesTrunc`) | <1 share | intentional; accrues to the pool |

Two of these are genuine value transfers present in every single operation and untouched by
compensation: the depositor pays up to ~1e-16 relative more than fair value, and the
withdrawer receives up to ~1e-16 relative less. At 100B that is fractions of a cent per
operation, but it is not zero.

The primary-field lag is not a loss — the value is retained in the buffer — but it is the
reason configs 3/5 (NAV reading both fields) exist, and the reason the buffer cannot be
paid out until it carries.

So the accurate one-line summary is: **compensation makes the vault's books exact; it does
not make the operation exact.**

## 1b. `computeWithdrawByAssets` — a defect compensation cannot touch

The by-assets path is structurally different and it dominates everything else measured.
The caller names an amount of assets; shares are derived and stored **round-to-nearest**
into an integer (`truncateShares = false`), and then the payout is recomputed from that
rounded share count. Unlike `computeDeposit`, which rejects with `tecINTERNAL` when the
recomputed amount exceeds what was offered, **there is no `assetsOut <= assets` guard** —
verified absent in both the Lean model and `VaultHelpers.cpp:412-417`.

So the payout misses the request in *either* direction by up to half a share's value.
200 000 single by-assets withdraws per config per scenario:

| scenario | ulp | over-paid | max over-pay | in ulps | max under-pay |
|---|---|---|---|---|---|
| 100B `p=0` | 1 | 50 % | 0.3333 | 0.3 | 0.3333 |
| 100B `p=2` | 0.01 | 50 % | 0.3333 | 33 | 0.3333 |
| 100B `p=4` | 1e-4 | 50 % | 0.3333 | **3 333** | 0.3333 |
| 10M `p=8` | 1e-8 | 52 % | 0.3333 | **33 333 034** | 0.3333 |

The absolute error is **identical across every precision** — it is not a precision
phenomenon at all. Expressed in ulps it looks catastrophic at `p=8` purely because the ulp
shrank while the error did not.

**The magnitude is `½ × NAV`, exactly.** Confirmed with directed probes rather than
inferred:

| NAV | predicted ½·NAV | measured max over-pay |
|---|---|---|
| 10 | 5 | **4.9917** |
| 2/3 | 0.3333 | **0.3333** |
| 0.1 | 0.05 | **0.04998** |

So a vault with few, valuable shares over-pays proportionally: at NAV = 10 that is **$5
handed out beyond the request, on ~50 % of withdrawals**. That is five orders of magnitude
larger than every rounding effect in this study.

**All five configurations are identical here**, to every digit. Kahan still keeps the books
exact — conservation error is 0 on this path too — so this is not an accounting leak. It is
a *request-fidelity* defect: the books correctly record a payout that was the wrong size.
No amount of compensation addresses it; it needs the missing guard (and a decision about
whether to round the share count down rather than to nearest).

## 2. What this costs at 100B

`assetsTotal = 100B` has 12 integer digits, so with a 16-digit mantissa **`precision`
cannot exceed 4**. That bounds what is achievable:

Figures are mean **conservation** drift per operation — the books against what actually
moved. Other error axes (pricing, request fidelity) are separate and are not reduced by
compensation; see the list below.

| `precision` | ulp | mean drift / op (no Kahan) | at 1 000 ops/day |
|---|---|---|---|
| 0 | 1 | 0.333 | **≈ $333 / day, $121 k / year** |
| 2 | 0.01 | 3.34e-3 | ≈ $1.22 / year |
| 4 (max) | 1e-4 | 2.2e-5 – 3.6e-5 | ≈ $0.01 / year |

So the exposure is dominated by the *choice of `precision`*, not by the algorithm.
`precision = 0` on a large vault leaks real money one operation at a time; `precision = 4`
is already negligible even with no compensation. Since `p = 4` is the ceiling for 100B,
that is also the floor on achievable drift — you cannot buy more precision by raising `p`.

Compensation is still worth having: it takes the conservation loss from ulp-scaled and
accumulating to bounded by the arithmetic width — around nine orders of magnitude at
`p = 0`. What it does **not** make exact:

* `assetsTotal` read alone still lags truth by up to 0.999 ulp; the difference sits in the
  buffer, which is sub-ulp and therefore not transferable until it carries.
* Deposit pricing (`charged` rounds `.upward`) and withdraw payout (`payout` rounds
  `.downward`) are unchanged by compensation — ~1e-16 relative, a real if tiny transfer
  between users and the pool.
* The by-assets `½ × NAV` over/under-payment (§1b) is untouched.
* Conservation itself is only *exactly* zero for single-magnitude workloads (§4b).

## 3. Which sites round

Fuzz-verified; `0/200` means measured exact, not assumed.

**Never round, both paths, all seeds:** `sharesMul`, `chargeMul`, `sharesTrunc`,
`sharesStore`, `sharesTotalAdd`, `wSharesSub`, `navBufferAdd`, `wKahanY`, and every Kahan
recovery step (`kahanBack`/`kahanBuffer`, `wKahanBack`/`wKahanBuffer`). The share-side
arithmetic is exact because shares are integral, and the Kahan recovery is exact because
Sterbenz applies.

**Deposit, worst single-op error at `p=8`:**

| site | rate | worst |
|---|---|---|
| `totalStore` (19d→16d + grid) | 148–200/200 | **3.33e-9** |
| `totalAdd` | 148/200 | 3.33e-12 |
| `chargeStore` (→16d, upward) | 148–200/200 | 9.55e-16 |
| `sharesDiv` | 0 or 200/200 — seed dependent | 4.96e-18 |
| `chargeDiv` | 148–200/200 | 1.33e-18 |
| `chargeCorr` | 148/400 | 3.33e-36 |

**Withdraw, 123B `p=4`:**

| site | rate | worst |
|---|---|---|
| `wTotalStore` | 200/200 | **3.68e-5** |
| `wTotalSub` | 200/200 | 4.97e-8 |
| `wStore` (payout, downward) | 199/200 | 9.96e-10 |
| `wDiv` | 200/200 | 4.95e-13 |
| `wMul` | 199/200 | 4.97e-2 † |
| `wCorr` | 200/400 | 4.94e-31 |

† `wMul`'s absolute error is in the units of the *product* (`nav × shares` ≈ 2e17), not of
assets. Only `wStore`, `wTotalSub` and `wTotalStore` produce asset-valued results and are
directly comparable. After the division, `wMul`'s contribution shows up in `wStore` at
≈1e-9 — three orders below `wTotalStore`.

**On both paths, storing the total at ledger width dominates by 3+ orders of magnitude.**
All the loss that matters is in the store, not the arithmetic.

`sharesDiv` is a trap worth recording: with `assetsTotal = 10^k` that division is exact,
so a power-of-ten seed reports `0/200` and makes mul/div compensation look pointless for
the wrong reason. `seedVaultAt` exists to avoid it.

## 4. Cumulative drift (sequences)

Conservation error again — the other axes of §1a accumulate too and are not shown here.

| deposits, `p=8` at digit limit | baseline | cfg 2–5 conservation |
|---|---|---|
| 10 | 3.33 ulp | **0** |
| 100 | 33.3 ulp | **0** |
| 1000 | 333.3 ulp | **0** |

| withdraws, 100B `p=4`, random burns | baseline | cfg 2–5 conservation |
|---|---|---|
| 1000 | 337.9 ulp = **0.0338 units** | **0** |

Baseline drift is exactly linear in `n` on both paths. Every Kahan configuration is
exactly zero at every length — for these single-magnitude workloads.

## 4b. Mixed deposit magnitudes: the compensation loses its own digits

The zeros above hold only while every deposit shares a magnitude. The fold-in step
`y = charged + buffer` has to represent digits from `charged`'s top down to the buffer's
bottom inside a 19-digit `Number`:

* with **one magnitude**, the buffer's lowest digit *is* `charged`'s lowest digit, so the
  span is ~16 digits and always fits — `kahanY` is exact;
* with **mixed magnitudes**, the buffer retains fine digits from a small deposit while a
  large one raises the top. Once the span exceeds 19 digits the buffer's low digits are
  destroyed, and that loss is unrecoverable because it is the compensation itself being
  truncated.

400 deposits, `p = 0`, `assetsTotal` = 100B, config 2:

| deposit magnitudes | `kahanY` rounds | worst | conservation | baseline |
|---|---|---|---|---|
| single magnitude (control) | **0/400** | 0 | **0** | 316.3 units |
| 1e7…1e8 mixed with 1…10 | **199/400** | 4.79e-11 | **7.44e-11** | 231.4 units |
| 1e10…1e11 mixed with 1…10 | **197/400** | 4.00e-8 | **3.42e-7** | 209.3 units |

The per-event loss is ≈ `top(charged) × 10^-19`, i.e. the `Number` ulp, which is what
identifies the span as the cause. `kahanBack` and `kahanBuffer` stay exact (0/400)
throughout, so the leak is specifically the fold-in, not the recovery.

So the accurate general statement is: **compensation reduces conservation error from
linear-in-`n` and ulp-scaled to bounded by the `Number` mantissa width** — still a factor
of ~6e8 on the worst case above, but not identically zero. The floor is set by the
arithmetic width, not by `precision`, so raising `precision` does not move it.

Practical consequence: the buffer's *effective* width is
`19 − (span of deposit magnitudes in decades)`. A vault seeing both 1e11 and 1e0 deposits
has roughly 8 digits of working compensation rather than 19.

Run it with `lake exe depositprecision span`.

## 5. What each approach buys

**Kahan on the stored total — the entire win.** Conservation error goes from
linear-in-`n` and ulp-scaled to bounded by the arithmetic width: identically zero for
single-magnitude workloads, and ≤ ~3.4e-7 units in the worst mixed-magnitude case measured
(§4b), against 209–333 units for the baseline. The primary field alone (what NAV reads in
configs 2/4) stayed within **0.999 ulp across all 16 M samples** — the `[0, ulp)` buffer
bound held empirically everywhere.

**mul/div residual carrying — no measurable benefit.** Config 4 ≡ config 2 and 5 ≡ 3 to
every digit printed, on every scenario, including odd seeds where both divisions round
200/200. The residuals are ~1e-13 to ~1e-31, orders below the store error. Not worth
building.

**NAV including the buffer — free, and helps at scale.** `navBufferAdd` never rounds, so
it costs nothing. No effect on conservation, but it keeps the value NAV reads close to
truth: over 1000 random deposits the primary-vs-truth gap drops from 9.997e-9 (≈1 ulp) to
3.98e-13. Worth taking.

**Mantissa headroom is not a substitute.** 1–4 spare digits leave baseline drift at
55–67 ulp over 100 deposits (against 33 with none — not even monotone).

## 6. Three conditions the compensation depends on

**The Kahan add/subtract must round away from the stored value.** With `.to_nearest` on
`assetsTotal + y`, the sum overshoots, `t` exceeds the true total, and the buffer goes
**negative** — measured, not theoretical. A negative buffer means `assetsTotal` overstates
holdings, the shortfall-on-withdrawal direction. `.downward` fixes it and holds the buffer
in `[0, ulp)` on every run.

**`precision = p` hard-caps the vault at `10^(16-p)`.** Seeded at
`assetsTotal = 99999999.99999999` with `p = 8`, deposits push past `10^8`, the stored
exponent has to rise, and the buffer grows to ≈9.9 ulp instead of staying below 1. The run
is flagged `OVER CAPACITY(200/200)` and the buffer violation coincides exactly with it. An
implementation must reject operations that would exceed `10^(16-p)`.

**The fold-in `charged + buffer` is exact only while the magnitude span fits the
arithmetic width.** Measured in §4b: mixing 1e10-scale and 1e0-scale deposits makes
`kahanY` round on ~half of all operations and conservation stops being exactly zero. This
is a property of how wide the arithmetic is, not of the rounding modes or the capacity
bound, so it is a third independent condition rather than a variant of the other two.

## 7. Incidental: a landmine in the model

`Number.zero` carries `exponent_ = -2147483648`, and `Number.toRat` builds
`10 ^ (-exponent)` for negative exponents. So `Number.toRat Number.zero` tries to
construct a power of ten with ~2.1 billion digits and never returns. This made the
experiment appear to cost ~1 minute per deposit until it was found; guarding it via
`numRat` / `staRat` took 125 deposits from >300 s to 6 ms.

Any code path that can hand a zero `Number` to `toRat` is exposed.
