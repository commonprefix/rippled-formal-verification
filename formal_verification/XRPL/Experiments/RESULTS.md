# Vault precision — results

Real `Number` (19-digit) / `STAmount` (16-digit), IOU only. `precision = p`, ulp = `10^-p`,
capacity = `10^(16-p)`. 200 000 single operations per config per scenario.
Detail and method in `FINDINGS.md`.

| cfg | Kahan on store | mul/div residual | NAV reads |
|---|---|---|---|
| 1 | – | – | `assetsTotal` |
| 2 | ✓ | – | `assetsTotal` |
| 3 | ✓ | – | `assetsTotal + buffer` |
| 4 | ✓ | ✓ | `assetsTotal` |
| 5 | ✓ | ✓ | `assetsTotal + buffer` |

## Single operation — conservation error, in asset units

Deposit

| scenario | ulp | lossy | base max | base mean | cfg 2–5 |
|---|---|---|---|---|---|
| 100B `p=0` | 1 | 50 % | **0.667** | **0.333** | **0** |
| 100B `p=2` | 0.01 | 67 % | 6.67e-3 | 3.34e-3 | **0** |
| 100B `p=4` | 1e-4 | 67 % | 3.33e-5 | 2.23e-5 | **0** |
| 123B `p=4` odd | 1e-4 | 100 % | 3.61e-5 | 2.28e-5 | **0** |
| 10M `p=8` | 1e-8 | 70 % | 3.33e-9 | 2.34e-9 | **0** |
| 12M `p=8` odd | 1e-8 | 100 % | 4.67e-9 | 2.74e-9 | **0** |

Withdraw by shares

| scenario | ulp | lossy | base max | base mean | cfg 2–5 |
|---|---|---|---|---|---|
| 100B `p=0` | 1 | 67 % | **0.667** | **0.333** | **0** |
| 100B `p=2` | 0.01 | 67 % | 6.67e-3 | 3.34e-3 | **0** |
| 100B `p=4` | 1e-4 | 67 % | 7.00e-5 | 3.61e-5 | **0** |
| 123B `p=4` odd | 1e-4 | 91 % | 9.00e-5 | 3.74e-5 | **0** |
| 10M `p=8` | 1e-8 | 67 % | 7.00e-9 | 3.61e-9 | **0** |
| 12M `p=8` odd | 1e-8 | 91 % | 9.00e-9 | 3.68e-9 | **0** |

## Worst case — directed search over prime `sharesTotal`

| `assetsTotal` | grid-down | baseline | cfg 2 primary lag |
|---|---|---|---|
| at 16-digit limit | inert | **0.500 ulp** | 0.999 ulp |
| below, spare digits | live | **0.970 ulp** | 0.970 ulp |

NAV = 2/3 seeds cap the observed error at 1/3 ulp — seed artifact, not a bound.

## Cost per operation, IOU worth $1

| `p` | ulp | capacity | no buffer | buffer |
|---|---|---|---|---|
| 0 | $1 | $1e16 | **$0.50 – $1.00** | **$0** |
| 2 | $0.01 | $1e14 | $0.005 – $0.01 | **$0** |
| 4 | $1e-4 | $1e12 | $5e-5 – $1e-4 | **$0** |
| 6 | $1e-6 | $1e10 | $5e-7 – $1e-6 | **$0** |
| 8 | $1e-8 | $1e8 | $5e-9 – $1e-8 | **$0** |

100B needs `p ≤ 4`. At the best available `p`: ~1 part in `10^15` of vault size.

## Withdraw by assets — over/under-payment

No `assetsOut <= assets` guard; shares round to nearest, not truncated.

| scenario | ulp | over-paid | max over | in ulps | max under |
|---|---|---|---|---|---|
| 100B `p=0` | 1 | 50 % | 0.3333 | 0.3 | 0.3333 |
| 100B `p=2` | 0.01 | 50 % | 0.3333 | 33 | 0.3333 |
| 100B `p=4` | 1e-4 | 50 % | 0.3333 | **3 333** | 0.3333 |
| 10M `p=8` | 1e-8 | 52 % | 0.3333 | **33 333 034** | 0.3333 |

Identical in all 5 configs. Independent of `p`. Magnitude = ½ × NAV:

| NAV | ½ × NAV | measured |
|---|---|---|
| 10 | 5 | **4.9917** |
| 2/3 | 0.3333 | **0.3333** |
| 0.1 | 0.05 | **0.04998** |

## Rounding sites

Deposit, `p=8`

| site | rate | worst |
|---|---|---|
| `totalStore` | 148–200/200 | **3.33e-9** |
| `totalAdd` | 148/200 | 3.33e-12 |
| `chargeStore` | 148–200/200 | 9.55e-16 |
| `sharesDiv` | 0 or 200/200 † | 4.96e-18 |
| `chargeDiv` | 148–200/200 | 1.33e-18 |
| `chargeCorr` | 148/400 | 3.33e-36 |

Withdraw, 123B `p=4`

| site | rate | worst |
|---|---|---|
| `wTotalStore` | 200/200 | **3.68e-5** |
| `wTotalSub` | 200/200 | 4.97e-8 |
| `wStore` | 199/200 | 9.96e-10 |
| `wDiv` | 200/200 | 4.95e-13 |
| `wMul` | 199/200 | 4.97e-2 ‡ |
| `wCorr` | 200/400 | 4.94e-31 |
| `waMul` | 200/200 | 4.99e-2 ‡ |
| `waDiv` | 200/200 | 4.86e-13 |
| `waSharesStore` | 200/200 | 4.98e-1 ‡ |

Measured exact, all seeds: `sharesMul`, `chargeMul`, `sharesTrunc`, `sharesStore`,
`sharesTotalAdd`, `wSharesSub`, `navBufferAdd`, `kahanBack`, `kahanBuffer`, `wKahanBack`,
`wKahanBuffer`.

† exact when `assetsTotal = 10^k`. ‡ units of the intermediate, not assets.

## Sequences — conservation

| deposits, `p=8` | baseline | cfg 2–5 |
|---|---|---|
| 10 | 3.33 ulp | **0** |
| 100 | 33.3 ulp | **0** |
| 1000 | 333.3 ulp | **0** |

| withdraws, 100B `p=4` | baseline | cfg 2–5 |
|---|---|---|
| 1000 random | 337.9 ulp = 0.0338 units | **0** |

## Mixed deposit magnitudes — 400 deposits, `p=0`, 100B

| magnitudes | `kahanY` rounds | worst | cfg 2 conservation | baseline |
|---|---|---|---|---|
| single (control) | **0/400** | 0 | **0** | 316.3 units |
| 1e7…1e8 + 1…10 | 199/400 | 4.79e-11 | **7.44e-11** | 231.4 units |
| 1e10…1e11 + 1…10 | 197/400 | 4.00e-8 | **3.42e-7** | 209.3 units |

Effective buffer width = `19 − magnitude span in decades`.

## Config differences

| pair | conservation | primary field |
|---|---|---|
| 2 vs 4 (mul/div residual) | identical | identical |
| 3 vs 5 | identical | identical |
| 2 vs 3 (NAV + buffer) | both 0 | 9.997e-9 → **3.98e-13** |

Two distinct outcomes only: with and without `navWithBuffer`. `kahanMulDiv` changes nothing
beyond the 5th significant figure of pricing.

## Rounding modes

| op | deposit | withdraw | status |
|---|---|---|---|
| `y = charged ± buffer` | `downward` | `upward` | reasoned |
| `sum` / `diff` | `downward` | `downward` | **proven** |
| `t = grid(·)` | `downward` | `downward` | **proven** |
| `back` | `downward` | `downward` | inert (exact) |
| `buffer'` | `downward` | `downward` | inert (exact) |

`to_nearest` on `sum`/`diff` drives the buffer negative. `downward`, not `towards_zero`.
Mode must be pinned across all five ops as one guard.

## Conditions the compensation depends on

| condition | if violated | measured |
|---|---|---|
| `sum`/`grid` round downward | buffer negative → total overstates | yes |
| `assetsTotal < 10^(16-p)` | buffer exceeds 1 ulp | 9.9 ulp |
| magnitude span < mantissa width | fold-in loses digits | 3.42e-7 units |
