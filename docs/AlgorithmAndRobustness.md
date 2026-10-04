# Algorithm 1, geometric search, and robustness

## Formalized claims

- `Geometric.lean` proves that the least integer K with q^K ≤ 1/R exists for 0 < ε < 1, q = 1−ε, R ≥ 1. It proves K ≤ ceil(log R / ε) from log(1−ε) ≤ −ε, rather than assuming any geometric-grid property.
- `geometric_cover_of_width` proves that the exact source grid with indices 1,...,K+1 contains a retained share between (1−ε)δ* and δ*.
- `shifted_contract_valid` proves strict positivity of every exact-algorithm agent share. This includes b=1 and optimum agent share zero.
- `Algorithm.lean` supplies a finite schedule and finite comparison fold returning an observed query record. `general_reward_approximation` discharges its scale certificate using the proved `reward_anchored_grid_scale` theorem; it has no welfare, scale, or grid-correctness hypothesis.
- `supply_oracle_approximation` needs a supply oracle only for nonnegative price vectors. Its reduction uses the proved larger-cost/larger-reward tie-break equivalence at strictly positive agent shares.
- `additiveAlgorithm1` evaluates response rewards by locally summing the cached singleton-reward table. `additiveAlgorithm1_eq` and `additiveAlgorithm1_approximation` connect that implementation to the exact proof.
- `algorithm1_output_mem_grid_of_welfare_pos` proves that the fallback welfare record cannot be selected on the positive-welfare branch, so the implementation returns one of Algorithm 1's recorded grid candidates.

## Explicit bounds and endpoints

With n ≥ 1, both exact and approximate routines have at most

    20 n log(n+1) / ε

response queries. The exact integer bounds, also valid at n=0, are:

- Exact: 1 + n(K+1), K least with (1−ε)^K ≤ 1/n².
- Approximate: 1 + n(K+2), K least with (1−ε/3)^K ≤ 1/(2n²).

The n=0 source routine makes its single welfare query and returns share one. The n=1 exact routine has K=0 and makes at most two response queries. Zero welfare returns share one exactly. The extra constant for n=0 is explicitly separated from the positive-n asymptotic statement.

General reward-value queries consist of n singleton reads plus one valuation for every queried response; there is one cost-value query. Additive response valuations are local cached sums and cause no extra reward-query calls.

## Theorem 7

`IsApproxOracle` takes an oracle of type Nat → Real → Finset. The first argument is the response-call index. Consequently repeated shares can return different approximate responses. No cross-query consistency or approximate tie-break is assumed.

`robustAlgorithm` follows the source appendix schedule:

1. Read singleton rewards.
2. Query the approximate response at agent share one and its exact reward and cost.
3. Set L = max(0,reward−cost). If L ≤ τ, return this observed pair.
4. Otherwise U=L+τ, ratio q=1−ε/3, width 2n², and query grid indices zero through K+1.
5. Return the observed pair of greatest realized principal utility.

`approximate_oracle_robustness` proves the exact guarantee

    realized utility ≥ (1−ε) OPT − 3τ/ε.

The proof establishes the clipped-welfare bounds, derives the widened reward-side bracket, proves the first-crossing coverage, and derives the payoff loss from the exact and approximate best-response inequalities. Its closed lower grid inequality is sufficient; this is not a claimed source correction.

## Actual query execution

The mathematical lists are connected to actual query instructions, not merely assigned a budget:

- `OracleProgram.lean` reifies response, reward and cost instructions and proves its exact-program interpretation equals `algorithm1`, with actual trace counts equal to the run annotations. The additive variant uses a stored singleton table.
- `RobustOracleProgram.lean` supplies `evalIndexed`, which advances its call index on response instructions and preserves it on reward/cost instructions.
- `evalIndexed_robustProgram` proves that executing the source approximate algorithm produces exactly `robustAlgorithm` and its complete chronological query-kind trace.
- `robustProgram_counts` proves response/reward/cost count correctness, including singleton and welfare calls.
- `robustProgram_query_bounds` applies the logarithmic bound to actual instruction traces, with exactly one cost query.
- `robustProgram_approximation` proves the utility guarantee directly for the interpreted program's output.

Arithmetic and comparisons on exact real inputs remain primitives. This is the paper's exact-real oracle-call model; no bit-complexity or floating-point claim is made.
