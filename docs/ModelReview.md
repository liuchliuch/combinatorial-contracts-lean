# Model formalization review

Source: `originals/tex/77-Approximating_Combinatorial_Contracts_with_Arbitrary_Costs.tex`, Section 2, response-reward monotonicity lemma, and the lower half of the welfare–profit comparison.

## Exact semantic coverage

- The finite ground type `ι` represents the paper's `[n]`; an action set is `Finset ι`.
- `Model` has a real-valued reward and cost. Nonnegativity and empty-set normalization are explicit fields. Reward monotonicity and union subadditivity are explicit fields. There is no extra regularity assumption on cost.
- `agentUtility` is exactly `α f(S) - c(S)`.
- `IsBestResponse` quantifies over every action set. `IsResponse` additionally requires maximal reward among all utility-maximizing sets. The latter is the paper's stated tie-breaking convention, including endpoints.
- `exists_response` proves oracle realizability by two finite maximizations. `response` uses classical choice only to select among sets having identical agent utility and reward. `response_reward_unique` proves this residual choice cannot affect reward or principal utility.
- `principal` is exactly `(1 - α) f(Sα)`. `welfare` is the welfare of the exact response at share one; `welfare_max` proves that it dominates every action set's welfare.
- `exists_optimum` proves attainment rather than assuming an optimal contract. It maximizes continuous principal utility over the compact set of feasible share/best-response pairs, then applies the stipulated reward tie-break. `optimum` is in `[0,1]`, and `principal_le_optimalValue` proves its optimality throughout that interval.
- `response_reward_monotone` proves the response-reward monotonicity lemma for arbitrary exact-response witnesses. Two optimality inequalities handle strictly increasing shares; the reward tie-break handles equal shares. The derived oracle reward is monotone for all real shares, in particular `[0,1]`.
- `principal_le_welfare` and `optimalValue_le_welfare` prove the lower half `P* ≤ W`, using the empty action's zero utility. The upper half `W ≤ n P*` belongs to `Welfare.lean` and is not presumed here.
- `cost_sub_eq_share_mul_reward_sub`, `tied_cost_le_iff_reward_le`, and `costTieResponse_iff_response` prove the exact larger-cost/larger-reward tie equivalence for positive shares.
- `HasAdditiveReward`, `supplyUtility_eq_agentUtility`, and `supplyResponse_iff_response` supply the full additive-reward supply-oracle reduction, including maximization and tie-breaking.

## Boundary handling

Empty ground types, zero rewards, zero costs, and zero welfare are admitted. Optimization permits shares zero and one. The positive-share requirement is retained for supply tie-breaking; it is not silently extended to zero. Nonnegative reward ensures principal utility is nonnegative on `[0,1]`. Positive optimal value forces the selected optimum below one.

## Verification

`lake env lean CombinatorialContracts/Model.lean` succeeds under Lean 4.24.0 and the project's pinned mathlib. The source uses no `sorry`, custom axiom, or hypothesis replacing an existence/optimization claim. The imported analysis facts are standard mathlib compactness and continuity theorems.
