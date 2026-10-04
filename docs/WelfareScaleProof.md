# Welfare and reward-anchored scale

Source: arXiv:2609.35803v1, Lemma 5 and Lemma 6.

## Definitions and assumptions

All final statements use `Model ι`, for an arbitrary finite ground type `ι`.
The reward is normalized, nonnegative, monotone, and subadditive. The cost is
normalized and nonnegative, with no additivity, monotonicity, or subadditivity
assumption. Responses and the optimal contract are constructed in `Model.lean`.
The optimum is attained with the paper's larger-reward tie-breaking.

## Finite-envelope foundation

`FiniteEnvelope.lean` constructs the finite set of pairwise line intersections
in `[0,1]`, adjoins both endpoints, and orders it. An active line at each gap's
midpoint is active throughout its closed interval. The proof uses affine
continuity and the intermediate value theorem: any reversal would force a
pairwise intersection inside a gap.

`FiniteEnvelope.exists_partition` provides strictly increasing endpoints,
active response witnesses, and the exact sum of interval lengths times slopes.
The identity is obtained by finite telescoping, not assumed integration facts.
`exists_partition_max_slope` additionally establishes the prescribed reward
(slopes) tie-break on each half-open piece.

## Lemma 5

`subadditive_le_sum_singletons` proves the singleton upper bound by finite-set
induction.

`finite_first_appearance_bound` refines the paper's first-appearance blocks
into individual actions. For each action that occurs, take its least response
index. Its total duration of presence is at most the remaining interval length
from that first appearance. Monotonicity bounds its singleton reward by the
reward of the response where it first appears. Its resulting charge is thus
bounded by optimal principal utility. Summing over the ground set gives the
factor `Fintype.card ι`. Actions that never occur contribute zero.

`welfare_le_card_mul_optimalValue` instantiates the full finite-envelope
construction and charging argument. The envelope at zero is zero by
nonnegative costs and the empty response; the envelope at one is welfare.
Endpoint activity suffices because the official tie-breaking response has at
least the reward of any active line.

The public combined statement is `welfare_profit_comparison`. It has no
positive-welfare or nonempty-ground assumption. Explicit degeneracies:

- `welfare_eq_zero_iff_optimalValue_eq_zero`
- `empty_ground_zero`

## Lemma 6

`exists_reward_anchor` constructs a largest singleton in any positive-reward
set and proves it is positive and approximates the set reward within the ground
cardinality. `optimal_reward_pos` and `card_pos_of_optimalValue_pos` establish
all positive denominators from positive optimum.

`scale_certificate_algebra` proves the sharp lower endpoint, upper endpoint,
and the ratio bound. `reward_anchored_scale` instantiates it directly with the
actual model and the already proved welfare theorem. The algorithm-ready
`reward_anchored_grid_scale` uses `b = min 1 (W/a)` and proves
`b / n² ≤ 1 - optimum ≤ b`, with both `a` and `b` positive.

## Verification

`lake build CombinatorialContracts.Scale` checks the entire dependency chain.
The audit in `logs/welfare-scale-axioms.log` reports only the standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom
axioms, or additional envelope/charging hypotheses occur in final theorems.
