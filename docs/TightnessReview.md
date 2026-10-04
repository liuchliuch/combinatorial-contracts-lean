# Proposition 9: actual finite tightness models

Source: Deng–Li–Liu, *Approximating Combinatorial Contracts with Arbitrary Costs*, arXiv:2609.35803v1, Proposition 9 and Appendix C. The checked TeX source is `originals/tex/77-Approximating_Combinatorial_Contracts_with_Arbitrary_Costs.tex`.

## Scope and source alignment

`CombinatorialContracts/Tightness.lean` proves the two constructions using actual finite action sets. It does not replace the constructions with hypotheses asserting the desired envelope, optimum, welfare, or ratios. The generic `RealizedChain` bridge is instantiated with proofs of every field: all designated action sets and their numerical rewards/costs are supplied; every non-designated set is proved strictly below the empty response on the complete feasible share interval `[0,1]`.

### Part (i): simultaneous quadratic localization loss

Namespace `CombinatorialContracts.Tightness.Bundle`.

- `Action m = Fin m ⊕ Fin m`; `action_count` proves cardinality `2*m`.
- `A m` is precisely the left summand; all its actions have reward one.
- Right action `i` has reward `R m (i+1) = m*2^(i+1)`, using zero-based `Fin m` indices.
- `D m η k = R m k - (1+η) - k/2` is an explicit closed form. `D_step` proves exactly the cost recurrence in Appendix C; this is not a replacement cost law.
- `cost` assigns `D m η 0` to `A m`, the relevant `D` to each right singleton, and `2*reward` to every other set. The empty set automatically receives zero.
- `D_nonneg`, `cost_nonneg`, and the `Model` construction establish all normalization-at-empty and nonnegativity obligations. `model_additive` proves reward additivity.
- `realized` proves the complete finite upper-envelope realization and excludes all other nonempty action sets.
- `optimalValue_eq` gives `P*=1+η`; `welfare_eq` gives `W=1+η+m/2`.
- `principal_at_optimal`, `response_at_optimal`, and `unique_optimal_pair` identify the unique optimal contract and selected set: `α*=1-(1+η)/m` and `S*=A m`.
- `anchor_reward` proves every item in `A m` has singleton reward one, so there is no unproved maximization step for the anchor.
- `localization_ratio` proves the exact displayed ratio.
- `unique_optimal_response_pair` strengthens uniqueness to every action set satisfying the paper’s tie-break, independent of the choice implementation.
- `normalizedModel` divides the entire raw instance by its positive total reward. `normalized_reward_univ` and `normalized_reward_le_one` prove total reward one and the full normalized reward range. `normalized_additive`, `normalized_isResponse`, `normalized_optimal_pair`, `normalized_unique_optimal_pair`, and `normalized_localization_ratio` prove that the complete result survives normalization.
- `quadratic_lower_bound` proves the explicit uniform bound `n²/16` for `n=2m`, stronger than merely attaching an informal asymptotic label. Its constant is uniform over `0<η<1` and `m≥2`.

### Part (ii): monotone-supermodular costs

Namespace `CombinatorialContracts.Tightness.Singleton`.

- The ground set is exactly `Fin n`.
- `Z`, `value`, and `entry` are the source's normalized geometric definitions, with zero-based indices.
- `singleCost` is the closed form `(r^i - 1 - i*(1-1/r))/Z`. `singleCost_zero` and `singleCost_step` prove the source's initial condition and recurrence, respectively.
- `cost` is exactly `sum_i d_i + 2*choose(card,2)`, including the quadratic interaction penalty.
- `model_additive` and `reward_univ` prove additive rewards and total reward exactly one. `reward_le_one` establishes the `[0,1]` range for every subset.
- `cost_insert` proves the exact marginal cost `d_i+2*card(S)`.
- `cost_mono` proves setwise cost monotonicity. `cost_supermodular` proves increasing marginal costs for every nested pair of sets and every new action, not merely convexity of the singleton-line list.
- `large_cost`, `large_utility_neg`, and `bestResponse_card_le_one` prove all sets of cardinality at least two are impossible best responses at every share in `[0,1]`.
- `realized` proves the remaining empty/singleton envelope. Entry zero is permitted for the first singleton, matching its zero cost and the reward-favoring tie break at `α=0`.
- `optimalValue_eq`, `welfare_eq`, and `welfare_ratio` prove the exact claimed welfare/optimum ratio for every `n≥2` and `r>1`.
- `ratio_approaches_n` proves an explicit quantified sharpness statement: for each positive tolerance, some admissible `r` gives a ratio strictly above `n−ε`.

## Bundled proposition statements

- `proposition9_i` is an unconditional existence theorem over the actual `2m`-action type. It includes normalized additive rewards, a feasible optimal contract and response, uniqueness among all response pairs, an explicitly positive largest singleton anchor, the exact displayed ratio, and its quadratic lower bound.
- `proposition9_ii` is an unconditional existence theorem over `Fin n`. It includes total reward one, the reward range, additivity, monotone costs, increasing marginal costs, and the exact ratio.

## Verification

`lake env lean -o .lake/build/lib/lean/CombinatorialContracts/Tightness.olean CombinatorialContracts/Tightness.lean` succeeds with no warnings.

The axiom audit in `logs/tightness-axioms.log` checks both bundled propositions, normalized pair uniqueness, and the quantified asymptotic statement. Every audited declaration depends only on Lean’s standard `propext`, `Classical.choice`, and `Quot.sound`. The checked source has no custom axioms or placeholders.

## Trust boundary

All statements are ordinary Lean theorems over the finite-set model. There are no `sorry`, `admit`, custom axioms, assumed envelope descriptions, assumed welfare identities, or assumed optima in this module. The only proof parameters are the source's explicit numerical conditions. The full formal build and axiom audit are recorded by the coordinating verification workflow.
