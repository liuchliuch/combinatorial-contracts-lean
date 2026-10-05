# Paper correspondence

Versioned source: [arXiv:2609.35803v1](https://arxiv.org/abs/2609.35803v1). The ten numbered results use the paper's shared counter; Proposition 9 has two separately checked parts.

| Paper item | Main Lean entry points |
|---|---|
| T1 — Supply-oracle resolution | `CombinatorialContracts.Paper.theorem1`, `CombinatorialContracts.Paper.theorem1_empty` |
| T2 — General reward theorem | `CombinatorialContracts.Paper.theorem2`, `CombinatorialContracts.Paper.theorem2_empty` |
| C3 — Exact–approximate separation | `CombinatorialContracts.LowerBounds.corollary3_exact_worst_instance`, `CombinatorialContracts.Paper.theorem1` |
| L4 — Response-reward monotonicity | `CombinatorialContracts.response_reward_monotone`, `CombinatorialContracts.response_reward_mono` |
| L5 — Welfare comparison | `CombinatorialContracts.welfare_profit_comparison` |
| L6 — Reward-anchored scale | `CombinatorialContracts.reward_anchored_scale_of_optimal_response` |
| T7 — Approximate-oracle robustness | `CombinatorialContracts.Paper.theorem7`, `CombinatorialContracts.Paper.theorem7_empty` |
| T8 — High-accuracy lower bound | `CombinatorialContracts.LowerBounds.hard_family`, `CombinatorialContracts.LowerBounds.accuracy_binary_bounds`, `CombinatorialContracts.LowerBounds.theorem8_worst_instance`, `CombinatorialContracts.LowerBounds.randomized_strategy_program_exact` |
| P9i — Joint tightness | `CombinatorialContracts.Tightness.proposition9_i` |
| P9ii — Welfare-gap tightness | `CombinatorialContracts.Tightness.proposition9_ii` |
| P10 — Equal-revenue anatomy | `CombinatorialContracts.EqualRevenue.proposition10` |

[`theorem-ledger.json`](theorem-ledger.json) also records 34 supporting claims and cited dependencies. [`Audit/targets.json`](../Audit/targets.json) maps the fixed interfaces to these items.

The program constructors `OracleProgram` and `SupplyProgram` (supporting item S19) remain fixed inductive definitions. They are preserved by the mathematical source inventory rather than exposed as replaceable type-valued Comparator holes.

Theorem 8 and Corollary 3 use the concrete restricted hard family and actual worst-instance expected query bounds. Accuracy and probability, measurability and value-query conditions appear in their full statements. The upper bounds refer to executed oracle programs. See [MODEL.md](MODEL.md) for domain boundaries.
