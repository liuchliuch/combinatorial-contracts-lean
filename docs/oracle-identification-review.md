# Adaptive randomized identification review

Source: arXiv:2609.35803v1, Appendix B.1, final identification/simulation argument.
Implementation: `CombinatorialContracts/OracleIdentification.lean`.
Reviewed and compiled with Lean 4.24.0 on 2026-10-03.

## Main verified claims

- `adaptive_identification_sum`: for a finite candidate set K and a genuine adaptive point-query decision tree, `|K| * (sum_success - 1) ≤ 2 * sum_probes`.
- `adaptive_identification`: equivalently, `|K| * successProbability ≤ 2 * expectedProbes + 1`, where both quantities average over a uniform hidden index.
- `randomized_identification_lintegral`: the same inequality averaged over an arbitrary independent probability-space seed, allowing infinite expected runtime. This formulation uses lower Lebesgue integrals and does not impose an integrability, finite-support, or finite-random-bit hypothesis.
- `randomized_identification` and `randomized_expected_probes_lower_bound`: real-integral versions for finite expectations. Success at least δ gives expected probes at least `(|K| * δ - 1) / 2`.
- `finite_randomized_identification`: elementary finite-seed version with arbitrary nonnegative real probabilities summing to one.
- `BatchProgram.compile_result`: exact semantic preservation by the explicit adaptive batch-to-point compiler.
- `BatchProgram.compile_probes_le` and `compile_supply_probes_le`: proved pathwise simulation overhead, including `B * supplyCalls + additionalValueCalls`.
- `BatchProgram.identification`, `randomized_identification`, `randomized_identification_lintegral`, `randomized_supply_identification`, and their finite-seed counterparts: direct compound-query versions using proved compilation overhead.

## Model and scope

`PointProgram` is an inductive terminating adaptive binary oracle program. Each query's yes/no continuation can choose entirely different subsequent queries and stopping times. A leaf can output any index, whether queried, unqueried, inside K, or outside K. Repeated queries and queries outside K are allowed and charged. There is no fixed-query-list assumption and no requirement that success first discovers the hidden point.

For each random seed, the program terminates. Program size and runtime need not have a uniform bound across seeds, and the nonnegative expectation may be infinite. The analytic theorem separates the seed probability space from the uniform hidden index, expressing their independence. Programs with genuinely nonterminating executions are not syntactically represented; the theorem does not silently claim a formal equivalence to an independently defined partial-machine model.

`BatchProgram Q κ α` is another inductive adaptive oracle program. Each label q has a public candidate list. Its answer is `some hidden` when the hidden index belongs to that list, and `none` otherwise. A query may thus reveal more information than a particular concrete supply answer, which is suitable for a lower bound. The compiler implements each batch using sequential point probes, stopping at a hit, and then follows the original answer-dependent continuation. Lists may contain repetitions. `callCost` measures charges on the actual path, and `map` decodes an output without adding calls.

Concrete candidate construction, correctness of decoded supply answers including tie-breaking, compilation from the original supply/reward/cost program, and approximation-to-hidden-index recovery are separate obligations in the construction/simulation files. The generic per-label length bound is a genuine simulation-complexity hypothesis, not an assumption of the desired query lower bound.

## Proof method

Structural induction on the adaptive point tree establishes the aggregate inequality for every finite K. A leaf is correct on at most one hidden index. At a query outside K, every input takes the no branch and pays one probe. At a query in K, separate that one input and invoke induction on K with the queried index erased. The successful no-branch inputs are at most `|K| - 1`. These facts yield the factor-two expected-probe inequality directly, without replacing the adaptive program by a prebuilt transcript.

Randomization integrates this pointwise deterministic inequality. The extended version uses exact scaling of lower integrals by finite constants and additivity with the constant function one; the real version uses standard integrability of the displayed expectations. Finite seeds use only weighted sums and nonnegative multiplication.

## Verification

Commands:

    PATH=$PWD/.toolchain/lean-4.24.0-linux/bin:$PATH lake build CombinatorialContracts.OracleIdentification
    PATH=$PWD/.toolchain/lean-4.24.0-linux/bin:$PATH lake env lean /tmp/oracle-identification-audit.lean

Audited main declarations depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; `BatchProgram.compile_result` only uses `propext`. There are no `sorry`, `admit`, custom axioms, or unproved search lower-bound assumptions in this file.
