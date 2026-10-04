# Equal revenue and supply-query lower bounds

## Concrete mathematics

`EqualRevenue.lean` defines the explicit indexed cost and binary encoding of actual
subsets of `Fin n`. The encoding is injective and surjective onto `[0,2^n)`, rather
than an assumed abstract collection of outcomes. `proposition10` packages the
actual-model equal-revenue optimum, exact harmonic welfare, explicit linear
harmonic bounds, and the largest-singleton reward scale inequalities.

`LowerBounds.lean` defines the actual perturbed cost and model. Discrete convexity
proves nonnegativity, monotonicity and supermodularity after perturbation. The
optimum is exactly `1 + ζ*k`, the optimal contract is unique, and every successful
high-accuracy contract identifies its hidden index by belonging to a disjoint
real interval. `decodeNat_correct` performs this decoding without another query.
The hidden family has exactly `2^(n-1)` members. `accuracy_binary_bounds` bounds the
accuracy between `1/(32*2^n)` and `1/(16*2^n)`.

## No assumed oracle lower bound

`SparseSupply.lean` proves the pair exclusion and full finite combinatorial
count, giving at most `4*(n+1)^2` approximate supply candidates for every real
price vector. `SharpSparseSupply.lean` additionally matches the full cited
source's half-minimum-critical-gap condition, not only the explicit perturbation.

`SupplySimulation.lean` constructs legal supply responses, including the larger-
cost tie-break, from batch hidden-index membership answers. `LowerBoundProgram.lean`
compiles an arbitrary actual `SupplyProgram` into adaptive point membership
queries. It preserves the output and bounds probes by
`4*(n+1)^2 * supply_calls + cost_value_calls` on every actual adaptive path.
Known reward queries require no hidden-information probes.

`OracleIdentification.lean` derives the identification bound from actual adaptive
decision trees, allows an unqueried final guess, and proves randomized bounds over
arbitrary probability spaces. No Yao principle or search lower bound is assumed.

## Terminal theorems

`MainLowerBound.theorem8_worst_instance` (namespace `LowerBounds`) takes constant
per-instance approximation success and polynomial expected extra cost-value
queries, and concludes that eventually some actual hidden instance needs at least
`(3/2)^n` expected supply calls. `corollary3_exact_worst_instance` proves the exact
lower-bound half of Corollary 3 directly from the same corrected family.
Both use extended nonnegative expectations, permit infinite expected query counts,
and explicitly prove uniform-average-to-worst-instance extraction. Random
indicators are integrable and count variables measurable, the ordinary regularity
requirements for probability and expectation. No finite-support randomization or
uniform query cap is required. Finite-real and finite-random-seed versions are
also provided.

`LowerBoundStrategy.lean` proves a representation bridge for arbitrary history-
dependent operational strategies that terminate on the finite actual hidden
family. A finite cap is derived separately for each deterministic seed; no
termination assumption is imposed on off-family answer histories. The bridge does
not model failure runs which diverge on an actual hidden instance. The stated
algorithm language therefore uses terminating randomized oracle algorithms, the
standard finite decision-tree interpretation of the query model.

The auxiliary external-source endpoint errors and the corrected restricted-family
scope are recorded in `source-corrections.md`. The final terminal theorem axiom
audit contains only `propext`, `Classical.choice`, and `Quot.sound`; see
`logs/lower-axioms.log`.
