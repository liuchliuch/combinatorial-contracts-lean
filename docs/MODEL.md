# Contract and oracle model

The action universe is finite. Rewards are normalized, nonnegative, monotone and subadditive; costs are normalized and nonnegative. Agent utility is `alpha * reward(S) - cost(S)`. A response maximizes this utility and breaks ties by gross reward, as required for principal-favoring ties on shares in `[0,1]`. The additive specialization represents a supply query at nonnegative prices using the proved response equivalence.

The upper-bound algorithms operate in the exact-real oracle model. `OracleProgram` and `SupplyProgram` execute explicit query traces: returned contract, returned response, reward/cost values and query budgets refer to the same execution. The positive-domain bounds use the explicit constant `20 * n * log(n+1) / epsilon`; empty action universes have separate constant-query theorems. Value queries and response queries are recorded separately.

Approximate-response execution uses an indexed oracle so successive calls can return different approximate responses. The guarantee is `(1-epsilon) * OPT - 3*tau/epsilon`, with `0 < epsilon < 1` and `tau >= 0`. The returned response is a recorded oracle response; exact best-response optimality is not assumed for that output.

The lower bounds quantify over concrete supply programs on the additive-reward, monotone-supermodular hard family. Constant-success guarantees, measurable query counts and polynomially many expected cost-value queries are explicit assumptions. Expectations use nonnegative extended reals and may be infinite. The finite-program compilation applies to actual terminating hard-family executions; a separate semantics for positive-probability nontermination is outside these statements.

Proposition 9(i) permits arbitrary normalized nonnegative costs. Proposition 9(ii) and the lower-bound family explicitly prove monotonicity and supermodularity. Tightness concerns the localization certificate; it does not assert a matching logarithmic query lower bound. See [source corrections](source-corrections.md) for the directly proved restricted family and the cited predecessor's endpoint issue.

These are oracle query-complexity results. They do not assert bit complexity for exact-real arithmetic.
