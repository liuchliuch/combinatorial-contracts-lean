# Final independent source-semantic review

**Decision: ACCEPTED for the exact frozen source inventory below.** All ten numbered source results (eleven ledger entries because Proposition 9 has two parts), all 34 supporting obligations, and the three required reconstructed dependency groups are covered. No unresolved semantic proof obligation remains in this reviewed scope. This is a semantic acceptance, separate from the final mechanical release certificate.

- Paper: Deng–Li–Liu, *Approximating Combinatorial Contracts with Arbitrary Costs*, arXiv:2609.35803v1.
- Inventory: `docs/release-candidate/source-inventory.json`.
- Inventory SHA-256: `e0c21c7deeb2f91f6b7c88e46f8918fbc2755ed1af9f154c9972567e0ac68f30`.
- Frozen ledger SHA-256: `128e2bb878304da1a002d8616f831bb4004a1b789d5b12e1531bda937cb8a36e`.
- Reviewed proof modules: 27, all explicitly imported by the aggregate.
- Independence: this reviewer authored no Lean proof in the project. The review read the retained original TeX and the proof sources, rather than inferring scope from names or successful compilation.

The inventory binds 51 proof, configuration, ledger, validation-script and original-source files, nine clean pinned dependency revisions/trees, and the Lean executable identity. The reviewer independently reran inventory verification and forbidden-token/import preflight at the final freeze; both passed. The 7,379-job prefreeze aggregate build log was also inspected. The final clean build, origin-complete axiom audit and trust-zero import replay are separate release gates and are not claimed complete by this document.

## Sources and comparison method

The entire retained main TeX was inspected, including all appendices. Its SHA-256 is `40a5d6ce804d6893687c2f8875f866dc3802765059f4c2f4ea1769fdb1c1c7e7`. The required external source is the retained arXiv:2403.09794v2 TeX, SHA-256 `076fb5325a5ff0dc7ba26db3349720ae9527136ce851ca3cd749746f63121f48`, especially its Section 4.3 and Appendices D/E. The needed external mathematical content is reconstructed in the project, not imported as an axiom or replacement hypothesis.

Every final module was inspected in full across the review passes. Final edits were reconciled against saved inspected snapshots, including the source-quantified Lemma 6, complete Proposition 10 wrapper, exact source sparse-supply tolerance, actual oracle programs, operational strategies, extended expectations and worst-instance extraction. Hash verification binds the result to the final files, not an earlier helper-only snapshot.

## Model and endpoint fidelity

`Model` represents all subsets of a finite action type. Rewards are normalized, nonnegative, monotone and subadditive. Costs are normalized and nonnegative, with no extra cost regularity in the upper-bound theorems. Agent utility is exactly alpha·reward−cost; principal utility is exactly (1−alpha)·reward.

`IsResponse` imposes utility maximization followed by maximal reward. Response existence, reward uniqueness across residual ties, welfare maximization and optimum attainment on [0,1] are proved. The optimum is not assumed as a certificate. The share-zero, share-one, empty-ground, zero-welfare, zero-reward and free-action cases are admitted and handled. The positive-share requirement for converting maximal-cost supply ties to maximal-reward contract ties is retained; a concrete regression proves why it cannot simply be dropped at zero.

The finite-envelope partition is constructed from all pairwise crossings. Active lines extend to closed subintervals; favorable endpoint representatives are supplied on the required half-open intervals. Exact telescoping gives welfare. It is not an assumed integration identity or an unproved piecewise-linearity premise.

## Numbered-result coverage

### T1: Supply-oracle resolution

Executed price-vector supply program; n singleton reward reads are cached before pricing. Every subsequent response value is a local sum. Supply correctness is required only for nonnegative prices, and all actual queried shares are positive. The returned feasible contract has exact favorable-response profit at least (1−epsilon)OPT. Executed supply count is at most 20n log(n+1)/epsilon for n≥1, reward count is exactly n, and cost count exactly one. Empty-ground execution is separate.

Declarations: `CombinatorialContracts.Paper.theorem1`, `CombinatorialContracts.Paper.theorem1_empty`.

### T2: General reward theorem

Executed response/reward/cost query program, with complete chronological trace and proved count projections. Deterministic finite comparison selects an observed candidate. Model-derived welfare and singleton scale discharge all structural premises. Both response and reward query counts satisfy the stated logarithmic bound, with one cost call; n=0 and n=1 are covered explicitly.

Declarations: `CombinatorialContracts.Paper.theorem2`, `CombinatorialContracts.Paper.theorem2_empty`.

### C3: Exact–approximate separation

Combines the reconstructed exact worst-instance exponential lower bound with Theorem 1. The exact lower bound is proved for the concrete additive-reward, monotone-supermodular-cost restricted family, including polynomial extra cost-value queries and arbitrary probability-space randomness; it is not assumed from the cited paper.

Declarations: `CombinatorialContracts.LowerBounds.corollary3_exact_worst_instance`, `CombinatorialContracts.Paper.theorem1`.

### L4: Response-reward monotonicity

Response-reward monotonicity is proved for arbitrary exact-response witnesses. Strictly ordered shares use the two optimality inequalities, while equal shares use the explicit favorable tie-break.

Declarations: `CombinatorialContracts.response_reward_monotone`, `CombinatorialContracts.response_reward_mono`.

### L5: Welfare comparison

Both OPT≤W and W≤nOPT are proved from the actual finite model. The upper bound constructs the envelope and charges each individual action from its first appearance. This is a valid documented alternate proof of the source epoch argument, with no cost-structure premise.

Declarations: `CombinatorialContracts.welfare_profit_comparison`.

### L6: Reward-anchored scale

The final model-facing theorem allows any feasible optimal contract/response pair and any largest-singleton action in that response. Anchor positivity, lower-endpoint positivity, both scale inequalities and the n² endpoint-ratio bound are proved, not assumed.

Declarations: `CombinatorialContracts.reward_anchored_scale_of_optimal_response`.

### T7: Approximate-oracle robustness

The approximate oracle is indexed separately at each response call, permitting different answers to repeated shares. The returned object is the actual recorded contract/response pair. The clipped welfare estimate, low-welfare branch, widened 2n² bracket, source grid indices 0 through K+1, deliberate undershoot, response-error estimate and exact 3tau/epsilon loss are all proved. Actual query-node counts and n=0 behavior are included.

Declarations: `CombinatorialContracts.Paper.theorem7`, `CombinatorialContracts.Paper.theorem7_empty`.

### T8: High-accuracy lower bound

The concrete binary-index hidden family is normalized/nonnegative with additive reward and monotone supermodular cost. Its perturbation, unique optimum, successful-contract decoder and gamma_n=Theta(2^−n) bounds are explicit. Full-source sparse supply is proved. Arbitrary adaptive supply/reward/cost programs compile to adaptive point probes with preserved output and bounded actual-path cost. The search lower bound includes unqueried final guesses and arbitrary random-seed probability spaces. The final ENNReal theorem includes infinite or mixed expected counts, polynomial auxiliary value budgets and a measurable worst-instance extraction, giving eventual (3/2)^n expected supply calls on an actual hidden instance.

Declarations: `CombinatorialContracts.LowerBounds.hard_family`, `CombinatorialContracts.LowerBounds.accuracy_binary_bounds`, `CombinatorialContracts.LowerBounds.theorem8_worst_instance`, `CombinatorialContracts.LowerBounds.randomized_strategy_program_exact`.

### P9i: Joint tightness

An actual 2m-action additive model is constructed. Every undesignated nonempty set is excluded from the envelope, and the favorable optimal contract/response pair is unique. The source ratio and the explicit n²/16 bound hold. The final existence theorem also instantiates the optional normalization by the positive actual total reward and preserves the ratio and uniqueness.

Declarations: `CombinatorialContracts.Tightness.proposition9_i`.

### P9ii: Welfare-gap tightness

An actual normalized additive model with total reward one is constructed for each n≥2 and r>1. All-set monotonicity and supermodularity are proved, all sets of size≥2 are excluded from responses, the singleton envelope is realized, and the exact welfare/optimum ratio n−(n−1)/r is proved.

Declarations: `CombinatorialContracts.Tightness.proposition9_ii`.

### P10: Equal-revenue anatomy

Actual binary-index sets form the required bijection. The equal-revenue costs, favorable critical responses, OPT=1 for n>0, W=H_(2^n−1), strict/weak factor-two singleton interval and n/2≤H≤n are proved. The final wrapper uses the source largest-reward condition rather than silently substituting a largest-index hypothesis.

Declarations: `CombinatorialContracts.EqualRevenue.proposition10`.

## Supporting-obligation reconciliation

The frozen ledger is the detailed declaration map. Every S01–S34 entry was reconciled with the original claim and its actual declaration. The following grouping records the substantive review:

- **S01–S07:** finite favorable response and optimum existence; degenerate cases; welfare comparisons; finite endpoint-correct affine partition; exact telescoping.
- **S08–S11:** first-appearance charging, sum exchange, singleton subadditivity and a positive maximal singleton. S08 is explicitly a replacement derivation: the code charges at most one term per ground action and proves the needed bound. It does not claim to construct the source's literal epoch-block objects. This alternate proof is accepted without adding assumptions.
- **S12–S18:** actual least stopping index and minimality, shifted grid cover, strict positive supply-query shares, cost/reward tie equivalence, deterministic finite selection, complete executed query traces and logarithmic counts including width one.
- **S19:** an exact-real oracle-call model, with local arithmetic/comparisons/sums treated as free operations. These declarations do not establish polynomial bit complexity, and no such claim is accepted.
- **S20–S21:** approximate welfare interval and low-welfare branch, widened anchor interval, extra-step margin and the source additive-loss constant, with independent per-call answers.
- **S22–S25:** actual binary subsets, base and perturbed envelopes, nonnegative monotone supermodular perturbed costs, and sparse supply. `SharpSparseSupply` proves the full positive sigma condition from the source, including the exact minimum consecutive critical gap 1/[N(N−1)], not merely the smaller chosen perturbation.
- **S26–S29:** legal larger-cost-tied supply simulation, actual adaptive query compilation, randomized expected-query identification, contract-only hidden-index decoding, gamma bounds and eventual exponential supply lower bounds despite polynomial cost-value queries.
- **S30–S32:** both concrete all-set tightness constructions, fully discharged generic-chain hypotheses, actual normalization/scaling specialization, and harmonic linear growth.
- **S33–S34:** history-dependent operational strategies are represented by finite programs whenever they terminate on the actual finite hidden family; no off-family termination or common random-seed cap is assumed. Extended expectations and the hidden-average-to-worst-instance conversion are proved, with the necessary per-instance measurability for the latter.

## Oracle and randomized-model scope

The finite query languages issue explicit response/supply/reward/cost instructions and record the executed query-kind trace. Bind/interpreter equalities connect mathematical runs to the actual instruction sequence. Cost annotations are not detached counters. The additive implementation constructs its price vectors only after reading and caching singleton rewards. The lower-bound compiler locally answers the public rewards and uses the concrete sparse candidate lists for supply calls.

A fixed legal supply oracle is constructed for the hard family, including maximal-cost tie-breaking. Lower bounds for this legal oracle establish the required worst-case oracle hardness. Approximation success decodes the real returned contract from pairwise disjoint profitable intervals, without hiding an additional oracle call.

The random seed is independent of the hidden instance and may range over an arbitrary probability space. Finite-real expectations have ordinary integrability hypotheses; extended nonnegative expectations include infinity. The final worst-instance result assumes measurability of each actual per-instance query count, so it does not incorrectly exchange arbitrary nonmeasurable lower integrals with finite averages.

The program language denotes terminating query executions. `LowerBoundStrategy` proves exact representation for unrestricted history-dependent strategies terminating on the finite actual family, with a separate finite unrolling for each seed. This does not assert that a divergent run is itself a finite program. Infinite expectation is nevertheless fully represented through unbounded finite runs across seeds. These are ordinary oracle-model scope conventions, not unproved lower-bound or sparse-supply hypotheses.

## Source-proof adaptations and correction

1. The welfare proof uses per-action first appearances rather than literal source epochs; the same required inequality is proved with the original assumptions.
2. The exact algorithm includes its initial welfare record as a fallback. The positive-welfare theorem proves that its selected output is a grid record, so this does not change the source result. The robust maximization may include the already queried initial pair and can only improve its guarantee.
3. Singleton reads are performed before the robust welfare branch. This permitted extra early work remains within the stated count and introduces no hidden calls.
4. The cited external source calls the base cost strictly monotone even though c(0)=c(1)=0, and its unrestricted perturbation premise includes a zero first gap. The main paper restricts hidden indices to k≥2. The formal proof constructs and proves that valid restricted family directly, preserving all main-paper theorem statements. It does not use the invalid unrestricted premise. The exact full-source sparse tolerance is separately reconstructed.
5. All generic envelope, chain, scale and scaling lemmas used for paper results have their hypotheses proved in the actual finite models. No conclusion is smuggled in as a model field or replacement assumption.

## Trust separation and acceptance conditions

Semantic acceptance covers the frozen mathematical statements, source scope and oracle semantics. Standard Lean logical foundations (`propext`, `Classical.choice`, `Quot.sound`) and pinned mathlib are permitted; admissions, custom theorem axioms and unchecked proof shortcuts are not. Source preflight found none of the forbidden tokens and no omitted aggregate module. The independent mechanical release must still verify all project declaration origins, their transitive axiom closures, and the trust-zero all-import replay for this same inventory.

Any change to a frozen source, dependency pin, original, ledger or validation script changes the bound inventory and invalidates this certificate until re-reviewed. No proof file was edited by this reviewer. The authoritative machine-readable semantic decision is `docs/release-candidate/semantic-certificate.json`.
