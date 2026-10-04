# Independent lower-bound review

Status: **ACCEPTED for the stated lower-stack scope at the frozen hashes below**.
Reviewer role: independent second reviewer; no proof declarations authored or edited.
Date: 2026-10-03; final acceptance 10:06 UTC.

## Sources and scope

The review read the actual Lean declarations against the local frozen official
source, rather than inferring coverage from declaration names or comments:

- arXiv:2609.35803v1, Theorem 8, Corollary 3, Proposition 10, Appendix B and B.1.
- arXiv:2403.09794v2 (DFGR26), Section 4.3 and Appendix E, including E.3's
  reference back to the ambiguity-interval counting proof.
- `EqualRevenue`, `LowerBounds`, `SparseSupply`, `SupplySimulation`,
  `OracleIdentification`, `LowerBoundProgram`, `MainLowerBound`, and
  `LowerBoundAsymptotics`, plus the completed `SharpSparseSupply` and
  `LowerBoundStrategy` additions, with the relevant `Model`, `ChainEnvelope`,
  and `SupplyProgram` definitions read directly.

Source TeX SHA-256:

```
40a5d6ce804d6893687c2f8875f866dc3802765059f4c2f4ea1769fdb1c1c7e7  originals/tex/77-Approximating_Combinatorial_Contracts_with_Arbitrary_Costs.tex
076fb5325a5ff0dc7ba26db3349720ae9527136ce851ca3cd749746f63121f48  originals/dependencies/dfgr26/tex/arxiv_25112025.tex
```

## Verified construction semantics

1. **Actual subsets, not abstract labels.** `binaryIndex` is the sum of
   distinct binary weights over `Finset (Fin n)`, with proved injectivity,
   surjectivity onto the integers below `2^n`, and compatibility with insertion.
   The reward is exactly that additive function. `cost t = t - harmonic t`
   follows from the finite sum of increments `t/(t+1)`.

2. **Endpoints are preserved.** The first increment and `cost 1` are zero.
   No strict monotonicity at zero is assumed. The base response at each
   positive binary index's critical share uses the explicit reward-maximizing
   tie-break. The Lean equalities give optimal value one, exact harmonic
   welfare, factor-two singleton localization, and the explicit bounds
   `n/2 ≤ H_(2^n-1) ≤ n`.

3. **The target hidden family is the restricted valid family.**
   `hiddenIndices n = Icc (2^(n-1)) (2^n-1)` has exactly `2^(n-1)` members
   for positive n. For n ≥ 2 all hidden indices are at least two and satisfy
   the source's upper-half condition. The cost reduction is exactly
   `ζ = 1/(8N^2)` at one set. Nonnegativity, normalization, monotonicity,
   supermodularity, distinctness of hidden cost functions, entry-share
   feasibility, and optimal value `1 + ζ*k` are derived for the actual models.
   They are not hypotheses of the oracle lower bound.

4. **No defective dependency premise is inherited.** The unrestricted
   perturbation minimum in DFGR26 Appendix E includes the zero first cost
   increment and, as printed, trivial supermodularity comparisons. Its
   claimed positivity therefore cannot be imported. The target paper's
   n ≥ 2, k ≥ 2 restricted family avoids this defect and is proved directly.

5. **Contract-only recovery is proved.** Every nonhidden response gives
   principal profit at most one. A profitable contract for hidden k lies in
   `[critical k - ζ, critical k)`, and these intervals are pairwise disjoint.
   The chosen accuracy `γ = 1/(32N)` forces profit strictly above one.
   `decode`, `decodeNat_correct`, and `decode_exact` consequently recover k
   from the real output share alone. The decoder does not query the returned
   contract's response or silently receive the hidden response set.
   `unique_optimal_contract` proves the claimed unique optimal share.

## Sparse supply and simulation

- `approxSupply` compares a subset with **every** action subset. Its price
  argument is `Fin n → ℝ`, without sign, rationality, finite-grid, or bit-length
  restrictions. This is stronger on prices than the paper's nonnegative-price
  definition.
- Pairwise exclusion is derived by comparing insertion/deletion of one binary
  action in two approximately optimal sets. The price contributions cancel.
  The proof uses a proved cost-increment gap and does not assume sparse supply.
- The finite-family counting theorem encodes a set by its least ambiguous
  action, the number of its lower bits, and two subsequent bits. Lower-bit
  nesting and a modular-distance argument prove injectivity, including the
  no-ambiguous-action sentinel. The explicit bound is `4*(n+1)^2`.
- Candidate enumeration is the image of a filter of the finite universe of
  subsets. It depends only on the known base cost, prices, and ζ. Computational
  efficiency of enumeration is deliberately not claimed; the paper counts
  oracle calls, allowing this enumeration to take exponential computation.
- Every perturbed utility maximizer belongs to this candidate family. On a
  missed batch, the fixed base response remains optimal and still maximizes
  cost over **all** perturbed optimizers. On a hit, the hidden index is known,
  so finite maximization of the fully determined model needs no further hidden
  information. `supplyAnswer_correct` certifies the precise larger-cost
  tie-break, rather than merely certifying utility maximization.
- The simulator chooses one deterministic legal oracle. A class-wide
  algorithmic correctness guarantee must apply to that legal oracle. The
  formal lower bound is about its actual execution, not an unproved equality
  with every possible residual tie selector.

### Full subsidiary tolerance range

The original generic sparse lemma uses the stricter sufficient condition
`2σ < 1/N^2`, which already suffices for Theorem 8's chosen ζ. The additional
`SharpSparseSupply` module closes the source's full range
`2σ < 1/(N*(N-1))`. Distinct increment indices ensure the smaller denominator
is at most N−1, yielding the sharper cost-block gap. The exact consecutive
critical gap is proved to be `1/(t*(t+1))`, its minimum is attained at t=N−1,
and `approxSupply_card_le_of_critical_gaps` uses the source's hypothesis of
being below half every consecutive gap. Thus no stronger replacement
hypothesis remains for that subsidiary statement (for the relevant n ≥ 2).

## Adaptive program semantics and query accounting

`SupplyProgram` has separate supply, reward-value, and cost-value nodes, each
with an answer-dependent continuation. Supply nodes contain actual real price
vectors. The compiler answers the known additive reward function locally,
turns each cost query into one point test, and turns each supply query into
the explicit finite candidate batch. Its result-preservation theorem applies
to arbitrary output types and every hidden-instance path. Its cost theorem
counts the original executed trace, not a worst-case or precomputed list.

The second compiler implements each batch by actual sequential point probes
and follows the branch for the batch's actual result, stopping at a hit when
possible. Thus

```
compiled probes ≤ 4*(n+1)^2 * actual supply calls + actual cost-value calls.
```

The point-program lower bound permits repeated probes, probes outside the
candidate set, different continuations after either answer, and arbitrary
final guesses. The leaf case proves that an unqueried guess can succeed on at
most one hidden index. Structural induction gives

```
|K| * successProbability ≤ 2 * expectedProbes + 1.
```

The `+1` is essential and is present. No assumption that success first probes
the hidden point replaces the identification theorem.

### Termination scope

The core program syntax is inductive and well founded. The additional
`LowerBoundStrategy` module independently defines unrestricted next-action
rules over full query/answer histories, with a fuel-indexed operational
semantics. These rules need not terminate on arbitrary histories. Its
finite-family representation theorem assumes termination only on the actual
hidden-instance family, takes the finite maximum of those termination times,
and proves that unrolling at that cap preserves every actual output and full
trace. The seedwise representative may have a different cap for each seed.
There is no uniform random-seed runtime restriction and no off-family
termination assumption.

Genuinely nonterminating actual sample paths remain outside the terminating
program's execution semantics. Infinite expectation across terminating seeds
is fully included. The code does not yet assign infinite query counts or a
failure event to divergent operational runs, and does not provide an
almost-sure-termination/null-set representation theorem. Claims must retain
this precise termination scope rather than describe divergence itself as
represented.

## Probability and asymptotics

The hidden index is averaged uniformly over the exact finite set K. The
algorithmic seed is independent: one function from a probability space to
programs is used for all k. Finite randomization allows arbitrary nonnegative
real weights summing to one, not just uniform or rational seed probabilities.
The probability-space versions impose no finite-support restriction.

The point and batch `lintegral` theorems permit infinite expected query counts.
They are valid even as lower integrals without measurability; ordinary
probabilistic interpretation requires the usual measurable random variables.
The real-integral variants correctly require integrability and do not pretend
Lean's integral of a nonintegrable function is its extended expectation.

The current main integration proves the finite-expectation tradeoff

```
2^(n-1) * average success ≤ 2*(4*(n+1)^2 * E[Q] + E[V]) + 1.
```

It additionally proves finite-sum/integral interchange and per-instance
success ⇒ uniform-average success. The asymptotic lemma proves, rather than
assumes, that a polynomial extra-cost-query term cannot absorb this exponential
bound. `theorem8_high_accuracy` and `corollary3_exact_lower_bound` compose the
actual execution inequality with these facts to obtain the eventual explicit
bound `(3/2)^n ≤ E[Q]`. The latter uses its own exact-success indicator and
proves exact success implies approximate success. No oracle lower bound or
unproved `hqueries` premise remains in those entry points.

The completed ENNReal integration has also been read directly:

- `randomized_high_accuracy_query_bound_lintegral` proves the actual-program
  supply/value tradeoff with extended expectations. Measurability of the
  value-count average is correctly required for the additive integral split.
- `eventually_exponential_supply_lower_bound_ennreal` proves the eventual
  exponential conclusion without converting an infinite value to a real.
  The proof also handles a possibly negative polynomial coefficient safely
  by replacing it with its maximum with zero.
- `theorem8_high_accuracy_ennreal` and
  `corollary3_exact_lower_bound_ennreal` remove the finite expected-supply-count
  hypothesis from the actual-program asymptotic wrappers.
- `lintegral_hiddenMean` and
  `exists_hidden_expected_supply_ge_average_ennreal` prove the finite uniform
  average/worst-instance conversion under measurability of actual per-instance
  counts. This condition matters: an arbitrary nonmeasurable lower integral
  cannot be silently interchanged with a finite sum.
- `theorem8_worst_instance` and `corollary3_exact_worst_instance` conclude,
  for all sufficiently large n, existence of an actual k in the hard family
  with expected supply count at least `(3/2)^n`. They allow arbitrary mixtures
  of finite and infinite expectation across dimensions. Success is required
  on each hard instance, with a fixed positive probability δ; additional
  cost-value queries have polynomial expected uniform-average count.

The exact lower-bound half of Corollary 3 is therefore direct and unassumed.
The upper approximation half is supplied by the separate operational upper
bound and is outside this lower-stack review's proof ownership.

## Final independent verification

The final independent build command was:

```
lake build CombinatorialContracts.MainLowerBound \
  CombinatorialContracts.LowerBoundStrategy \
  CombinatorialContracts.SharpSparseSupply
```

It completed successfully (7369 Lake jobs), rebuilding the final equal-revenue
addition, lower family, candidate bounds, simulator, compiler, strategy bridge,
and main lower-bound integration. Remaining warnings are style-only linters.

The release inventory was independently hashed and all 51 enumerated source
files were independently rehashed against it with zero mismatches. Its
SHA-256 is
`e0c21c7deeb2f91f6b7c88e46f8918fbc2755ed1af9f154c9972567e0ac68f30`.
The inventory is `docs/release-candidate/source-inventory.json` and also binds
the pinned package trees, toolchain, source originals, ledger, and scripts.

An independent `lake env lean --trust=0 --stdin` replay importing
LowerBoundProgram and LowerBoundAsymptotics checked 14 public entry points
covering the concrete family, anatomy, decoder, sparse count, legal simulator,
compiler result/count, adaptive/randomized identification, and finite
asymptotic lemma. Their transitive axiom sets were exactly the permitted
`propext`, `Classical.choice`, and `Quot.sound`. This run preceded the final
main/extended-asymptotic additions and is not a substitute for their final
verification.

A direct source scan found no `sorry`, `admit`, custom axioms, unsafe
declarations, extern implementations, or opaque proof substitutions in the
reviewed lower stack.

The final independent origin-complete audit imported MainLowerBound,
LowerBoundStrategy, and SharpSparseSupply with Lean `--trust=0`; it selected
all declarations by originating module in the 13-module footprint below,
including private and generated constants, and ran `Lean.collectAxioms` on
each full transitive closure. It checked **909 declarations in all 13
requested modules**, terminating successfully with only `propext`,
`Classical.choice`, and `Quot.sound`. This was a fresh independent audit of
the frozen built modules, not reliance on the author's selected-entrypoint
log. Exact terminal summary:

```
PASS: lower-stack origin-complete audit of 909 declarations in 13 modules under --trust=0; only propext, Classical.choice, Quot.sound.
```

## Frozen review footprint

The lower-stack semantic acceptance is specific to the following SHA-256
values. Directly inspected foundational definitions are included. The release
inventory above supplies the remaining imported-project and dependency pins.

```

730ad85f9cf5d9430313cff56aef354d28539d3646cc62179a666f276e8a5997  CombinatorialContracts/EqualRevenue.lean
1e6569d98118494d7b96340a5a83d7216b01560462fb194a3346a4cc6f3dd99c  CombinatorialContracts/LowerBounds.lean
66c1b6ef26068e1b953860f05fc053080a20f0bc852394627b648e56458d72ef  CombinatorialContracts/SparseSupply.lean
74065bda388bdc03563bf30c759166a8abffc494a55c8eb9a92456dc34912e2c  CombinatorialContracts/SharpSparseSupply.lean
e56799591d43b46525cd6f47d6d695f49a905420993d5da3685d3bcd777647e2  CombinatorialContracts/SupplySimulation.lean
518f621b52c9e1ccbd485ed9630cae344000403ecaf764c829dda5147093f89f  CombinatorialContracts/OracleIdentification.lean
62e77aa480df6ac2e61d7b96db9b8baa8ce109abcf3cfa791dca7f8a5fb831ce  CombinatorialContracts/LowerBoundProgram.lean
388d2bdaa85dafb5c531f396ab52217ce78a5bdf5ea077a40d70199c02d57523  CombinatorialContracts/MainLowerBound.lean
62a71011c1af6e92cc93ff37b4dade4b23eb2fb5153f0c55180e81a257205449  CombinatorialContracts/LowerBoundAsymptotics.lean
f2e2cca3210749b28854a2a6e4d234574662002fef834cdcc2589b25d33bfb5d  CombinatorialContracts/LowerBoundStrategy.lean
2a89c3c567fd77906bc84e18ea84e0f8477e5f93130333ef01a1fa0d70b9fd7e  CombinatorialContracts/Model.lean
5dd17825f879cf8fd40229cb61cf904263ca2c51722aa35e30326352216c3324  CombinatorialContracts/ChainEnvelope.lean
d3ca0f786dad443f2b16adbbdc0744d88fb3866db2afe93dcbca7ead1b25fb77  CombinatorialContracts/SupplyProgram.lean
```

## Final judgment

**Accepted.** At the frozen inventory and hashes above, the lower stack
proves the concrete hard family, full source-tolerance sparse-supply bound,
exact legal supply simulation, contract-only decoder, adaptive search lower
bound including the unqueried guess, arbitrary independent seed
randomization, per-instance success averaging, extended expectations,
polynomial-extra-query asymptotics, and an actual worst-instance lower bound
for both high-accuracy approximation and exact optimization. Proposition 10's
assembled anatomy statement is also accepted.

There is no remaining replacement sparse-supply, identification, query-cost,
or exponential-growth assumption in the terminal lower-bound theorems. The
algorithmic success and polynomial auxiliary-query hypotheses are the
intended source premises. The explicitly documented measurability and
actual-path termination scope remains part of this acceptance; divergent
runs themselves are not assigned operational infinite counts by the syntax.

All proof files in this footprint were explicitly frozen before the final
independent build. The final build, 51-file inventory match, and 909-declaration
transitive axiom audit passed. Any later change to these proof contents or
semantic dependencies requires renewed review. This is lower-stack
certification, not a claim that this reviewer independently reviewed all
upper-bound proofs. The pinned NarrowDNF project and dependencies have not
been modified by this reviewer.

