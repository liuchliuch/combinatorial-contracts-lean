# Combinatorial contracts in Lean

Lean 4 formalization of Xiaotie Deng, Hanyu Li and Chenghua Liu,
[*Approximating Combinatorial Contracts with Arbitrary Costs*](https://arxiv.org/abs/2609.35803v1).

The 27 proof modules cover all 10 numbered results and 34 supporting obligations.
The algorithms use the paper's exact-real oracle-query model, with explicit query
bounds, approximate responses and randomized lower bounds. Arithmetic and
comparisons are exact primitives; no polynomial bit-complexity claim is made.

## Build and verify

Install [Elan](https://github.com/leanprover/elan), Python 3, Bash and Git, then run:

```sh
lake exe cache get
python3 scripts/verify_publication.py
```

Lean 4.24.0 and all nine dependency revisions are pinned. The verifier checks
that every mathematical source and configuration matches the recorded release,
cleans this project only, builds all proofs, audits every originating declaration,
replays imports with trust level zero and runs the finite regression checks.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted axioms.

## Review the paper correspondence

- [Theorem ledger](docs/theorem-ledger.json): source statements and proof entry points.
- [Model review](docs/ModelReview.md) and [algorithm review](docs/AlgorithmAndRobustness.md): constructions and computational scope.
- [Source corrections](docs/source-corrections.md): the cited lower-bound endpoint repair.
- [Verification](docs/PUBLICATION_VERIFICATION.md): retained evidence and reproduction scope.

Lower-bound strategies terminate on the actual hard-family paths. Expectations
may be infinite across random seeds; positive-probability nonterminating failure
executions are not separately modeled. Favorable tie-breaking and zero-action
boundaries remain explicit in the statements.

Original paper files and required cited-source files retain their original text
and recorded hashes. No software license has been selected for this release.
