# Source audit: external equal-revenue lower-bound dependency

Official source inspected: arXiv:2403.09794v2, downloaded from
https://arxiv.org/src/2403.09794v2 and frozen in originals/dependencies/dfgr26.

Appendix D defines c(0)=0 and c(t)-c(t-1)=(t-1)/t. Consequently c(1)=0.
The lemma labelled `lem:cMonoSuperMod` incorrectly calls this cost strictly
monotone: the empty set and the first singleton have the same cost. The cost
is nondecreasing, and its increments are strictly increasing.

Appendix E, display `eq:eps_0_SupMod_c`, asks for a strictly positive perturbation
smaller than every consecutive cost increment including t=1. This is impossible
because that increment is zero. Lowering the cost of index 1 would also make it
negative. The displayed supermodular minimum uses S⊆T rather than S⊊T, which
likewise includes zero marginal gaps.

These endpoint errors do not invalidate the restricted family used in
arXiv:2609.35803v1: that paper takes n≥2 and hidden indices
ceil((2^n-1)/2)≤k≤2^n-1, hence k≥2, and explicitly uses strict inclusions when
bounding nontrivial supermodular gaps. Its perturbation is 1/(8(2^n-1)^2).
The formal development must derive the nonnegative monotone supermodular
restricted family directly, and must not assume the invalid unrestricted
perturbation premise from the external source.

The sparse-supply argument is separately in Appendix E.3 and refers to the
counting proof in Section 4.3. Its hypothesis is a perturbation less than half
the smallest positive difference of distinct critical shares. This statement
is compatible with the main paper's choice. No main-paper theorem has been
refuted by this audit.
