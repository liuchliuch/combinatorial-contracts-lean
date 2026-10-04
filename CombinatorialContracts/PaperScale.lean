import CombinatorialContracts.Scale

/-!
# Source-quantified reward-anchored scale

This file states Lemma 6 with the paper's universal choices: any optimal
contract-response pair and any largest-singleton action in that response.
The selected `optimum` and `response` witnesses are not part of the statement.
-/

namespace CombinatorialContracts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma 6, with every optimal pair and every largest-singleton choice
allowed. The singleton reward and the lower endpoint are strictly positive,
so the endpoint-ratio assertion is nondegenerate. -/
theorem reward_anchored_scale_of_optimal_response (M : Model ι)
    {α : ℝ} {S : Finset ι} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hS : IsResponse M α S)
    (hoptimal : (1 - α) * M.reward S = optimalValue M)
    (hopt : 0 < optimalValue M) {j : ι} (hj : j ∈ S)
    (hmax : ∀ i ∈ S, M.reward {i} ≤ M.reward {j}) :
    0 < M.reward {j} ∧
      0 < welfare M / ((Fintype.card ι : ℝ) ^ 2 * M.reward {j}) ∧
      welfare M / ((Fintype.card ι : ℝ) ^ 2 * M.reward {j}) ≤ 1 - α ∧
      1 - α ≤ min 1 (welfare M / M.reward {j}) ∧
      min 1 (welfare M / M.reward {j}) /
          (welfare M / ((Fintype.card ι : ℝ) ^ 2 * M.reward {j})) ≤
        (Fintype.card ι : ℝ) ^ 2 := by
  have hδ : 0 ≤ 1 - α := sub_nonneg.mpr hα.2
  have hSpos : 0 < M.reward S := by
    have hv := M.reward_nonneg S
    nlinarith [hoptimal]
  have hav : M.reward {j} ≤ M.reward S :=
    M.reward_mono (Finset.singleton_subset_iff.mpr hj)
  have hva : M.reward S ≤ (Fintype.card ι : ℝ) * M.reward {j} := by
    calc
      M.reward S ≤ ∑ i ∈ S, M.reward {i} :=
        subadditive_le_sum_singletons M.reward M.reward_empty M.reward_subadditive S
      _ ≤ ∑ _i ∈ S, M.reward {j} := Finset.sum_le_sum hmax
      _ = (S.card : ℝ) * M.reward {j} := by simp
      _ ≤ (Fintype.card ι : ℝ) * M.reward {j} :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S)
          (M.reward_nonneg _)
  have ha : 0 < M.reward {j} := by
    by_contra h
    have hprod : (Fintype.card ι : ℝ) * M.reward {j} ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt h)
    linarith
  have hn : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨j⟩ : 0 < Fintype.card ι)
  have hPW : optimalValue M ≤ welfare M := by
    calc
      optimalValue M = (1 - α) * M.reward S := hoptimal.symm
      _ = principal M α := by
        unfold principal
        rw [response_reward_unique M hS (response_spec M α)]
      _ ≤ welfare M := principal_le_welfare M α
  exact ⟨ha, scale_certificate_algebra hn ha hopt hδ (by linarith [hα.1])
    hoptimal.symm hav hva hPW (welfare_le_card_mul_optimalValue M)⟩

end CombinatorialContracts
