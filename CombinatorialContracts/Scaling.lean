import CombinatorialContracts.Model

namespace CombinatorialContracts
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rescale rewards and costs by the same strictly positive constant. -/
def scaledModel (M : Model ι) (scale : ℝ) (hscale : 0 < scale) : Model ι where
  reward S := scale * M.reward S
  cost S := scale * M.cost S
  reward_empty := by simp [M.reward_empty]
  cost_empty := by simp [M.cost_empty]
  reward_nonneg S := mul_nonneg hscale.le (M.reward_nonneg S)
  cost_nonneg S := mul_nonneg hscale.le (M.cost_nonneg S)
  reward_mono := fun _ _ h => mul_le_mul_of_nonneg_left (M.reward_mono h) hscale.le
  reward_subadditive S T := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (M.reward_subadditive S T) hscale.le

@[simp] theorem scaled_agentUtility (M : Model ι) (scale : ℝ) (hscale : 0 < scale)
    (α : ℝ) (S : Finset ι) :
    agentUtility (scaledModel M scale hscale) α S = scale * agentUtility M α S := by
  simp only [agentUtility, scaledModel]
  ring

@[simp] theorem scaled_bestResponse_iff (M : Model ι) (scale : ℝ) (hscale : 0 < scale)
    (α : ℝ) (S : Finset ι) :
    IsBestResponse (scaledModel M scale hscale) α S ↔ IsBestResponse M α S := by
  simp only [IsBestResponse, scaled_agentUtility, mul_le_mul_left hscale]

@[simp] theorem scaled_response_iff (M : Model ι) (scale : ℝ) (hscale : 0 < scale)
    (α : ℝ) (S : Finset ι) :
    IsResponse (scaledModel M scale hscale) α S ↔ IsResponse M α S := by
  simp only [IsResponse, scaled_bestResponse_iff]
  change (IsBestResponse M α S ∧ ∀ T, IsBestResponse M α T →
    scale * M.reward T ≤ scale * M.reward S) ↔ _
  simp only [mul_le_mul_iff_right₀ hscale]

theorem scaled_principal (M : Model ι) (scale : ℝ) (hscale : 0 < scale) (α : ℝ) :
    principal (scaledModel M scale hscale) α = scale * principal M α := by
  have hs : IsResponse M α (response (scaledModel M scale hscale) α) :=
    (scaled_response_iff M scale hscale α _).mp (response_spec _ _)
  have hr := response_reward_unique M hs (response_spec M α)
  change (1-α)*(scale*M.reward (response (scaledModel M scale hscale) α)) =
    scale*((1-α)*M.reward (response M α))
  rw [hr]
  ring

theorem scaled_welfare (M : Model ι) (scale : ℝ) (hscale : 0 < scale) :
    welfare (scaledModel M scale hscale) = scale * welfare M := by
  have hs : IsBestResponse M 1 (response (scaledModel M scale hscale) 1) :=
    (scaled_bestResponse_iff M scale hscale 1 _).mp (response_best _ _)
  have hu := le_antisymm (hs (response M 1))
    (response_best M 1 (response (scaledModel M scale hscale) 1))
  rw [welfare_eq_agentUtility, scaled_agentUtility, ← hu, ← welfare_eq_agentUtility]

theorem scaled_optimalValue (M : Model ι) (scale : ℝ) (hscale : 0 < scale) :
    optimalValue (scaledModel M scale hscale) = scale * optimalValue M := by
  apply le_antisymm
  · change principal (scaledModel M scale hscale) (optimum (scaledModel M scale hscale)) ≤ _
    rw [scaled_principal]
    exact mul_le_mul_of_nonneg_left
      (principal_le_optimalValue M (optimum_mem _)) hscale.le
  · have h := principal_le_optimalValue (scaledModel M scale hscale) (optimum_mem M)
    rw [scaled_principal] at h
    exact h

theorem scaled_additive (M : Model ι) (scale : ℝ) (hscale : 0 < scale)
    (ha : HasAdditiveReward M) : HasAdditiveReward (scaledModel M scale hscale) := by
  intro S
  simp only [scaledModel, ha S, Finset.mul_sum]

theorem scaled_total_one (M : Model ι) (h : 0 < M.reward Finset.univ) :
    (scaledModel M (1 / M.reward Finset.univ) (one_div_pos.mpr h)).reward Finset.univ = 1 := by
  simp [scaledModel, ne_of_gt h]

theorem scaled_reward_le_one (M : Model ι) (h : 0 < M.reward Finset.univ)
    (S : Finset ι) :
    (scaledModel M (1 / M.reward Finset.univ) (one_div_pos.mpr h)).reward S ≤ 1 := by
  have hm := (scaledModel M (1 / M.reward Finset.univ) (one_div_pos.mpr h)).reward_mono
    (Finset.subset_univ S)
  rwa [scaled_total_one M h] at hm

end CombinatorialContracts
