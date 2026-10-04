import CombinatorialContracts.Model

namespace CombinatorialContracts.EndpointRegression

/-- One free action, used to expose the zero-share supply tie edge case. -/
def freeAction : Model (Fin 1) where
  reward S := S.card
  cost _ := 0
  reward_empty := by simp
  cost_empty := rfl
  reward_nonneg := by intro; positivity
  cost_nonneg := by intro; rfl
  reward_mono := by
    intro S T h
    change (S.card : ℝ) ≤ T.card
    exact_mod_cast Finset.card_le_card h
  reward_subadditive := by
    intro S T
    exact_mod_cast Finset.card_union_le S T

/-- At zero prices, the cost-based supply tie rule may select the empty set. -/
theorem supply_may_return_empty_at_zero :
    IsSupplyResponse freeAction (fun _ => 0) ∅ := by
  constructor <;> simp [supplyUtility, freeAction]

/-- Principal-favoring contract tie-breaking cannot select that empty set.
This verifies why Algorithm 1's positive-share shift is essential. -/
theorem response_cannot_return_empty_at_zero :
    ¬ IsResponse freeAction 0 ∅ := by
  intro h
  have hb : IsBestResponse freeAction 0 ({0} : Finset (Fin 1)) := by
    intro T
    simp [agentUtility, freeAction]
  have hbad := h.2 {0} hb
  norm_num [freeAction] at hbad

/-- At the other endpoint, the principal always receives zero. -/
example : principal freeAction 1 = 0 := principal_one _

/-- Empty ground sets have only the empty response and zero principal value. -/
theorem empty_ground_principal (M : Model (Fin 0)) (α : ℝ) : principal M α = 0 := by
  have hs : response M α = ∅ := by
    ext i
    exact Fin.elim0 i
  simp [principal, hs, M.reward_empty]

theorem empty_ground_optimalValue (M : Model (Fin 0)) : optimalValue M = 0 :=
  empty_ground_principal M _

theorem empty_ground_welfare (M : Model (Fin 0)) : welfare M = 0 := by
  have hs : response M 1 = ∅ := by
    ext i
    exact Fin.elim0 i
  simp [welfare, hs, M.reward_empty, M.cost_empty]

end CombinatorialContracts.EndpointRegression
