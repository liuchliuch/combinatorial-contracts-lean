import Mathlib

/-!
# Exact finite combinatorial-contract model

This file formalizes Section 2 and the response monotonicity lemma of
Deng–Li–Liu, *Approximating Combinatorial Contracts with Arbitrary Costs*,
arXiv:2609.35803v1. A response maximizes agent utility and then gross reward.
No restriction is imposed on the cost beyond normalization and nonnegativity.
-/

namespace CombinatorialContracts

universe u

/-- A normalized nonnegative, monotone subadditive reward and an arbitrary
normalized nonnegative cost on the subsets of a finite ground set. -/
structure Model (ι : Type u) [Fintype ι] [DecidableEq ι] where
  reward : Finset ι → ℝ
  cost : Finset ι → ℝ
  reward_empty : reward ∅ = 0
  cost_empty : cost ∅ = 0
  reward_nonneg : ∀ S, 0 ≤ reward S
  cost_nonneg : ∀ S, 0 ≤ cost S
  reward_mono : Monotone reward
  reward_subadditive : ∀ S T, reward (S ∪ T) ≤ reward S + reward T

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The agent's expected payment minus effort cost. -/
def agentUtility (M : Model ι) (α : ℝ) (S : Finset ι) : ℝ :=
  α * M.reward S - M.cost S

/-- The agent chooses a utility-maximizing action set. -/
def IsBestResponse (M : Model ι) (α : ℝ) (S : Finset ι) : Prop :=
  ∀ T, agentUtility M α T ≤ agentUtility M α S

/-- The exact response convention in the paper: among utility maximizers,
choose one of largest gross reward. -/
def IsResponse (M : Model ι) (α : ℝ) (S : Finset ι) : Prop :=
  IsBestResponse M α S ∧ ∀ T, IsBestResponse M α T → M.reward T ≤ M.reward S

@[simp] theorem agentUtility_empty (M : Model ι) (α : ℝ) :
    agentUtility M α ∅ = 0 := by
  simp [agentUtility, M.reward_empty, M.cost_empty]

/-- Finite maximization, followed by finite reward maximization, realizes the
stated tie-breaking rule, for every real share. -/
theorem exists_response (M : Model ι) (α : ℝ) : ∃ S, IsResponse M α S := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset ι)) (agentUtility M α) Finset.univ_nonempty
  have hS' : IsBestResponse M α S := fun T => hS T (Finset.mem_univ T)
  let B := Finset.univ.filter (IsBestResponse M α)
  have hB : B.Nonempty := ⟨S, by simp [B, hS']⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image B M.reward hB
  exact ⟨T, (Finset.mem_filter.mp hT).2, fun U hU =>
    hmax U (by simp [B, hU])⟩

/-- An exact best-response oracle with the paper's reward tie-break. -/
noncomputable def response (M : Model ι) (α : ℝ) : Finset ι :=
  Classical.choose (exists_response M α)

theorem response_spec (M : Model ι) (α : ℝ) : IsResponse M α (response M α) :=
  Classical.choose_spec (exists_response M α)

theorem response_best (M : Model ι) (α : ℝ) : IsBestResponse M α (response M α) :=
  (response_spec M α).1

/-- Principal utility under the exact response oracle. -/
noncomputable def principal (M : Model ι) (α : ℝ) : ℝ :=
  (1 - α) * M.reward (response M α)

/-- A single response query at share one obtains maximum total welfare. -/
noncomputable def welfare (M : Model ι) : ℝ :=
  M.reward (response M 1) - M.cost (response M 1)

theorem welfare_eq_agentUtility (M : Model ι) :
    welfare M = agentUtility M 1 (response M 1) := by
  simp [welfare, agentUtility]

theorem welfare_max (M : Model ι) (S : Finset ι) :
    M.reward S - M.cost S ≤ welfare M := by
  simpa [agentUtility, welfare] using response_best M 1 S

theorem welfare_nonneg (M : Model ι) : 0 ≤ welfare M := by
  simpa [M.reward_empty, M.cost_empty] using welfare_max M ∅

theorem bestResponse_agentUtility_nonneg (M : Model ι) {α : ℝ} {S : Finset ι}
    (hS : IsBestResponse M α S) : 0 ≤ agentUtility M α S := by
  simpa using hS ∅

theorem response_cost_le (M : Model ι) (α : ℝ) :
    M.cost (response M α) ≤ α * M.reward (response M α) := by
  have h := bestResponse_agentUtility_nonneg M (response_best M α)
  dsimp [agentUtility] at h
  linarith

/-- The lower half of the welfare–profit comparison is independent of any
cost regularity and of reward monotonicity or subadditivity. -/
theorem principal_le_welfare (M : Model ι) (α : ℝ) :
    principal M α ≤ welfare M := by
  have hcost := response_cost_le M α
  have hw := welfare_max M (response M α)
  dsimp [principal]
  nlinarith

theorem principal_nonneg (M : Model ι) {α : ℝ} (hα : α ≤ 1) :
    0 ≤ principal M α :=
  mul_nonneg (sub_nonneg.mpr hα) (M.reward_nonneg _)

/-- Equal-share exact responses always have equal rewards. -/
theorem response_reward_unique (M : Model ι) {α : ℝ} {S T : Finset ι}
    (hS : IsResponse M α S) (hT : IsResponse M α T) :
    M.reward S = M.reward T :=
  le_antisymm (hT.2 S hS.1) (hS.2 T hT.1)

/-- Response-reward monotonicity (Lemma 4). The two best-response inequalities
handle distinct shares; the explicit tie-break handles equal shares. -/
theorem response_reward_monotone (M : Model ι) {α β : ℝ} {S T : Finset ι}
    (hαβ : α ≤ β) (hS : IsResponse M α S) (hT : IsResponse M β T) :
    M.reward S ≤ M.reward T := by
  rcases hαβ.eq_or_lt with h | h
  · subst β
    exact hT.2 S hS.1
  · have hST := hS.1 T
    have hTS := hT.1 S
    dsimp [agentUtility] at hST hTS
    by_contra hnot
    have hr : 0 < M.reward S - M.reward T := sub_pos.mpr (lt_of_not_ge hnot)
    have hp := mul_pos (sub_pos.mpr h) hr
    nlinarith

theorem response_reward_mono (M : Model ι) :
    Monotone (fun α : ℝ => M.reward (response M α)) :=
  fun _ _ h => response_reward_monotone M h (response_spec M _) (response_spec M _)

/-- Tied agent utilities satisfy the reward/cost difference identity used by
the paper's reduction to a supply oracle. -/
theorem cost_sub_eq_share_mul_reward_sub (M : Model ι) {α : ℝ} {S T : Finset ι}
    (h : agentUtility M α S = agentUtility M α T) :
    M.cost S - M.cost T = α * (M.reward S - M.reward T) := by
  dsimp [agentUtility] at h
  nlinarith

/-- At positive agent shares, larger-cost and larger-reward tie-breaking agree. -/
theorem tied_cost_le_iff_reward_le (M : Model ι) {α : ℝ} {S T : Finset ι}
    (hα : 0 < α) (h : agentUtility M α S = agentUtility M α T) :
    M.cost S ≤ M.cost T ↔ M.reward S ≤ M.reward T := by
  have heq := cost_sub_eq_share_mul_reward_sub M h
  constructor <;> intro hle
  · by_contra hnot
    have hp := mul_pos hα (sub_pos.mpr (lt_of_not_ge hnot))
    linarith
  · have hp := mul_nonpos_of_nonneg_of_nonpos hα.le (sub_nonpos.mpr hle)
    linarith

/-- The standard larger-cost supply tie-break. -/
def IsCostTieResponse (M : Model ι) (α : ℝ) (S : Finset ι) : Prop :=
  IsBestResponse M α S ∧ ∀ T, IsBestResponse M α T → M.cost T ≤ M.cost S

theorem costTieResponse_iff_response (M : Model ι) {α : ℝ} {S : Finset ι}
    (hα : 0 < α) : IsCostTieResponse M α S ↔ IsResponse M α S := by
  constructor
  · rintro ⟨hS, hcost⟩
    refine ⟨hS, fun T hT => ?_⟩
    exact (tied_cost_le_iff_reward_le M hα (le_antisymm (hS T) (hT S))).mp
      (hcost T hT)
  · rintro ⟨hS, hreward⟩
    refine ⟨hS, fun T hT => ?_⟩
    exact (tied_cost_le_iff_reward_le M hα (le_antisymm (hS T) (hT S))).mpr
      (hreward T hT)

/-- Every finite combinatorial-contract instance attains its principal optimum.
We maximize the continuous pair objective over all feasible best-response
pairs. The feasible set is compact. Replacing its maximizer by the stipulated
reward-favoring response can only increase principal utility on `[0,1]`. -/
theorem exists_optimum (M : Model ι) :
    ∃ α ∈ Set.Icc (0 : ℝ) 1, ∀ β ∈ Set.Icc (0 : ℝ) 1,
      principal M β ≤ principal M α := by
  classical
  letI : TopologicalSpace (Finset ι) := ⊥
  letI : DiscreteTopology (Finset ι) := ⟨rfl⟩
  let K : Set (ℝ × Finset ι) :=
    {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ IsBestResponse M p.1 p.2}
  have hreward : Continuous (M.reward : Finset ι → ℝ) :=
    continuous_of_discreteTopology
  have hcost : Continuous (M.cost : Finset ι → ℝ) :=
    continuous_of_discreteTopology
  have hu : Continuous (fun p : ℝ × Finset ι => agentUtility M p.1 p.2) := by
    exact (continuous_fst.mul (hreward.comp continuous_snd)).sub
      (hcost.comp continuous_snd)
  have hclosed : IsClosed {p : ℝ × Finset ι | IsBestResponse M p.1 p.2} := by
    have hc : IsClosed (⋂ T : Finset ι,
        {p : ℝ × Finset ι | agentUtility M p.1 T ≤ agentUtility M p.1 p.2}) :=
      isClosed_iInter fun T => isClosed_le
        ((continuous_fst.mul continuous_const).sub continuous_const) hu
    simpa only [← Set.setOf_forall, IsBestResponse] using hc
  have hcompact : IsCompact K := by
    have hbase : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Finset ι))) :=
      isCompact_Icc.prod (Set.toFinite _).isCompact
    have heq : K = (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Finset ι))) ∩
        {p : ℝ × Finset ι | IsBestResponse M p.1 p.2} := by
      ext p
      simp [K]
    rw [heq]
    exact hbase.inter_right hclosed
  have hnonempty : K.Nonempty := by
    exact ⟨(0, response M 0), ⟨by norm_num, response_best M 0⟩⟩
  let F : ℝ × Finset ι → ℝ := fun p => (1 - p.1) * M.reward p.2
  have hF : Continuous F :=
    (continuous_const.sub continuous_fst).mul (hreward.comp continuous_snd)
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hnonempty hF.continuousOn
  refine ⟨p.1, hp.1, fun β hβ => ?_⟩
  have hle : principal M β ≤ F p := by
    change F (β, response M β) ≤ F p
    exact hmax (show (β, response M β) ∈ K from ⟨hβ, response_best M β⟩)
  have hrewardle := (response_spec M p.1).2 p.2 hp.2
  have hple : F p ≤ principal M p.1 :=
    mul_le_mul_of_nonneg_left hrewardle (sub_nonneg.mpr hp.1.2)
  exact hle.trans hple

/-- An optimal contract, whose existence is proved from the finite model. -/
noncomputable def optimum (M : Model ι) : ℝ :=
  Classical.choose (exists_optimum M)

theorem optimum_mem (M : Model ι) : optimum M ∈ Set.Icc (0 : ℝ) 1 :=
  (Classical.choose_spec (exists_optimum M)).1

/-- The paper's `P* = OPT`. -/
noncomputable def optimalValue (M : Model ι) : ℝ := principal M (optimum M)

theorem principal_le_optimalValue (M : Model ι) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) : principal M α ≤ optimalValue M :=
  (Classical.choose_spec (exists_optimum M)).2 α hα

theorem optimalValue_nonneg (M : Model ι) : 0 ≤ optimalValue M :=
  principal_nonneg M (optimum_mem M).2

theorem optimalValue_le_welfare (M : Model ι) : optimalValue M ≤ welfare M :=
  principal_le_welfare M (optimum M)

/-- Any best-response set (even without the tie-break) earns at most the
optimal principal utility at a feasible contract. -/
theorem bestResponse_principal_le_optimalValue (M : Model ι) {α : ℝ}
    {S : Finset ι} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hS : IsBestResponse M α S) :
    (1 - α) * M.reward S ≤ optimalValue M := by
  apply le_trans _ (principal_le_optimalValue M hα)
  exact mul_le_mul_of_nonneg_left ((response_spec M α).2 S hS)
    (sub_nonneg.mpr hα.2)

@[simp] theorem principal_one (M : Model ι) : principal M 1 = 0 := by
  simp [principal]

theorem response_zero_cost (M : Model ι) : M.cost (response M 0) = 0 := by
  apply le_antisymm _ (M.cost_nonneg _)
  simpa using response_cost_le M 0

@[simp] theorem agentUtility_response_zero (M : Model ι) :
    agentUtility M 0 (response M 0) = 0 := by
  simp [agentUtility, response_zero_cost]

theorem optimum_lt_one_of_optimalValue_pos (M : Model ι)
    (h : 0 < optimalValue M) : optimum M < 1 := by
  refine lt_of_le_of_ne (optimum_mem M).2 ?_
  intro heq
  have : optimalValue M = 0 := by simp [optimalValue, heq]
  linarith

/-- Additivity is a separate, stronger reward assumption used only for the
supply-oracle reduction. -/
def HasAdditiveReward (M : Model ι) : Prop :=
  ∀ S, M.reward S = ∑ i ∈ S, M.reward {i}

/-- Standard supply utility at item prices `p`. -/
def supplyUtility (M : Model ι) (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ i ∈ S, p i) - M.cost S

/-- With additive rewards the payment is exactly the sum of item prices. -/
theorem supplyUtility_eq_agentUtility (M : Model ι) (hadd : HasAdditiveReward M)
    (α : ℝ) (S : Finset ι) :
    supplyUtility M (fun i => α * M.reward {i}) S = agentUtility M α S := by
  simp only [supplyUtility, agentUtility, hadd S, Finset.mul_sum]

/-- A supply oracle maximizes the value of supplied items minus cost and
breaks ties toward higher cost, as specified in Section 2 of the paper. -/
def IsSupplyResponse (M : Model ι) (p : ι → ℝ) (S : Finset ι) : Prop :=
  (∀ T, supplyUtility M p T ≤ supplyUtility M p S) ∧
  ∀ T, (∀ U, supplyUtility M p U ≤ supplyUtility M p T) → M.cost T ≤ M.cost S

/-- For additive rewards and positive shares, the ordinary supply oracle
with its larger-cost tie-break implements exactly the paper's response rule. -/
theorem supplyResponse_iff_response (M : Model ι) (hadd : HasAdditiveReward M)
    {α : ℝ} {S : Finset ι} (hα : 0 < α) :
    IsSupplyResponse M (fun i => α * M.reward {i}) S ↔ IsResponse M α S := by
  have heq : IsSupplyResponse M (fun i => α * M.reward {i}) S ↔
      IsCostTieResponse M α S := by
    simp only [IsSupplyResponse, IsCostTieResponse, IsBestResponse,
      supplyUtility_eq_agentUtility M hadd]
  exact heq.trans (costTieResponse_iff_response M hα)

end CombinatorialContracts
