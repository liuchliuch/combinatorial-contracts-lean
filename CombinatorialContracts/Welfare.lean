import CombinatorialContracts.Model
import CombinatorialContracts.FiniteEnvelope

/-!
# Welfare and first appearances

The discrete charging lemma below refines the paper's first-appearance blocks
into individual actions. It needs no structure whatsoever on costs.
-/

namespace CombinatorialContracts

open scoped BigOperators

/-- Normalized subadditivity bounds the reward by its singleton rewards. -/
theorem subadditive_le_sum_singletons {ι : Type*} [DecidableEq ι]
    (f : Finset ι → ℝ) (hempty : f ∅ = 0)
    (hsub : ∀ S T, f (S ∪ T) ≤ f S + f T) (S : Finset ι) :
    f S ≤ ∑ i ∈ S, f {i} := by
  induction S using Finset.induction_on with
  | empty => simp [hempty]
  | @insert i S hi ih =>
      calc
        f (insert i S) = f ({i} ∪ S) := by simp
        _ ≤ f {i} + f S := hsub _ _
        _ ≤ f {i} + ∑ j ∈ S, f {j} := add_le_add_left ih _
        _ = ∑ j ∈ insert i S, f {j} := by rw [Finset.sum_insert hi]

/-- A discrete response curve can charge each action only from its first
appearance onward. This is the finite first-appearance argument, including
empty ground sets and zero-length pieces. -/
theorem finite_first_appearance_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Finset ι → ℝ) (hzero : f ∅ = 0)
    (hnonneg : ∀ S, 0 ≤ f S) (hmono : Monotone f)
    (hsub : ∀ S T, f (S ∪ T) ≤ f S + f T)
    (k : ℕ) (a : ℕ → ℝ) (S : ℕ → Finset ι) (P : ℝ)
    (hP : 0 ≤ P) (hend : a k = 1)
    (hstep : ∀ t < k, a t ≤ a (t + 1))
    (hupper : ∀ t < k, a t ≤ 1)
    (hprofit : ∀ t < k, (1 - a t) * f (S t) ≤ P) :
    (∑ t ∈ Finset.range k, (a (t + 1) - a t) * f (S t)) ≤
      (Fintype.card ι : ℝ) * P := by
  classical
  let d : ℕ → ℝ := fun t => a (t + 1) - a t
  have hd : ∀ t < k, 0 ≤ d t := fun t ht => sub_nonneg.mpr (hstep t ht)
  have hcharge : ∀ i : ι,
      (∑ t ∈ (Finset.range k).filter (fun t => i ∈ S t), d t) * f {i} ≤ P := by
    intro i
    let visits := (Finset.range k).filter (fun t => i ∈ S t)
    by_cases hv : visits.Nonempty
    · let first := visits.min' hv
      have hfmem : first ∈ visits := Finset.min'_mem visits hv
      have hfirst : first < k ∧ i ∈ S first := by
        simpa only [visits, Finset.mem_filter, Finset.mem_range] using hfmem
      have hsubset : visits ⊆ Finset.Ico first k := by
        intro t ht
        exact Finset.mem_Ico.mpr ⟨Finset.min'_le visits t ht,
          Finset.mem_range.mp (Finset.mem_filter.mp ht).1⟩
      have htime : (∑ t ∈ visits, d t) ≤ 1 - a first := by
        calc
          (∑ t ∈ visits, d t) ≤ ∑ t ∈ Finset.Ico first k, d t :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
              intro t ht _
              exact hd t (Finset.mem_Ico.mp ht).2)
          _ = a k - a first := Finset.sum_Ico_sub a (Nat.le_of_lt hfirst.1)
          _ = 1 - a first := by rw [hend]
      calc
        (∑ t ∈ (Finset.range k).filter (fun t => i ∈ S t), d t) * f {i}
            ≤ (1 - a first) * f {i} := mul_le_mul_of_nonneg_right htime (hnonneg _)
        _ ≤ (1 - a first) * f (S first) :=
          mul_le_mul_of_nonneg_left (hmono (Finset.singleton_subset_iff.mpr hfirst.2))
            (sub_nonneg.mpr (hupper first hfirst.1))
        _ ≤ P := hprofit first hfirst.1
    · have he : visits = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
      change (∑ t ∈ visits, d t) * f {i} ≤ P
      simpa [he] using hP
  calc
    (∑ t ∈ Finset.range k, (a (t + 1) - a t) * f (S t))
        ≤ ∑ t ∈ Finset.range k, d t * ∑ i ∈ S t, f {i} := by
          apply Finset.sum_le_sum
          intro t ht
          exact mul_le_mul_of_nonneg_left (subadditive_le_sum_singletons f hzero hsub (S t))
            (hd t (Finset.mem_range.mp ht))
    _ = ∑ t ∈ Finset.range k, ∑ i : ι, if i ∈ S t then d t * f {i} else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      simp [Finset.mul_sum, Finset.sum_ite_mem]
    _ = ∑ i : ι, ∑ t ∈ Finset.range k, if i ∈ S t then d t * f {i} else 0 :=
      Finset.sum_comm
    _ = ∑ i : ι, (∑ t ∈ (Finset.range k).filter (fun t => i ∈ S t), d t) * f {i} := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul, Finset.sum_filter]
    _ ≤ ∑ _i : ι, P := Finset.sum_le_sum (fun i _ => hcharge i)
    _ = (Fintype.card ι : ℝ) * P := by simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The affine envelope is exactly the best-response agent utility. -/
theorem envelope_eq_agentUtility (M : Model ι) (α : ℝ) :
    FiniteEnvelope.envelope M.reward M.cost α = agentUtility M α (response M α) := by
  exact (FiniteEnvelope.active_eq_envelope M.reward M.cost α (response M α)
    (response_best M α)).symm

/-- Nonnegative normalized costs force the initial envelope height to zero. -/
theorem envelope_zero (M : Model ι) :
    FiniteEnvelope.envelope M.reward M.cost 0 = 0 := by
  have he : FiniteEnvelope.IsActive M.reward M.cost 0 ∅ := by
    intro S
    simpa [FiniteEnvelope.line, M.cost_empty] using neg_nonpos.mpr (M.cost_nonneg S)
  have h := FiniteEnvelope.active_eq_envelope M.reward M.cost 0 ∅ he
  simpa [FiniteEnvelope.line, M.cost_empty] using h.symm

/-- The terminal envelope height is the welfare returned by a share-one query. -/
theorem envelope_one (M : Model ι) :
    FiniteEnvelope.envelope M.reward M.cost 1 = welfare M := by
  rw [envelope_eq_agentUtility, welfare_eq_agentUtility]

/-- Lemma 5, substantive upper comparison. The affine partition and all
first-appearance charges are constructed, with no regularity assumption on
costs beyond normalization and nonnegativity. -/
theorem welfare_le_card_mul_optimalValue (M : Model ι) :
    welfare M ≤ (Fintype.card ι : ℝ) * optimalValue M := by
  obtain ⟨k, a, S, _, _, hend, hstep, hbounds, hactive, harea⟩ :=
    FiniteEnvelope.exists_partition M.reward M.cost
  have hprofit : ∀ t < k, (1 - a t) * M.reward (S t) ≤ optimalValue M := by
    intro t ht
    have hbest : IsBestResponse M (a t) (S t) :=
      hactive t ht (a t) ⟨le_rfl, (hstep t ht).le⟩
    calc
      (1 - a t) * M.reward (S t) ≤ principal M (a t) :=
        mul_le_mul_of_nonneg_left ((response_spec M (a t)).2 (S t) hbest)
          (sub_nonneg.mpr (hbounds t (Nat.le_of_lt ht)).2)
      _ ≤ optimalValue M := principal_le_optimalValue M (hbounds t (Nat.le_of_lt ht))
  have hcharge := finite_first_appearance_bound M.reward M.reward_empty M.reward_nonneg
    M.reward_mono M.reward_subadditive k a S (optimalValue M)
    (optimalValue_nonneg M) hend (fun t ht => (hstep t ht).le)
    (fun t ht => (hbounds t (Nat.le_of_lt ht)).2) hprofit
  rw [harea, envelope_one, envelope_zero, sub_zero] at hcharge
  exact hcharge

/-- Lemma 5, both inequalities, including all degenerate cases. -/
theorem welfare_profit_comparison (M : Model ι) :
    optimalValue M ≤ welfare M ∧
      welfare M ≤ (Fintype.card ι : ℝ) * optimalValue M :=
  ⟨optimalValue_le_welfare M, welfare_le_card_mul_optimalValue M⟩

/-- Zero welfare and zero optimal principal utility are equivalent. -/
theorem welfare_eq_zero_iff_optimalValue_eq_zero (M : Model ι) :
    welfare M = 0 ↔ optimalValue M = 0 := by
  constructor
  · intro h
    exact le_antisymm (by simpa [h] using optimalValue_le_welfare M) (optimalValue_nonneg M)
  · intro h
    exact le_antisymm (by simpa [h] using welfare_le_card_mul_optimalValue M)
      (welfare_nonneg M)

/-- With no actions, both benchmark and optimum are exactly zero. -/
theorem empty_ground_zero (M : Model ι) (hn : Fintype.card ι = 0) :
    welfare M = 0 ∧ optimalValue M = 0 := by
  have hw : welfare M = 0 := le_antisymm
    (by simpa [hn] using welfare_le_card_mul_optimalValue M) (welfare_nonneg M)
  exact ⟨hw, (welfare_eq_zero_iff_optimalValue_eq_zero M).mp hw⟩

end CombinatorialContracts
