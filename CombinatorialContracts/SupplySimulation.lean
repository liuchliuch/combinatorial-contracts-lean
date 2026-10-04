import CombinatorialContracts.LowerBounds
import CombinatorialContracts.SparseSupply

/-!
# Concrete sparse-supply simulation

One batch of equality tests on the polynomial-sized base approximate-supply
family simulates a legal supply response to the hidden perturbation. The
simulation preserves the specified larger-cost tie-break.
-/
namespace CombinatorialContracts.LowerBounds
noncomputable section
open Finset EqualRevenue
attribute [local instance] Classical.propDecidable

/-- Finite utility maximization followed by cost maximization realizes the
paper's precise supply-response convention. -/
theorem exists_supplyResponse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Model ι) (p : ι → ℝ) : ∃ S, IsSupplyResponse M p S := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset ι)) (supplyUtility M p) Finset.univ_nonempty
  have hS' : ∀ T, supplyUtility M p T ≤ supplyUtility M p S :=
    fun T => hS T (Finset.mem_univ T)
  let B := Finset.univ.filter (fun S => ∀ T, supplyUtility M p T ≤ supplyUtility M p S)
  have hB : B.Nonempty := ⟨S, by simp [B, hS']⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image B M.cost hB
  exact ⟨T, (Finset.mem_filter.mp hT).2, fun U hU => hmax U (by simp [B, hU])⟩

/-- A fixed, deterministic legal supply response. -/
def chosenSupplyResponse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Model ι) (p : ι → ℝ) : Finset ι :=
  Classical.choose (exists_supplyResponse M p)

theorem chosenSupplyResponse_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Model ι) (p : ι → ℝ) : IsSupplyResponse M p (chosenSupplyResponse M p) :=
  Classical.choose_spec (exists_supplyResponse M p)

/-- Candidate indices depend on the known base instance and prices only. -/
def candidateIndices (n : ℕ) (p : Fin n → ℝ) : Finset ℕ :=
  (approxSupply n p (perturbation (2^n-1))).image binaryIndex

theorem candidateIndices_card (n : ℕ) (p : Fin n → ℝ) :
    (candidateIndices n p).card ≤ 4*(n+1)^2 :=
  (Finset.card_image_le).trans (approxSupply_card_explicit n p)

theorem supplyUtility_perturbed (n k : ℕ) (hk : 2 ≤ k) (p : Fin n → ℝ)
    (S : Finset (Fin n)) :
    supplyUtility (model n k hk) p S = supplyUtility (EqualRevenue.model n) p S +
      if binaryIndex S = k then perturbation (2^n-1) else 0 := by
  simp only [supplyUtility, model, EqualRevenue.model, perturbedCost]
  ring

theorem supplyUtility_perturbed_bounds (n k : ℕ) (hk : 2 ≤ k) (p : Fin n → ℝ)
    (S : Finset (Fin n)) :
    supplyUtility (EqualRevenue.model n) p S ≤ supplyUtility (model n k hk) p S ∧
    supplyUtility (model n k hk) p S ≤
      supplyUtility (EqualRevenue.model n) p S + perturbation (2^n-1) := by
  rw [supplyUtility_perturbed]
  have hζ : 0 ≤ perturbation (2^n-1) := by unfold perturbation; positivity
  split_ifs <;> constructor <;> linarith

/-- Every exact perturbed optimizer lies in the explicit base approximate
supply family; the statement does not need any tie-breaking hypothesis. -/
theorem perturbed_optimizer_mem_approxSupply {n k : ℕ} (hk : 2 ≤ k)
    (p : Fin n → ℝ) {S : Finset (Fin n)}
    (hS : ∀ T, supplyUtility (model n k hk) p T ≤ supplyUtility (model n k hk) p S) :
    S ∈ approxSupply n p (perturbation (2^n-1)) := by
  apply mem_approxSupply.mpr
  intro T
  exact (supplyUtility_perturbed_bounds n k hk p T).1.trans
    ((hS T).trans (supplyUtility_perturbed_bounds n k hk p S).2)

private theorem base_optimizer_mem_approxSupply {n : ℕ} (p : Fin n → ℝ)
    {S : Finset (Fin n)}
    (hS : ∀ T, supplyUtility (EqualRevenue.model n) p T ≤
      supplyUtility (EqualRevenue.model n) p S) :
    S ∈ approxSupply n p (perturbation (2^n-1)) := by
  apply mem_approxSupply.mpr
  intro T
  have hζ : 0 ≤ perturbation (2^n-1) := by unfold perturbation; positivity
  exact (hS T).trans (by linarith)

private theorem noncandidate_index_ne {n k : ℕ} {p : Fin n → ℝ}
    (hk : k ∉ candidateIndices n p) {S : Finset (Fin n)}
    (hS : S ∈ approxSupply n p (perturbation (2^n-1))) : binaryIndex S ≠ k := by
  intro heq
  apply hk
  exact Finset.mem_image.mpr ⟨S, hS, heq⟩

private theorem noncandidate_cost_eq {n k : ℕ} (hk : 2 ≤ k) {p : Fin n → ℝ}
    (hmiss : k ∉ candidateIndices n p) {S : Finset (Fin n)}
    (hS : S ∈ approxSupply n p (perturbation (2^n-1))) :
    (model n k hk).cost S = (EqualRevenue.model n).cost S := by
  simp only [model, EqualRevenue.model, perturbedCost,
    noncandidate_index_ne hmiss hS, ↓reduceIte, sub_zero]

private theorem noncandidate_supplyUtility_eq {n k : ℕ} (hk : 2 ≤ k) {p : Fin n → ℝ}
    (hmiss : k ∉ candidateIndices n p) {S : Finset (Fin n)}
    (hS : S ∈ approxSupply n p (perturbation (2^n-1))) :
    supplyUtility (model n k hk) p S = supplyUtility (EqualRevenue.model n) p S := by
  rw [supplyUtility_perturbed]
  simp [noncandidate_index_ne hmiss hS]

/-- A missed batch leaves a fixed base response legal for the hidden model,
including all cost-based tie-breaking comparisons. -/
theorem base_supplyResponse_of_not_mem {n k : ℕ} (hk : 2 ≤ k) (p : Fin n → ℝ)
    (hmiss : k ∉ candidateIndices n p) {S : Finset (Fin n)}
    (hS : IsSupplyResponse (EqualRevenue.model n) p S) :
    IsSupplyResponse (model n k hk) p S := by
  have hSa := base_optimizer_mem_approxSupply p hS.1
  have hSe := noncandidate_supplyUtility_eq hk hmiss hSa
  have hSc := noncandidate_cost_eq hk hmiss hSa
  obtain ⟨R, hR⟩ := exists_supplyResponse (model n k hk) p
  have hRa := perturbed_optimizer_mem_approxSupply hk p hR.1
  have hRe := noncandidate_supplyUtility_eq hk hmiss hRa
  have hbest : ∀ T, supplyUtility (model n k hk) p T ≤ supplyUtility (model n k hk) p S := by
    intro T
    have hmax := hR.1 T
    rw [hRe] at hmax
    rw [hSe]
    exact hmax.trans (hS.1 R)
  refine ⟨hbest, ?_⟩
  intro T hT
  have hTa := perturbed_optimizer_mem_approxSupply hk p hT
  have hTe := noncandidate_supplyUtility_eq hk hmiss hTa
  have hTc := noncandidate_cost_eq hk hmiss hTa
  rw [hSc, hTc]
  apply hS.2 T
  intro U
  have hST := hT S
  rw [hSe, hTe] at hST
  exact (hS.1 U).trans hST

/-- The single batch answer exposes the hidden index if it is in the known
candidate family, and says `none` otherwise. -/
def supplyBatchHit (n k : ℕ) (p : Fin n → ℝ) : Option ℕ :=
  if k ∈ candidateIndices n p then some k else none

/-- Simulation uses only prices, the known base model, and the batch answer.
Small invalid indices receive a harmless base fallback. -/
def supplyAnswer (n : ℕ) (p : Fin n → ℝ) (hit : Option ℕ) : Finset (Fin n) :=
  match hit with
  | none => chosenSupplyResponse (EqualRevenue.model n) p
  | some k => if hk : 2 ≤ k then chosenSupplyResponse (model n k hk) p
      else chosenSupplyResponse (EqualRevenue.model n) p

/-- The concrete batch simulator always returns a legal supply answer. -/
theorem supplyAnswer_correct {n k : ℕ} (hk : 2 ≤ k) (p : Fin n → ℝ) :
    IsSupplyResponse (model n k hk) p (supplyAnswer n p (supplyBatchHit n k p)) := by
  by_cases hhit : k ∈ candidateIndices n p
  · simp only [supplyBatchHit, hhit, ↓reduceIte, supplyAnswer, hk, ↓reduceDIte]
    exact chosenSupplyResponse_spec _ _
  · simp only [supplyBatchHit, hhit, ↓reduceIte, supplyAnswer]
    exact base_supplyResponse_of_not_mem hk p hhit (chosenSupplyResponse_spec _ _)

/-- Explicit statement of the simulation interface without the batch wrapper. -/
theorem supplyAnswer_correct_if {n k : ℕ} (hk : 2 ≤ k) (p : Fin n → ℝ) :
    IsSupplyResponse (model n k hk) p
      (supplyAnswer n p (if k ∈ candidateIndices n p then some k else none)) :=
  supplyAnswer_correct hk p

end
end CombinatorialContracts.LowerBounds
