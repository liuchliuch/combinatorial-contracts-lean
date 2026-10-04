import CombinatorialContracts.SupplySimulation
import CombinatorialContracts.OracleIdentification
import CombinatorialContracts.SupplyProgram

/-!
# Operational compilation of arbitrary supply algorithms

The reduction below accepts the actual adaptive `SupplyProgram` datatype.
It locally answers known reward queries, compiles cost queries to singleton
equality tests, and compiles supply queries to the concrete sparse batches.
Result preservation and the query bound hold on every hidden-instance path.
-/
namespace CombinatorialContracts.LowerBounds
noncomputable section
open Finset EqualRevenue OracleIdentification
attribute [local instance] Classical.propDecidable

abbrev SupplyLabel (n : ℕ) := Sum (Fin n → ℝ) (Finset (Fin n))

def supplyOracle (n k : ℕ) (p : Fin n → ℝ) : Finset (Fin n) :=
  supplyAnswer n p (supplyBatchHit n k p)

theorem supplyOracle_legal {n k : ℕ} (hk : 2 ≤ k) (p : Fin n → ℝ) :
    IsSupplyResponse (model n k hk) p (supplyOracle n k p) :=
  supplyAnswer_correct hk p

/-- The exact original program execution against a legal oracle for the
concrete perturbed instance. -/
def execute {α : Type*} (n k : ℕ) (program : SupplyProgram (Fin n) α) : α × List QueryKind :=
  SupplyProgram.eval (supplyOracle n k) (fun S => binaryIndex S)
    (fun S => perturbedCost k (perturbation (2^n-1)) (binaryIndex S)) program

theorem execute_eq_model {α : Type*} (n k : ℕ) (hk : 2 ≤ k)
    (program : SupplyProgram (Fin n) α) :
    execute n k program = SupplyProgram.eval (supplyOracle n k)
      (model n k hk).reward (model n k hk).cost program := rfl

/-- Public candidate batches for the two types of unknown oracle information. -/
def batchCandidates (n : ℕ) : SupplyLabel n → List ℕ
  | .inl p => (candidateIndices n p).toList
  | .inr S => [binaryIndex S]

def batchWeight (n : ℕ) : SupplyLabel n → ℕ
  | .inl _ => 4*(n+1)^2
  | .inr _ => 1

theorem batchCandidates_length (n : ℕ) (q : SupplyLabel n) :
    (batchCandidates n q).length ≤ batchWeight n q := by
  cases q with
  | inl p => simpa [batchCandidates, batchWeight] using candidateIndices_card n p
  | inr S => simp [batchCandidates, batchWeight]

/-- One equality-test answer determines the cost of the queried subset. -/
def costAnswer {n : ℕ} (S : Finset (Fin n)) (hit : Option ℕ) : ℝ :=
  cost (binaryIndex S) - if hit = some (binaryIndex S) then perturbation (2^n-1) else 0

theorem costAnswer_correct {n : ℕ} (k : ℕ) (S : Finset (Fin n)) :
    costAnswer S (batchAnswer [binaryIndex S] k) =
      perturbedCost k (perturbation (2^n-1)) (binaryIndex S) := by
  by_cases h : binaryIndex S = k
  · simp [costAnswer, batchAnswer, perturbedCost, h]
  · simp [costAnswer, batchAnswer, perturbedCost, h, Ne.symm h]

theorem supply_batchAnswer (n k : ℕ) (p : Fin n → ℝ) :
    batchAnswer (batchCandidates n (.inl p)) k = supplyBatchHit n k p := by
  simp [batchAnswer, batchCandidates, supplyBatchHit]

/-- Structural compilation of the given adaptive program. Reward nodes are
answered locally from the known additive reward function. -/
def compileSupplyProgram {α : Type*} (n : ℕ) :
    SupplyProgram (Fin n) α → BatchProgram (SupplyLabel n) ℕ α
  | .pure x => .pure x
  | .supply p next => .ask (.inl p) (fun hit =>
      compileSupplyProgram n (next (supplyAnswer n p hit)))
  | .reward S next => compileSupplyProgram n (next (binaryIndex S))
  | .cost S next => .ask (.inr S) (fun hit =>
      compileSupplyProgram n (next (costAnswer S hit)))

/-- Full adaptive-result preservation, for arbitrary output types. -/
theorem compileSupplyProgram_result {α : Type*} (n k : ℕ)
    (program : SupplyProgram (Fin n) α) :
    BatchProgram.result (batchCandidates n) k (compileSupplyProgram n program) =
      (execute n k program).1 := by
  induction program with
  | pure x => rfl
  | supply p next ih =>
      simp only [compileSupplyProgram, BatchProgram.result, supply_batchAnswer,
        ih, execute, SupplyProgram.eval, supplyOracle]
  | reward S next ih =>
      simpa only [compileSupplyProgram, execute, SupplyProgram.eval] using ih (binaryIndex S)
  | cost S next ih =>
      simp only [compileSupplyProgram, BatchProgram.result, batchCandidates,
        costAnswer_correct, ih, execute, SupplyProgram.eval]

/-- Exact accounting: reward queries need no hidden-index probes, and the
other query types retain their actual answer-dependent execution counts. -/
theorem compileSupplyProgram_callCost {α : Type*} (n k : ℕ)
    (program : SupplyProgram (Fin n) α) :
    BatchProgram.callCost (batchWeight n) (batchCandidates n) k
      (compileSupplyProgram n program) =
      4*(n+1)^2 * (execute n k program).2.count .response +
        (execute n k program).2.count .cost := by
  induction program with
  | pure x => simp [compileSupplyProgram, BatchProgram.callCost, execute, SupplyProgram.eval]
  | supply p next ih =>
      simp only [compileSupplyProgram, BatchProgram.callCost, batchWeight,
        supply_batchAnswer, ih, execute, SupplyProgram.eval, supplyOracle]
      simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm]
  | reward S next ih =>
      simpa [compileSupplyProgram, execute, SupplyProgram.eval] using ih (binaryIndex S)
  | cost S next ih =>
      simp only [compileSupplyProgram, BatchProgram.callCost, batchWeight,
        batchCandidates, costAnswer_correct, ih, execute, SupplyProgram.eval]
      simp [Nat.add_assoc, Nat.add_comm]

/-- The actual point-probe decision tree produced from the original program. -/
def compiledPointProgram {α : Type*} (n : ℕ) (program : SupplyProgram (Fin n) α) :
    PointProgram ℕ α := BatchProgram.compile (batchCandidates n) (compileSupplyProgram n program)

theorem compiledPointProgram_result {α : Type*} (n k : ℕ)
    (program : SupplyProgram (Fin n) α) :
    (compiledPointProgram n program).result (pointOracle k) = (execute n k program).1 := by
  rw [compiledPointProgram, BatchProgram.compile_result, compileSupplyProgram_result]

/-- Primitive probes are bounded by the polynomial supply charge plus the
actual number of additional cost-value queries. -/
theorem compiledPointProgram_probes_le {α : Type*} (n k : ℕ)
    (program : SupplyProgram (Fin n) α) :
    (compiledPointProgram n program).probes (pointOracle k) ≤
      4*(n+1)^2 * (execute n k program).2.count .response +
        (execute n k program).2.count .cost := by
  exact (BatchProgram.compile_probes_le (batchCandidates n) k (batchWeight n)
    (batchCandidates_length n) (compileSupplyProgram n program)).trans_eq
      (compileSupplyProgram_callCost n k program)

end
end CombinatorialContracts.LowerBounds
