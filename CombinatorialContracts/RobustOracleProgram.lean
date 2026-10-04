import CombinatorialContracts.OracleProgram
import CombinatorialContracts.Robustness

/-! # Actual oracle execution for the approximate-response algorithm -/
namespace CombinatorialContracts
namespace OracleProgram

variable {ι α β : Type*}

/-- Stateful response interpretation: a response node advances the call index;
reward and cost nodes preserve it. Thus repeated shares need not give the same
response. The output contains the actual chronological query-kind trace. -/
def evalIndexed (oracle : ℕ → ℝ → Finset ι) (value costValue : Finset ι → ℝ) :
    OracleProgram ι α → ℕ → α × List QueryKind
  | .pure x, _ => (x, [])
  | .response a k, t =>
    let result := evalIndexed oracle value costValue (k (oracle t a)) (t + 1)
    (result.1, .response :: result.2)
  | .reward s k, t =>
    let result := evalIndexed oracle value costValue (k (value s)) t
    (result.1, .reward :: result.2)
  | .cost s k, t =>
    let result := evalIndexed oracle value costValue (k (costValue s)) t
    (result.1, .cost :: result.2)

theorem evalIndexed_bind (oracle : ℕ → ℝ → Finset ι)
    (value costValue : Finset ι → ℝ) (p : OracleProgram ι α)
    (f : α → OracleProgram ι β) (t : ℕ) :
    evalIndexed oracle value costValue (bind p f) t =
      let first := evalIndexed oracle value costValue p t
      let second := evalIndexed oracle value costValue (f first.1)
        (t + first.2.count .response)
      (second.1, first.2 ++ second.2) := by
  induction p generalizing t with
  | pure x => simp [bind, evalIndexed]
  | response a k ih =>
    simp [bind, evalIndexed, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | reward s k ih => simp [bind, evalIndexed, ih]
  | cost s k ih => simp [bind, evalIndexed, ih]

@[simp] theorem evalIndexed_queryRecord (oracle : ℕ → ℝ → Finset ι)
    (value costValue : Finset ι → ℝ) (a : ℝ) (t : ℕ) :
    evalIndexed oracle value costValue (queryRecord a) t =
      (QueryRecord.query (oracle t) value a, [.response, .reward]) := rfl

theorem evalIndexed_queryRecords (oracle : ℕ → ℝ → Finset ι)
    (value costValue : Finset ι → ℝ) (as : List ℝ) (t : ℕ) :
    evalIndexed oracle value costValue (queryRecords as) t =
      (as.mapIdx (fun i a => QueryRecord.query (oracle (t + i)) value a),
        recordTrace as) := by
  induction as generalizing t with
  | nil => rfl
  | cons a as ih =>
    simp [queryRecords, evalIndexed_bind, ih, evalIndexed, recordTrace,
      List.mapIdx_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem evalIndexed_readSingletons [DecidableEq ι]
    (oracle : ℕ → ℝ → Finset ι) (value costValue : Finset ι → ℝ)
    (is : List ι) (t : ℕ) :
    evalIndexed oracle value costValue (readSingletons is) t =
      (is.map (fun i => value {i}), List.replicate is.length .reward) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp [readSingletons, evalIndexed, evalIndexed_bind, ih, List.replicate_succ,
      List.count_replicate]

/-- The exact appendix instruction sequence after the singleton reads:
response at one, its exact reward, one exact cost, then the widened grid. -/
noncomputable def robustGeometricProgram (anchors : List ℝ) (n : ℕ) (ε τ : ℝ) :
    OracleProgram ι (OracleRun ι) :=
  bind (queryRecord 1) (fun initial =>
    .cost initial.response (fun c =>
      let L := max 0 (initial.reward - c)
      if L ≤ τ then .pure ⟨initial, []⟩ else
        bind (queryRecords (gridShares anchors (L + τ) (1 - ε / 3)
          (leastGridSteps (1 - ε / 3) (2 * (n : ℝ) ^ 2) + 1) 0))
          (fun records => .pure ⟨initial, records⟩)))

/-- Reified source algorithm. The final comparison fold is pure and causes no
extra oracle calls. -/
noncomputable def robustProgram [Fintype ι] [DecidableEq ι] (ε τ : ℝ) :
    OracleProgram ι (OracleRun ι) :=
  bind (readSingletons Finset.univ.toList) (fun anchors =>
    robustGeometricProgram anchors (Fintype.card ι) ε τ)

noncomputable def robustTrace [Fintype ι] [DecidableEq ι]
    (oracle : ℕ → ℝ → Finset ι) (value costValue : Finset ι → ℝ)
    (ε τ : ℝ) : List QueryKind :=
  List.replicate (Fintype.card ι) .reward ++ [.response, .reward, .cost] ++
    let L := max 0 (value (oracle 0 1) - costValue (oracle 0 1))
    if L ≤ τ then [] else
      recordTrace (gridShares (Finset.univ.toList.map fun i : ι => value {i})
        (L + τ) (1 - ε / 3)
        (leastGridSteps (1 - ε / 3) (2 * (Fintype.card ι : ℝ) ^ 2) + 1) 0)

/-- The independently stateful execution returns exactly the run used in the
robustness proof, together with its complete query trace. -/
theorem evalIndexed_robustProgram [Fintype ι] [DecidableEq ι]
    (oracle : ℕ → ℝ → Finset ι) (value costValue : Finset ι → ℝ) (ε τ : ℝ) :
    evalIndexed oracle value costValue (robustProgram ε τ) 0 =
      (robustAlgorithm oracle value costValue ε τ,
        robustTrace oracle value costValue ε τ) := by
  simp only [robustProgram, evalIndexed_bind, evalIndexed_readSingletons]
  simp only [robustGeometricProgram, evalIndexed_bind, List.count_replicate]
  simp [evalIndexed, evalIndexed_queryRecord, robustAlgorithm, robustTrace,
    QueryRecord.query, evalIndexed_bind, evalIndexed_queryRecords]
  split <;> simp [evalIndexed, evalIndexed_bind, evalIndexed_queryRecords,
    Nat.add_comm, List.append_assoc, QueryRecord.query]

/-- All three annotations are the counts of actual executed oracle nodes;
there are no uncounted reward or cost calls. -/
theorem robustProgram_counts [Fintype ι] [DecidableEq ι]
    (oracle : ℕ → ℝ → Finset ι) (value costValue : Finset ι → ℝ) (ε τ : ℝ) :
    let executed := evalIndexed oracle value costValue (robustProgram ε τ) 0
    executed.2.count .response = executed.1.responseQueries ∧
    executed.2.count .reward = executed.1.rewardQueries ∧
    executed.2.count .cost = executed.1.costQueries := by
  rw [evalIndexed_robustProgram]
  simp [robustTrace, robustAlgorithm, OracleRun.responseQueries, OracleRun.rewardQueries,
    OracleRun.costQueries, QueryRecord.query]
  split <;> simp [recordTrace_response, recordTrace_reward, recordTrace_cost,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, List.count_replicate]

/-- End-to-end program correctness for Theorem 7. -/
theorem robustProgram_approximation [Fintype ι] [DecidableEq ι]
    (M : Model ι) {oracle : ℕ → ℝ → Finset ι} {ε τ : ℝ}
    (ho : IsApproxOracle M τ oracle) (hε : 0 < ε) (hε1 : ε < 1) (hτ : 0 ≤ τ) :
    (1 - ε) * optimalValue M - 3 * τ / ε ≤
      (evalIndexed oracle M.reward M.cost (robustProgram ε τ) 0).1.output.utility := by
  rw [evalIndexed_robustProgram]
  exact approximate_oracle_robustness M ho hε hε1 hτ



/-- Actual executed query counts have the claimed representation-independent
bound. The reward bound includes the `n` singleton reads and every response
valuation; exactly one cost query is executed. -/
theorem robustProgram_query_bounds [Fintype ι] [DecidableEq ι]
    (oracle : ℕ → ℝ → Finset ι) (value costValue : Finset ι → ℝ)
    {ε τ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hn : 1 ≤ Fintype.card ι) :
    let executed := evalIndexed oracle value costValue (robustProgram ε τ) 0
    (executed.2.count .response : ℝ) ≤
        20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε ∧
    (executed.2.count .reward : ℝ) ≤
        Fintype.card ι + 20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε ∧
    executed.2.count .cost = 1 := by
  obtain ⟨hr, hv, hc⟩ := robustProgram_counts oracle value costValue ε τ
  dsimp only
  rw [hr, hv, hc, evalIndexed_robustProgram]
  have hb := robustAlgorithm_logarithmic_query_bound oracle value costValue (τ := τ) hε hε1 hn
  refine ⟨hb, ?_, rfl⟩
  simp only [OracleRun.rewardQueries, Nat.cast_add]
  exact add_le_add_left hb _

end OracleProgram
end CombinatorialContracts
