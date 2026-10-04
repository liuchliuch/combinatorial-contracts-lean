import CombinatorialContracts.SupplyProgram
import CombinatorialContracts.RobustOracleProgram

/-!
# Executed paper theorems

Theorem 1 uses actual supply-program executions with a cached singleton table.
Theorem 2 uses actual response-program executions. Their guarantees concern the
principal's exact favorable-response utility at the returned contract. Theorem 7
instead concerns the actual recorded approximate response, with an independently
indexed answer at every response call. All query bounds count executed nodes.
The empty ground set is handled separately from the logarithmic complexity domain.
-/
namespace CombinatorialContracts
namespace Paper

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The logarithmic budget also pays for all `n` singleton reads. -/
theorem logarithmic_value_query_bound {n : ℕ} {ε R : ℝ}
    (hn : 1 ≤ n) (hε : 0 < ε) (hε1 : ε < 1) (hR : 1 ≤ R)
    (hlogR : Real.log R ≤ 3 * Real.log (n + 1)) :
    (n + (1 + n * (leastGridSteps (1 - ε / 3) R + 2)) : ℕ) ≤
      20 * (n : ℝ) * Real.log (n + 1) / ε := by
  have hρ : 0 < ε / 3 := by positivity
  have hρ1 : ε / 3 < 1 := by linarith
  have hk := leastGridSteps_add_one_bound hρ hρ1 hR
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log (n + 1) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ n + 1)
    have := Real.log_two_gt_d9
    linarith
  have hlogε : (1 / 2 : ℝ) ≤ Real.log (n + 1) / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hk' : (leastGridSteps (1 - ε / 3) R + 2 : ℕ) ≤
      15 * Real.log (n + 1) / ε := by
    push_cast at hk ⊢
    have hl : Real.log R / (ε / 3) ≤ 9 * Real.log (n + 1) / ε := by
      apply (div_le_div_iff₀ hρ hε).mpr
      nlinarith
    rw [mul_div_assoc] at hl ⊢
    linarith
  have hm := mul_le_mul_of_nonneg_left hk' (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hu : (1 : ℝ) ≤ 2 * n * (Real.log (n + 1) / ε) := by nlinarith
  have hn' : (n : ℝ) ≤ 2 * n * (Real.log (n + 1) / ε) := by nlinarith
  push_cast at hm ⊢
  simp only [mul_div_assoc] at hm ⊢
  nlinarith

/-- Both response and reward budgets for the mathematical run, including
singleton reads; subsequently transferred to actual execution traces. -/
theorem exact_run_query_bounds {oracle : ℝ → Finset ι}
    (value cost : Finset ι → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hn : 1 ≤ Fintype.card ι) :
    ((algorithm1 oracle value cost ε).responseQueries : ℝ) ≤
        20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε ∧
    ((algorithm1 oracle value cost ε).rewardQueries : ℝ) ≤
        20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε := by
  have hnR : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hR : (1 : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by nlinarith
  have hρ : 0 < ε / 3 := by positivity
  have hρ1 : ε / 3 < 1 := by linarith
  have hK := leastGridSteps_mono_base (by linarith : 0 ≤ 1 - ε)
    (by linarith : 1 - ε ≤ 1 - ε / 3)
    ⟨_, leastGridSteps_spec hρ hρ1 hR⟩
  have hc := algorithm1_query_count (oracle := oracle) value cost ε
  have hc' : (algorithm1 oracle value cost ε).responseQueries ≤
      1 + Fintype.card ι *
        (leastGridSteps (1 - ε / 3) ((Fintype.card ι : ℝ)^2) + 2) := by
    apply hc.trans
    gcongr
    omega
  refine ⟨algorithm1_logarithmic_query_bound value cost hε hε1 hn, ?_⟩
  exact (Nat.cast_le.mpr (Nat.add_le_add_left hc' (Fintype.card ι))).trans
    (logarithmic_value_query_bound hn hε hε1 hR (log_square_bound hn))

/-- Exact outputs retain a valid contract and exact recorded response, and their
recorded score equals the actual principal objective. -/
theorem exact_run_outcome (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    let r := (algorithm1 oracle M.reward M.cost ε).output
    r.share ∈ Set.Icc (0 : ℝ) 1 ∧
    IsResponse M r.share r.response ∧
    r.reward = M.reward r.response ∧
    r.utility = principal M r.share ∧
    (1 - ε) * optimalValue M ≤ principal M r.share := by
  dsimp only
  obtain ⟨a, ha, ha1, heq⟩ := algorithm1_output_valid M ho hε hε1
  have hu := algorithm1_output_utility_eq M ho hε hε1
  refine ⟨?_, ?_, ?_, hu, ?_⟩
  · rw [heq, QueryRecord.query_share]
    exact ⟨ha.le, ha1⟩
  · simpa [heq, QueryRecord.query] using ho a ha ha1
  · simp [heq, QueryRecord.query]
  · rw [← hu]
    exact general_reward_approximation M ho hε hε1

/-- Source Theorem 2, bundled for one actual execution. No welfare, scale, or
counting certificate is an input hypothesis. -/
theorem theorem2 (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hn : 1 ≤ Fintype.card ι) :
    let executed := OracleProgram.eval oracle M.reward M.cost
      (OracleProgram.algorithm1Program ε)
    let r := executed.1.output
    r.share ∈ Set.Icc (0 : ℝ) 1 ∧
    IsResponse M r.share r.response ∧
    r.reward = M.reward r.response ∧
    r.utility = principal M r.share ∧
    (1 - ε) * optimalValue M ≤ principal M r.share ∧
    r ∈ executed.1.initial :: executed.1.grid ∧
    executed.2.count .response = executed.1.responseQueries ∧
    executed.2.count .reward = executed.1.rewardQueries ∧
    (executed.2.count .response : ℝ) ≤
      20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε ∧
    (executed.2.count .reward : ℝ) ≤
      20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε ∧
    executed.2.count .cost = 1 := by
  dsimp only
  obtain ⟨hr, hv, hc⟩ := OracleProgram.algorithm1Program_counts oracle M.reward M.cost ε
  have he := OracleProgram.eval_algorithm1Program oracle M.reward M.cost ε
  obtain ⟨ha, hs, hrew, hu, happ⟩ := exact_run_outcome M ho hε hε1
  obtain ⟨hqr, hqv⟩ := exact_run_query_bounds (oracle := oracle) M.reward M.cost hε hε1 hn
  refine ⟨?_, ?_, ?_, ?_, ?_, OracleRun.output_mem _, hr, hv, ?_, ?_, ?_⟩
  · simpa only [he] using ha
  · simpa only [he] using hs
  · simpa only [he] using hrew
  · simpa only [he] using hu
  · simpa only [he] using happ
  · simpa only [hr, he] using hqr
  · simpa only [hv, he] using hqv
  · simpa only [OracleRun.costQueries] using hc

/-- Source Theorem 1. The supply trace tag is `response`; its reward count is
exactly `n` because every response reward is computed from the cached table. -/
theorem theorem1 (M : Model ι) (hadd : HasAdditiveReward M)
    (supply : (ι → ℝ) → Finset ι)
    (hsupply : ∀ p, (∀ i, 0 ≤ p i) → IsSupplyResponse M p (supply p))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hn : 1 ≤ Fintype.card ι) :
    let executed := SupplyProgram.eval supply M.reward M.cost (SupplyProgram.algorithm ε)
    let r := executed.1.output
    r.share ∈ Set.Icc (0 : ℝ) 1 ∧
    IsResponse M r.share r.response ∧
    r.reward = M.reward r.response ∧
    r.utility = principal M r.share ∧
    (1 - ε) * optimalValue M ≤ principal M r.share ∧
    r ∈ executed.1.initial :: executed.1.grid ∧
    executed.2.count .response = executed.1.responseQueries ∧
    (executed.2.count .response : ℝ) ≤
      20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε ∧
    executed.2.count .reward = Fintype.card ι ∧
    executed.2.count .cost = 1 := by
  let oracle := fun α => supply (fun i => α * M.reward {i})
  have ho : IsExactPositiveOracle M oracle := by
    intro α hα _
    exact (supplyResponse_iff_response M hadd hα).mp
      (hsupply _ (fun i => mul_nonneg hα.le (M.reward_nonneg {i})))
  have he : (SupplyProgram.eval supply M.reward M.cost (SupplyProgram.algorithm ε)).1 =
      algorithm1 oracle M.reward M.cost ε := by
    rw [SupplyProgram.eval_algorithm]
    exact additiveAlgorithm1_eq M hadd supply ε
  dsimp only
  obtain ⟨hr, hv, hc⟩ := SupplyProgram.algorithm_counts supply M.reward M.cost ε
  obtain ⟨ha, hs, hrew, hu, happ⟩ := exact_run_outcome M ho hε hε1
  have hq := algorithm1_logarithmic_query_bound (oracle := oracle) M.reward M.cost hε hε1 hn
  refine ⟨?_, ?_, ?_, ?_, ?_, OracleRun.output_mem _, hr, ?_, hv, hc⟩
  · simpa only [he] using ha
  · simpa only [he] using hs
  · simpa only [he] using hrew
  · simpa only [he] using hu
  · simpa only [he] using happ
  · simpa only [hr, he] using hq

/-- Source Theorem 7. Approximation is measured on the selected, actually
recorded contract/response pair, never on a later replay of the oracle. -/
theorem theorem7 (M : Model ι) {oracle : ℕ → ℝ → Finset ι} {ε τ : ℝ}
    (ho : IsApproxOracle M τ oracle) (hε : 0 < ε) (hε1 : ε < 1)
    (hτ : 0 ≤ τ) (hn : 1 ≤ Fintype.card ι) :
    let executed := OracleProgram.evalIndexed oracle M.reward M.cost
      (OracleProgram.robustProgram ε τ) 0
    let r := executed.1.output
    r.share ∈ Set.Icc (0 : ℝ) 1 ∧
    IsApproxBestResponse M τ r.share r.response ∧
    r.reward = M.reward r.response ∧
    (1 - ε) * optimalValue M - 3 * τ / ε ≤
      (1 - r.share) * M.reward r.response ∧
    r ∈ executed.1.initial :: executed.1.grid ∧
    (∃ t, r = QueryRecord.query (oracle t) M.reward r.share) ∧
    executed.2.count .response = executed.1.responseQueries ∧
    executed.2.count .reward = executed.1.rewardQueries ∧
    (executed.2.count .response : ℝ) ≤
      20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε ∧
    (executed.2.count .reward : ℝ) ≤
      20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε ∧
    executed.2.count .cost = 1 := by
  dsimp only
  obtain ⟨hr, hv, hc⟩ := OracleProgram.robustProgram_counts oracle M.reward M.cost ε τ
  have he := OracleProgram.evalIndexed_robustProgram oracle M.reward M.cost ε τ
  have hout := OracleRun.output_mem (robustAlgorithm oracle M.reward M.cost ε τ)
  obtain ⟨t, a, ha, heq⟩ := robustAlgorithm_record_valid M hε hε1 hτ hout
  have hrew : (robustAlgorithm oracle M.reward M.cost ε τ).output.reward =
      M.reward (robustAlgorithm oracle M.reward M.cost ε τ).output.response := by
    simp [heq, QueryRecord.query]
  have happ := OracleProgram.robustProgram_approximation M ho hε hε1 hτ
  have hqr := robustAlgorithm_logarithmic_query_bound oracle M.reward M.cost
    (τ := τ) hε hε1 hn
  have hnR : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hqv : ((robustAlgorithm oracle M.reward M.cost ε τ).rewardQueries : ℝ) ≤
      20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε :=
    (Nat.cast_le.mpr (Nat.add_le_add_left
      (robustAlgorithm_query_count oracle M.reward M.cost ε τ) (Fintype.card ι))).trans
        (logarithmic_value_query_bound hn hε hε1 (by nlinarith)
          (log_double_square_bound hn))
  refine ⟨?_, ?_, ?_, ?_, OracleRun.output_mem _, ?_, hr, hv, ?_, ?_, ?_⟩
  · simpa only [he, heq, QueryRecord.query_share] using ha
  · simpa [he, heq, QueryRecord.query] using ho t a ha
  · simpa only [he] using hrew
  · simpa only [he, QueryRecord.utility, hrew] using happ
  · refine ⟨t, ?_⟩
    simp only [he, heq, QueryRecord.query_share]
  · rw [hr, he]
    exact hqr
  · rw [hv, he]
    exact hqv
  · simpa only [OracleRun.costQueries] using hc

/-- No available action means the exact optimum is zero. -/
theorem empty_optimalValue (M : Model ι) (hn : Fintype.card ι = 0) :
    optimalValue M = 0 := by
  letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
  apply (welfare_eq_zero_iff_optimalValue_eq_zero M).mp
  simp [welfare, Finset.eq_empty_of_isEmpty, M.reward_empty, M.cost_empty]

/-- The exact response routine on `n=0`: the welfare query has constant cost,
so this case is not incorrectly charged against `n log(n+1)`. -/
theorem theorem2_empty (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) (hn : Fintype.card ι = 0) (ε : ℝ) :
    let executed := OracleProgram.eval oracle M.reward M.cost
      (OracleProgram.algorithm1Program ε)
    executed.1.output.share = 1 ∧
    principal M executed.1.output.share = 0 ∧
    optimalValue M = 0 ∧
    executed.2.count .response = 1 ∧
    executed.2.count .reward = 1 ∧
    executed.2.count .cost = 1 := by
  dsimp only
  obtain ⟨ha, hq⟩ := algorithm1_empty_ground_set M ho hn ε
  have he := OracleProgram.eval_algorithm1Program oracle M.reward M.cost ε
  obtain ⟨hr, hv, hc⟩ := OracleProgram.algorithm1Program_counts oracle M.reward M.cost ε
  refine ⟨?_, ?_, empty_optimalValue M hn, ?_, ?_, ?_⟩
  · simpa only [he] using ha
  · simp only [he, ha, principal, sub_self, zero_mul]
  · rw [hr, he, hq]
  · rw [hv, he, OracleRun.rewardQueries, hn, hq]
  · simpa only [OracleRun.costQueries] using hc

/-- The cached additive routine performs no singleton reads on the empty set. -/
theorem theorem1_empty (M : Model ι) (hadd : HasAdditiveReward M)
    (supply : (ι → ℝ) → Finset ι)
    (hsupply : ∀ p, (∀ i, 0 ≤ p i) → IsSupplyResponse M p (supply p))
    (hn : Fintype.card ι = 0) (ε : ℝ) :
    let executed := SupplyProgram.eval supply M.reward M.cost (SupplyProgram.algorithm ε)
    executed.1.output.share = 1 ∧
    principal M executed.1.output.share = 0 ∧
    optimalValue M = 0 ∧
    executed.2.count .response = 1 ∧
    executed.2.count .reward = 0 ∧
    executed.2.count .cost = 1 := by
  let oracle := fun α => supply (fun i => α * M.reward {i})
  have ho : IsExactPositiveOracle M oracle := by
    intro α hα _
    exact (supplyResponse_iff_response M hadd hα).mp
      (hsupply _ (fun i => mul_nonneg hα.le (M.reward_nonneg {i})))
  have he : (SupplyProgram.eval supply M.reward M.cost (SupplyProgram.algorithm ε)).1 =
      algorithm1 oracle M.reward M.cost ε := by
    rw [SupplyProgram.eval_algorithm]
    exact additiveAlgorithm1_eq M hadd supply ε
  dsimp only
  obtain ⟨ha, hq⟩ := algorithm1_empty_ground_set M ho hn ε
  obtain ⟨hr, hv, hc⟩ := SupplyProgram.algorithm_counts supply M.reward M.cost ε
  refine ⟨?_, ?_, empty_optimalValue M hn, ?_, hv.trans hn, hc⟩
  · simpa only [he] using ha
  · simp only [he, ha, principal, sub_self, zero_mul]
  · rw [hr, he, hq]

/-- On the empty ground set every approximate answer is empty. The robust
routine returns its initial queried pair, with zero realized payoff. -/
theorem theorem7_empty (M : Model ι) (oracle : ℕ → ℝ → Finset ι)
    (hn : Fintype.card ι = 0) (ε : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    let executed := OracleProgram.evalIndexed oracle M.reward M.cost
      (OracleProgram.robustProgram ε τ) 0
    executed.1.output.share = 1 ∧
    executed.1.output.response = ∅ ∧
    (1 - executed.1.output.share) * M.reward executed.1.output.response = 0 ∧
    optimalValue M = 0 ∧
    executed.2.count .response = 1 ∧
    executed.2.count .reward = 1 ∧
    executed.2.count .cost = 1 := by
  letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
  have he := OracleProgram.evalIndexed_robustProgram oracle M.reward M.cost ε τ
  obtain ⟨hr, hv, hc⟩ := OracleProgram.robustProgram_counts oracle M.reward M.cost ε τ
  dsimp only
  have hout : (robustAlgorithm oracle M.reward M.cost ε τ).output =
      QueryRecord.query (oracle 0) M.reward 1 := by
    simp [robustAlgorithm, QueryRecord.query, Finset.eq_empty_of_isEmpty,
      M.reward_empty, M.cost_empty, hτ, OracleRun.output, bestOf]
  have hq : (robustAlgorithm oracle M.reward M.cost ε τ).responseQueries = 1 := by
    simp [robustAlgorithm, QueryRecord.query, Finset.eq_empty_of_isEmpty,
      M.reward_empty, M.cost_empty, hτ, OracleRun.responseQueries]
  refine ⟨?_, ?_, ?_, empty_optimalValue M hn, ?_, ?_, ?_⟩
  · simp only [he, hout, QueryRecord.query_share]
  · exact Finset.eq_empty_of_isEmpty _
  · simp only [he, hout, QueryRecord.query_share, sub_self, zero_mul]
  · rw [hr, he, hq]
  · rw [hv, he, OracleRun.rewardQueries, hn, hq]
  · simpa only [OracleRun.costQueries] using hc

end Paper
end CombinatorialContracts
