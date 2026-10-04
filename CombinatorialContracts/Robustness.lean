import CombinatorialContracts.Algorithm

/-!
# Approximate-oracle robustness (Theorem 7)

The oracle is indexed by call number. In particular, two calls at the same share
are allowed to return different approximate responses. The algorithm returns the
observed contract–response pair, not an unobserved replay of that contract.
-/
namespace CombinatorialContracts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Additive-error best response, without any tie-breaking restriction. -/
def IsApproxBestResponse (M : Model ι) (τ α : ℝ) (S : Finset ι) : Prop :=
  ∀ T, agentUtility M α T - τ ≤ agentUtility M α S

/-- The response can depend on the call index as well as the share. -/
def IsApproxOracle (M : Model ι) (τ : ℝ) (oracle : ℕ → ℝ → Finset ι) : Prop :=
  ∀ t α, α ∈ Set.Icc (0 : ℝ) 1 → IsApproxBestResponse M τ α (oracle t α)

theorem approximate_welfare_estimate (M : Model ι) {τ : ℝ} {T : Finset ι}
    (hT : IsApproxBestResponse M τ 1 T) :
    welfare M - τ ≤ M.reward T - M.cost T ∧
      M.reward T - M.cost T ≤ welfare M := by
  constructor
  · simpa [agentUtility, welfare] using hT (response M 1)
  · exact welfare_max M T

theorem approximate_clipped_welfare_estimate (M : Model ι) {τ : ℝ} {T : Finset ι}
    (hT : IsApproxBestResponse M τ 1 T) :
    max 0 (M.reward T - M.cost T) ≤ welfare M ∧
      welfare M ≤ max 0 (M.reward T - M.cost T) + τ := by
  obtain ⟨hl, hu⟩ := approximate_welfare_estimate M hT
  constructor
  · exact max_le (welfare_nonneg M) hu
  · have := le_max_right 0 (M.reward T - M.cost T)
    linarith

/-- Widening a certified welfare scale by a factor at most two widens the
retained-share interval by at most the same factor. -/
theorem widened_reward_scale {W U n a δ : ℝ} (hn : 0 < n) (ha : 0 < a)
    (hWU : W ≤ U) (hU2 : U ≤ 2 * W)
    (hlo : W / (n ^ 2 * a) ≤ δ) (hhi : δ ≤ min 1 (W / a)) :
    min 1 (U / a) / (2 * n ^ 2) ≤ δ ∧ δ ≤ min 1 (U / a) := by
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  have hWδ := (div_le_iff₀ (mul_pos hn2 ha)).mp hlo
  have hb : min 1 (U / a) * a ≤ U :=
    (le_div_iff₀ ha).mp (min_le_right _ _)
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2 * n ^ 2)).mpr
    nlinarith
  · exact hhi.trans (min_le_min_left 1 ((div_le_div_iff_of_pos_right ha).mpr hWU))

/-- The payoff margin created by deliberately moving one grid step farther.
This proof uses only the two response inequalities; no response consistency is
assumed. -/
theorem approximate_undershoot_payoff (M : Model ι) {ε τ δ : ℝ} {T : Finset ι}
    (hε : 0 < ε) (hε1 : ε < 1) (hτ : 0 ≤ τ)
    (hP : 0 < optimalValue M)
    (hlo : (1 - ε / 3) ^ 2 * (1 - optimum M) ≤ δ)
    (hhi : δ ≤ (1 - ε / 3) * (1 - optimum M))
    (hT : IsApproxBestResponse M τ (1 - δ) T) :
    (1 - ε) * optimalValue M - 3 * τ / ε ≤ δ * M.reward T := by
  let D := 1 - optimum M
  let ρ := ε / 3
  let R := M.reward (response M (optimum M))
  have hD : 0 < D := sub_pos.mpr (optimum_lt_one_of_optimalValue_pos M hP)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hR : 0 ≤ R := M.reward_nonneg _
  have hδ0 : 0 ≤ δ := le_trans (mul_nonneg (sq_nonneg _) hD.le) hlo
  have hδD : δ ≤ D := by
    have hm := mul_nonneg hρ.le hD.le
    dsimp [D, ρ] at *
    nlinarith
  have hsep : ρ * D ≤ D - δ := by dsimp [D, ρ] at *; nlinarith
  have h1 := hT (response M (optimum M))
  have h2 := response_best M (optimum M) T
  have hprod : (D - δ) * (R - M.reward T) ≤ τ := by
    dsimp [D, R, agentUtility] at *
    nlinarith
  have hdiff : R - M.reward T ≤ τ / (ρ * D) := by
    apply (le_div_iff₀ (mul_pos hρ hD)).mpr
    by_cases hd : 0 ≤ R - M.reward T
    · have hm := mul_le_mul_of_nonneg_right hsep hd
      nlinarith
    · have hm := mul_nonpos_of_nonneg_of_nonpos (mul_pos hρ hD).le (le_of_not_ge hd)
      nlinarith
  have hr : R - τ / (ρ * D) ≤ M.reward T := by linarith
  have hret : (1 - ε) * (D * R) ≤ δ * R := by
    have hq : (1 - ε) * D ≤ δ := by
      have hDε := mul_nonneg (sq_nonneg ε) hD.le
      dsimp [D] at *
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hq hR]
  have herror : δ * (τ / (ρ * D)) ≤ τ / ρ := by
    have ht : 0 ≤ τ / (ρ * D) := div_nonneg hτ (mul_pos hρ hD).le
    calc
      _ ≤ D * (τ / (ρ * D)) := mul_le_mul_of_nonneg_right hδD ht
      _ = τ / ρ := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hr hδ0
  have hPV : optimalValue M = D * R := rfl
  have herr : τ / ρ = 3 * τ / ε := by dsimp [ρ]; ring
  rw [hPV]
  rw [herr] at herror
  nlinarith

/-- Source appendix schedule: query index zero through `K+1`, where `K`
covers width `2 n²`; subsequent oracle answers are indexed independently. -/
noncomputable def robustAlgorithm (oracle : ℕ → ℝ → Finset ι)
    (value cost : Finset ι → ℝ) (ε τ : ℝ) : OracleRun ι :=
  let initial := QueryRecord.query (oracle 0) value 1
  let L := max 0 (initial.reward - cost initial.response)
  let K := leastGridSteps (1 - ε / 3) (2 * (Fintype.card ι : ℝ) ^ 2)
  ⟨initial, if L ≤ τ then [] else
    (gridShares (Finset.univ.toList.map fun i : ι => value {i})
      (L + τ) (1 - ε / 3) (K + 1) 0).mapIdx
      (fun t α => QueryRecord.query (oracle (t + 1)) value α)⟩

/-- A source-grid contract is feasible, including share zero when `b=1`. -/
theorem gridShares_nonnegative {anchors : List ℝ} {W q α : ℝ} {K offset : ℕ}
    (hW : 0 ≤ W) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hα : α ∈ gridShares anchors W q K offset) : α ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [gridShares, List.mem_flatMap] at hα
  obtain ⟨a, _, ha⟩ := hα
  split_ifs at ha with ha0
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
    have hb : 0 ≤ min 1 (W / a) := le_min zero_le_one (div_nonneg hW ha0.le)
    have hb1 : min 1 (W / a) ≤ 1 := min_le_left _ _
    have hpow : 0 ≤ q ^ (k + offset) := pow_nonneg hq _
    have hpow1 : q ^ (k + offset) ≤ 1 := pow_le_one₀ hq hq1
    have hmul0 := mul_nonneg hb hpow
    have hmul1 : min 1 (W / a) * q ^ (k + offset) ≤ 1 := by nlinarith
    constructor <;> linarith
  · simp at ha



theorem robustAlgorithm_record_valid (M : Model ι)
    {oracle : ℕ → ℝ → Finset ι} {ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hτ : 0 ≤ τ)
    {r : QueryRecord ι}
    (hr : r ∈ (robustAlgorithm oracle M.reward M.cost ε τ).initial ::
      (robustAlgorithm oracle M.reward M.cost ε τ).grid) :
    ∃ t α, α ∈ Set.Icc (0 : ℝ) 1 ∧
      r = QueryRecord.query (oracle t) M.reward α := by
  simp only [robustAlgorithm] at hr
  rcases List.mem_cons.mp hr with h | h
  · exact ⟨0, 1, by norm_num, h⟩
  · split_ifs at h with hz
    · simp at h
    · obtain ⟨t, ht, heq⟩ := List.mem_mapIdx.mp h
      refine ⟨t + 1, _, ?_, heq.symm⟩
      apply gridShares_nonnegative _ (by linarith) (by linarith)
        (List.getElem_mem ht)
      exact add_nonneg (le_max_left _ _) hτ

theorem robustAlgorithm_output_nonneg (M : Model ι)
    {oracle : ℕ → ℝ → Finset ι} {ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hτ : 0 ≤ τ) :
    0 ≤ (robustAlgorithm oracle M.reward M.cost ε τ).output.utility := by
  obtain ⟨t, α, hα, heq⟩ := robustAlgorithm_record_valid M hε hε1 hτ
    (OracleRun.output_mem (robustAlgorithm oracle M.reward M.cost ε τ))
  rw [heq]
  exact mul_nonneg (sub_nonneg.mpr hα.2) (M.reward_nonneg _)

/-- Theorem 7, including arbitrary per-query approximate responses and the
paper's exact additive loss `3τ/ε`. -/
theorem approximate_oracle_robustness (M : Model ι)
    {oracle : ℕ → ℝ → Finset ι} {ε τ : ℝ}
    (ho : IsApproxOracle M τ oracle)
    (hε : 0 < ε) (hε1 : ε < 1) (hτ : 0 ≤ τ) :
    (1 - ε) * optimalValue M - 3 * τ / ε ≤
      (robustAlgorithm oracle M.reward M.cost ε τ).output.utility := by
  let L := max 0 (M.reward (oracle 0 1) - M.cost (oracle 0 1))
  obtain ⟨hLW, hWL⟩ := approximate_clipped_welfare_estimate M
    (ho 0 1 (by norm_num))
  change L ≤ welfare M at hLW
  change welfare M ≤ L + τ at hWL
  have houtnn := robustAlgorithm_output_nonneg M (oracle := oracle) hε hε1 hτ
  have hPnn := optimalValue_nonneg M
  have hPW := optimalValue_le_welfare M
  have herr : 0 ≤ 3 * τ / ε := by positivity
  have hPε : (1 - ε) * optimalValue M ≤ optimalValue M := by nlinarith
  by_cases hL : L ≤ τ
  · have htarget : (1 - ε) * optimalValue M - 3 * τ / ε ≤ 0 := by
      have hτle : 2 * τ ≤ 3 * τ / ε := by
        apply (le_div_iff₀ hε).mpr
        nlinarith
      linarith
    exact htarget.trans houtnn
  by_cases hp : 0 < optimalValue M
  swap
  · have heq : optimalValue M = 0 := le_antisymm (le_of_not_gt hp) hPnn
    rw [heq]
    nlinarith
  obtain ⟨j, _, ha, hlo, hhi, _⟩ := reward_anchored_scale M hp
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast card_pos_of_optimalValue_pos M hp
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast card_pos_of_optimalValue_pos M hp
  have hR : (1 : ℝ) ≤ 2 * (Fintype.card ι : ℝ) ^ 2 := by nlinarith
  have hL0 : 0 ≤ L := le_max_left _ _
  have hU2 : L + τ ≤ 2 * welfare M := by linarith
  obtain ⟨hwlo, hwhi⟩ := widened_reward_scale hn ha hWL hU2 hlo hhi
  have hb : 0 ≤ min 1 ((L + τ) / M.reward {j}) :=
    le_min zero_le_one (div_nonneg (add_nonneg hL0 hτ) ha.le)
  obtain ⟨k, hk, hklo, hkhi⟩ := robust_source_grid_cover
    (by positivity : 0 < ε / 3) (by linarith : ε / 3 < 1) hR hb
    (sub_nonneg.mpr (optimum_mem M).2) hwlo hwhi
  let δ := min 1 ((L + τ) / M.reward {j}) * (1 - ε / 3) ^ k
  let shares := gridShares (Finset.univ.toList.map fun i : ι => M.reward {i})
    (L + τ) (1 - ε / 3)
    (leastGridSteps (1 - ε / 3) (2 * (Fintype.card ι : ℝ) ^ 2) + 1) 0
  have hmem : 1 - δ ∈ shares := by
    apply mem_gridShares (offset := 0) _ ha (by omega)
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨j, rfl⟩
  obtain ⟨t, ht, hidx⟩ := List.mem_iff_getElem.mp hmem
  have hα : 1 - δ ∈ Set.Icc (0 : ℝ) 1 :=
    gridShares_nonnegative (add_nonneg hL0 hτ) (by linarith) (by linarith) hmem
  have hgood := approximate_undershoot_payoff M hε hε1 hτ hp hklo hkhi
    (ho (t + 1) (1 - δ) hα)
  have hgmem : QueryRecord.query (oracle (t + 1)) M.reward (1 - δ) ∈
      (robustAlgorithm oracle M.reward M.cost ε τ).grid := by
    simp only [robustAlgorithm, QueryRecord.query]
    change _ ∈ if L ≤ τ then [] else
      shares.mapIdx (fun t α => QueryRecord.query (oracle (t + 1)) M.reward α)
    rw [if_neg hL]
    apply List.mem_mapIdx.mpr
    exact ⟨t, ht, by rw [hidx]; rfl⟩
  have hrecord : (1 - ε) * optimalValue M - 3 * τ / ε ≤
      (QueryRecord.query (oracle (t + 1)) M.reward (1 - δ)).utility := by
    simpa [QueryRecord.query, QueryRecord.utility] using hgood
  exact hrecord.trans (OracleRun.utility_le_output _ (List.mem_cons_of_mem _ hgmem))

theorem robustAlgorithm_query_count (oracle : ℕ → ℝ → Finset ι)
    (value cost : Finset ι → ℝ) (ε τ : ℝ) :
    (robustAlgorithm oracle value cost ε τ).responseQueries ≤
      1 + Fintype.card ι *
        (leastGridSteps (1 - ε / 3) (2 * (Fintype.card ι : ℝ)^2) + 2) := by
  unfold robustAlgorithm OracleRun.responseQueries
  dsimp
  split
  · simp
  · simp only [List.length_mapIdx]
    have h := length_gridShares_le
      (Finset.univ.toList.map fun i : ι => value {i})
      (max 0 (value (oracle 0 1) - cost (oracle 0 1)) + τ)
      (1 - ε / 3) (leastGridSteps (1 - ε / 3) (2 * (Fintype.card ι : ℝ)^2) + 1) 0
    simpa using Nat.add_le_add_left h 1

theorem robustAlgorithm_logarithmic_query_bound (oracle : ℕ → ℝ → Finset ι)
    (value cost : Finset ι → ℝ) {ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hn : 1 ≤ Fintype.card ι) :
    ((robustAlgorithm oracle value cost ε τ).responseQueries : ℝ) ≤
      20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε := by
  have hnR : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  exact (Nat.cast_le.mpr (robustAlgorithm_query_count oracle value cost ε τ)).trans
    (logarithmic_query_bound hn hε hε1 (by nlinarith) (log_double_square_bound hn))

end CombinatorialContracts
