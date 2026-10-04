import CombinatorialContracts.Geometric
import CombinatorialContracts.Scale

/-!
# An explicit finite exact-real oracle algorithm

A run records every response query together with its answer and exact reward.
Its output is selected by a finite comparison fold over those records.  Thus the
implementation never uses an optimum or a scale certificate as input.
-/
namespace CombinatorialContracts

/-- Finite comparison-based maximization, with a fallback for an empty list. -/
noncomputable def bestOf {β : Type*} (score : β → ℝ) (fallback : β) : List β → β
  | [] => fallback
  | x :: xs =>
      let y := bestOf score fallback xs
      if score y ≤ score x then x else y

theorem score_le_bestOf {β : Type*} (score : β → ℝ) (fallback : β)
    (xs : List β) {x : β} (hx : x ∈ fallback :: xs) :
    score x ≤ score (bestOf score fallback xs) := by
  induction xs with
  | nil =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simpa [hx, bestOf]
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    have htail : score (bestOf score fallback ys) ≤
        score (bestOf score fallback (y :: ys)) := by
      simp only [bestOf]
      split <;> simp_all
    rcases hx with rfl | rfl | hx
    · exact (ih (by simp)).trans htail
    · simp only [bestOf]
      split <;> simp_all only [le_refl, not_le, le_of_lt]
    · exact (ih (by simp [hx])).trans htail

theorem bestOf_mem {β : Type*} (score : β → ℝ) (fallback : β) (xs : List β) :
    bestOf score fallback xs ∈ fallback :: xs := by
  induction xs with
  | nil => simp [bestOf]
  | cons y ys ih =>
    simp only [bestOf]
    split
    · simp
    · simp only [List.mem_cons] at ih ⊢
      tauto

/-- One response-oracle call and the exact reward of the returned response. -/
structure QueryRecord (ι : Type*) where
  share : ℝ
  response : Finset ι
  reward : ℝ

namespace QueryRecord

def utility {ι : Type*} (r : QueryRecord ι) : ℝ := (1 - r.share) * r.reward

noncomputable def query {ι : Type*} (oracle : ℝ → Finset ι)
    (value : Finset ι → ℝ) (α : ℝ) : QueryRecord ι :=
  let answer := oracle α
  ⟨α, answer, value answer⟩

@[simp] theorem query_share {ι : Type*} (oracle : ℝ → Finset ι)
    (value : Finset ι → ℝ) (α : ℝ) : (query oracle value α).share = α := rfl

@[simp] theorem query_response {ι : Type*} (oracle : ℝ → Finset ι)
    (value : Finset ι → ℝ) (α : ℝ) : (query oracle value α).response = oracle α := rfl

@[simp] theorem query_reward {ι : Type*} (oracle : ℝ → Finset ι)
    (value : Finset ι → ℝ) (α : ℝ) : (query oracle value α).reward = value (oracle α) := rfl

end QueryRecord

/-- A recorded run. `initial` is the welfare query at share one. -/
structure OracleRun (ι : Type*) where
  initial : QueryRecord ι
  grid : List (QueryRecord ι)

namespace OracleRun

noncomputable def output {ι : Type*} (run : OracleRun ι) : QueryRecord ι :=
  bestOf QueryRecord.utility run.initial run.grid

def responseQueries {ι : Type*} (run : OracleRun ι) : ℕ := 1 + run.grid.length

def costQueries {ι : Type*} (_run : OracleRun ι) : ℕ := 1

def rewardQueries {ι : Type*} [Fintype ι] (run : OracleRun ι) : ℕ :=
  Fintype.card ι + run.responseQueries

theorem output_mem {ι : Type*} (run : OracleRun ι) :
    run.output ∈ run.initial :: run.grid := bestOf_mem _ _ _

theorem utility_le_output {ι : Type*} (run : OracleRun ι)
    {r : QueryRecord ι} (hr : r ∈ run.initial :: run.grid) :
    r.utility ≤ run.output.utility := score_le_bestOf _ _ _ hr

end OracleRun

/-- Contract schedule for a list of singleton reward values. `offset = 1` is
Algorithm 1. `offset = 2` is the deliberate extra undershoot for robustness. -/
noncomputable def gridShares (anchors : List ℝ) (W q : ℝ) (K offset : ℕ) : List ℝ :=
  anchors.flatMap fun a =>
    if 0 < a then (List.range (K + 1)).map
      (fun k => 1 - min 1 (W / a) * q ^ (k + offset)) else []

theorem mem_gridShares {anchors : List ℝ} {W q a : ℝ} {K offset k : ℕ}
    (ha : a ∈ anchors) (ha0 : 0 < a) (hk : k < K + 1) :
    1 - min 1 (W / a) * q ^ (k + offset) ∈ gridShares anchors W q K offset := by
  simp only [gridShares, List.mem_flatMap]
  refine ⟨a, ha, ?_⟩
  simp only [if_pos ha0, List.mem_map, List.mem_range]
  exact ⟨k, hk, rfl⟩

theorem length_gridShares_le (anchors : List ℝ) (W q : ℝ) (K offset : ℕ) :
    (gridShares anchors W q K offset).length ≤ anchors.length * (K + 1) := by
  induction anchors with
  | nil => simp [gridShares]
  | cons a as ih =>
    simp only [gridShares, List.flatMap_cons, List.length_append, List.length_cons] at *
    split <;> simp_all only [List.length_map, List.length_range, List.length_nil]
    all_goals nlinarith

/-- The run queries the welfare response once, then precisely the finite
schedule. No query to the cost oracle is performed after the welfare query. -/
noncomputable def geometricRun {ι : Type*} (anchors : List ℝ)
    (oracle : ℝ → Finset ι) (value cost : Finset ι → ℝ)
    (q : ℝ) (K offset : ℕ) : OracleRun ι :=
  let initial := QueryRecord.query oracle value 1
  let W := initial.reward - cost initial.response
  ⟨initial, if W = 0 then [] else
    (gridShares anchors W q K offset).map (QueryRecord.query oracle value)⟩

/-- Algorithm 1. `anchors` contains one exact singleton-reward query per item.
Only exact arithmetic/order and the displayed oracles are used. -/
noncomputable def algorithm1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (oracle : ℝ → Finset ι) (value cost : Finset ι → ℝ) (ε : ℝ) : OracleRun ι :=
  geometricRun (Finset.univ.toList.map fun i : ι => value {i}) oracle value cost
    (1 - ε) (leastGridSteps (1 - ε) ((Fintype.card ι : ℝ) ^ 2)) 1

/-- Count every response query, including the welfare query. -/
theorem geometricRun_responseQueries_le {ι : Type*} (anchors : List ℝ)
    (oracle : ℝ → Finset ι) (value cost : Finset ι → ℝ)
    (q : ℝ) (K offset : ℕ) :
    (geometricRun anchors oracle value cost q K offset).responseQueries ≤
      1 + anchors.length * (K + 1) := by
  unfold geometricRun OracleRun.responseQueries
  dsimp
  split
  · simp
  · simpa only [List.length_map] using Nat.add_le_add_left
      (length_gridShares_le anchors _ q K offset) 1



variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact responses are needed only at strictly positive shares, which permits
implementation by the standard supply oracle. -/
def IsExactPositiveOracle (M : Model ι) (oracle : ℝ → Finset ι) : Prop :=
  ∀ α, 0 < α → α ≤ 1 → IsResponse M α (oracle α)

theorem oracle_welfare_eq (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) :
    M.reward (oracle 1) - M.cost (oracle 1) = welfare M := by
  have h1 := (ho 1 zero_lt_one le_rfl).1
  have h2 := response_best M 1
  have ha := h1 (response M 1)
  have hb := h2 (oracle 1)
  simp only [agentUtility, one_mul] at ha hb
  exact le_antisymm hb ha

theorem query_utility_eq_principal (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (QueryRecord.query oracle M.reward α).utility = principal M α := by
  have heq := response_reward_unique M (ho α hα hα1) (response_spec M α)
  simp [QueryRecord.query, QueryRecord.utility, principal, heq]

theorem gridShares_valid {anchors : List ℝ} {W q α : ℝ} {K offset : ℕ}
    (hW : 0 ≤ W) (hq : 0 < q) (hq1 : q < 1) (ho : 1 ≤ offset)
    (hα : α ∈ gridShares anchors W q K offset) : 0 < α ∧ α ≤ 1 := by
  simp only [gridShares, List.mem_flatMap] at hα
  obtain ⟨a, _, ha⟩ := hα
  split_ifs at ha with ha0
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
    have hb : 0 ≤ min 1 (W / a) := le_min zero_le_one (div_nonneg hW ha0.le)
    have hb1 : min 1 (W / a) ≤ 1 := min_le_left _ _
    have hk : k + offset = (k + offset - 1) + 1 := by omega
    rw [hk]
    exact shifted_contract_valid hq hq1 hb hb1
  · simp at ha

theorem geometricRun_record_valid {anchors : List ℝ} {oracle : ℝ → Finset ι}
    {value cost : Finset ι → ℝ} {q : ℝ} {K offset : ℕ}
    (hW : 0 ≤ value (oracle 1) - cost (oracle 1))
    (hq : 0 < q) (hq1 : q < 1) (ho : 1 ≤ offset)
    {r : QueryRecord ι}
    (hr : r ∈ (geometricRun anchors oracle value cost q K offset).initial ::
      (geometricRun anchors oracle value cost q K offset).grid) :
    ∃ α, 0 < α ∧ α ≤ 1 ∧ r = QueryRecord.query oracle value α := by
  simp only [geometricRun] at hr
  rcases List.mem_cons.mp hr with h | h
  · exact ⟨1, zero_lt_one, le_rfl, h⟩
  · split_ifs at h with hz
    · simp at h
    · obtain ⟨α, hα, rfl⟩ := List.mem_map.mp h
      obtain ⟨ha0, ha1⟩ := gridShares_valid hW hq hq1 ho hα
      exact ⟨α, ha0, ha1, rfl⟩

theorem algorithm1_output_valid (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ α, 0 < α ∧ α ≤ 1 ∧
      (algorithm1 oracle M.reward M.cost ε).output =
        QueryRecord.query oracle M.reward α := by
  apply geometricRun_record_valid (q := 1 - ε) (offset := 1)
    (by rw [oracle_welfare_eq M ho]; exact welfare_nonneg M)
    (by linarith) (by linarith) le_rfl
  exact OracleRun.output_mem _

theorem algorithm1_output_utility_eq (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (algorithm1 oracle M.reward M.cost ε).output.utility =
      principal M (algorithm1 oracle M.reward M.cost ε).output.share := by
  obtain ⟨α, ha0, ha1, heq⟩ := algorithm1_output_valid M ho hε hε1
  rw [heq, QueryRecord.query_share]
  exact query_utility_eq_principal M ho ha0 ha1

theorem algorithm1_query_count {oracle : ℝ → Finset ι}
    (value cost : Finset ι → ℝ) (ε : ℝ) :
    (algorithm1 oracle value cost ε).responseQueries ≤
      1 + Fintype.card ι * (leastGridSteps (1 - ε) ((Fintype.card ι : ℝ) ^ 2) + 1) := by
  simpa [algorithm1] using geometricRun_responseQueries_le
    (Finset.univ.toList.map fun i : ι => value {i}) oracle value cost (1 - ε)
    (leastGridSteps (1 - ε) ((Fintype.card ι : ℝ) ^ 2)) 1

/-- The approximation implication from an explicit scale certificate. The final
paper theorem below discharges this certificate from the model assumptions. -/
theorem algorithm1_approx_of_scale (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hscale : 0 < optimalValue M → ∃ j : ι, 0 < M.reward {j} ∧
      min 1 (welfare M / M.reward {j}) / (Fintype.card ι : ℝ) ^ 2 ≤ 1 - optimum M ∧
      1 - optimum M ≤ min 1 (welfare M / M.reward {j})) :
    (1 - ε) * optimalValue M ≤
      (algorithm1 oracle M.reward M.cost ε).output.utility := by
  obtain ⟨αout, hout0, hout1, hout⟩ := algorithm1_output_valid M ho hε hε1
  have houtnn : 0 ≤ (algorithm1 oracle M.reward M.cost ε).output.utility := by
    rw [hout, query_utility_eq_principal M ho hout0 hout1]
    exact principal_nonneg M hout1
  by_cases hp : 0 < optimalValue M
  swap
  · have heq : optimalValue M = 0 := le_antisymm (le_of_not_gt hp) (optimalValue_nonneg M)
    simpa [heq] using houtnn
  obtain ⟨j, hj0, hjlo, hjhi⟩ := hscale hp
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  have hnR : (1 : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    nlinarith
  have hW : 0 < welfare M := hp.trans_le (optimalValue_le_welfare M)
  have hb : 0 ≤ min 1 (welfare M / M.reward {j}) :=
    le_min zero_le_one (div_nonneg hW.le hj0.le)
  obtain ⟨k, hk, hklo, hkhi⟩ := geometric_cover_of_width hε hε1 hnR hb hjlo hjhi
  let δ := min 1 (welfare M / M.reward {j}) * (1 - ε) ^ (k + 1)
  have hδ0 : 0 ≤ δ := mul_nonneg hb (pow_nonneg (by linarith) _)
  have ha : 0 < 1 - δ ∧ 1 - δ ≤ 1 :=
    shifted_contract_valid (by linarith) (by linarith) hb (min_le_left _ _)
  have hrew : M.reward (response M (optimum M)) ≤ M.reward (response M (1 - δ)) :=
    response_reward_mono M (by dsimp [δ]; linarith)
  have hgood : (1 - ε) * optimalValue M ≤ principal M (1 - δ) := by
    have hr0 := M.reward_nonneg (response M (optimum M))
    have h1 := mul_le_mul_of_nonneg_right hklo hr0
    have h2 := mul_le_mul_of_nonneg_left hrew hδ0
    dsimp [principal, optimalValue, δ] at *
    nlinarith
  have hgmem : QueryRecord.query oracle M.reward (1 - δ) ∈
      (algorithm1 oracle M.reward M.cost ε).grid := by
    simp only [algorithm1, geometricRun, QueryRecord.query]
    rw [oracle_welfare_eq M ho, if_neg (ne_of_gt hW)]
    apply List.mem_map.mpr
    refine ⟨1 - δ, ?_, rfl⟩
    apply mem_gridShares _ hj0 hk
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨j, rfl⟩
  calc
    (1 - ε) * optimalValue M ≤ principal M (1 - δ) := hgood
    _ = (QueryRecord.query oracle M.reward (1 - δ)).utility :=
      (query_utility_eq_principal M ho ha.1 ha.2).symm
    _ ≤ (algorithm1 oracle M.reward M.cost ε).output.utility :=
      OracleRun.utility_le_output _ (List.mem_cons_of_mem _ hgmem)



/-- Theorem 2: Algorithm 1 achieves the paper's general-reward approximation,
with all structural claims proved from the model assumptions. -/
theorem general_reward_approximation (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) * optimalValue M ≤
      (algorithm1 oracle M.reward M.cost ε).output.utility := by
  apply algorithm1_approx_of_scale M ho hε hε1
  intro hp
  obtain ⟨j, _, ha, _, hl, hu⟩ := reward_anchored_grid_scale M hp
  exact ⟨j, ha, hl, hu⟩

/-- Theorem 1's supply-oracle implementation, including the positive-share
condition needed for the larger-cost tie-break. -/
theorem supply_oracle_approximation (M : Model ι) (hadd : HasAdditiveReward M)
    (supply : (ι → ℝ) → Finset ι)
    (hsupply : ∀ p, (∀ i, 0 ≤ p i) → IsSupplyResponse M p (supply p))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) * optimalValue M ≤
      (algorithm1 (fun α => supply (fun i => α * M.reward {i}))
        M.reward M.cost ε).output.utility := by
  apply general_reward_approximation M _ hε hε1
  intro α ha _
  exact (supplyResponse_iff_response M hadd ha).mp
    (hsupply _ (fun i => mul_nonneg ha.le (M.reward_nonneg {i})))



/-- A uniform numerical bound, rather than an unproved asymptotic annotation. -/
theorem algorithm1_logarithmic_query_bound {oracle : ℝ → Finset ι}
    (value cost : Finset ι → ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hn : 1 ≤ Fintype.card ι) :
    ((algorithm1 oracle value cost ε).responseQueries : ℝ) ≤
      20 * (Fintype.card ι : ℝ) * Real.log (Fintype.card ι + 1) / ε := by
  have hnR : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hR : (1 : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by nlinarith
  have hρ : 0 < ε / 3 := by positivity
  have hρ1 : ε / 3 < 1 := by linarith
  have hK := leastGridSteps_mono_base (by linarith : 0 ≤ 1 - ε)
    (by linarith : 1 - ε ≤ 1 - ε / 3)
    ⟨_, leastGridSteps_spec hρ hρ1 hR⟩
  have hcount := algorithm1_query_count (oracle := oracle) value cost ε
  have hcount' : (algorithm1 oracle value cost ε).responseQueries ≤
      1 + Fintype.card ι *
        (leastGridSteps (1 - ε / 3) ((Fintype.card ι : ℝ)^2) + 2) := by
    apply hcount.trans
    gcongr
    omega
  exact (Nat.cast_le.mpr hcount').trans
    (logarithmic_query_bound hn hε hε1 hR (log_square_bound hn))

/-- In the additive case response rewards are evaluated locally from the cached
singleton table; they do not require reward-value queries. -/
noncomputable def additiveAlgorithm1 (a : ι → ℝ)
    (supply : (ι → ℝ) → Finset ι) (cost : Finset ι → ℝ) (ε : ℝ) : OracleRun ι :=
  geometricRun (Finset.univ.toList.map a)
    (fun α => supply (fun i => α * a i)) (fun S => ∑ i ∈ S, a i) cost
    (1 - ε) (leastGridSteps (1 - ε) ((Fintype.card ι : ℝ) ^ 2)) 1

theorem additiveAlgorithm1_eq (M : Model ι) (hadd : HasAdditiveReward M)
    (supply : (ι → ℝ) → Finset ι) (ε : ℝ) :
    additiveAlgorithm1 (fun i => M.reward {i}) supply M.cost ε =
      algorithm1 (fun α => supply (fun i => α * M.reward {i})) M.reward M.cost ε := by
  have hv : (fun S => ∑ i ∈ S, M.reward {i}) = M.reward :=
    funext fun S => (hadd S).symm
  simp only [additiveAlgorithm1, algorithm1, hv]

theorem additiveAlgorithm1_approximation (M : Model ι) (hadd : HasAdditiveReward M)
    (supply : (ι → ℝ) → Finset ι)
    (hsupply : ∀ p, (∀ i, 0 ≤ p i) → IsSupplyResponse M p (supply p))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) * optimalValue M ≤
      (additiveAlgorithm1 (fun i => M.reward {i}) supply M.cost ε).output.utility := by
  rw [additiveAlgorithm1_eq M hadd]
  exact supply_oracle_approximation M hadd supply hsupply hε hε1

@[simp] theorem algorithm1_zero_welfare (M : Model ι) {oracle : ℝ → Finset ι}
    (ho : IsExactPositiveOracle M oracle) (hW : welfare M = 0) (ε : ℝ) :
    (algorithm1 oracle M.reward M.cost ε).output = QueryRecord.query oracle M.reward 1 := by
  simp [algorithm1, geometricRun, QueryRecord.query, oracle_welfare_eq M ho,
    hW, OracleRun.output, bestOf]

theorem algorithm1_single_action_queries {oracle : ℝ → Finset ι}
    (value cost : Finset ι → ℝ) (ε : ℝ) (hn : Fintype.card ι = 1) :
    (algorithm1 oracle value cost ε).responseQueries ≤ 2 := by
  simpa [hn] using algorithm1_query_count (oracle := oracle) value cost ε



/-- On the nonzero-welfare branch the extra fallback welfare record cannot be
selected: a grid response has strictly positive utility. Thus the returned
record is exactly one of the source algorithm's recorded grid candidates. -/
theorem algorithm1_output_mem_grid_of_welfare_pos (M : Model ι)
    {oracle : ℝ → Finset ι} (ho : IsExactPositiveOracle M oracle)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hW : 0 < welfare M) :
    (algorithm1 oracle M.reward M.cost ε).output ∈
      (algorithm1 oracle M.reward M.cost ε).grid := by
  have hp : 0 < optimalValue M := by
    have hn : optimalValue M ≠ 0 := by
      intro hz
      have := (welfare_eq_zero_iff_optimalValue_eq_zero M).mpr hz
      linarith
    exact lt_of_le_of_ne (optimalValue_nonneg M) (Ne.symm hn)
  have hpos : 0 < (algorithm1 oracle M.reward M.cost ε).output.utility :=
    (mul_pos (by linarith) hp).trans_le (general_reward_approximation M ho hε hε1)
  rcases List.mem_cons.mp (OracleRun.output_mem
    (algorithm1 oracle M.reward M.cost ε)) with heq | hmem
  · rw [heq] at hpos
    simp [algorithm1, geometricRun, QueryRecord.query, QueryRecord.utility] at hpos
  · exact hmem

/-- The literal source routine makes one welfare query on the empty ground set,
then returns share one. Its exceptional constant cost is explicit. -/
theorem algorithm1_empty_ground_set (M : Model ι)
    {oracle : ℝ → Finset ι} (ho : IsExactPositiveOracle M oracle)
    (hn : Fintype.card ι = 0) (ε : ℝ) :
    (algorithm1 oracle M.reward M.cost ε).output.share = 1 ∧
      (algorithm1 oracle M.reward M.cost ε).responseQueries = 1 := by
  letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
  have hW : welfare M = 0 := by
    simp [welfare, Finset.eq_empty_of_isEmpty, M.reward_empty, M.cost_empty]
  constructor
  · rw [algorithm1_zero_welfare M ho hW]
    rfl
  · simp [algorithm1, geometricRun, QueryRecord.query, OracleRun.responseQueries,
      oracle_welfare_eq M ho, hW]

end CombinatorialContracts
