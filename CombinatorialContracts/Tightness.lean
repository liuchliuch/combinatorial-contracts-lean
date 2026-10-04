import CombinatorialContracts.Model
import CombinatorialContracts.ChainRealization
import CombinatorialContracts.Scaling

/-!
# Concrete localization tightness instances (Proposition 9)

The constructions here use actual finite sets of actions and additive rewards.
All non-designated action sets are excluded directly from the agent problem.
-/
namespace CombinatorialContracts.Tightness
noncomputable section
open Finset

/-- An additive nonnegative reward supplies all reward fields of `Model`. -/
def additiveModel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (c : Finset ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hc0 : c ∅ = 0) (hc : ∀ S, 0 ≤ c S) : Model ι where
  reward S := ∑ i ∈ S, v i
  cost := c
  reward_empty := by simp
  cost_empty := hc0
  reward_nonneg S := sum_nonneg fun i _ => hv i
  cost_nonneg := hc
  reward_mono := fun S T h => sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hv i)
  reward_subadditive S T := by
    have h := sum_union_inter (s₁ := S) (s₂ := T) (f := v)
    have hn : 0 ≤ ∑ i ∈ S ∩ T, v i := sum_nonneg fun i _ => hv i
    linarith

@[simp] theorem additiveModel_reward {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (c : Finset ι → ℝ) (hv hc0 hc) (S : Finset ι) :
    (additiveModel v c hv hc0 hc).reward S = ∑ i ∈ S, v i := rfl

@[simp] theorem additiveModel_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (c : Finset ι → ℝ) (hv hc0 hc) (S : Finset ι) :
    (additiveModel v c hv hc0 hc).cost S = c S := rfl

theorem additiveModel_additive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (c : Finset ι → ℝ) (hv hc0 hc) :
    HasAdditiveReward (additiveModel v c hv hc0 hc) := by
  intro S
  simp

/-- Strictly ordered designated rewards make the response set itself unique,
not only its reward. -/
theorem realized_response_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Model ι} {n : ℕ} (C : RealizedChain M n)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) {S T : Finset ι}
    (hS : IsResponse M α S) (hT : IsResponse M α T) : S = T := by
  have hdesign : ∀ U, IsResponse M α U → ∃ j, j ≤ n ∧ U = C.sets j := by
    intro U hU
    by_contra h
    have hn : ∀ j, j ≤ n → U ≠ C.sets j := by simpa using h
    have hneg := C.excluded_utility_neg α hα U hn
    have hpos := bestResponse_agentUtility_nonneg M hU.1
    linarith
  obtain ⟨i, hi, rfl⟩ := hdesign S hS
  obtain ⟨j, hj, rfl⟩ := hdesign T hT
  have he := response_reward_unique M hS hT
  rw [C.reward_eq i hi, C.reward_eq j hj] at he
  have hlt : ∀ a b, a < b → b ≤ n → C.chain.reward a < C.chain.reward b := by
    intro a b hab hbn
    exact (C.reward_strict a (by omega)).trans_le
      (C.chain.reward_mono (a+1) b (by omega) hbn)
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have := hlt i j h hj; linarith
    · exact h
    · have := hlt j i h hi; linarith
  rw [hij]

namespace Singleton

/-- The source's geometric normalization. -/
def Z (n : ℕ) (r : ℝ) : ℝ := ∑ i ∈ range n, r ^ i

def value (n : ℕ) (r : ℝ) (i : ℕ) : ℝ := r ^ i / Z n r

def entry (r : ℝ) (i : ℕ) : ℝ := 1 - 1 / r ^ i

/-- Closed form of the source's recursively defined singleton costs. -/
def rawCost (r : ℝ) (i : ℕ) : ℝ := r ^ i - 1 - (i : ℝ) * (1 - 1 / r)
def singleCost (n : ℕ) (r : ℝ) (i : ℕ) : ℝ := rawCost r i / Z n r

def cost {n : ℕ} (r : ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, singleCost n r i) + 2 * (S.card.choose 2 : ℝ)

@[simp] theorem rawCost_zero (r : ℝ) : rawCost r 0 = 0 := by simp [rawCost]
@[simp] theorem entry_zero (r : ℝ) : entry r 0 = 0 := by simp [entry]
@[simp] theorem singleCost_zero (n : ℕ) (r : ℝ) : singleCost n r 0 = 0 := by
  simp [singleCost]

 theorem Z_pos {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 0 < r) : 0 < Z n r := by
  unfold Z
  exact sum_pos (fun i _ => pow_pos hr i) ⟨0, mem_range.mpr hn⟩

 theorem value_pos {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 0 < r) (i : ℕ) :
    0 < value n r i := div_pos (pow_pos hr _) (Z_pos hn hr)

 theorem rawCost_step {r : ℝ} (hr : r ≠ 0) (i : ℕ) :
    rawCost r (i+1) - rawCost r i =
      entry r (i+1) * (r ^ (i+1) - r ^ i) := by
  simp only [rawCost, entry, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  ring

 theorem entry_nonneg {r : ℝ} (hr : 1 ≤ r) (i : ℕ) : 0 ≤ entry r i := by
  have hp : (1 : ℝ) ≤ r ^ i := one_le_pow₀ hr
  unfold entry
  have : 1 / r ^ i ≤ 1 := (div_le_one (by positivity)).mpr hp
  linarith

 theorem entry_lt_one {r : ℝ} (hr : 0 < r) (i : ℕ) : entry r i < 1 := by
  unfold entry
  have : 0 < 1 / r ^ i := by positivity
  linarith

 theorem entry_strictMono {r : ℝ} (hr : 1 < r) : StrictMono (entry r) := by
  intro i j hij
  have hp : r ^ i < r ^ j := pow_lt_pow_right₀ hr hij
  have hi : 0 < r ^ i := pow_pos (by linarith) _
  have h := one_div_lt_one_div_of_lt hi hp
  unfold entry
  linarith

 theorem rawCost_nonneg {r : ℝ} (hr : 1 < r) (i : ℕ) : 0 ≤ rawCost r i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hs := rawCost_step (ne_of_gt (lt_trans zero_lt_one hr)) i
    have he := entry_nonneg hr.le (i+1)
    have hp : 0 ≤ r ^ (i+1) - r ^ i := by
      exact sub_nonneg.mpr (pow_le_pow_right₀ hr.le (by omega))
    have := mul_nonneg he hp
    linarith

 theorem singleCost_step {n : ℕ} {r : ℝ} (hr : r ≠ 0) (i : ℕ) :
    singleCost n r (i+1) - singleCost n r i =
      entry r (i+1) * (value n r (i+1) - value n r i) := by
  unfold singleCost value
  rw [← sub_div, rawCost_step hr]
  ring

 theorem singleCost_nonneg {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 1 < r) (i : ℕ) :
    0 ≤ singleCost n r i :=
  div_nonneg (rawCost_nonneg hr i) (Z_pos hn (by linarith)).le

 theorem cost_nonneg {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 1 < r)
    (S : Finset (Fin n)) : 0 ≤ cost r S := by
  unfold cost
  exact add_nonneg (sum_nonneg (fun i _ => singleCost_nonneg hn hr i)) (by positivity)

@[simp] theorem cost_empty (n : ℕ) (r : ℝ) : cost r (∅ : Finset (Fin n)) = 0 := by
  simp [cost]

@[simp] theorem cost_singleton {n : ℕ} (r : ℝ) (i : Fin n) :
    cost r {i} = singleCost n r i := by simp [cost]

/-- Exactly the normalized additive-reward, quadratic-interaction-cost instance
in Appendix C(ii). -/
def model (n : ℕ) (r : ℝ) (hn : 0 < n) (hr : 1 < r) : Model (Fin n) :=
  additiveModel (fun i => value n r i) (cost r)
    (fun i => (value_pos hn (by linarith) i).le) (cost_empty n r)
    (cost_nonneg hn hr)

 theorem model_additive (n : ℕ) (r : ℝ) (hn : 0 < n) (hr : 1 < r) :
    HasAdditiveReward (model n r hn hr) := by
  intro S
  simp [model]

 theorem reward_univ (n : ℕ) (r : ℝ) (hn : 0 < n) (hr : 1 < r) :
    (model n r hn hr).reward univ = 1 := by
  change (∑ i : Fin n, r ^ (i : ℕ) / Z n r) = 1
  rw [← sum_div, Fin.sum_univ_eq_sum_range]
  exact div_self (ne_of_gt (Z_pos hn (by linarith)))

 theorem reward_le_one (n : ℕ) (r : ℝ) (hn : 0 < n) (hr : 1 < r)
    (S : Finset (Fin n)) : (model n r hn hr).reward S ≤ 1 := by
  rw [← reward_univ n r hn hr]
  exact (model n r hn hr).reward_mono (subset_univ S)

 theorem choose_two_pos {k : ℕ} (hk : 2 ≤ k) : 1 ≤ k.choose 2 := by
  exact Nat.succ_le_iff.mpr (Nat.choose_pos hk)

 theorem large_cost {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 1 < r)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) : 2 ≤ cost r S := by
  have hs : 0 ≤ ∑ i ∈ S, singleCost n r i := sum_nonneg fun i _ => singleCost_nonneg hn hr i
  have hc : (1 : ℝ) ≤ S.card.choose 2 := by exact_mod_cast choose_two_pos hS
  unfold cost
  linarith

/-- Every set of at least two actions is strictly worse than doing nothing,
including both boundary contracts. -/
 theorem large_utility_neg {n : ℕ} {r α : ℝ} (hn : 0 < n) (hr : 1 < r)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    agentUtility (model n r hn hr) α S < 0 := by
  have hR := reward_le_one n r hn hr S
  have hR0 := (model n r hn hr).reward_nonneg S
  have hC := large_cost hn hr S hS
  have hp : α * (model n r hn hr).reward S ≤ 1 := by nlinarith [hα.1, hα.2]
  change α * (model n r hn hr).reward S - cost r S < 0
  linarith

 theorem bestResponse_card_le_one {n : ℕ} {r α : ℝ} (hn : 0 < n) (hr : 1 < r)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) {S : Finset (Fin n)}
    (hS : IsBestResponse (model n r hn hr) α S) : S.card ≤ 1 := by
  by_contra h
  have := large_utility_neg hn hr hα S (by omega)
  have := bestResponse_agentUtility_nonneg (model n r hn hr) hS
  linarith

 theorem cost_insert {n : ℕ} (r : ℝ) {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    cost r (insert i S) - cost r S = singleCost n r i + 2 * S.card := by
  simp only [cost, sum_insert hi, card_insert_of_notMem hi]
  rw [show S.card + 1 = Nat.succ S.card by rfl,
    show 2 = Nat.succ 1 by rfl, Nat.choose_succ_succ]
  simp only [Nat.choose_one_right, Nat.cast_add]
  ring

/-- The cost function is monotone on all subsets, not merely singleton lines. -/
 theorem cost_mono {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 1 < r) :
    Monotone (cost (n := n) r) := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro S i hi
  have he := cost_insert r hi
  have hd := singleCost_nonneg hn hr i
  have hc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  linarith

/-- Increasing marginal costs establish supermodularity on the ground set. -/
 theorem cost_supermodular {n : ℕ} (r : ℝ) {S T : Finset (Fin n)}
    (hST : S ⊆ T) {i : Fin n} (hi : i ∉ T) :
    cost r (insert i S) - cost r S ≤ cost r (insert i T) - cost r T := by
  rw [cost_insert r (fun h => hi (hST h)), cost_insert r hi]
  have hc : (S.card : ℝ) ≤ T.card := by exact_mod_cast card_le_card hST
  linarith

 def chain (n : ℕ) (r : ℝ) (hn : 0 < n) (hr : 1 < r) : LineChain n where
  reward
    | 0 => 0
    | i+1 => value n r i
  cost
    | 0 => 0
    | i+1 => singleCost n r i
  entry
    | 0 => 0
    | i+1 => entry r i
  reward_mono := by
    intro i j hij hj
    cases i with
    | zero => cases j with
      | zero => exact le_rfl
      | succ j => exact (value_pos hn (by linarith) j).le
    | succ i => cases j with
      | zero => omega
      | succ j =>
        exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hr.le (by omega))
          (Z_pos hn (by linarith)).le
  entry_mono := by
    intro i j hi hij hj
    cases i with
    | zero => omega
    | succ i => cases j with
      | zero => omega
      | succ j => exact (entry_strictMono hr).monotone (by omega)
  cost_step := by
    intro i hi
    cases i with
    | zero => simp
    | succ i => exact singleCost_step (ne_of_gt (lt_trans zero_lt_one hr)) i

 def sets (n : ℕ) : ℕ → Finset (Fin n)
  | 0 => ∅
  | i+1 => if hi : i < n then {⟨i, hi⟩} else ∅

@[simp] theorem sets_zero (n : ℕ) : sets n 0 = ∅ := rfl
@[simp] theorem sets_succ {n i : ℕ} (hi : i < n) : sets n (i+1) = {⟨i, hi⟩} := by
  simp [sets, hi]

 def realized (n : ℕ) (r : ℝ) (hn : 0 < n) (hr : 1 < r) :
    RealizedChain (model n r hn hr) n where
  chain := chain n r hn hr
  sets := sets n
  set_zero := rfl
  reward_eq := by
    intro i hi
    cases i with
    | zero => simp [chain, model]
    | succ i => simp [sets_succ (show i < n by omega), model, chain]
  cost_eq := by
    intro i hi
    cases i with
    | zero => simp [chain, model]
    | succ i => simp [sets_succ (show i < n by omega), model, chain]
  reward_strict := by
    intro i hi
    cases i with
    | zero => exact value_pos hn (by linarith) 0
    | succ i =>
      exact (div_lt_div_iff_of_pos_right (Z_pos hn (by linarith))).mpr
        (pow_lt_pow_right₀ hr (by omega))
  entry_strict := by
    intro i hi hin
    cases i with
    | zero => omega
    | succ i => exact entry_strictMono hr (by omega)
  entry_mem := by
    intro i hi hin
    cases i with
    | zero => omega
    | succ i => exact ⟨entry_nonneg hr.le i, (entry_lt_one (by linarith) i).le⟩
  excluded_utility_neg := by
    intro α hα S hS
    apply large_utility_neg hn hr hα S
    by_contra h
    have hcard : S.card ≤ 1 := by omega
    by_cases hE : S.card = 0
    · exact hS 0 (by omega) (by simpa using card_eq_zero.mp hE)
    · obtain ⟨i, rfl⟩ := card_eq_one.mp (show S.card = 1 by omega)
      exact hS (i.val+1) (by omega) (by simp)

 theorem entry_profit {n : ℕ} {r : ℝ} (_hn : 0 < n) (hr : 1 < r) (i : ℕ) :
    (1 - entry r i) * value n r i = 1 / Z n r := by
  have hp : r ^ i ≠ 0 := ne_of_gt (pow_pos (by linarith : 0 < r) _)
  unfold entry value
  field_simp
  ring

 theorem optimalValue_eq {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 1 < r) :
    optimalValue (model n r hn hr) = 1 / Z n r := by
  have h := (realized n r hn hr).optimalValue_eq_entry (k := 1) (by omega) hn
    (by
      intro i hi hin
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      change (1-entry r j)*value n r j ≤ (1-entry r 0)*value n r 0
      rw [entry_profit hn hr j, entry_profit hn hr 0])
  simpa [realized, chain, entry, value] using h

 theorem singleton_welfare {n : ℕ} {r : ℝ} (i : ℕ) :
    value n r i - singleCost n r i =
      (1 / Z n r) * (1 + (i : ℝ) * (1 - 1 / r)) := by
  unfold value singleCost rawCost
  ring

 theorem welfare_eq {n : ℕ} {r : ℝ} (hn : 0 < n) (hr : 1 < r) :
    welfare (model n r hn hr) =
      (1 / Z n r) * ((n : ℝ) - (n-1 : ℝ) / r) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [(realized (k+1) r hn hr).welfare_eq_last (by omega)]
  change value (k+1) r k - singleCost (k+1) r k = _
  rw [singleton_welfare]
  push_cast
  ring

/-- Proposition 9(ii), with its exact ratio for every admissible parameter. -/
 theorem welfare_ratio {n : ℕ} {r : ℝ} (hn : 2 ≤ n) (hr : 1 < r) :
    welfare (model n r (by omega) hr) / optimalValue (model n r (by omega) hr) =
      (n : ℝ) - (n-1 : ℝ) / r := by
  rw [welfare_eq, optimalValue_eq]
  exact mul_div_cancel_left₀ _ (one_div_ne_zero (ne_of_gt (Z_pos (by omega) (by linarith))))

/-- The linear welfare bound is approached arbitrarily closely by the concrete
normalized monotone-supermodular instances. -/
 theorem ratio_approaches_n {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, ∃ hr : 1 < r,
      (n : ℝ) - ε < welfare (model n r (by omega) hr) /
        optimalValue (model n r (by omega) hr) := by
  let r : ℝ := 2 + (n : ℝ) / ε
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hr : 1 < r := by dsimp [r]; have := div_nonneg hn0 hε.le; linarith
  refine ⟨r, hr, ?_⟩
  rw [welfare_ratio hn hr]
  have hden : 0 < r := by linarith
  have hbound : (n-1 : ℝ) / r < ε := by
    apply (div_lt_iff₀ hden).mpr
    dsimp [r]
    have he : ε * ((n : ℝ) / ε) = n := by field_simp
    nlinarith
  linarith

end Singleton
namespace Bundle

abbrev Action (m : ℕ) := Fin m ⊕ Fin m

def R (m k : ℕ) : ℝ := (m : ℝ) * 2 ^ k
def D (m : ℕ) (η : ℝ) (k : ℕ) : ℝ := R m k - (1+η) - (k : ℝ)/2
def a (m : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 - (1+η)/(m : ℝ) else 1 - 1/R m k

def weight (m : ℕ) : Action m → ℝ
  | .inl _ => 1
  | .inr i => R m (i.val+1)

def reward (m : ℕ) (S : Finset (Action m)) : ℝ := ∑ i ∈ S, weight m i

def A (m : ℕ) : Finset (Action m) := univ.map Function.Embedding.inl

def bCost (m : ℕ) (η : ℝ) : Action m → ℝ
  | .inl _ => 0
  | .inr i => D m η (i.val+1)

def cost (m : ℕ) (η : ℝ) (S : Finset (Action m)) : ℝ :=
  if S = A m then D m η 0 else
  if ∃ i : Fin m, S = {Sum.inr i} then ∑ i ∈ S, bCost m η i else 2 * reward m S

 theorem R_pos {m : ℕ} (hm : 0 < m) (k : ℕ) : 0 < R m k := by
  unfold R
  positivity

@[simp] theorem R_zero (m : ℕ) : R m 0 = m := by simp [R]
 theorem R_succ (m k : ℕ) : R m (k+1) = 2 * R m k := by simp [R, pow_succ]; ring
 theorem R_strictMono {m : ℕ} (hm : 0 < m) : StrictMono (R m) := by
  intro i j hij
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by norm_num) hij) (by exact_mod_cast hm)

 theorem a_mem {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (k : ℕ) : 0 < a m η k ∧ a m η k < 1 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  unfold a
  split_ifs with hk
  · have hp : 0 < (1+η)/(m : ℝ) := by positivity
    have hp1 : (1+η)/(m : ℝ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    constructor <;> linarith
  · have hp := R_pos (by omega : 0 < m) k
    have hR : (1 : ℝ) < R m k := by
      have h := (R_strictMono (by omega : 0 < m)).monotone (Nat.zero_le k)
      simp only [R_zero] at h
      linarith
    have hq : 0 < 1 / R m k := by positivity
    have hq1 : 1 / R m k < 1 := (div_lt_one hp).mpr hR
    constructor <;> linarith

 theorem a_strictMono {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) :
    StrictMono (a m η) := by
  apply strictMono_nat_of_lt_succ
  intro k
  cases k with
  | zero =>
    simp only [a, Nat.succ_ne_zero, if_false, R_succ, R_zero, ite_true]
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have h : 1 / (2*(m : ℝ)) < (1+η)/(m : ℝ) := by
      apply (div_lt_div_iff₀ (by positivity) hm').mpr
      nlinarith
    linarith
  | succ k =>
    simp only [a, Nat.succ_ne_zero, if_false]
    have h := one_div_lt_one_div_of_lt (R_pos (by omega : 0 < m) (k+1))
      (R_strictMono (by omega : 0 < m) (Nat.lt_succ_self (k+1)))
    linarith

 theorem D_step {m : ℕ} {η : ℝ} (hm : 0 < m) (k : ℕ) :
    D m η (k+1) - D m η k = a m η (k+1) * (R m (k+1)-R m k) := by
  have hp : R m k ≠ 0 := ne_of_gt (R_pos hm k)
  simp only [D, a, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Nat.cast_add, Nat.cast_one, R_succ]
  field_simp
  ring

 theorem D_nonneg {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (k : ℕ) : 0 ≤ D m η k := by
  induction k with
  | zero =>
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [D, R_zero, Nat.cast_zero, zero_div, sub_zero]
    linarith
  | succ k ih =>
    have he := D_step (η := η) (by omega : 0 < m) k
    have ha := (a_mem hm hη hη1 (k+1)).1.le
    have hR := (R_strictMono (by omega : 0 < m)).monotone (Nat.le_succ k)
    have hp := mul_nonneg ha (sub_nonneg.mpr hR)
    linarith

 theorem weight_pos {m : ℕ} (hm : 0 < m) (i : Action m) : 0 < weight m i := by
  cases i with
  | inl i => exact zero_lt_one
  | inr i => exact R_pos hm (i.val+1)

 theorem reward_pos {m : ℕ} (hm : 0 < m) {S : Finset (Action m)} (hS : S.Nonempty) :
    0 < reward m S := sum_pos (fun i _ => weight_pos hm i) hS

 theorem A_nonempty {m : ℕ} (hm : 0 < m) : (A m).Nonempty := by
  exact ⟨Sum.inl ⟨0, hm⟩, by simp [A]⟩

@[simp] theorem reward_A (m : ℕ) : reward m (A m) = m := by
  simp [reward, A, weight]

@[simp] theorem reward_b (m : ℕ) (i : Fin m) : reward m {Sum.inr i} = R m (i.val+1) := by
  simp [reward, weight]

 theorem b_ne_A {m : ℕ} (hm : 0 < m) (i : Fin m) : {Sum.inr i} ≠ A m := by
  intro h
  have hx : Sum.inl (⟨0, hm⟩ : Fin m) ∈ A m := by simp [A]
  rw [← h] at hx
  simp at hx

@[simp] theorem cost_A (m : ℕ) (η : ℝ) : cost m η (A m) = D m η 0 := by simp [cost]
@[simp] theorem cost_b {m : ℕ} (hm : 0 < m) (η : ℝ) (i : Fin m) :
    cost m η {Sum.inr i} = D m η (i.val+1) := by
  simp [cost, b_ne_A hm i, bCost]

 theorem cost_nonneg {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (S : Finset (Action m)) : 0 ≤ cost m η S := by
  unfold cost
  split_ifs with hA hB
  · exact D_nonneg hm hη hη1 0
  · exact sum_nonneg fun i _ => by
      cases i with
      | inl i => exact le_rfl
      | inr i => exact D_nonneg hm hη hη1 (i.val+1)
  · exact mul_nonneg (by norm_num) (sum_nonneg fun i _ => (weight_pos (by omega) i).le)

 theorem cost_empty {m : ℕ} {η : ℝ} (hm : 0 < m) : cost m η ∅ = 0 := by
  have hA : (∅ : Finset (Action m)) ≠ A m := fun h =>
    (A_nonempty hm).ne_empty h.symm
  simp [cost, hA, reward]

 def model (m : ℕ) (η : ℝ) (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) : Model (Action m) :=
  additiveModel (weight m) (cost m η) (fun i => (weight_pos (by omega) i).le)
    (cost_empty (by omega)) (cost_nonneg hm hη hη1)

 theorem model_additive (m : ℕ) (η : ℝ) (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    HasAdditiveReward (model m η hm hη hη1) := by intro S; simp [model]

 theorem action_count (m : ℕ) : Fintype.card (Action m) = 2*m := by simp [Action]; omega

 def chain (m : ℕ) (η : ℝ) (hm : 2 ≤ m) (hη : 0 < η) : LineChain (m+1) where
  reward
    | 0 => 0
    | k+1 => R m k
  cost
    | 0 => 0
    | k+1 => D m η k
  entry
    | 0 => 0
    | k+1 => a m η k
  reward_mono := by
    intro i j hij hj
    cases i with
    | zero => cases j with
      | zero => exact le_rfl
      | succ j => exact (R_pos (by omega) j).le
    | succ i => cases j with
      | zero => omega
      | succ j => exact (R_strictMono (by omega : 0 < m)).monotone (by omega)
  entry_mono := by
    intro i j hi hij hj
    cases i with
    | zero => omega
    | succ i => cases j with
      | zero => omega
      | succ j => exact (a_strictMono hm hη).monotone (by omega)
  cost_step := by
    intro i hi
    cases i with
    | zero =>
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      simp only [D, a, R_zero, Nat.cast_zero, zero_div, sub_zero, ite_true]
      field_simp [hm0]
    | succ i => exact D_step (by omega) i

 def sets (m : ℕ) : ℕ → Finset (Action m)
  | 0 => ∅
  | 1 => A m
  | k+2 => if hk : k < m then {Sum.inr ⟨k, hk⟩} else ∅

@[simp] theorem sets_zero (m : ℕ) : sets m 0 = ∅ := rfl
@[simp] theorem sets_one (m : ℕ) : sets m 1 = A m := rfl
@[simp] theorem sets_add_two {m k : ℕ} (hk : k < m) :
    sets m (k+2) = {Sum.inr ⟨k, hk⟩} := by simp [sets, hk]

 def realized (m : ℕ) (η : ℝ) (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    RealizedChain (model m η hm hη hη1) (m+1) where
  chain := chain m η hm hη
  sets := sets m
  set_zero := rfl
  reward_eq := by
    intro i hi
    cases i with
    | zero => simp [chain, model]
    | succ i => cases i with
      | zero => simpa [model, chain, reward] using reward_A m
      | succ i =>
        change reward m (sets m (i+2)) = R m (i+1)
        rw [sets_add_two (by omega), reward_b]
  cost_eq := by
    intro i hi
    cases i with
    | zero => exact cost_empty (by omega)
    | succ i => cases i with
      | zero => exact cost_A m η
      | succ i =>
        change cost m η (sets m (i+2)) = D m η (i+1)
        rw [sets_add_two (by omega), cost_b (by omega)]
  reward_strict := by
    intro i hi
    cases i with
    | zero => exact R_pos (by omega) 0
    | succ i => exact R_strictMono (by omega : 0 < m) (Nat.lt_succ_self i)
  entry_strict := by
    intro i hi hin
    cases i with
    | zero => omega
    | succ i => exact a_strictMono hm hη (Nat.lt_succ_self i)
  entry_mem := by
    intro i hi hin
    cases i with
    | zero => omega
    | succ i => exact ⟨(a_mem hm hη hη1 i).1.le, (a_mem hm hη hη1 i).2.le⟩
  excluded_utility_neg := by
    intro α hα S hS
    have hA : S ≠ A m := hS 1 (by omega)
    have hb : ¬ ∃ i : Fin m, S = {Sum.inr i} := by
      rintro ⟨i, hi⟩
      exact hS (i.val+2) (by omega) (by simpa using hi)
    have hE : S.Nonempty := nonempty_iff_ne_empty.mpr (hS 0 (by omega))
    have hR : 0 < reward m S := reward_pos (by omega) hE
    change α * reward m S - cost m η S < 0
    rw [cost, if_neg hA, if_neg hb]
    nlinarith [hα.2]

 theorem entry_profit_zero {m : ℕ} {η : ℝ} (hm : 0 < m) :
    (1-a m η 0)*R m 0 = 1+η := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [a, hm0]

 theorem entry_profit_succ {m : ℕ} {η : ℝ} (hm : 0 < m) (k : ℕ) :
    (1-a m η (k+1))*R m (k+1) = 1 := by
  have hR : R m (k+1) ≠ 0 := ne_of_gt (R_pos hm (k+1))
  simp [a, hR]

 theorem optimalValue_eq {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    optimalValue (model m η hm hη hη1) = 1+η := by
  have he := (realized m η hm hη hη1).optimalValue_eq_entry (k := 1) (by omega) (by omega)
    (by
      intro i hi hin
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      change (1-a m η j)*R m j ≤ (1-a m η 0)*R m 0
      rw [entry_profit_zero (by omega)]
      cases j with
      | zero => rw [entry_profit_zero (by omega)]
      | succ j => rw [entry_profit_succ (by omega)]; linarith)
  simpa only [realized, chain, entry_profit_zero (by omega : 0 < m)] using he

/-- The source's optimal principal contract and response are unique. -/
 theorem unique_optimal_pair {m : ℕ} {η α : ℝ}
    (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hop : principal (model m η hm hη hη1) α = optimalValue (model m η hm hη hη1)) :
    α = 1-(1+η)/(m : ℝ) ∧ response (model m η hm hη hη1) α = A m := by
  have he := (realized m η hm hη hη1).unique_optimal_pair (k := 1) (by omega) (by omega)
    (by
      change 0 < (1-a m η 0)*R m 0
      rw [entry_profit_zero (by omega)]
      linarith)
    (by
      intro i hi hin hne
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      change (1-a m η (k+1))*R m (k+1) < (1-a m η 0)*R m 0
      rw [entry_profit_zero (by omega), entry_profit_succ (by omega)]
      linarith) hα hop
  simpa [realized, chain, a] using he

 theorem welfare_eq {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    welfare (model m η hm hη hη1) = 1+η+(m : ℝ)/2 := by
  rw [(realized m η hm hη hη1).welfare_eq_last (by omega)]
  change R m m - D m η m = _
  unfold D
  ring

 theorem principal_at_optimal {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    principal (model m η hm hη hη1) (1-(1+η)/(m : ℝ)) = 1+η := by
  have he := (realized m η hm hη hη1).principal_entry (k := 1) (by omega) (by omega)
  simpa [realized, chain, a, ne_of_gt (show (0 : ℝ) < m by exact_mod_cast (show 0 < m by omega))] using he

 theorem response_at_optimal {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    response (model m η hm hη hη1) (1-(1+η)/(m : ℝ)) = A m := by
  have ha := a_mem hm hη hη1 0
  have hav : 1-(1+η)/(m : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [a] using And.intro ha.1.le ha.2.le
  exact (unique_optimal_pair hm hη hη1 hav (by rw [principal_at_optimal, optimalValue_eq])).2

 theorem anchor_reward {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (i : Action m) (hi : i ∈ A m) : (model m η hm hη hη1).reward {i} = 1 := by
  cases i with
  | inl i => simp [model, weight]
  | inr i => simp [A] at hi

/-- Proposition 9(i)'s exact certificate ratio, with any (equally rewarding)
anchor in its uniquely optimal action set. -/
 theorem localization_ratio {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (i : Action m) (hi : i ∈ A m) :
    welfare (model m η hm hη hη1) /
      ((1-(1-(1+η)/(m : ℝ))) * (model m η hm hη hη1).reward {i}) =
      (m : ℝ) * (1+η+(m : ℝ)/2)/(1+η) := by
  rw [welfare_eq, anchor_reward hm hη hη1 i hi]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hp : 1+η ≠ 0 := by linarith
  field_simp [hm0, hp]
  ring

/-- A uniform explicit Ω(n²) constant, with n=2m. -/
 theorem quadratic_lower_bound {m : ℕ} {η : ℝ} (_hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    ((2*m : ℕ) : ℝ)^2 / 16 ≤ (m : ℝ)*(1+η+(m : ℝ)/2)/(1+η) := by
  have hp : 0 < 1+η := by linarith
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  apply (le_div_iff₀ hp).mpr
  push_cast
  have hsq : 0 ≤ (m : ℝ)^2 := sq_nonneg _
  nlinarith

/-- Pair uniqueness also holds for every response satisfying the paper's
explicit tie-breaking rule, independent of the chosen response implementation. -/
 theorem unique_optimal_response_pair {m : ℕ} {η α : ℝ}
    (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) {S : Finset (Action m)}
    (hS : IsResponse (model m η hm hη hη1) α S)
    (hop : (1-α)*(model m η hm hη hη1).reward S = optimalValue (model m η hm hη hη1)) :
    α = 1-(1+η)/(m : ℝ) ∧ S = A m := by
  have hs := realized_response_unique (realized m η hm hη hη1) hα hS
    (response_spec (model m η hm hη hη1) α)
  subst S
  exact unique_optimal_pair hm hη hη1 hα hop

 theorem total_reward_pos {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    0 < (model m η hm hη hη1).reward univ := by
  have hle := (model m η hm hη hη1).reward_mono (subset_univ (A m))
  have heq : (model m η hm hη hη1).reward (A m) = m := reward_A m
  rw [heq] at hle
  exact lt_of_lt_of_le (by exact_mod_cast (show 0 < m by omega)) hle

 def factor (m : ℕ) (η : ℝ) (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) : ℝ :=
  1 / (model m η hm hη hη1).reward univ

 theorem factor_pos {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    0 < factor m η hm hη hη1 := one_div_pos.mpr (total_reward_pos hm hη hη1)

/-- The source's optional normalization, applied to the actual finite model. -/
 def normalizedModel (m : ℕ) (η : ℝ) (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    Model (Action m) := scaledModel (model m η hm hη hη1)
      (factor m η hm hη hη1) (factor_pos hm hη hη1)

 theorem normalized_additive {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    HasAdditiveReward (normalizedModel m η hm hη hη1) :=
  scaled_additive _ _ _ (model_additive m η hm hη hη1)

 theorem normalized_reward_univ {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    (normalizedModel m η hm hη hη1).reward univ = 1 :=
  scaled_total_one _ (total_reward_pos hm hη hη1)

 theorem normalized_reward_le_one {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (S : Finset (Action m)) : (normalizedModel m η hm hη hη1).reward S ≤ 1 :=
  scaled_reward_le_one _ (total_reward_pos hm hη hη1) S

 theorem normalized_isResponse {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    IsResponse (normalizedModel m η hm hη hη1) (1-(1+η)/(m : ℝ)) (A m) := by
  rw [normalizedModel, scaled_response_iff]
  have he := (realized m η hm hη hη1).isResponse_at_entry (k := 1) (by omega) (by omega)
  simpa [realized, chain, a] using he

 theorem normalized_optimalValue {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    optimalValue (normalizedModel m η hm hη hη1) = factor m η hm hη hη1*(1+η) := by
  rw [normalizedModel, scaled_optimalValue, optimalValue_eq]

 theorem normalized_optimal_pair {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    (1-(1-(1+η)/(m : ℝ)))*(normalizedModel m η hm hη hη1).reward (A m) =
      optimalValue (normalizedModel m η hm hη hη1) := by
  rw [normalized_optimalValue]
  change (1-(1-(1+η)/(m : ℝ)))*(factor m η hm hη hη1 * reward m (A m)) = _
  rw [reward_A]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp
  ring

 theorem normalized_unique_optimal_pair {m : ℕ} {η α : ℝ}
    (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) {S : Finset (Action m)}
    (hS : IsResponse (normalizedModel m η hm hη hη1) α S)
    (hop : (1-α)*(normalizedModel m η hm hη hη1).reward S =
      optimalValue (normalizedModel m η hm hη hη1)) :
    α = 1-(1+η)/(m : ℝ) ∧ S = A m := by
  have hr := (scaled_response_iff _ _ (factor_pos hm hη hη1) α S).mp hS
  apply unique_optimal_response_pair hm hη hη1 hα hr
  rw [normalizedModel, scaled_optimalValue] at hop
  change (1-α)*(factor m η hm hη hη1 * (model m η hm hη hη1).reward S) = _ at hop
  have hs : factor m η hm hη hη1 * ((1-α)*(model m η hm hη hη1).reward S) =
      factor m η hm hη hη1 * optimalValue (model m η hm hη hη1) := by
    nlinarith [hop]
  exact (mul_left_cancel₀ (ne_of_gt (factor_pos hm hη hη1))) hs

 theorem normalized_anchor {m : ℕ} {η : ℝ} (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1)
    (i : Action m) (hi : i ∈ A m) :
    (normalizedModel m η hm hη hη1).reward {i} = factor m η hm hη hη1 := by
  change factor m η hm hη hη1 * (model m η hm hη hη1).reward {i} = _
  rw [anchor_reward hm hη hη1 i hi, mul_one]

 theorem normalized_localization_ratio {m : ℕ} {η : ℝ}
    (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) (i : Action m) (hi : i ∈ A m) :
    welfare (normalizedModel m η hm hη hη1) /
      ((1-(1-(1+η)/(m : ℝ))) * (normalizedModel m η hm hη hη1).reward {i}) =
      (m : ℝ)*(1+η+(m : ℝ)/2)/(1+η) := by
  rw [normalized_anchor hm hη hη1 i hi, normalizedModel, scaled_welfare, welfare_eq]
  have hf : factor m η hm hη hη1 ≠ 0 := ne_of_gt (factor_pos hm hη hη1)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hp : 1+η ≠ 0 := by linarith
  field_simp [hf, hm0, hp]
  ring

end Bundle

/-- Proposition 9(i), including normalization, the unique optimal response pair,
the maximal singleton anchor, the exact ratio, and an explicit quadratic bound. -/
theorem proposition9_i (m : ℕ) (η : ℝ) (hm : 2 ≤ m) (hη : 0 < η) (hη1 : η < 1) :
    ∃ M : Model (Bundle.Action m), HasAdditiveReward M ∧ M.reward univ = 1 ∧
      (∀ T, M.reward T ≤ 1) ∧
      ∃ α ∈ Set.Icc (0 : ℝ) 1, ∃ S : Finset (Bundle.Action m),
        IsResponse M α S ∧ (1-α)*M.reward S = optimalValue M ∧
        (∀ β ∈ Set.Icc (0 : ℝ) 1, ∀ T, IsResponse M β T →
          (1-β)*M.reward T = optimalValue M → β = α ∧ T = S) ∧
        ∃ j ∈ S, 0 < M.reward {j} ∧ (∀ i ∈ S, M.reward {i} ≤ M.reward {j}) ∧
          welfare M / ((1-α)*M.reward {j}) = (m : ℝ)*(1+η+(m : ℝ)/2)/(1+η) ∧
          ((2*m : ℕ) : ℝ)^2/16 ≤ welfare M / ((1-α)*M.reward {j}) := by
  refine ⟨Bundle.normalizedModel m η hm hη hη1,
    Bundle.normalized_additive hm hη hη1, Bundle.normalized_reward_univ hm hη hη1,
    Bundle.normalized_reward_le_one hm hη hη1, 1-(1+η)/(m : ℝ), ?_, Bundle.A m,
    Bundle.normalized_isResponse hm hη hη1, Bundle.normalized_optimal_pair hm hη hη1,
    ?_, Sum.inl ⟨0, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have ha := Bundle.a_mem hm hη hη1 0
    simpa [Bundle.a] using And.intro ha.1.le ha.2.le
  · intro β hβ T hT hop
    exact Bundle.normalized_unique_optimal_pair hm hη hη1 hβ hT hop
  · simp [Bundle.A]
  · rw [Bundle.normalized_anchor hm hη hη1 _ (by simp [Bundle.A])]
    exact Bundle.factor_pos hm hη hη1
  · intro i hi
    rw [Bundle.normalized_anchor hm hη hη1 i hi,
      Bundle.normalized_anchor hm hη hη1 _ (by simp [Bundle.A])]
  · exact Bundle.normalized_localization_ratio hm hη hη1 _ (by simp [Bundle.A])
  · rw [Bundle.normalized_localization_ratio hm hη hη1 _ (by simp [Bundle.A])]
    exact Bundle.quadratic_lower_bound hm hη hη1

/-- Proposition 9(ii), bundled as an unconditional existence theorem about a
finite model with the complete cost-class and normalization guarantees. -/
theorem proposition9_ii (n : ℕ) (r : ℝ) (hn : 2 ≤ n) (hr : 1 < r) :
    ∃ M : Model (Fin n), HasAdditiveReward M ∧ M.reward univ = 1 ∧
      (∀ S, M.reward S ≤ 1) ∧ Monotone M.cost ∧
      (∀ S T, S ⊆ T → ∀ i, i ∉ T →
        M.cost (insert i S)-M.cost S ≤ M.cost (insert i T)-M.cost T) ∧
      welfare M / optimalValue M = (n : ℝ)-(n-1 : ℝ)/r := by
  refine ⟨Singleton.model n r (by omega) hr, Singleton.model_additive n r (by omega) hr,
    Singleton.reward_univ n r (by omega) hr, Singleton.reward_le_one n r (by omega) hr, Singleton.cost_mono (by omega) hr,
    ?_, Singleton.welfare_ratio hn hr⟩
  intro S T hST i hi
  exact Singleton.cost_supermodular r hST hi

end
end CombinatorialContracts.Tightness
