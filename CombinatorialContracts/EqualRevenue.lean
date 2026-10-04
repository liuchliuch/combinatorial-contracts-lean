import CombinatorialContracts.Model

/-!
# The concrete equal-revenue sequence

All definitions in this file are the explicit functions from the equal-revenue appendix of
arXiv:2609.35803v1 (the binary index is zero-based).  In particular, the first
increment is zero; claims of *strict* monotonicity at zero in the cited external
paper are not assumed.
-/
namespace CombinatorialContracts.EqualRevenue

noncomputable section
open Finset

def increment (i : ℕ) : ℝ := (i : ℝ) / (i + 1)
def cost (t : ℕ) : ℝ := ∑ i ∈ range t, increment i
def harmonic (t : ℕ) : ℝ := ∑ i ∈ range t, 1 / ((i : ℝ) + 1)
def utility (α : ℝ) (t : ℕ) : ℝ := α * t - cost t
def critical (t : ℕ) : ℝ := 1 - 1 / (t : ℝ)

@[simp] theorem cost_zero : cost 0 = 0 := by simp [cost]
@[simp] theorem harmonic_zero : harmonic 0 = 0 := by simp [harmonic]
@[simp] theorem increment_zero : increment 0 = 0 := by simp [increment]
@[simp] theorem cost_one : cost 1 = 0 := by simp [cost]

theorem cost_succ (t : ℕ) : cost (t + 1) = cost t + increment t := by
  simp [cost, sum_range_succ]
theorem harmonic_succ (t : ℕ) : harmonic (t + 1) = harmonic t + 1 / ((t : ℝ) + 1) := by
  simp [harmonic, sum_range_succ]

theorem increment_eq (t : ℕ) : increment t = 1 - 1 / ((t : ℝ) + 1) := by
  unfold increment
  have : (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem increment_nonneg (t : ℕ) : 0 ≤ increment t := by unfold increment; positivity

theorem increment_lt_one (t : ℕ) : increment t < 1 := by
  rw [increment_eq]
  have : 0 < 1 / ((t : ℝ) + 1) := by positivity
  linarith

theorem increment_strictMono : StrictMono increment := by
  intro a b hab
  rw [increment_eq, increment_eq]
  have ha : (0 : ℝ) < a + 1 := by positivity
  have hab' : (a : ℝ) + 1 < b + 1 := by exact_mod_cast Nat.add_lt_add_right hab 1
  have := one_div_lt_one_div_of_lt ha hab'
  linarith

theorem cost_nonneg (t : ℕ) : 0 ≤ cost t := sum_nonneg fun i _ => increment_nonneg i

theorem cost_mono : Monotone cost := by
  apply monotone_nat_of_le_succ
  intro t
  rw [cost_succ]
  exact le_add_of_nonneg_right (increment_nonneg t)

theorem cost_eq (t : ℕ) : cost t = (t : ℝ) - harmonic t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [cost_succ, harmonic_succ, ih, increment_eq]
    push_cast
    ring

theorem harmonic_mono : Monotone harmonic := by
  apply monotone_nat_of_le_succ
  intro t
  rw [harmonic_succ]
  exact le_add_of_nonneg_right (by positivity)

theorem welfare_eq_harmonic (t : ℕ) : (t : ℝ) - cost t = harmonic t := by
  rw [cost_eq]
  ring

theorem utility_succ (α : ℝ) (t : ℕ) :
    utility α (t + 1) = utility α t + (α - increment t) := by
  simp only [utility, cost_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem critical_succ (t : ℕ) : critical (t + 1) = increment t := by
  rw [increment_eq]
  simp [critical]

theorem critical_profit {t : ℕ} (ht : 0 < t) : (1 - critical t) * t = 1 := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ht
  simp [critical, ht']

/-- Every earlier line is weakly below the line with index `t` at its entry. -/
theorem utility_le_at_entry {s t : ℕ} (hst : s ≤ t) :
    utility (increment t) s ≤ utility (increment t) t := by
  induction t with
  | zero => have : s = 0 := Nat.eq_zero_of_le_zero hst; subst s; exact le_rfl
  | succ t ih =>
    rcases eq_or_lt_of_le hst with he | he
    · subst s; exact le_rfl
    · have hs : s ≤ t := Nat.le_of_lt_succ he
      have hbase := ih hs
      have hs' : (s : ℝ) ≤ t := by exact_mod_cast hs
      have hd : increment t ≤ increment (t + 1) := increment_strictMono.monotone (Nat.le_succ t)
      have hshift : utility (increment (t + 1)) s ≤ utility (increment (t + 1)) t := by
        unfold utility at *
        nlinarith
      rw [utility_succ]
      linarith

theorem utility_le_add {s d : ℕ} {α : ℝ}
    (h : ∀ i, s ≤ i → i < s + d → increment i ≤ α) :
    utility α s ≤ utility α (s + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hh := ih (fun i hi hj => h i hi (by omega))
    rw [show s + (d + 1) = (s + d) + 1 by omega, utility_succ]
    have := h (s + d) (by omega) (by omega)
    linarith

theorem utility_add_le {s d : ℕ} {α : ℝ}
    (h : ∀ i, s ≤ i → i < s + d → α ≤ increment i) :
    utility α (s + d) ≤ utility α s := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hh := ih (fun i hi hj => h i hi (by omega))
    rw [show s + (d + 1) = (s + d) + 1 by omega, utility_succ]
    have := h (s + d) (by omega) (by omega)
    linarith

/-- Consecutive marginal costs locate the maximizing line, including all ties. -/
theorem utility_max_at {t : ℕ} {α : ℝ}
    (hlo : ∀ i, i < t → increment i ≤ α)
    (hhi : ∀ i, t ≤ i → α ≤ increment i) (s : ℕ) :
    utility α s ≤ utility α t := by
  by_cases hs : s ≤ t
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
    exact utility_le_add (fun i _ hi => hlo i hi)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hs)
    exact utility_add_le (fun i hi _ => hhi i hi)

theorem critical_max {t : ℕ} (ht : 0 < t) (s : ℕ) :
    utility (critical t) s ≤ utility (critical t) t := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [critical_succ]
  exact utility_max_at
    (fun i hi => increment_strictMono.monotone (by omega))
    (fun i hi => increment_strictMono.monotone (by omega)) s


/-- Binary encoding of actual action subsets, not an abstract outcome count. -/
def binaryIndex {n : ℕ} (S : Finset (Fin n)) : ℕ := ∑ i ∈ S, 2 ^ (i : ℕ)

@[simp] theorem binaryIndex_empty (n : ℕ) : binaryIndex (∅ : Finset (Fin n)) = 0 := by
  simp [binaryIndex]

@[simp] theorem binaryIndex_singleton {n : ℕ} (i : Fin n) : binaryIndex {i} = 2 ^ (i : ℕ) := by
  simp [binaryIndex]

theorem binaryIndex_insert {n : ℕ} {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    binaryIndex (insert i S) = 2 ^ (i : ℕ) + binaryIndex S := by
  simp [binaryIndex, hi]

theorem binaryIndex_eq_map {n : ℕ} (S : Finset (Fin n)) :
    binaryIndex S = ∑ i ∈ S.map Fin.valEmbedding, 2 ^ i := by
  simp [binaryIndex]

theorem binaryIndex_injective (n : ℕ) :
    Function.Injective (binaryIndex (n := n)) := by
  intro S T h
  apply Finset.map_injective Fin.valEmbedding
  apply Finset.geomSum_injective (n := 2) (by omega)
  simpa only [← binaryIndex_eq_map] using h

theorem binaryIndex_lt {n : ℕ} (S : Finset (Fin n)) : binaryIndex S < 2 ^ n := by
  rw [binaryIndex_eq_map]
  apply Nat.geomSum_lt (by omega)
  intro k hk
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hk
  exact i.isLt

theorem binaryIndex_surjective {n t : ℕ} (ht : t < 2 ^ n) :
    ∃ S : Finset (Fin n), binaryIndex S = t := by
  let e : Finset (Fin n) → Fin (2 ^ n) := fun S => ⟨binaryIndex S, binaryIndex_lt S⟩
  have hi : Function.Injective e := by
    intro S T h
    exact binaryIndex_injective n (congrArg Fin.val h)
  have hb := (Fintype.bijective_iff_injective_and_card e).mpr ⟨hi, by simp⟩
  obtain ⟨S, hS⟩ := hb.surjective ⟨t, ht⟩
  exact ⟨S, congrArg Fin.val hS⟩

theorem binaryIndex_mono {n : ℕ} : Monotone (binaryIndex (n := n)) := by
  intro S T hST
  exact Finset.sum_le_sum_of_subset hST

theorem binaryIndex_strictMono {n : ℕ} : StrictMono (binaryIndex (n := n)) := by
  intro S T hST
  exact lt_of_le_of_ne (binaryIndex_mono hST.le)
    (fun h => hST.ne (binaryIndex_injective n h))

theorem binaryIndex_union_add_inter {n : ℕ} (S T : Finset (Fin n)) :
    binaryIndex (S ∪ T) + binaryIndex (S ∩ T) = binaryIndex S + binaryIndex T := by
  exact sum_union_inter

/-- Welfare is maximized by the largest binary index. -/
theorem binary_welfare_max {n : ℕ} (S : Finset (Fin n)) :
    (binaryIndex S : ℝ) - cost (binaryIndex S) ≤ harmonic (2 ^ n - 1) := by
  rw [welfare_eq_harmonic]
  exact harmonic_mono (by have := binaryIndex_lt S; omega)

theorem cost_add (x a : ℕ) :
    cost (x + a) - cost x = ∑ i ∈ range a, increment (x + i) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show x + (a + 1) = (x + a) + 1 by omega, cost_succ, sum_range_succ, ← ih]
    ring

/-- Convexity of the explicit indexed cost. -/
theorem cost_add_mono {x y a : ℕ} (hxy : x ≤ y) :
    cost (x + a) - cost x ≤ cost (y + a) - cost y := by
  rw [cost_add, cost_add]
  exact sum_le_sum (fun i _ => increment_strictMono.monotone (by omega))

/-- Increasing marginal costs on actual binary-encoded subsets. -/
theorem binary_cost_supermodular {n : ℕ} {S T : Finset (Fin n)}
    (hST : S ⊆ T) {i : Fin n} (hi : i ∉ T) :
    cost (binaryIndex (insert i S)) - cost (binaryIndex S) ≤
      cost (binaryIndex (insert i T)) - cost (binaryIndex T) := by
  have his : i ∉ S := fun h => hi (hST h)
  rw [binaryIndex_insert his, binaryIndex_insert hi, add_comm (2 ^ (i : ℕ)),
    add_comm (2 ^ (i : ℕ))]
  exact cost_add_mono (binaryIndex_mono hST)


def model (n : ℕ) : Model (Fin n) where
  reward S := binaryIndex S
  cost S := cost (binaryIndex S)
  reward_empty := by simp
  cost_empty := by simp
  reward_nonneg S := Nat.cast_nonneg _
  cost_nonneg S := cost_nonneg _
  reward_mono := fun S T h => by
    change (binaryIndex S : ℝ) ≤ binaryIndex T
    exact_mod_cast binaryIndex_mono h
  reward_subadditive S T := by
    have h := binaryIndex_union_add_inter S T
    have hn : binaryIndex (S ∪ T) ≤ binaryIndex S + binaryIndex T := by omega
    exact_mod_cast hn

@[simp] theorem model_reward (n : ℕ) (S : Finset (Fin n)) :
    (model n).reward S = binaryIndex S := rfl
@[simp] theorem model_cost (n : ℕ) (S : Finset (Fin n)) :
    (model n).cost S = cost (binaryIndex S) := rfl
@[simp] theorem model_utility (n : ℕ) (α : ℝ) (S : Finset (Fin n)) :
    agentUtility (model n) α S = utility α (binaryIndex S) := rfl

theorem utility_later_lt_entry {t s : ℕ} (ht : 0 < t) (hts : t < s) :
    utility (critical t) s < utility (critical t) t := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [critical_succ]
  have hs : t + 1 + 1 ≤ s := by omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  have hh : utility (increment t) (t + 1 + 1 + d) ≤
      utility (increment t) (t + 1 + 1) :=
    utility_add_le (fun i hi _ => increment_strictMono.monotone (by omega))
  rw [utility_succ (increment t) (t + 1)] at hh
  have hstrict := increment_strictMono (Nat.lt_succ_self t)
  linarith

theorem critical_isResponse {n : ℕ} {S : Finset (Fin n)} (hS : 0 < binaryIndex S) :
    IsResponse (model n) (critical (binaryIndex S)) S := by
  refine ⟨fun T => critical_max hS _, ?_⟩
  intro T hT
  by_contra h
  have hst : binaryIndex S < binaryIndex T := by
    simpa only [model_reward, Nat.cast_le, not_le] using h
  have hlt := utility_later_lt_entry hS hst
  have hge := hT S
  rw [model_utility, model_utility] at hge
  linarith

theorem critical_response_index {n t : ℕ} (ht : 0 < t) (htn : t < 2 ^ n) :
    binaryIndex (response (model n) (critical t)) = t := by
  obtain ⟨S, hS⟩ := binaryIndex_surjective htn
  have hresp := critical_isResponse (hS ▸ ht)
  rw [hS] at hresp
  have hr := response_reward_unique (model n) (response_spec _ _) hresp
  simpa only [model_reward, Nat.cast_inj, hS] using hr

theorem model_critical_profit {n t : ℕ} (ht : 0 < t) (htn : t < 2 ^ n) :
    principal (model n) (critical t) = 1 := by
  rw [principal, model_reward, critical_response_index ht htn]
  exact critical_profit ht

theorem principal_le_one (n : ℕ) (α : ℝ) : principal (model n) α ≤ 1 := by
  let t := binaryIndex (response (model n) α)
  by_cases ht : t = 0
  · change (1 - α) * (t : ℝ) ≤ 1
    simp [ht]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero ht
    obtain ⟨S, hS⟩ := binaryIndex_surjective (n := n) (t := u) (by
      have := binaryIndex_lt (response (model n) α); dsimp [t] at hu; omega)
    have hbest := response_best (model n) α S
    simp only [model_utility, hS] at hbest
    change utility α u ≤ utility α t at hbest
    rw [hu, utility_succ] at hbest
    have hα : increment u ≤ α := by linarith
    have hα' : critical t ≤ α := by rw [hu, critical_succ]; exact hα
    have ht' : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hp := critical_profit htpos
    change (1 - α) * (t : ℝ) ≤ 1
    nlinarith

/-- Proposition 10, first equality, including actual exact tie-breaking. -/
theorem optimalValue_eq_one {n : ℕ} (hn : 0 < n) : optimalValue (model n) = 1 := by
  apply le_antisymm
  · exact principal_le_one n _
  · have ht : 1 < 2 ^ n := Nat.one_lt_pow hn.ne' (by omega)
    have hp := model_critical_profit (n := n) (t := 1) (by omega) ht
    have hl := principal_le_optimalValue (model n) (α := critical 1) (by norm_num [critical])
    linarith

/-- Proposition 10, exact harmonic welfare. -/
theorem welfare_eq {n : ℕ} : welfare (model n) = harmonic (2 ^ n - 1) := by
  apply le_antisymm
  · exact binary_welfare_max _
  · have hn : 0 < 2 ^ n := by positivity
    obtain ⟨S, hS⟩ := binaryIndex_surjective (n := n) (t := 2 ^ n - 1) (by omega)
    have hh := welfare_max (model n) S
    simpa only [model_reward, model_cost, hS, welfare_eq_harmonic] using hh

/-- The largest singleton in a set is within a factor two of its total reward. -/
theorem largest_binary_weight_bounds {n : ℕ} {S : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ S) (hmax : ∀ i ∈ S, i ≤ j) :
    2 ^ (j : ℕ) ≤ binaryIndex S ∧ binaryIndex S < 2 * 2 ^ (j : ℕ) := by
  constructor
  · unfold binaryIndex; exact single_le_sum (f := fun i : Fin n => 2 ^ (i : ℕ)) (fun _ _ => Nat.zero_le _) hj
  · rw [binaryIndex_eq_map]
    have hb : ∑ k ∈ S.map Fin.valEmbedding, 2 ^ k < 2 ^ ((j : ℕ) + 1) := by
      apply Nat.geomSum_lt (by omega)
      intro k hk
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hk
      have := hmax i hi
      exact Nat.lt_succ_of_le this
    simpa [pow_succ, mul_comm] using hb

/-- Proposition 10, equation (12), without an omitted reciprocal side condition. -/
theorem singleton_scale {n : ℕ} {S : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ S) (hmax : ∀ i ∈ S, i ≤ j) :
    1 / (2 * (2 : ℝ) ^ (j : ℕ)) < 1 - critical (binaryIndex S) ∧
      1 - critical (binaryIndex S) ≤ 1 / (2 : ℝ) ^ (j : ℕ) := by
  obtain ⟨hl, hu⟩ := largest_binary_weight_bounds hj hmax
  have hl' : (2 : ℝ) ^ (j : ℕ) ≤ binaryIndex S := by exact_mod_cast hl
  have hu' : (binaryIndex S : ℝ) < 2 * (2 : ℝ) ^ (j : ℕ) := by exact_mod_cast hu
  have hp : (0 : ℝ) < (2 : ℝ) ^ (j : ℕ) := by positivity
  have ht : (0 : ℝ) < binaryIndex S := lt_of_lt_of_le hp hl'
  simp only [critical, sub_sub_cancel]
  exact ⟨one_div_lt_one_div_of_lt ht hu', one_div_le_one_div_of_le hp hl'⟩


theorem harmonic_add (x a : ℕ) :
    harmonic (x + a) - harmonic x = ∑ i ∈ range a, 1 / ((x + i : ℕ) + 1 : ℝ) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show x + (a + 1) = (x + a) + 1 by omega, harmonic_succ, sum_range_succ, ← ih]
    push_cast
    ring

theorem harmonic_dyadic_step {p : ℕ} (hp : 0 < p) :
    (1 / 2 : ℝ) ≤ harmonic (2 * p - 1) - harmonic (p - 1) ∧
      harmonic (2 * p - 1) - harmonic (p - 1) ≤ 1 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [show 2 * p - 1 = (p - 1) + p by omega, harmonic_add]
  have hden (i : ℕ) : ((p - 1 + i : ℕ) + 1 : ℝ) = p + i := by
    have he : p - 1 + i + 1 = p + i := by omega
    exact_mod_cast he
  simp only [hden]
  have hl : ∑ i ∈ range p, (1 / (2 * p : ℝ)) ≤ ∑ i ∈ range p, 1 / ((p : ℝ) + i) := by
    apply sum_le_sum
    intro i hi
    apply one_div_le_one_div_of_le (by positivity)
    have hi' : (i : ℝ) < p := by exact_mod_cast mem_range.mp hi
    linarith
  have hu : ∑ i ∈ range p, 1 / ((p : ℝ) + i) ≤ ∑ i ∈ range p, (1 / (p : ℝ)) := by
    apply sum_le_sum
    intro i hi
    apply one_div_le_one_div_of_le hp'
    exact le_add_of_nonneg_right (Nat.cast_nonneg i)
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hp'
  have hls : (∑ i ∈ range p, (1 / (2 * p : ℝ))) = 1 / 2 := by
    simp only [sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hus : (∑ i ∈ range p, (1 / (p : ℝ))) = 1 := by simp [hp0]
  rw [hls] at hl
  rw [hus] at hu
  exact ⟨hl, hu⟩

/-- Explicit linear bounds imply the paper's Θ(n) welfare/profit gap. -/
theorem harmonic_binary_bounds (n : ℕ) :
    (n : ℝ) / 2 ≤ harmonic (2 ^ n - 1) ∧ harmonic (2 ^ n - 1) ≤ n := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih =>
    have hs := harmonic_dyadic_step (p := 2 ^ n) (by positivity)
    rw [pow_succ, Nat.mul_comm]
    push_cast
    constructor <;> linarith


theorem increment_gap {x y N : ℕ} (hxy : x < y) (hy : y < N) :
    1 / (N : ℝ) ^ 2 ≤ increment y - increment x := by
  have hx0 : (0 : ℝ) < x + 1 := by positivity
  have hy0 : (0 : ℝ) < y + 1 := by positivity
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdiff : (1 : ℝ) ≤ (y : ℝ) - x := by
    have : x + 1 ≤ y := by omega
    have hh : (x : ℝ) + 1 ≤ y := by exact_mod_cast this
    linarith
  have hxN : (x : ℝ) + 1 ≤ N := by exact_mod_cast (by omega : x + 1 ≤ N)
  have hyN : (y : ℝ) + 1 ≤ N := by exact_mod_cast hy
  have hid : increment y - increment x = ((y : ℝ) - x) / (((x : ℝ) + 1) * (y + 1)) := by
    rw [increment_eq, increment_eq]
    field_simp
    ring
  rw [hid]
  apply div_le_div₀ (by linarith) hdiff (mul_pos hx0 hy0)
  nlinarith


/-- The source's largest-reward formulation of the singleton scale bound. -/
theorem singleton_scale_of_largest_reward {n : ℕ} {S : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ S) (hmax : ∀ i ∈ S, (model n).reward {i} ≤ (model n).reward {j}) :
    1 / (2 * (model n).reward {j}) < 1 - critical (binaryIndex S) ∧
      1 - critical (binaryIndex S) ≤ 1 / (model n).reward {j} := by
  have hm : ∀ i ∈ S, i ≤ j := by
    intro i hi
    have hh := hmax i hi
    simp only [model_reward, binaryIndex_singleton] at hh
    have hn : 2 ^ (i : ℕ) ≤ 2 ^ (j : ℕ) := by exact_mod_cast hh
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hn
  simpa only [model_reward, binaryIndex_singleton, Nat.cast_pow, Nat.cast_ofNat] using
    singleton_scale hj hm

theorem model_additive (n : ℕ) : HasAdditiveReward (model n) := by
  intro S
  simp [model_reward, binaryIndex]

/-- Proposition 10, assembled with the actual model, harmonic identity,
explicit linear growth, and the source's reward-based maximum condition. -/
theorem proposition10 {n : ℕ} (hn : 0 < n) :
    optimalValue (model n) = 1 ∧ welfare (model n) = harmonic (2 ^ n - 1) ∧
    (n : ℝ) / 2 ≤ harmonic (2 ^ n - 1) ∧ harmonic (2 ^ n - 1) ≤ n ∧
    (∀ (S : Finset (Fin n)) (j : Fin n), j ∈ S →
      (∀ i ∈ S, (model n).reward {i} ≤ (model n).reward {j}) →
      1 / (2 * (model n).reward {j}) < 1 - critical (binaryIndex S) ∧
        1 - critical (binaryIndex S) ≤ 1 / (model n).reward {j}) := by
  exact ⟨optimalValue_eq_one hn, welfare_eq, (harmonic_binary_bounds n).1,
    (harmonic_binary_bounds n).2, fun S j hj hm => singleton_scale_of_largest_reward hj hm⟩

end
end CombinatorialContracts.EqualRevenue
