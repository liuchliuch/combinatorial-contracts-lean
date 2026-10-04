import CombinatorialContracts.EqualRevenue
import CombinatorialContracts.ChainEnvelope

/-!
# Concrete lower-bound family and oracle reductions

The hidden set is restricted to the upper half of the nonzero binary indices,
as in Theorem 8 of arXiv:2609.35803v1. No sparse-oracle property or
identification bound is introduced as an axiom.
-/
namespace CombinatorialContracts.LowerBounds
noncomputable section
open Finset EqualRevenue

/-- Lower exactly one indexed cost. -/
def perturbedCost (k : ℕ) (ζ : ℝ) (t : ℕ) : ℝ :=
  cost t - if t = k then ζ else 0

def perturbation (N : ℕ) : ℝ := 1 / (8 * (N : ℝ) ^ 2)
def accuracy (N : ℕ) : ℝ := 1 / (32 * (N : ℝ))

def perturbedIncrement (k : ℕ) (ζ : ℝ) (t : ℕ) : ℝ :=
  perturbedCost k ζ (t + 1) - perturbedCost k ζ t

theorem perturbedIncrement_eq (k t : ℕ) (ζ : ℝ) :
    perturbedIncrement k ζ t = increment t -
      (if t + 1 = k then ζ else 0) + (if t = k then ζ else 0) := by
  simp only [perturbedIncrement, perturbedCost, cost_succ]
  ring

theorem perturbedIncrement_bounds {k t : ℕ} {ζ : ℝ} (hζ : 0 ≤ ζ) :
    increment t - ζ ≤ perturbedIncrement k ζ t ∧
      perturbedIncrement k ζ t ≤ increment t + ζ := by
  rw [perturbedIncrement_eq]
  split_ifs <;> constructor <;> linarith

theorem perturbedIncrement_strictMono {k N : ℕ} {ζ : ℝ}
    (hζ : 0 ≤ ζ) (hsmall : 2 * ζ < 1 / (N : ℝ) ^ 2)
    {x y : ℕ} (hxy : x < y) (hy : y < N) :
    perturbedIncrement k ζ x < perturbedIncrement k ζ y := by
  have hgap := increment_gap hxy hy
  have hx := perturbedIncrement_bounds (k := k) (t := x) hζ
  have hy := perturbedIncrement_bounds (k := k) (t := y) hζ
  linarith

theorem perturbedIncrement_nonneg {k t : ℕ} {ζ : ℝ}
    (hk : 2 ≤ k) (hζ : 0 ≤ ζ) (hsmall : ζ ≤ 1 / 2) :
    0 ≤ perturbedIncrement k ζ t := by
  by_cases ht : t = 0
  · subst t
    simp [perturbedIncrement_eq, show 1 ≠ k by omega, show 0 ≠ k by omega]
  · have h1 : (1 / 2 : ℝ) ≤ increment t := by
      have hh := increment_strictMono.monotone (show 1 ≤ t by omega)
      norm_num [increment] at hh ⊢
      exact hh
    have hb := perturbedIncrement_bounds (k := k) (t := t) hζ
    linarith

theorem perturbedCost_mono {k : ℕ} {ζ : ℝ}
    (hk : 2 ≤ k) (hζ : 0 ≤ ζ) (hsmall : ζ ≤ 1 / 2) :
    Monotone (perturbedCost k ζ) := by
  apply monotone_nat_of_le_succ
  intro t
  have hh := perturbedIncrement_nonneg (t := t) hk hζ hsmall
  unfold perturbedIncrement at hh
  linarith

@[simp] theorem perturbedCost_zero {k : ℕ} (hk : 0 < k) (ζ : ℝ) :
    perturbedCost k ζ 0 = 0 := by
  simp [perturbedCost, Nat.ne_of_lt hk]

theorem perturbedCost_nonneg {k t : ℕ} {ζ : ℝ}
    (hk : 2 ≤ k) (hζ : 0 ≤ ζ) (hsmall : ζ ≤ 1 / 2) :
    0 ≤ perturbedCost k ζ t := by
  have hh := perturbedCost_mono hk hζ hsmall (Nat.zero_le t)
  simpa [perturbedCost_zero (by omega : 0 < k)] using hh

theorem perturbedCost_add (k x a : ℕ) (ζ : ℝ) :
    perturbedCost k ζ (x + a) - perturbedCost k ζ x =
      ∑ i ∈ range a, perturbedIncrement k ζ (x + i) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, ← ih]
    simp only [perturbedIncrement]
    rw [show x + (a + 1) = x + a + 1 by omega]
    ring

theorem perturbedCost_add_mono {k N x y a : ℕ} {ζ : ℝ}
    (hζ : 0 ≤ ζ) (hsmall : 2 * ζ < 1 / (N : ℝ) ^ 2)
    (hxy : x ≤ y) (hya : y + a ≤ N) :
    perturbedCost k ζ (x + a) - perturbedCost k ζ x ≤
      perturbedCost k ζ (y + a) - perturbedCost k ζ y := by
  rw [perturbedCost_add, perturbedCost_add]
  apply sum_le_sum
  intro i hi
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (perturbedIncrement_strictMono hζ hsmall (by omega)
      (by have := mem_range.mp hi; omega)).le

theorem perturbation_pos {N : ℕ} (hN : 0 < N) : 0 < perturbation N := by
  unfold perturbation
  positivity

theorem perturbation_small {N : ℕ} (hN : 0 < N) :
    2 * perturbation N < 1 / (N : ℝ) ^ 2 ∧ perturbation N ≤ 1 / 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold perturbation
  constructor
  · field_simp
    nlinarith
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (N : ℝ) ^ 2)).mpr
    nlinarith

/-- The actual nonnegative normalized set-cost model from the paper. -/
def model (n k : ℕ) (hk : 2 ≤ k) : Model (Fin n) where
  reward S := binaryIndex S
  cost S := perturbedCost k (perturbation (2 ^ n - 1)) (binaryIndex S)
  reward_empty := by simp
  cost_empty := by simp [perturbedCost_zero (by omega : 0 < k)]
  reward_nonneg S := Nat.cast_nonneg _
  cost_nonneg S := by
    apply perturbedCost_nonneg hk
    · unfold perturbation; positivity
    · by_cases hn : n = 0
      · subst n; norm_num [perturbation]
      · exact (perturbation_small (by have := Nat.one_lt_pow hn (by omega : 1 < 2); omega)).2
  reward_mono := (EqualRevenue.model n).reward_mono
  reward_subadditive := (EqualRevenue.model n).reward_subadditive

/-- Monotonicity is proved for every actual pair of action subsets. -/
theorem model_cost_mono {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    Monotone (model n k hk).cost := by
  have hN : 0 < 2 ^ n - 1 := by have := Nat.one_lt_pow hn.ne' (by omega : 1 < 2); omega
  intro S T hST
  exact perturbedCost_mono hk (perturbation_pos hN).le (perturbation_small hN).2
    (binaryIndex_mono hST)

/-- Supermodularity survives the perturbation, by discrete convexity. -/
theorem model_cost_supermodular {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    {S T : Finset (Fin n)} (hST : S ⊆ T) {i : Fin n} (hi : i ∉ T) :
    (model n k hk).cost (insert i S) - (model n k hk).cost S ≤
      (model n k hk).cost (insert i T) - (model n k hk).cost T := by
  have hN : 0 < 2 ^ n - 1 := by have := Nat.one_lt_pow hn.ne' (by omega : 1 < 2); omega
  change perturbedCost _ _ _ - perturbedCost _ _ _ ≤ perturbedCost _ _ _ - perturbedCost _ _ _
  have his : i ∉ S := fun h => hi (hST h)
  rw [binaryIndex_insert his, binaryIndex_insert hi, add_comm (2 ^ (i : ℕ)),
    add_comm (2 ^ (i : ℕ))]
  apply perturbedCost_add_mono (perturbation_pos hN).le (perturbation_small hN).1
    (binaryIndex_mono hST)
  have hb := binaryIndex_lt (insert i T)
  rw [binaryIndex_insert hi] at hb
  omega


def entry (k : ℕ) (ζ : ℝ) (t : ℕ) : ℝ := perturbedIncrement k ζ (t - 1)

def chain (N k : ℕ) (ζ : ℝ) (hζ : 0 ≤ ζ) (hsmall : 2 * ζ < 1 / (N : ℝ) ^ 2) :
    LineChain N where
  reward t := t
  cost := perturbedCost k ζ
  entry := entry k ζ
  reward_mono i j hij _ := by exact_mod_cast hij
  entry_mono i j hi hij hj := by
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · exact (perturbedIncrement_strictMono hζ hsmall (by omega) (by omega)).le
  cost_step i hi := by
    simp [entry, perturbedIncrement]

theorem entry_hidden {k : ℕ} (hk : 0 < k) (ζ : ℝ) :
    entry k ζ k = critical k - ζ := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [entry, perturbedIncrement_eq, critical_succ]

theorem entry_other {k t : ℕ} (ht : 0 < t) (htk : t ≠ k) (ζ : ℝ) (hζ : 0 ≤ ζ) :
    critical t ≤ entry k ζ t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  simp only [entry, Nat.succ_sub_one, perturbedIncrement_eq, critical_succ]
  simp only [htk, ↓reduceIte, sub_zero]
  split_ifs <;> linarith

theorem hidden_entry_nonneg {N k : ℕ} (hk : 2 ≤ k) (hN : 0 < N) :
    0 ≤ entry k (perturbation N) k :=
  perturbedIncrement_nonneg hk (perturbation_pos hN).le (perturbation_small hN).2

theorem hidden_entry_lt_one {N k : ℕ} (hk : 0 < k) (hN : 0 < N) :
    entry k (perturbation N) k < 1 := by
  rw [entry_hidden hk]
  have hh : 0 < 1 / (k : ℝ) := by positivity
  have hz := perturbation_pos hN
  unfold critical
  linarith

theorem hidden_isResponse {n k : ℕ} (hk : 2 ≤ k) (hkn : k < 2 ^ n)
    {S : Finset (Fin n)} (hS : binaryIndex S = k) :
    IsResponse (model n k hk) (entry k (perturbation (2 ^ n - 1)) k) S := by
  let N := 2 ^ n - 1
  have hN : 0 < N := by dsimp [N]; omega
  let L := chain N k (perturbation N) (perturbation_pos hN).le (perturbation_small hN).1
  have hbest : IsBestResponse (model n k hk) (entry k (perturbation N) k) S := by
    intro T
    have hh := L.utility_le_at_entry (k := k) (j := binaryIndex T) (by omega)
      (by dsimp [N]; omega) (by have := binaryIndex_lt T; dsimp [N]; omega)
    change _ ≤ _ at hh
    simpa only [LineChain.utility, L, chain, agentUtility, model, N, hS] using hh
  refine ⟨hbest, ?_⟩
  intro T hT
  by_contra hnot
  have hlt : k < binaryIndex T := by
    change ¬(binaryIndex T : ℝ) ≤ binaryIndex S at hnot
    rw [hS] at hnot
    exact_mod_cast lt_of_not_ge hnot
  have hentry : L.entry k < L.entry (k + 1) := by
    change perturbedIncrement _ _ (k - 1) < perturbedIncrement _ _ (k + 1 - 1)
    apply perturbedIncrement_strictMono (perturbation_pos hN).le (perturbation_small hN).1
    · omega
    · have := binaryIndex_lt T; dsimp [N]; omega
  have hstrict := L.utility_lt_at_entry_of_later (k := k) (j := binaryIndex T)
    (by omega) hlt (by have := binaryIndex_lt T; dsimp [N]; omega) hentry
    (by change (k : ℝ) < (k + 1 : ℕ); exact_mod_cast Nat.lt_succ_self k)
  have hge := hT S
  change _ ≤ _ at hge
  simp only [agentUtility, model, hS] at hge
  simp only [LineChain.utility, L, chain, N] at hstrict
  linarith

theorem hidden_response_index {n k : ℕ} (hk : 2 ≤ k) (hkn : k < 2 ^ n) :
    binaryIndex (response (model n k hk) (entry k (perturbation (2 ^ n - 1)) k)) = k := by
  obtain ⟨S, hS⟩ := binaryIndex_surjective hkn
  have hh := hidden_isResponse hk hkn hS
  have heq := response_reward_unique (model n k hk) (response_spec _ _) hh
  change (binaryIndex _ : ℝ) = binaryIndex S at heq
  rw [hS] at heq
  exact_mod_cast heq

theorem hidden_profit {n k : ℕ} (hk : 2 ≤ k) (hkn : k < 2 ^ n) :
    principal (model n k hk) (entry k (perturbation (2 ^ n - 1)) k) =
      1 + perturbation (2 ^ n - 1) * k := by
  unfold principal
  change (1 - entry _ _ _) * (binaryIndex _ : ℝ) = _
  rw [hidden_response_index hk hkn, entry_hidden (by omega)]
  have hh := critical_profit (t := k) (by omega)
  nlinarith

/-- An induced nonhidden response can never yield profit above one. -/
theorem nonhidden_profit_le_one {n k : ℕ} (hk : 2 ≤ k) (α : ℝ)
    (hother : binaryIndex (response (model n k hk) α) ≠ k) :
    principal (model n k hk) α ≤ 1 := by
  let t := binaryIndex (response (model n k hk) α)
  by_cases ht : t = 0
  · change (1 - α) * (t : ℝ) ≤ 1
    simp [ht]
  · obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero ht
    obtain ⟨S, hS⟩ := binaryIndex_surjective (n := n) (t := u) (by
      have := binaryIndex_lt (response (model n k hk) α); dsimp [t] at hu; omega)
    have hb := response_best (model n k hk) α S
    change α * (binaryIndex S : ℝ) - perturbedCost _ _ (binaryIndex S) ≤
      α * (t : ℝ) - perturbedCost _ _ t at hb
    rw [hS, hu] at hb
    have hent : entry k (perturbation (2 ^ n - 1)) t ≤ α := by
      rw [hu]
      simp only [entry, Nat.succ_sub_one, perturbedIncrement]
      push_cast at hb
      linarith
    have hζ : 0 ≤ perturbation (2 ^ n - 1) := by unfold perturbation; positivity
    have ho := entry_other (t := t) (k := k) (by omega) hother _ hζ
    have hp := critical_profit (t := t) (by omega)
    have ht' : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    change (1 - α) * (t : ℝ) ≤ 1
    nlinarith


theorem response_entry_le {n k : ℕ} (hk : 2 ≤ k) (α : ℝ)
    (ht : 0 < binaryIndex (response (model n k hk) α)) :
    entry k (perturbation (2 ^ n - 1)) (binaryIndex (response (model n k hk) α)) ≤ α := by
  let t := binaryIndex (response (model n k hk) α)
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  obtain ⟨S, hS⟩ := binaryIndex_surjective (n := n) (t := u) (by
    have := binaryIndex_lt (response (model n k hk) α); omega)
  have hb := response_best (model n k hk) α S
  change α * (binaryIndex S : ℝ) - perturbedCost _ _ (binaryIndex S) ≤
    α * (binaryIndex (response (model n k hk) α) : ℝ) - perturbedCost _ _ _ at hb
  rw [hS, hu] at hb
  rw [hu]
  simp only [entry, Nat.succ_sub_one, perturbedIncrement]
  push_cast at hb
  linarith

theorem principal_le_hidden {n k : ℕ} (hk : 2 ≤ k) (α : ℝ) :
    principal (model n k hk) α ≤ 1 + perturbation (2 ^ n - 1) * k := by
  by_cases hh : binaryIndex (response (model n k hk) α) = k
  · have hent := response_entry_le (n := n) hk α (by omega)
    rw [hh, entry_hidden (by omega)] at hent
    have hp := critical_profit (t := k) (by omega)
    have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    change (1 - α) * (binaryIndex _ : ℝ) ≤ _
    rw [hh]
    nlinarith
  · have hnonneg : 0 ≤ perturbation (2 ^ n - 1) * k := by unfold perturbation; positivity
    exact (nonhidden_profit_le_one hk α hh).trans (by linarith)

theorem optimalValue_eq_hidden {n k : ℕ} (hk : 2 ≤ k) (hkn : k < 2 ^ n) :
    optimalValue (model n k hk) = 1 + perturbation (2 ^ n - 1) * k := by
  apply le_antisymm
  · exact principal_le_hidden hk _
  · have hN : 0 < 2 ^ n - 1 := by omega
    have hentry : entry k (perturbation (2 ^ n - 1)) k ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hidden_entry_nonneg hk hN, (hidden_entry_lt_one (by omega) hN).le⟩
    simpa only [hidden_profit hk hkn] using principal_le_optimalValue (model n k hk) hentry

theorem accuracy_advantage {N k : ℕ} (hN : 0 < N) (hNk : N ≤ 2 * k) :
    1 < (1 - accuracy N) * (1 + perturbation N * k) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNk' : (N : ℝ) ≤ 2 * k := by exact_mod_cast hNk
  have ha : 0 < 1 - accuracy N := by
    unfold accuracy
    have : 1 / (32 * (N : ℝ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have hg : 1 / (16 * (N : ℝ)) ≤ perturbation N * k := by
    unfold perturbation
    field_simp
    nlinarith
  have hc : 1 < (1 - accuracy N) * (1 + 1 / (16 * (N : ℝ))) := by
    unfold accuracy
    field_simp
    nlinarith
  exact hc.trans_le (mul_le_mul_of_nonneg_left (by linarith) ha.le)

/-- Any successful high-accuracy contract gives strictly more than one. -/
theorem approximate_profit_gt_one {n k : ℕ} (hk : 2 ≤ k) (hkn : k < 2 ^ n)
    (hhalf : 2 ^ n - 1 ≤ 2 * k) {α : ℝ}
    (happrox : (1 - accuracy (2 ^ n - 1)) * optimalValue (model n k hk) ≤
      principal (model n k hk) α) :
    1 < principal (model n k hk) α := by
  rw [optimalValue_eq_hidden hk hkn] at happrox
  exact lt_of_lt_of_le (accuracy_advantage (by omega) hhalf) happrox

/-- The contract alone reveals the hidden index: no extra oracle call is hidden
in the lower-bound reduction. -/
theorem profitable_contract_interval {n k : ℕ} (hk : 2 ≤ k) {α : ℝ}
    (hprofit : 1 < principal (model n k hk) α) :
    critical k - perturbation (2 ^ n - 1) ≤ α ∧ α < critical k := by
  have hresp : binaryIndex (response (model n k hk) α) = k := by
    by_contra hh
    have := nonhidden_profit_le_one hk α hh
    linarith
  have hlo := response_entry_le (n := n) hk α (by omega)
  rw [hresp, entry_hidden (by omega)] at hlo
  have hp := critical_profit (t := k) (by omega)
  change 1 < (1 - α) * (binaryIndex _ : ℝ) at hprofit
  rw [hresp] at hprofit
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  exact ⟨hlo, by nlinarith⟩

/-- Profitable output intervals for distinct hidden instances are disjoint. -/
theorem decoding_unique {N k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkN : k ≤ N) (hlN : l ≤ N) {α : ℝ}
    (hki : critical k - perturbation N ≤ α ∧ α < critical k)
    (hli : critical l - perturbation N ≤ α ∧ α < critical l) : k = l := by
  have hN : 0 < N := by omega
  have hζ := perturbation_small hN
  have hz := perturbation_pos hN
  have aux {a b : ℕ} (ha : 0 < a) (hab : a < b) (hbN : b ≤ N) :
      1 / (N : ℝ) ^ 2 ≤ critical b - critical a := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    rw [critical_succ, critical_succ]
    exact increment_gap (by omega) (by omega)
  rcases lt_trichotomy k l with h | h | h
  · have hg := aux hk h hlN
    exfalso; linarith
  · exact h
  · have hg := aux hl h hkN
    exfalso; linarith


def hiddenIndices (n : ℕ) : Finset ℕ := Icc (2 ^ (n - 1)) (2 ^ n - 1)
abbrev Hidden (n : ℕ) := {k : ℕ // k ∈ hiddenIndices n}

theorem hiddenIndices_card {n : ℕ} (hn : 0 < n) :
    (hiddenIndices n).card = 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [hiddenIndices, Nat.succ_sub_one, Nat.card_Icc, pow_succ]
  have hp := Nat.two_pow_pos m
  omega

theorem hidden_properties {n : ℕ} (hn : 2 ≤ n) (k : Hidden n) :
    2 ≤ k.val ∧ k.val < 2 ^ n ∧ 2 ^ n - 1 ≤ 2 * k.val := by
  have hk := mem_Icc.mp k.property
  have hp : 2 ≤ 2 ^ (n - 1) := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (i := 1) (j := n - 1) (by omega)
    simpa using this
  have he : 2 ^ n = 2 * 2 ^ (n - 1) := by
    nth_rw 1 [show n = (n - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  constructor
  · omega
  constructor
  · have := Nat.two_pow_pos n; omega
  · omega

theorem model_additive (n k : ℕ) (hk : 2 ≤ k) : HasAdditiveReward (model n k hk) := by
  intro S
  change (binaryIndex S : ℝ) = ∑ i ∈ S, (binaryIndex {i} : ℝ)
  simp only [binaryIndex]
  simp

/-- Explicit bounds certify γₙ = Θ(2⁻ⁿ). -/
theorem accuracy_binary_bounds {n : ℕ} (hn : 0 < n) :
    1 / (32 * (2 : ℝ) ^ n) ≤ accuracy (2 ^ n - 1) ∧
      accuracy (2 ^ n - 1) ≤ 1 / (16 * (2 : ℝ) ^ n) := by
  have hpow : 1 < 2 ^ n := Nat.one_lt_pow hn.ne' (by omega)
  have hN : (0 : ℝ) < (2 ^ n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < 2 ^ n - 1)
  have hu : ((2 ^ n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (by omega : 2 ^ n - 1 ≤ 2 ^ n)
  have hl : (2 : ℝ) ^ n ≤ 2 * ((2 ^ n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ^ n ≤ 2 * (2 ^ n - 1))
  unfold accuracy
  constructor
  · exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Deterministic decoding from a real contract, using only the known base data. -/
def decode (n : ℕ) (α : ℝ) : Option (Hidden n) :=
  if h : ∃ k : Hidden n, critical k.val - perturbation (2 ^ n - 1) ≤ α ∧ α < critical k.val
  then some (Classical.choose h) else none

theorem decode_correct {n : ℕ} (hn : 2 ≤ n) (k : Hidden n) {α : ℝ}
    (happrox : (1 - accuracy (2 ^ n - 1)) *
      optimalValue (model n k.val (hidden_properties hn k).1) ≤
      principal (model n k.val (hidden_properties hn k).1) α) :
    decode n α = some k := by
  have hp := hidden_properties hn k
  have hg := approximate_profit_gt_one hp.1 hp.2.1 hp.2.2 happrox
  have hkint := profitable_contract_interval hp.1 hg
  have he : ∃ l : Hidden n, critical l.val - perturbation (2 ^ n - 1) ≤ α ∧ α < critical l.val :=
    ⟨k, hkint⟩
  rw [decode, dif_pos he]
  congr 1
  apply Subtype.ext
  have hl := Classical.choose_spec he
  have hprop := hidden_properties hn (Classical.choose he)
  exact decoding_unique (by omega) (by omega) (by omega) (by omega) hl hkint

/-- Exact optimization is a special case of the same identification reduction. -/
theorem decode_exact {n : ℕ} (hn : 2 ≤ n) (k : Hidden n) {α : ℝ}
    (hopt : principal (model n k.val (hidden_properties hn k).1) α =
      optimalValue (model n k.val (hidden_properties hn k).1)) :
    decode n α = some k := by
  apply decode_correct hn k
  rw [hopt]
  have hg : 0 ≤ accuracy (2 ^ n - 1) := by unfold accuracy; positivity
  have hv := optimalValue_nonneg (model n k.val (hidden_properties hn k).1)
  nlinarith


/-- The hidden entry is the unique globally optimal feasible contract. -/
theorem unique_optimal_contract {n k : ℕ} (hk : 2 ≤ k) (hkn : k < 2 ^ n)
    {α : ℝ} (hopt : principal (model n k hk) α = optimalValue (model n k hk)) :
    α = entry k (perturbation (2 ^ n - 1)) k := by
  have hN : 0 < 2 ^ n - 1 := by omega
  have hz := perturbation_pos hN
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [optimalValue_eq_hidden hk hkn] at hopt
  have hprofit : 1 < principal (model n k hk) α := by
    have := mul_pos hz hk'
    linarith
  have hr : binaryIndex (response (model n k hk) α) = k := by
    by_contra hh
    have := nonhidden_profit_le_one hk α hh
    linarith
  change (1 - α) * (binaryIndex _ : ℝ) = _ at hopt
  rw [hr] at hopt
  rw [entry_hidden (by omega)]
  have hp := critical_profit (t := k) (by omega)
  nlinarith

/-- Distinct candidate indices really give distinct cost functions. -/
theorem hidden_models_distinct {n : ℕ} (hn : 2 ≤ n) {k l : Hidden n} (hkl : k ≠ l) :
    (model n k.val (hidden_properties hn k).1).cost ≠
      (model n l.val (hidden_properties hn l).1).cost := by
  have hk := hidden_properties hn k
  have hl := hidden_properties hn l
  have hne : k.val ≠ l.val := fun h => hkl (Subtype.ext h)
  obtain ⟨S, hS⟩ := binaryIndex_surjective hk.2.1
  intro heq
  have hh := congrFun heq S
  change perturbedCost k.val _ (binaryIndex S) = perturbedCost l.val _ (binaryIndex S) at hh
  rw [hS] at hh
  simp only [perturbedCost, hne, ↓reduceIte, sub_zero] at hh
  have hz := perturbation_pos (N := 2 ^ n - 1) (by omega)
  linarith

/-- Complete concrete family certificate used by both lower bounds. -/
theorem hard_family {n : ℕ} (hn : 2 ≤ n) (k : Hidden n) :
    HasAdditiveReward (model n k.val (hidden_properties hn k).1) ∧
    Monotone (model n k.val (hidden_properties hn k).1).cost ∧
    (∀ (S T : Finset (Fin n)), S ⊆ T → ∀ i : Fin n, i ∉ T →
      (model n k.val (hidden_properties hn k).1).cost (insert i S) -
        (model n k.val (hidden_properties hn k).1).cost S ≤
      (model n k.val (hidden_properties hn k).1).cost (insert i T) -
        (model n k.val (hidden_properties hn k).1).cost T) ∧
    optimalValue (model n k.val (hidden_properties hn k).1) =
      1 + perturbation (2 ^ n - 1) * k.val := by
  have hk := hidden_properties hn k
  exact ⟨model_additive n k.val hk.1, model_cost_mono hk.1 (by omega),
    fun S T hST i hi => model_cost_supermodular hk.1 (by omega) hST hi,
    optimalValue_eq_hidden hk.1 hk.2.1⟩


def decodeNat (n : ℕ) (α : ℝ) : ℕ := ((decode n α).map Subtype.val).getD 0

def instanceAt (n k : ℕ) : Model (Fin n) :=
  if hk : 2 ≤ k then model n k hk else EqualRevenue.model n

@[simp] theorem instanceAt_eq {n k : ℕ} (hk : 2 ≤ k) :
    instanceAt n k = model n k hk := by simp [instanceAt, hk]

theorem decodeNat_correct {n k : ℕ} (hn : 2 ≤ n) (hk : k ∈ hiddenIndices n) {α : ℝ}
    (happrox : (1 - accuracy (2 ^ n - 1)) * optimalValue (instanceAt n k) ≤
      principal (instanceAt n k) α) : decodeNat n α = k := by
  let K : Hidden n := ⟨k, hk⟩
  have hprop := hidden_properties hn K
  have h2 : 2 ≤ k := hprop.1
  rw [instanceAt_eq h2] at happrox
  have hh := decode_correct hn K happrox
  simp only [decodeNat, hh, Option.map_some, Option.getD_some]
  rfl

theorem hiddenIndices_nonempty {n : ℕ} (hn : 0 < n) : (hiddenIndices n).Nonempty := by
  apply card_pos.mp
  rw [hiddenIndices_card hn]
  positivity

end
end CombinatorialContracts.LowerBounds
