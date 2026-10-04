import CombinatorialContracts.Model
import CombinatorialContracts.ChainEnvelope

namespace CombinatorialContracts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite chain realized by actual action sets of a model. Each field is
proved for the concrete tightness constructions; none is a paper-level assumption. -/
structure RealizedChain (M : Model ι) (n : ℕ) where
  chain : LineChain n
  sets : ℕ → Finset ι
  set_zero : sets 0 = ∅
  reward_eq : ∀ i, i ≤ n → M.reward (sets i) = chain.reward i
  cost_eq : ∀ i, i ≤ n → M.cost (sets i) = chain.cost i
  reward_strict : ∀ i, i < n → chain.reward i < chain.reward (i+1)
  entry_strict : ∀ i, 1 ≤ i → i < n → chain.entry i < chain.entry (i+1)
  entry_mem : ∀ i, 1 ≤ i → i ≤ n → chain.entry i ∈ Set.Icc (0 : ℝ) 1
  excluded_utility_neg : ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ S,
    (∀ i, i ≤ n → S ≠ sets i) → agentUtility M α S < 0

namespace RealizedChain
variable {M : Model ι} {n : ℕ} (C : RealizedChain M n)

theorem utility_eq (α : ℝ) {i : ℕ} (hi : i ≤ n) :
    agentUtility M α (C.sets i) = C.chain.utility α i := by
  simp [agentUtility, LineChain.utility, C.reward_eq i hi, C.cost_eq i hi]

@[simp] theorem reward_zero : C.chain.reward 0 = 0 := by
  rw [← C.reward_eq 0 (Nat.zero_le _), C.set_zero, M.reward_empty]

@[simp] theorem cost_zero : C.chain.cost 0 = 0 := by
  rw [← C.cost_eq 0 (Nat.zero_le _), C.set_zero, M.cost_empty]

theorem utility_entry_nonneg {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    0 ≤ C.chain.utility (C.chain.entry k) k := by
  have h := C.chain.utility_le_at_entry hk hkn (Nat.zero_le n)
  simpa [LineChain.utility] using h

theorem isBestResponse_at_entry {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsBestResponse M (C.chain.entry k) (C.sets k) := by
  intro S
  by_cases hs : ∃ j, j ≤ n ∧ S = C.sets j
  · obtain ⟨j, hj, rfl⟩ := hs
    rw [C.utility_eq _ hj, C.utility_eq _ hkn]
    exact C.chain.utility_le_at_entry hk hkn hj
  · have hn : ∀ i, i ≤ n → S ≠ C.sets i := by simpa using hs
    have hneg := C.excluded_utility_neg _ (C.entry_mem k hk hkn) S hn
    rw [C.utility_eq _ hkn]
    exact hneg.le.trans (C.utility_entry_nonneg hk hkn)

theorem isResponse_at_entry {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsResponse M (C.chain.entry k) (C.sets k) := by
  refine ⟨C.isBestResponse_at_entry hk hkn, ?_⟩
  intro S hS
  by_cases hs : ∃ j, j ≤ n ∧ S = C.sets j
  · obtain ⟨j, hj, rfl⟩ := hs
    rw [C.reward_eq j hj, C.reward_eq k hkn]
    by_cases hjk : j ≤ k
    · exact C.chain.reward_mono j k hjk hkn
    · have hkj : k < j := by omega
      have hlt := C.chain.utility_lt_at_entry_of_later hk hkj hj
        (C.entry_strict k hk (by omega)) (C.reward_strict k (by omega))
      have hle := hS (C.sets k)
      rw [C.utility_eq _ hkn, C.utility_eq _ hj] at hle
      linarith
  · have hn : ∀ i, i ≤ n → S ≠ C.sets i := by simpa using hs
    have hneg := C.excluded_utility_neg _ (C.entry_mem k hk hkn) S hn
    have hnonneg := bestResponse_agentUtility_nonneg M hS
    linarith

theorem principal_entry {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    principal M (C.chain.entry k) = (1-C.chain.entry k)*C.chain.reward k := by
  have hr := response_reward_unique M (response_spec M (C.chain.entry k))
    (C.isResponse_at_entry hk hkn)
  rw [principal, hr, C.reward_eq k hkn]

theorem principal_le_of_entry_le {P α : ℝ} (hP : 0 ≤ P)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hentries : ∀ i, 1 ≤ i → i ≤ n → (1-C.chain.entry i)*C.chain.reward i ≤ P) :
    principal M α ≤ P := by
  let S := response M α
  have hS : IsBestResponse M α S := response_best M α
  have hs : ∃ j, j ≤ n ∧ S = C.sets j := by
    by_contra h
    have hn : ∀ i, i ≤ n → S ≠ C.sets i := by simpa using h
    have hneg := C.excluded_utility_neg α hα S hn
    have hnonneg := bestResponse_agentUtility_nonneg M hS
    linarith
  obtain ⟨j, hj, hs⟩ := hs
  change (1-α)*M.reward S ≤ P
  rw [hs, C.reward_eq j hj]
  cases j with
  | zero => simpa using hP
  | succ i =>
    have hu := hS (C.sets i)
    rw [hs, C.utility_eq _ (by omega), C.utility_eq _ hj] at hu
    have hn : 0 ≤ C.chain.reward (i+1) := by
      rw [← C.reward_eq (i+1) hj]
      exact M.reward_nonneg _
    exact (C.chain.principal_le_entry (by omega) (C.reward_strict i (by omega)) hn hu).trans
      (hentries (i+1) (by omega) hj)

theorem optimalValue_le_of_entry_le {P : ℝ} (hP : 0 ≤ P)
    (hentries : ∀ i, 1 ≤ i → i ≤ n → (1-C.chain.entry i)*C.chain.reward i ≤ P) :
    optimalValue M ≤ P := C.principal_le_of_entry_le hP (optimum_mem M) hentries

theorem optimalValue_eq_entry {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hentries : ∀ i, 1 ≤ i → i ≤ n →
      (1-C.chain.entry i)*C.chain.reward i ≤ (1-C.chain.entry k)*C.chain.reward k) :
    optimalValue M = (1-C.chain.entry k)*C.chain.reward k := by
  have hp : 0 ≤ (1-C.chain.entry k)*C.chain.reward k := by
    rw [← C.principal_entry hk hkn]
    exact principal_nonneg M (C.entry_mem k hk hkn).2
  apply le_antisymm (C.optimalValue_le_of_entry_le hp hentries)
  rw [← C.principal_entry hk hkn]
  exact principal_le_optimalValue M (C.entry_mem k hk hkn)

theorem welfare_eq_last (hn : 1 ≤ n) :
    welfare M = C.chain.reward n - C.chain.cost n := by
  have hlast : IsBestResponse M 1 (C.sets n) := by
    intro S
    by_cases hs : ∃ j, j ≤ n ∧ S = C.sets j
    · obtain ⟨j, hj, rfl⟩ := hs
      rw [C.utility_eq _ hj, C.utility_eq _ le_rfl]
      have he := C.chain.utility_le_at_entry hn le_rfl hj
      have hr := C.chain.reward_mono j n hj le_rfl
      have ha := (C.entry_mem n hn le_rfl).2
      have hp := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hr)
      dsimp [LineChain.utility] at he ⊢
      nlinarith
    · have hx : ∀ i, i ≤ n → S ≠ C.sets i := by simpa using hs
      have hneg := C.excluded_utility_neg 1 (by norm_num) S hx
      have he := C.utility_entry_nonneg hn le_rfl
      have hr : 0 ≤ C.chain.reward n := by
        rw [← C.reward_eq n le_rfl]; exact M.reward_nonneg _
      have ha := (C.entry_mem n hn le_rfl).2
      rw [C.utility_eq _ le_rfl]
      dsimp [LineChain.utility] at he ⊢
      nlinarith
  have heq := le_antisymm (hlast (response M 1)) (response_best M 1 (C.sets n))
  rw [← welfare_eq_agentUtility M, C.utility_eq _ le_rfl] at heq
  simpa [LineChain.utility] using heq

/-- A strictly best positive entry profit has a unique optimal contract and
response set, even when nonmaximal entries tie or entry one is zero. -/
theorem unique_optimal_pair {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hp : 0 < (1-C.chain.entry k)*C.chain.reward k)
    (hstrict : ∀ i, 1 ≤ i → i ≤ n → i ≠ k →
      (1-C.chain.entry i)*C.chain.reward i < (1-C.chain.entry k)*C.chain.reward k)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hop : principal M α = optimalValue M) :
    α = C.chain.entry k ∧ response M α = C.sets k := by
  have hentries : ∀ i, 1 ≤ i → i ≤ n →
      (1-C.chain.entry i)*C.chain.reward i ≤ (1-C.chain.entry k)*C.chain.reward k := by
    intro i hi hin
    by_cases he : i = k
    · subst i; rfl
    · exact (hstrict i hi hin he).le
  have hopt := C.optimalValue_eq_entry hk hkn hentries
  have hvalue : principal M α = (1-C.chain.entry k)*C.chain.reward k := hop.trans hopt
  let S := response M α
  have hS : IsBestResponse M α S := response_best M α
  have hs : ∃ j, j ≤ n ∧ S = C.sets j := by
    by_contra h
    have hx : ∀ i, i ≤ n → S ≠ C.sets i := by simpa using h
    have hneg := C.excluded_utility_neg α hα S hx
    have hnonneg := bestResponse_agentUtility_nonneg M hS
    linarith
  obtain ⟨j, hj, hs⟩ := hs
  have hprincipal : principal M α = (1-α)*C.chain.reward j := by
    change (1-α)*M.reward S = _
    rw [hs, C.reward_eq j hj]
  have hjpos : 1 ≤ j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz, C.reward_zero, mul_zero] at hprincipal
    linarith
  have hjk : j = k := by
    by_contra hne
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hu := hS (C.sets i)
    rw [hs, C.utility_eq _ (by omega), C.utility_eq _ hj] at hu
    have hnr : 0 ≤ C.chain.reward (i+1) := by
      rw [← C.reward_eq (i+1) hj]; exact M.reward_nonneg _
    have hle := C.chain.principal_le_entry (by omega)
      (C.reward_strict i (by omega)) hnr hu
    have hlt := hstrict (i+1) (by omega) hj hne
    rw [hprincipal] at hvalue
    linarith
  subst j
  have hr : 0 < C.chain.reward k := by
    have h1 := C.reward_strict 0 (by omega)
    have h2 := C.chain.reward_mono 1 k hk hkn
    simp only [C.reward_zero, zero_add] at h1
    linarith
  refine ⟨?_, hs⟩
  rw [hprincipal] at hvalue
  nlinarith

end RealizedChain
end CombinatorialContracts
