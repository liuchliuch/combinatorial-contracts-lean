import Mathlib

namespace CombinatorialContracts

/-- A chain of affine response lines, with consecutive crossing parameters.
The index zero can represent the empty response. -/
structure LineChain (n : ℕ) where
  reward : ℕ → ℝ
  cost : ℕ → ℝ
  entry : ℕ → ℝ
  reward_mono : ∀ i j, i ≤ j → j ≤ n → reward i ≤ reward j
  entry_mono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ n → entry i ≤ entry j
  cost_step : ∀ i, i < n → cost (i+1) - cost i =
    entry (i+1) * (reward (i+1) - reward i)

namespace LineChain
variable {n : ℕ} (L : LineChain n)

def utility (α : ℝ) (i : ℕ) : ℝ := α * L.reward i - L.cost i

theorem utility_step (α : ℝ) {i : ℕ} (hi : i < n) :
    L.utility α (i+1) - L.utility α i =
      (α - L.entry (i+1)) * (L.reward (i+1) - L.reward i) := by
  dsimp [utility]
  rw [show L.cost (i+1) = L.cost i + L.entry (i+1) *
    (L.reward (i+1) - L.reward i) by linarith [L.cost_step i hi]]
  ring

theorem utility_step_nonneg {α : ℝ} {i : ℕ} (hi : i < n)
    (hα : L.entry (i+1) ≤ α) : L.utility α i ≤ L.utility α (i+1) := by
  have hr : 0 ≤ L.reward (i+1) - L.reward i :=
    sub_nonneg.mpr (L.reward_mono i (i+1) (by omega) (by omega))
  have h := mul_nonneg (sub_nonneg.mpr hα) hr
  rw [← L.utility_step α hi] at h
  linarith

theorem utility_step_nonpos {α : ℝ} {i : ℕ} (hi : i < n)
    (hα : α ≤ L.entry (i+1)) : L.utility α (i+1) ≤ L.utility α i := by
  have hr : 0 ≤ L.reward (i+1) - L.reward i :=
    sub_nonneg.mpr (L.reward_mono i (i+1) (by omega) (by omega))
  have h := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hα) hr
  rw [← L.utility_step α hi] at h
  linarith

theorem utility_le_at_entry {k j : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hj : j ≤ n) :
    L.utility (L.entry k) j ≤ L.utility (L.entry k) k := by
  by_cases hjk : j ≤ k
  · have h : ∀ d, j + d ≤ k → L.utility (L.entry k) j ≤
        L.utility (L.entry k) (j+d) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        intro hd
        have hx : j+d < n := by omega
        have ha : L.entry (j+d+1) ≤ L.entry k :=
          L.entry_mono _ _ (by omega) (by omega) hkn
        exact le_trans (ih (by omega)) (by
          simpa [Nat.add_assoc] using L.utility_step_nonneg hx ha)
    simpa [Nat.add_sub_of_le hjk] using h (k-j) (by omega)
  · have h : ∀ d, k+d ≤ n → L.utility (L.entry k) (k+d) ≤
        L.utility (L.entry k) k := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        intro hd
        have hx : k+d < n := by omega
        have ha : L.entry k ≤ L.entry (k+d+1) :=
          L.entry_mono _ _ hk (by omega) (by omega)
        exact le_trans (by
          simpa [Nat.add_assoc] using L.utility_step_nonpos hx ha) (ih (by omega))
    have hkj : k ≤ j := by omega
    simpa [Nat.add_sub_of_le hkj] using h (j-k) (by omega)

/-- Any response defeating its predecessor can only be induced at or above
its entry threshold, provided its reward is strictly larger. -/
theorem entry_le_of_predecessor_le {α : ℝ} {i : ℕ} (hi : i < n)
    (hr : L.reward i < L.reward (i+1))
    (hu : L.utility α i ≤ L.utility α (i+1)) : L.entry (i+1) ≤ α := by
  have hp : 0 ≤ (α - L.entry (i+1)) * (L.reward (i+1) - L.reward i) := by
    rw [← L.utility_step α hi]
    exact sub_nonneg.mpr hu
  have hd : 0 < L.reward (i+1) - L.reward i := sub_pos.mpr hr
  nlinarith

/-- Consequently an induced line's principal utility is bounded by its
utility at its entry threshold. -/
theorem principal_le_entry {α : ℝ} {i : ℕ} (hi : i < n)
    (hr : L.reward i < L.reward (i+1)) (hn : 0 ≤ L.reward (i+1))
    (hu : L.utility α i ≤ L.utility α (i+1)) :
    (1-α) * L.reward (i+1) ≤ (1-L.entry (i+1)) * L.reward (i+1) := by
  exact mul_le_mul_of_nonneg_right (by
    linarith [L.entry_le_of_predecessor_le hi hr hu]) hn

/-- Later lines are strictly inferior at the current entry if the next
crossing is strictly later and the next reward is strictly larger. -/
theorem utility_lt_at_entry_of_later {k j : ℕ} (hk : 1 ≤ k)
    (hkj : k < j) (hjn : j ≤ n)
    (he : L.entry k < L.entry (k+1))
    (hr : L.reward k < L.reward (k+1)) :
    L.utility (L.entry k) j < L.utility (L.entry k) k := by
  have hstep : L.utility (L.entry k) (k+1) < L.utility (L.entry k) k := by
    have h := mul_neg_of_neg_of_pos (sub_neg.mpr he) (sub_pos.mpr hr)
    rw [← L.utility_step (L.entry k) (by omega)] at h
    linarith
  have htail : ∀ d, k+1+d ≤ n → L.utility (L.entry k) (k+1+d) ≤
      L.utility (L.entry k) (k+1) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      have hx : k+1+d < n := by omega
      have ha : L.entry k ≤ L.entry (k+1+d+1) :=
        L.entry_mono _ _ hk (by omega) (by omega)
      exact le_trans (by
        simpa [Nat.add_assoc] using L.utility_step_nonpos hx ha) (ih (by omega))
  have hj : k+1 ≤ j := by omega
  have hle : L.utility (L.entry k) j ≤ L.utility (L.entry k) (k+1) := by
    simpa [Nat.add_sub_of_le hj] using htail (j-(k+1)) (by omega)
  exact lt_of_le_of_lt hle hstep

end LineChain
end CombinatorialContracts
