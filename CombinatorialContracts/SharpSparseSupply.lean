import CombinatorialContracts.SparseSupply

/-!
# Sparse supply at the full source tolerance

For the equal-revenue cost, distinct increments below the terminal index `N`
are separated by at least `1 / (N * (N - 1))`.  This closes the full tolerance
range in the sparse-supply paragraph of arXiv:2609.35803v1: an arbitrary positive
`σ` below half the minimum critical-contract gap, rather than just the smaller
explicit perturbation used by the lower bound.  Prices may be arbitrary reals.
-/
namespace CombinatorialContracts.EqualRevenue
noncomputable section
open Finset

/-- The sharper denominator uses the fact that the two increment indices are
*distinct*: the smaller denominator is at most `N - 1`.  The hypotheses already
imply `2 ≤ N`, so both factors in the denominator are positive. -/
theorem increment_gap_sharp {x y N : ℕ} (hxy : x < y) (hy : y < N) :
    1 / ((N : ℝ) * (N - 1)) ≤ increment y - increment x := by
  have hx0 : (0 : ℝ) < x + 1 := by positivity
  have hy0 : (0 : ℝ) < y + 1 := by positivity
  have hN : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hdiff : (1 : ℝ) ≤ (y : ℝ) - x := by
    have hh : (x : ℝ) + 1 ≤ y := by exact_mod_cast hxy
    linarith
  have hxN : (x : ℝ) + 1 ≤ N - 1 := by
    have hh : (x : ℝ) + 2 ≤ N := by
      exact_mod_cast (by omega : x + 2 ≤ N)
    linarith
  have hyN : (y : ℝ) + 1 ≤ N := by exact_mod_cast hy
  have hid : increment y - increment x =
      ((y : ℝ) - x) / (((x : ℝ) + 1) * (y + 1)) := by
    rw [increment_eq, increment_eq]
    field_simp
    ring
  rw [hid]
  apply div_le_div₀ (by linarith) hdiff (mul_pos hx0 hy0)
  calc
    ((x : ℝ) + 1) * (y + 1) ≤ (N - 1) * N :=
      mul_le_mul hxN hyN (le_of_lt hy0) (by linarith)
    _ = (N : ℝ) * (N - 1) := mul_comm _ _

/-- Every nonempty block of increments inherits the sharp separation. -/
theorem cost_add_gap_sharp {x y a N : ℕ} (hxy : x < y)
    (ha : 0 < a) (hN : y + a ≤ N) :
    1 / ((N : ℝ) * (N - 1)) ≤
      (cost (y + a) - cost y) - (cost (x + a) - cost x) := by
  have hg : (a : ℝ) * (1 / ((N : ℝ) * (N - 1))) ≤
      (cost (y + a) - cost y) - (cost (x + a) - cost x) := by
    calc
      (a : ℝ) * (1 / ((N : ℝ) * (N - 1))) =
          ∑ j ∈ range a, (1 / ((N : ℝ) * (N - 1))) := by simp
      _ ≤ ∑ j ∈ range a, (increment (y + j) - increment (x + j)) := by
        apply sum_le_sum
        intro j hj
        exact increment_gap_sharp (by omega) (by have := mem_range.mp hj; omega)
      _ = (cost (y + a) - cost y) - (cost (x + a) - cost x) := by
        rw [cost_add, cost_add, sum_sub_distrib]
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hnon : (0 : ℝ) ≤ 1 / ((N : ℝ) * (N - 1)) :=
    div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
  nlinarith

/-- Uniform exclusion at the full source tolerance.  Positivity of `σ` is not
needed for this stronger statement; the positive source range is below. -/
theorem approxSupply_pairBound_sharp {n : ℕ} {p : Fin n → ℝ} {σ : ℝ}
    (hσ : 2 * σ < 1 / (((2 ^ n - 1 : ℕ) : ℝ) * (((2 ^ n - 1 : ℕ) : ℝ) - 1))) :
    PairBound (approxSupply n p σ) := by
  intro S hS T hT i hiT hiS
  by_contra hnot
  have hfar : binaryIndex S + 2 * 2 ^ i.val < binaryIndex T := by omega
  let U := T.erase i
  have hiU : i ∉ U := by simp [U]
  have hTU : T = insert i U := by simp [U, hiT]
  have hidxT : binaryIndex T = 2 ^ i.val + binaryIndex U := by
    rw [hTU, binaryIndex_insert hiU]
  have hidxS : binaryIndex (insert i S) = 2 ^ i.val + binaryIndex S :=
    binaryIndex_insert hiS
  have hst : binaryIndex S < binaryIndex U := by omega
  have hN : binaryIndex U + 2 ^ i.val ≤ 2 ^ n - 1 := by
    have := binaryIndex_lt T
    omega
  have hgap := cost_add_gap_sharp (a := 2 ^ i.val) hst (by positivity) hN
  have hs := (mem_approxSupply.mp hS) (insert i S)
  have ht := (mem_approxSupply.mp hT) U
  have hpS : (∑ j ∈ insert i S, p j) = p i + ∑ j ∈ S, p j := sum_insert hiS
  have hpT : (∑ j ∈ T, p j) = p i + ∑ j ∈ U, p j := by
    rw [hTU, sum_insert hiU]
  change (∑ j ∈ insert i S, p j) - cost (binaryIndex (insert i S)) ≤
    (∑ j ∈ S, p j) - cost (binaryIndex S) + σ at hs
  change (∑ j ∈ U, p j) - cost (binaryIndex U) ≤
    (∑ j ∈ T, p j) - cost (binaryIndex T) + σ at ht
  rw [hpS, hidxS] at hs
  rw [hpT, hidxT] at ht
  simp only [add_comm (2 ^ i.val)] at hs ht
  linarith

/-- The generic quadratic bound for the entire sharp tolerance interval. -/
theorem approxSupply_card_le_sharp {n : ℕ} (p : Fin n → ℝ) {σ : ℝ}
    (hσ : 2 * σ < 1 / (((2 ^ n - 1 : ℕ) : ℝ) * (((2 ^ n - 1 : ℕ) : ℝ) - 1))) :
    (approxSupply n p σ).card ≤ 4 * (n + 1) ^ 2 :=
  card_le_of_pairBound (approxSupply_pairBound_sharp hσ)

/-- Consecutive positive critical-contract gaps have the source's exact form. -/
theorem critical_gap_eq {t : ℕ} (ht : 0 < t) :
    critical (t + 1) - critical t = 1 / ((t : ℝ) * ((t : ℝ) + 1)) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
  simp only [critical, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The minimum critical gap is attained at the final positive gap, with all
endpoints explicit. -/
theorem critical_gap_minimum {N : ℕ} (hN : 2 ≤ N) :
    (∀ t ∈ Ico 1 N,
      1 / ((N : ℝ) * (N - 1)) ≤ critical (t + 1) - critical t) ∧
    (N - 1 ∈ Ico 1 N ∧ critical ((N - 1) + 1) - critical (N - 1) =
      1 / ((N : ℝ) * (N - 1))) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · intro t ht
    obtain ⟨ht0, htN⟩ := mem_Ico.mp ht
    rw [critical_gap_eq (by omega)]
    apply one_div_le_one_div_of_le (by positivity)
    have ht1 : (t : ℝ) + 1 ≤ N := by exact_mod_cast htN
    have ht' : (t : ℝ) ≤ N - 1 := by linarith
    calc
      (t : ℝ) * ((t : ℝ) + 1) ≤ (N - 1) * N :=
        mul_le_mul ht' ht1 (by positivity) (by linarith)
      _ = (N : ℝ) * (N - 1) := mul_comm _ _
  · refine ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [critical_gap_eq (by omega)]
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one]
    rw [hcast]
    congr 1
    ring

/-- Literal positive-`σ` source range, written using its exact minimum. -/
theorem approxSupply_card_le_source {n : ℕ} (_hn : 2 ≤ n)
    (p : Fin n → ℝ) {σ : ℝ} (_hσpos : 0 < σ)
    (hσ : σ < (1 / 2 : ℝ) *
      (1 / (((2 ^ n - 1 : ℕ) : ℝ) * (((2 ^ n - 1 : ℕ) : ℝ) - 1)))) :
    (approxSupply n p σ).card ≤ 4 * (n + 1) ^ 2 := by
  apply approxSupply_card_le_sharp
  linarith

/-- Equivalent source formulation: the tolerance is below half of every
positive consecutive critical-contract gap.  The final gap witnesses the
sharp hypothesis, so no stronger replacement bound is assumed. -/
theorem approxSupply_card_le_of_critical_gaps {n : ℕ} (hn : 2 ≤ n)
    (p : Fin n → ℝ) {σ : ℝ} (hσpos : 0 < σ)
    (hσ : ∀ t ∈ Ico 1 (2 ^ n - 1),
      σ < (1 / 2 : ℝ) * (critical (t + 1) - critical t)) :
    (approxSupply n p σ).card ≤ 4 * (n + 1) ^ 2 := by
  have hpow : 4 ≤ 2 ^ n := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hN : 2 ≤ 2 ^ n - 1 := by omega
  obtain ⟨_, hmem, hgap⟩ := critical_gap_minimum hN
  have hh := hσ (2 ^ n - 1 - 1) hmem
  rw [hgap] at hh
  exact approxSupply_card_le_source hn p hσpos hh

end
end CombinatorialContracts.EqualRevenue
