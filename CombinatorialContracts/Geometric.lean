import Mathlib

/-!
# Finite geometric search

This file proves the geometric covering step, including the shifted positive-share
variant, and bounds the *least* number of contractions by a logarithmic expression.
No spacing assumption on best-response breakpoints is involved.
-/

namespace CombinatorialContracts

/-- The exact-real loop count: the first power reaching the requested width.
The fallback merely makes the function total on invalid inputs. -/
noncomputable def leastGridSteps (q R : ℝ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, q ^ k ≤ 1 / R then Nat.find h else 0

theorem pow_ceil_log_le_inv {ε R : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hR : 1 ≤ R) :
    (1 - ε) ^ ⌈Real.log R / ε⌉₊ ≤ 1 / R := by
  have hq : 0 < 1 - ε := by linarith
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  apply (Real.log_le_log_iff (pow_pos hq _) (div_pos zero_lt_one hRp)).mp
  rw [Real.log_pow, one_div, Real.log_inv]
  have hlog := Real.log_le_sub_one_of_pos hq
  have hc := Nat.le_ceil (Real.log R / ε)
  have hce : Real.log R ≤ (⌈Real.log R / ε⌉₊ : ℝ) * ε :=
    (div_le_iff₀ hε).mp hc
  have hk : (0 : ℝ) ≤ ⌈Real.log R / ε⌉₊ := Nat.cast_nonneg _
  nlinarith

theorem leastGridSteps_spec {ε R : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hR : 1 ≤ R) :
    (1 - ε) ^ leastGridSteps (1 - ε) R ≤ 1 / R := by
  have he : ∃ k : ℕ, (1 - ε) ^ k ≤ 1 / R :=
    ⟨_, pow_ceil_log_le_inv hε hε1 hR⟩
  rw [leastGridSteps, dif_pos he]
  exact Nat.find_spec he

theorem leastGridSteps_le_ceil {ε R : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hR : 1 ≤ R) :
    leastGridSteps (1 - ε) R ≤ ⌈Real.log R / ε⌉₊ := by
  have he : ∃ k : ℕ, (1 - ε) ^ k ≤ 1 / R :=
    ⟨_, pow_ceil_log_le_inv hε hε1 hR⟩
  rw [leastGridSteps, dif_pos he]
  exact Nat.find_min' he (pow_ceil_log_le_inv hε hε1 hR)

theorem leastGridSteps_minimal {q R : ℝ} (he : ∃ k : ℕ, q ^ k ≤ 1 / R)
    {j : ℕ} (hj : j < leastGridSteps q R) : 1 / R < q ^ j := by
  rw [leastGridSteps, dif_pos he] at hj
  have h := Nat.find_min he hj
  exact lt_of_not_ge h

@[simp] theorem leastGridSteps_one (q : ℝ) : leastGridSteps q 1 = 0 := by
  have he : ∃ k : ℕ, q ^ k ≤ 1 / (1 : ℝ) := ⟨0, by simp⟩
  simp only [leastGridSteps, dif_pos he]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' he (m := 0) (by simp))

/-- A shifted grid contains a multiplicatively close point. The index starts at
one, ensuring positive agent shares when `b ≤ 1`. -/
theorem shifted_geometric_cover {q b δ : ℝ} {K : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hb : 0 ≤ b)
    (hδb : δ ≤ b) (hlast : b * q ^ (K + 1) ≤ δ) :
    ∃ k : ℕ, k < K + 1 ∧ q * δ ≤ b * q ^ (k + 1) ∧
      b * q ^ (k + 1) ≤ δ := by
  induction K generalizing b with
  | zero =>
    refine ⟨0, by omega, ?_, by simpa using hlast⟩
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hδb hq.le
  | succ K ih =>
    by_cases hfirst : b * q ≤ δ
    · refine ⟨0, by omega, ?_, by simpa using hfirst⟩
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hδb hq.le
    · have hnext : (b * q) * q ^ (K + 1) ≤ δ := by
        convert hlast using 1 <;> ring
      obtain ⟨k, hk, hklo, hkhi⟩ :=
        ih (mul_nonneg hb hq.le) (le_of_not_ge hfirst) hnext
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · convert hklo using 1 <;> ring
      · convert hkhi using 1 <;> ring

theorem geometric_cover_of_width {ε R b δ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hR : 1 ≤ R)
    (hb : 0 ≤ b) (hlo : b / R ≤ δ) (hhi : δ ≤ b) :
    ∃ k : ℕ, k < leastGridSteps (1 - ε) R + 1 ∧
      (1 - ε) * δ ≤ b * (1 - ε) ^ (k + 1) ∧
      b * (1 - ε) ^ (k + 1) ≤ δ := by
  apply shifted_geometric_cover (by linarith) (by linarith) hb hhi
  have hk := leastGridSteps_spec hε hε1 hR
  have hpow : (1 - ε) ^ (leastGridSteps (1 - ε) R + 1) ≤
      (1 - ε) ^ leastGridSteps (1 - ε) R := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by linarith) _) (by linarith)
  calc
    b * (1 - ε) ^ (leastGridSteps (1 - ε) R + 1)
        ≤ b * (1 / R) := mul_le_mul_of_nonneg_left (hpow.trans hk) hb
    _ = b / R := by ring
    _ ≤ δ := hlo

/-- One additional undershoot supplies the strict utility margin needed for an
approximate response oracle. The closed lower inequality also covers endpoint
coincidences, including an optimum at zero agent share. -/
theorem robust_geometric_cover {ρ R b δ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hR : 1 ≤ R)
    (hb : 0 ≤ b) (hlo : b / R ≤ δ) (hhi : δ ≤ b) :
    ∃ k : ℕ, k < leastGridSteps (1 - ρ) R + 1 ∧
      (1 - ρ) ^ 2 * δ ≤ b * (1 - ρ) ^ (k + 2) ∧
      b * (1 - ρ) ^ (k + 2) ≤ (1 - ρ) * δ := by
  obtain ⟨k, hk, hlo, hhi⟩ := geometric_cover_of_width hρ hρ1 hR hb hlo hhi
  have hq : 0 ≤ 1 - ρ := by linarith
  refine ⟨k, hk, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hlo hq
    convert h using 1 <;> ring
  · have h := mul_le_mul_of_nonneg_left hhi hq
    convert h using 1 <;> ring

theorem shifted_contract_valid {q b : ℝ} {k : ℕ}
    (hq : 0 < q) (hq1 : q < 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < 1 - b * q ^ (k + 1) ∧ 1 - b * q ^ (k + 1) ≤ 1 := by
  have hp0 : 0 ≤ q ^ (k + 1) := pow_nonneg hq.le _
  have hp1 : q ^ (k + 1) < 1 := pow_lt_one₀ hq.le hq1 (by omega)
  have hbp : b * q ^ (k + 1) ≤ q ^ (k + 1) :=
    mul_le_of_le_one_left hp0 hb1
  have hbp0 := mul_nonneg hb hp0
  constructor <;> linarith

/-- A directly usable real-valued query bound, prior to specializing the width
as `n²` or `2n²`. -/
theorem leastGridSteps_add_one_bound {ε R : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hR : 1 ≤ R) :
    (leastGridSteps (1 - ε) R + 1 : ℕ) ≤ Real.log R / ε + 2 := by
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR
  have hc := Nat.ceil_lt_add_one (div_nonneg hlog hε.le)
  have hk := leastGridSteps_le_ceil hε hε1 hR
  have hk' : (leastGridSteps (1 - ε) R : ℝ) ≤ ⌈Real.log R / ε⌉₊ :=
    Nat.cast_le.mpr hk
  push_cast
  linarith



/-- The paper's unshifted first crossing, including index zero. -/
theorem unshifted_geometric_cover {q b δ : ℝ} {K : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hδ : 0 ≤ δ)
    (hδb : δ ≤ b) (hlast : b * q ^ K ≤ δ) :
    ∃ k : ℕ, k ≤ K ∧ q * δ ≤ b * q ^ k ∧ b * q ^ k ≤ δ := by
  have he : ∃ k : ℕ, b * q ^ k ≤ δ := ⟨K, hlast⟩
  let k := Nat.find he
  refine ⟨k, Nat.find_min' he hlast, ?_, Nat.find_spec he⟩
  cases hk : k with
  | zero =>
    have hbδ : b ≤ δ := by
      have hf : b * q ^ k ≤ δ := Nat.find_spec he
      simpa [hk] using hf
    have heq : b = δ := le_antisymm hbδ hδb
    rw [pow_zero, mul_one, heq]
    exact mul_le_of_le_one_left hδ hq1
  | succ j =>
    have hj : j < Nat.find he := by change j < k; omega
    have hprev : δ < b * q ^ j := lt_of_not_ge (Nat.find_min he hj)
    have h := mul_le_mul_of_nonneg_left hprev.le hq.le
    convert h using 1 <;> ring


/-- The robustness appendix queries indices zero through `K+1`. -/
theorem robust_source_grid_cover {ρ R b δ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hR : 1 ≤ R)
    (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hlo : b / R ≤ δ) (hhi : δ ≤ b) :
    ∃ k : ℕ, k < leastGridSteps (1 - ρ) R + 2 ∧
      (1 - ρ) ^ 2 * δ ≤ b * (1 - ρ) ^ k ∧
      b * (1 - ρ) ^ k ≤ (1 - ρ) * δ := by
  have hlast : b * (1 - ρ) ^ leastGridSteps (1 - ρ) R ≤ δ := by
    calc
      _ ≤ b * (1 / R) := mul_le_mul_of_nonneg_left
        (leastGridSteps_spec hρ hρ1 hR) hb
      _ = b / R := by ring
      _ ≤ δ := hlo
  obtain ⟨k, hk, hklo, hkhi⟩ := unshifted_geometric_cover
    (by linarith : 0 < 1 - ρ) (by linarith) hδ hhi hlast
  refine ⟨k + 1, by omega, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hklo (by linarith : 0 ≤ 1 - ρ)
    convert h using 1 <;> ring
  · have h := mul_le_mul_of_nonneg_left hkhi (by linarith : 0 ≤ 1 - ρ)
    convert h using 1 <;> ring

/-- A single explicit constant proves representation independence. Both paper
widths `n²` and `2n²` satisfy the logarithmic width hypothesis. -/
theorem logarithmic_query_bound {n : ℕ} {ε R : ℝ}
    (hn : 1 ≤ n) (hε : 0 < ε) (hε1 : ε < 1) (hR : 1 ≤ R)
    (hlogR : Real.log R ≤ 3 * Real.log (n + 1)) :
    (1 + n * (leastGridSteps (1 - ε / 3) R + 2) : ℕ) ≤
      20 * (n : ℝ) * Real.log (n + 1) / ε := by
  have hρ : 0 < ε / 3 := by positivity
  have hρ1 : ε / 3 < 1 := by linarith
  have hk := leastGridSteps_add_one_bound hρ hρ1 hR
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log (n + 1) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ n + 1)
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
  push_cast
  calc
    1 + (n : ℝ) * ((leastGridSteps (1 - ε / 3) R : ℝ) + 2)
        ≤ 1 + n * (15 * Real.log (n + 1) / ε) := by simpa only [Nat.cast_add, Nat.cast_ofNat] using add_le_add_left hm 1
    _ ≤ 20 * n * Real.log (n + 1) / ε := by
      simp only [mul_div_assoc]
      nlinarith



theorem leastGridSteps_mono_base {q q' R : ℝ}
    (hq : 0 ≤ q) (hqq' : q ≤ q') (he' : ∃ k : ℕ, q' ^ k ≤ 1 / R) :
    leastGridSteps q R ≤ leastGridSteps q' R := by
  have he : ∃ k : ℕ, q ^ k ≤ 1 / R := by
    obtain ⟨k, hk⟩ := he'
    exact ⟨k, (pow_le_pow_left₀ hq hqq' k).trans hk⟩
  rw [leastGridSteps, dif_pos he, leastGridSteps, dif_pos he']
  exact Nat.find_min' he ((pow_le_pow_left₀ hq hqq' _).trans (Nat.find_spec he'))

theorem log_double_square_bound {n : ℕ} (hn : 1 ≤ n) :
    Real.log (2 * (n : ℝ) ^ 2) ≤ 3 * Real.log (n + 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hl1 := Real.log_le_log hnp (by linarith : (n : ℝ) ≤ n + 1)
  have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (by linarith : (2 : ℝ) ≤ n + 1)
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hnp.ne'), Real.log_pow]
  norm_num
  linarith

theorem log_square_bound {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) ^ 2) ≤ 3 * Real.log (n + 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  apply le_trans _ (log_double_square_bound hn)
  exact Real.log_le_log (sq_pos_of_pos hnp) (by nlinarith)

end CombinatorialContracts
