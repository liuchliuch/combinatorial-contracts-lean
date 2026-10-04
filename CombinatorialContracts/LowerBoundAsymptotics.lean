import Mathlib

namespace CombinatorialContracts
open Filter Asymptotics
open scoped ENNReal

/-- Polynomially many auxiliary queries do not absorb an exponential lower
bound. This lemma makes the paper's final exponential asymptotic explicit. -/
theorem polynomial_mul_smaller_exponential (d : ℕ) :
    (fun n : ℕ => ((n : ℝ)+1)^d * (3/2 : ℝ)^n) =o[atTop]
      (fun n : ℕ => (2 : ℝ)^n) := by
  have h := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
    (R := ℝ) d (r₁ := (3/2 : ℝ)) (r₂ := 2) (by norm_num)).comp_tendsto
      (show Tendsto (fun n : ℕ => n+1) atTop atTop from tendsto_add_atTop_nat 1)
  have h' : (fun n : ℕ => (3/2 : ℝ) * (((n : ℝ)+1)^d * (3/2 : ℝ)^n))
      =o[atTop] (fun n : ℕ => 2 * (2 : ℝ)^n) := by
    convert h using 1 <;> ext n <;> simp [pow_succ] <;> ring
  have h'' := h'.const_mul_left (2/3 : ℝ)
  convert h''.of_const_mul_right using 1 <;> ext n <;> ring

theorem shifted_polynomial_littleO (d : ℕ) :
    (fun n : ℕ => ((n : ℝ)+1)^d) =o[atTop] (fun n : ℕ => (2 : ℝ)^n) := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt
    (R := ℝ) d (r := 2) (by norm_num)).comp_tendsto
      (show Tendsto (fun n : ℕ => n+1) atTop atTop from tendsto_add_atTop_nat 1)
  have h' : (fun n : ℕ => ((n : ℝ)+1)^d)
      =o[atTop] (fun n : ℕ => 2 * (2 : ℝ)^n) := by
    simpa [Function.comp_def, pow_succ, mul_comm] using h
  exact h'.of_const_mul_right

theorem eventually_exponential_supply_lower_bound
    (Q V : ℕ → ℝ) (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hqueries : ∀ᶠ n : ℕ in atTop,
      δ * (2 : ℝ)^(n-1) ≤ 8*((n : ℝ)+1)^2*Q n + 2*V n + 1)
    (hpoly : ∀ᶠ n : ℕ in atTop, V n ≤ C*((n : ℝ)+1)^d) :
    ∀ᶠ n : ℕ in atTop, (3/2 : ℝ)^n ≤ Q n := by
  have hsmall : (fun n : ℕ => 8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n) +
      2*C*((n : ℝ)+1)^d + 1) =o[atTop] (fun n : ℕ => (2 : ℝ)^n) := by
    have h1 := (polynomial_mul_smaller_exponential 2).const_mul_left 8
    have h2 := (shifted_polynomial_littleO d).const_mul_left (2*C)
    have h3 := shifted_polynomial_littleO 0
    simpa using (h1.add h2).add h3
  have hbound := hsmall.bound (show 0 < δ/4 by positivity)
  filter_upwards [hqueries, hpoly, hbound, eventually_ge_atTop 1] with n hq hv hb hn
  have hp : 0 < (2 : ℝ)^n := by positivity
  have hc : 0 < ((n : ℝ)+1)^2 := by positivity
  have he : (2 : ℝ)^n = 2 * (2 : ℝ)^(n-1) := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ, mul_comm]
  have hb' : 8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n)+2*C*((n : ℝ)+1)^d+1 ≤
      δ/4*(2 : ℝ)^n := by
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_pos hp] using hb)
  by_contra hnot
  have hlt : Q n < (3/2 : ℝ)^n := lt_of_not_ge hnot
  have hmul := mul_lt_mul_of_pos_left hlt (show 0 < 8*((n : ℝ)+1)^2 by positivity)
  nlinarith

/-- Extended expectations, including infinite expected supply counts. No
conversion of an infinite expectation to a real number is used. -/
theorem eventually_exponential_supply_lower_bound_ennreal
    (Q V : ℕ → ℝ≥0∞) (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hqueries : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (δ*(2 : ℝ)^(n-1)) ≤
        ENNReal.ofReal (8*((n : ℝ)+1)^2)*Q n + 2*V n + 1)
    (hpoly : ∀ᶠ n : ℕ in atTop, V n ≤ ENNReal.ofReal (C*((n : ℝ)+1)^d)) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((3/2 : ℝ)^n) ≤ Q n := by
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hsmall : (fun n : ℕ => 8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n) +
      2*D*((n : ℝ)+1)^d + 1) =o[atTop] (fun n : ℕ => (2 : ℝ)^n) := by
    have h1 := (polynomial_mul_smaller_exponential 2).const_mul_left 8
    have h2 := (shifted_polynomial_littleO d).const_mul_left (2*D)
    have h3 := shifted_polynomial_littleO 0
    simpa using (h1.add h2).add h3
  have hbound := hsmall.bound (show 0 < δ/4 by positivity)
  filter_upwards [hqueries, hpoly, hbound, eventually_ge_atTop 1] with n hq hv hb hn
  by_contra hnot
  have hQ : Q n ≤ ENNReal.ofReal ((3/2 : ℝ)^n) := (lt_of_not_ge hnot).le
  have hV : V n ≤ ENNReal.ofReal (D*((n : ℝ)+1)^d) := by
    apply hv.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hF0 : 0 ≤ 8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n)+2*D*((n : ℝ)+1)^d+1 := by positivity
  have he : ENNReal.ofReal (8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n)+2*D*((n : ℝ)+1)^d+1) =
      ENNReal.ofReal (8*((n : ℝ)+1)^2)*ENNReal.ofReal ((3/2 : ℝ)^n) +
        2*ENNReal.ofReal (D*((n : ℝ)+1)^d)+1 := by
    have hA : ENNReal.ofReal (8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n)) =
        ENNReal.ofReal (8*((n : ℝ)+1)^2)*ENNReal.ofReal ((3/2 : ℝ)^n) := by
      rw [show 8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n) =
        (8*((n : ℝ)+1)^2)*(3/2 : ℝ)^n by ring,
        ENNReal.ofReal_mul (by positivity)]
    have hB : ENNReal.ofReal (2*D*((n : ℝ)+1)^d) =
        2*ENNReal.ofReal (D*((n : ℝ)+1)^d) := by
      rw [show 2*D*((n : ℝ)+1)^d = 2*(D*((n : ℝ)+1)^d) by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), hA, hB]
    norm_num
  have hle : ENNReal.ofReal (δ*(2 : ℝ)^(n-1)) ≤
      ENNReal.ofReal (8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n)+2*D*((n : ℝ)+1)^d+1) := by
    rw [he]
    apply hq.trans
    gcongr
  have hreal := (ENNReal.ofReal_le_ofReal_iff hF0).mp hle
  have hp : 0 < (2 : ℝ)^n := by positivity
  have he2 : (2 : ℝ)^n = 2*(2 : ℝ)^(n-1) := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ, mul_comm]
  have hb' : 8*(((n : ℝ)+1)^2*(3/2 : ℝ)^n)+2*D*((n : ℝ)+1)^d+1 ≤
      δ/4*(2 : ℝ)^n := by
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_pos hp] using hb)
  nlinarith

end CombinatorialContracts
