import CombinatorialContracts.LowerBoundProgram
import CombinatorialContracts.LowerBoundAsymptotics

/-!
# High-accuracy and exact supply-query lower bounds

All lower bounds below concern executions of the actual adaptive SupplyProgram
oracle language. The hard family, supply simulation, point-query compilation,
contract-only decoder, and randomized identification bound are proved in the
imported modules. Only algorithmic success and ordinary expectation regularity
are hypotheses of the resulting randomized complexity bounds.
-/
namespace CombinatorialContracts.LowerBounds
noncomputable section
open Finset EqualRevenue OracleIdentification MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Decode an original program's real output with no further queries. -/
def identificationProgram (n : ℕ) (program : SupplyProgram (Fin n) ℝ) : PointProgram ℕ ℕ :=
  (compiledPointProgram n program).bind (fun α => .pure (decodeNat n α))

@[simp] theorem identificationProgram_result (n k : ℕ)
    (program : SupplyProgram (Fin n) ℝ) :
    (identificationProgram n program).result (pointOracle k) = decodeNat n (execute n k program).1 := by
  simp [identificationProgram, PointProgram.result, compiledPointProgram_result]

@[simp] theorem identificationProgram_probes (n k : ℕ)
    (program : SupplyProgram (Fin n) ℝ) :
    (identificationProgram n program).probes (pointOracle k) =
      (compiledPointProgram n program).probes (pointOracle k) := by
  simp [identificationProgram, PointProgram.probes]

/-- Indicator of successful high-accuracy output on the actual hidden model. -/
def approximationIndicator (n : ℕ) (program : SupplyProgram (Fin n) ℝ) (k : ℕ) : ℝ :=
  if (1 - accuracy (2 ^ n - 1)) * optimalValue (instanceAt n k) ≤
      principal (instanceAt n k) (execute n k program).1 then 1 else 0

/-- Uniform average over the exponentially many actual hidden instances. -/
def hiddenMean (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ k ∈ hiddenIndices n, f k) / (hiddenIndices n).card

def approximationProbability (n : ℕ) (program : SupplyProgram (Fin n) ℝ) : ℝ :=
  hiddenMean n (approximationIndicator n program)

def expectedSupplyCalls (n : ℕ) (program : SupplyProgram (Fin n) ℝ) : ℝ :=
  hiddenMean n (fun k => ((execute n k program).2.count .response : ℝ))

def expectedValueCalls (n : ℕ) (program : SupplyProgram (Fin n) ℝ) : ℝ :=
  hiddenMean n (fun k => ((execute n k program).2.count .cost : ℝ))

theorem hiddenMean_nonneg (n : ℕ) {f : ℕ → ℝ}
    (hf : ∀ k ∈ hiddenIndices n, 0 ≤ f k) : 0 ≤ hiddenMean n f :=
  div_nonneg (sum_nonneg hf) (Nat.cast_nonneg _)

theorem approximationProbability_nonneg (n : ℕ) (program : SupplyProgram (Fin n) ℝ) :
    0 ≤ approximationProbability n program := by
  apply hiddenMean_nonneg
  intro k hk
  unfold approximationIndicator
  split_ifs <;> norm_num

theorem expectedSupplyCalls_nonneg (n : ℕ) (program : SupplyProgram (Fin n) ℝ) :
    0 ≤ expectedSupplyCalls n program := hiddenMean_nonneg n (fun _ _ => Nat.cast_nonneg _)

theorem expectedValueCalls_nonneg (n : ℕ) (program : SupplyProgram (Fin n) ℝ) :
    0 ≤ expectedValueCalls n program := hiddenMean_nonneg n (fun _ _ => Nat.cast_nonneg _)

theorem approximation_le_identification {n : ℕ} (hn : 2 ≤ n)
    (program : SupplyProgram (Fin n) ℝ) :
    approximationProbability n program ≤ successProbability (hiddenIndices n) (identificationProgram n program) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  unfold approximationIndicator
  split_ifs with hsuccess
  · have hh := decodeNat_correct hn hk hsuccess
    simp only [correct, identificationProgram_result, hh, ↓reduceIte]
    exact le_rfl
  · exact correct_nonneg _ _

theorem identificationProbes_le {n : ℕ} (program : SupplyProgram (Fin n) ℝ) :
    expectedProbes (hiddenIndices n) (identificationProgram n program) ≤
      (4 * (n + 1) ^ 2 : ℕ) * expectedSupplyCalls n program + expectedValueCalls n program := by
  have hh : (∑ k ∈ hiddenIndices n,
      ((identificationProgram n program).probes (pointOracle k) : ℝ)) ≤
      ∑ k ∈ hiddenIndices n,
        (((4 * (n + 1) ^ 2 : ℕ) : ℝ) * ((execute n k program).2.count .response : ℝ) +
          ((execute n k program).2.count .cost : ℝ)) := by
    apply sum_le_sum
    intro k hk
    rw [identificationProgram_probes]
    exact_mod_cast compiledPointProgram_probes_le n k program
  have hd := div_le_div_of_nonneg_right hh (Nat.cast_nonneg (hiddenIndices n).card)
  unfold expectedProbes probeSum expectedSupplyCalls expectedValueCalls hiddenMean
  rw [sum_add_distrib, ← mul_sum] at hd
  convert hd using 1 <;> ring

/-- Quantitative Theorem 8 for each deterministic adaptive program. The final
`+1` rigorously accounts for an unqueried output guess. -/
theorem high_accuracy_query_bound {n : ℕ} (hn : 2 ≤ n)
    (program : SupplyProgram (Fin n) ℝ) :
    (2 : ℝ) ^ (n - 1) * approximationProbability n program ≤
      2 * ((4 * (n + 1) ^ 2 : ℕ) * expectedSupplyCalls n program +
        expectedValueCalls n program) + 1 := by
  have hi := adaptive_identification (hiddenIndices n) (hiddenIndices_nonempty (by omega))
    (identificationProgram n program)
  have hs := approximation_le_identification hn program
  have hq := identificationProbes_le program
  rw [hiddenIndices_card (by omega)] at hi
  push_cast at hi
  have hn0 : (0 : ℝ) ≤ 2 ^ (n - 1) := by positivity
  nlinarith

/-- Arbitrary randomized algorithms, with ordinary finite real expectations.
The result is an expectation over both the independent random seed and a
uniform hidden instance, so some hidden instance attains this lower bound. -/
theorem randomized_high_accuracy_query_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    (program : Ω → SupplyProgram (Fin n) ℝ)
    (hs : Integrable (fun ω => approximationProbability n (program ω)) μ)
    (hQ : Integrable (fun ω => expectedSupplyCalls n (program ω)) μ)
    (hV : Integrable (fun ω => expectedValueCalls n (program ω)) μ) :
    (2 : ℝ) ^ (n - 1) * (∫ ω, approximationProbability n (program ω) ∂μ) ≤
      2 * (((4 * (n + 1) ^ 2 : ℕ) : ℝ) * (∫ ω, expectedSupplyCalls n (program ω) ∂μ) +
        (∫ ω, expectedValueCalls n (program ω) ∂μ)) + 1 := by
  let B : ℝ := (4 * (n + 1) ^ 2 : ℕ)
  have hi := integral_mono (hs.const_mul ((2 : ℝ) ^ (n - 1)))
    (((hQ.const_mul B).add hV).const_mul 2 |>.add (integrable_const (1 : ℝ)))
    (fun ω => high_accuracy_query_bound hn (program ω))
  have hsum : Integrable (fun ω => B * expectedSupplyCalls n (program ω) + expectedValueCalls n (program ω)) μ :=
    (hQ.const_mul B).add hV
  have hsum2 : Integrable (fun ω => 2 * (B * expectedSupplyCalls n (program ω) + expectedValueCalls n (program ω))) μ :=
    hsum.const_mul 2
  simp only [Pi.add_apply] at hi
  rw [integral_add hsum2 (integrable_const (1 : ℝ))] at hi
  simp_rw [integral_const_mul] at hi
  rw [integral_add (hQ.const_mul B) hV, integral_const_mul] at hi
  simpa only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul, B] using hi

/-- Finite random seeds and arbitrary real probabilities, with no analytic
hypotheses at all. -/
theorem finite_randomized_high_accuracy_query_bound {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (hw : ∀ ω, 0 ≤ weight ω) (htotal : ∑ ω, weight ω = 1)
    {n : ℕ} (hn : 2 ≤ n) (program : Ω → SupplyProgram (Fin n) ℝ) :
    (2 : ℝ) ^ (n - 1) * (∑ ω, weight ω * approximationProbability n (program ω)) ≤
      2 * (((4 * (n + 1) ^ 2 : ℕ) : ℝ) * (∑ ω, weight ω * expectedSupplyCalls n (program ω)) +
        (∑ ω, weight ω * expectedValueCalls n (program ω))) + 1 := by
  have hi : (∑ ω, weight ω * ((2 : ℝ) ^ (n - 1) * approximationProbability n (program ω))) ≤
      ∑ ω, weight ω * (2 * (((4 * (n + 1) ^ 2 : ℕ) : ℝ) * expectedSupplyCalls n (program ω) +
        expectedValueCalls n (program ω)) + 1) :=
    sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (high_accuracy_query_bound hn (program ω)) (hw ω))
  calc
    _ = ∑ ω, weight ω * ((2 : ℝ) ^ (n - 1) * approximationProbability n (program ω)) := by
      rw [mul_sum]; apply sum_congr rfl; intro ω _; ring
    _ ≤ _ := hi
    _ = _ := by
      simp only [mul_add, mul_one, sum_add_distrib, htotal]
      repeat rw [mul_sum]
      congr 1
      congr 1 <;> apply sum_congr rfl <;> intro ω _ <;> ring


theorem integrable_hiddenMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ∈ hiddenIndices n, Integrable (f k) μ) :
    Integrable (fun ω => hiddenMean n (fun k => f k ω)) μ :=
  (integrable_finset_sum (hiddenIndices n) hf).div_const _

theorem integral_hiddenMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ∈ hiddenIndices n, Integrable (f k) μ) :
    (∫ ω, hiddenMean n (fun k => f k ω) ∂μ) =
      (∑ k ∈ hiddenIndices n, ∫ ω, f k ω ∂μ) / (hiddenIndices n).card := by
  unfold hiddenMean
  rw [integral_div, integral_finset_sum _ hf]

/-- A success guarantee on every instance implies the uniform-average success
premise used by the decision-tree lower bound. -/
theorem average_success_of_each_instance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n) (δ : ℝ) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ∈ hiddenIndices n, Integrable (f k) μ)
    (hgood : ∀ k ∈ hiddenIndices n, δ ≤ ∫ ω, f k ω ∂μ) :
    δ ≤ ∫ ω, hiddenMean n (fun k => f k ω) ∂μ := by
  rw [integral_hiddenMean μ n hf]
  have hc : (0 : ℝ) < (hiddenIndices n).card := by
    exact_mod_cast (hiddenIndices_nonempty hn).card_pos
  apply (le_div_iff₀ hc).mpr
  calc
    δ * ((hiddenIndices n).card : ℝ) = ∑ k ∈ hiddenIndices n, δ := by simp; ring
    _ ≤ _ := sum_le_sum hgood

/-- Any success event implying the required approximation obeys the same
query lower bound. This lets the exact corollary use its own success event. -/
theorem randomized_query_bound_of_score {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    (program : Ω → SupplyProgram (Fin n) ℝ) (score : Ω → ℝ)
    (hs : Integrable score μ)
    (hscore : ∀ ω, score ω ≤ approximationProbability n (program ω))
    (hQ : Integrable (fun ω => expectedSupplyCalls n (program ω)) μ)
    (hV : Integrable (fun ω => expectedValueCalls n (program ω)) μ) :
    (2 : ℝ) ^ (n - 1) * (∫ ω, score ω ∂μ) ≤
      2 * (((4 * (n + 1) ^ 2 : ℕ) : ℝ) * (∫ ω, expectedSupplyCalls n (program ω) ∂μ) +
        (∫ ω, expectedValueCalls n (program ω) ∂μ)) + 1 := by
  have hpoint ω := le_trans
    (mul_le_mul_of_nonneg_left (hscore ω) (by positivity : (0 : ℝ) ≤ 2 ^ (n - 1)))
    (high_accuracy_query_bound hn (program ω))
  let B : ℝ := (4 * (n + 1) ^ 2 : ℕ)
  have hsum : Integrable (fun ω => B * expectedSupplyCalls n (program ω) + expectedValueCalls n (program ω)) μ :=
    (hQ.const_mul B).add hV
  have hsum2 : Integrable (fun ω => 2 * (B * expectedSupplyCalls n (program ω) + expectedValueCalls n (program ω))) μ :=
    hsum.const_mul 2
  have hi := integral_mono (hs.const_mul ((2 : ℝ) ^ (n - 1)))
    (hsum2.add (integrable_const (1 : ℝ))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add hsum2 (integrable_const (1 : ℝ))] at hi
  simp_rw [integral_const_mul] at hi
  rw [integral_add (hQ.const_mul B) hV, integral_const_mul] at hi
  simpa only [integral_const, measureReal_univ_eq_one, one_smul, B] using hi

private theorem exponential_bound_of_score {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (program : (n : ℕ) → Ω → SupplyProgram (Fin n) ℝ) (score : ℕ → Ω → ℝ)
    (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hs : ∀ n, 2 ≤ n → Integrable (score n) μ)
    (hscore : ∀ n, 2 ≤ n → ∀ ω, score n ω ≤ approximationProbability n (program n ω))
    (hgood : ∀ n, 2 ≤ n → δ ≤ ∫ ω, score n ω ∂μ)
    (hQ : ∀ n, 2 ≤ n → Integrable (fun ω => expectedSupplyCalls n (program n ω)) μ)
    (hV : ∀ n, 2 ≤ n → Integrable (fun ω => expectedValueCalls n (program n ω)) μ)
    (hpoly : ∀ᶠ n : ℕ in Filter.atTop,
      (∫ ω, expectedValueCalls n (program n ω) ∂μ) ≤ C * ((n : ℝ) + 1) ^ d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (3 / 2 : ℝ) ^ n ≤ ∫ ω, expectedSupplyCalls n (program n ω) ∂μ := by
  apply eventually_exponential_supply_lower_bound
    (fun n => ∫ ω, expectedSupplyCalls n (program n ω) ∂μ)
    (fun n => ∫ ω, expectedValueCalls n (program n ω) ∂μ) δ C d hδ ?_ hpoly
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hh := randomized_query_bound_of_score μ hn (program n) (score n)
    (hs n hn) (hscore n hn) (hQ n hn) (hV n hn)
  have hg := mul_le_mul_of_nonneg_left (hgood n hn)
    (by positivity : (0 : ℝ) ≤ 2 ^ (n - 1))
  push_cast at hh
  nlinarith

/-- Theorem 8: constant success on every hard instance, with polynomially
many extra cost-value queries, forces exponentially many expected supply
queries. The explicit base 3/2 is a witness for the stated 2^{Ω(n)} bound.
Randomness is an arbitrary probability space, not a finite list of seeds. -/
theorem theorem8_high_accuracy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (program : (n : ℕ) → Ω → SupplyProgram (Fin n) ℝ)
    (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hs : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      Integrable (fun ω => approximationIndicator n (program n ω) k) μ)
    (hgood : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      δ ≤ ∫ ω, approximationIndicator n (program n ω) k ∂μ)
    (hQ : ∀ n, 2 ≤ n → Integrable (fun ω => expectedSupplyCalls n (program n ω)) μ)
    (hV : ∀ n, 2 ≤ n → Integrable (fun ω => expectedValueCalls n (program n ω)) μ)
    (hpoly : ∀ᶠ n : ℕ in Filter.atTop,
      (∫ ω, expectedValueCalls n (program n ω) ∂μ) ≤ C * ((n : ℝ) + 1) ^ d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (3 / 2 : ℝ) ^ n ≤ ∫ ω, expectedSupplyCalls n (program n ω) ∂μ := by
  apply exponential_bound_of_score μ program
    (fun n ω => approximationProbability n (program n ω)) δ C d hδ
  · intro n hn
    exact integrable_hiddenMean μ n (hs n hn)
  · intro n hn ω; exact le_rfl
  · intro n hn
    exact average_success_of_each_instance μ (by omega) δ (hs n hn) (hgood n hn)
  · exact hQ
  · exact hV
  · exact hpoly

def exactIndicator (n : ℕ) (program : SupplyProgram (Fin n) ℝ) (k : ℕ) : ℝ :=
  if principal (instanceAt n k) (execute n k program).1 = optimalValue (instanceAt n k)
    then 1 else 0

def exactProbability (n : ℕ) (program : SupplyProgram (Fin n) ℝ) : ℝ :=
  hiddenMean n (exactIndicator n program)

theorem exactProbability_le_approximation (n : ℕ) (program : SupplyProgram (Fin n) ℝ) :
    exactProbability n program ≤ approximationProbability n program := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  unfold exactIndicator approximationIndicator
  split_ifs with hopt happ happ
  · exact le_rfl
  · exfalso
    apply happ
    rw [hopt]
    have hg : 0 ≤ accuracy (2 ^ n - 1) := by unfold accuracy; positivity
    have hv := optimalValue_nonneg (instanceAt n k)
    nlinarith
  · norm_num
  · exact le_rfl

/-- The exact lower-bound half of Corollary 3, proved directly for the
restricted nonnegative family rather than postulated from the cited paper. -/
theorem corollary3_exact_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (program : (n : ℕ) → Ω → SupplyProgram (Fin n) ℝ)
    (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hs : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      Integrable (fun ω => exactIndicator n (program n ω) k) μ)
    (hgood : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      δ ≤ ∫ ω, exactIndicator n (program n ω) k ∂μ)
    (hQ : ∀ n, 2 ≤ n → Integrable (fun ω => expectedSupplyCalls n (program n ω)) μ)
    (hV : ∀ n, 2 ≤ n → Integrable (fun ω => expectedValueCalls n (program n ω)) μ)
    (hpoly : ∀ᶠ n : ℕ in Filter.atTop,
      (∫ ω, expectedValueCalls n (program n ω) ∂μ) ≤ C * ((n : ℝ) + 1) ^ d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (3 / 2 : ℝ) ^ n ≤ ∫ ω, expectedSupplyCalls n (program n ω) ∂μ := by
  apply exponential_bound_of_score μ program
    (fun n ω => exactProbability n (program n ω)) δ C d hδ
  · intro n hn
    exact integrable_hiddenMean μ n (hs n hn)
  · intro n hn ω; exact exactProbability_le_approximation n _
  · intro n hn
    exact average_success_of_each_instance μ (by omega) δ (hs n hn) (hgood n hn)
  · exact hQ
  · exact hV
  · exact hpoly


/-- Extended-expectation version of the actual-program lower bound. In
particular, infinite expected supply-query counts are included. -/
theorem randomized_high_accuracy_query_bound_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    (program : Ω → SupplyProgram (Fin n) ℝ)
    (hV : Measurable (fun ω => expectedValueCalls n (program ω))) :
    (2 : ℝ≥0∞) ^ (n - 1) *
        (∫⁻ ω, ENNReal.ofReal (approximationProbability n (program ω)) ∂μ) ≤
      2 * (((4 * (n + 1) ^ 2 : ℕ) : ℝ≥0∞) *
        (∫⁻ ω, ENNReal.ofReal (expectedSupplyCalls n (program ω)) ∂μ) +
        (∫⁻ ω, ENNReal.ofReal (expectedValueCalls n (program ω)) ∂μ)) + 1 := by
  have hpoint (ω : Ω) :
      (2 : ℝ≥0∞) ^ (n - 1) * ENNReal.ofReal (approximationProbability n (program ω)) ≤
      2 * (((4 * (n + 1) ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (expectedSupplyCalls n (program ω)) +
        ENNReal.ofReal (expectedValueCalls n (program ω))) + 1 := by
    have hh := ENNReal.ofReal_le_ofReal (high_accuracy_query_bound hn (program ω))
    have hQ := expectedSupplyCalls_nonneg n (program ω)
    have hV := expectedValueCalls_nonneg n (program ω)
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) hV,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)] at hh
    simpa [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1),
      ENNReal.ofReal_add (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 1)] using hh
  have hh := lintegral_mono (μ := μ) hpoint
  rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ measurable_const] at hh
  rw [lintegral_const_mul' _ _ (by norm_num)] at hh
  rw [lintegral_add_right _ hV.ennreal_ofReal,
    lintegral_const_mul' ((4 * (n + 1) ^ 2 : ℕ) : ℝ≥0∞) _ (ENNReal.natCast_ne_top _)] at hh
  simpa using hh

/-- A finite uniform average has a genuine worst hidden instance. -/
theorem exists_hidden_at_least_mean {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) :
    ∃ k ∈ hiddenIndices n, hiddenMean n f ≤ f k := by
  obtain ⟨k, hk, hmax⟩ := exists_max_image (hiddenIndices n) f (hiddenIndices_nonempty hn)
  refine ⟨k, hk, ?_⟩
  have hc : (0 : ℝ) < (hiddenIndices n).card := by
    exact_mod_cast (hiddenIndices_nonempty hn).card_pos
  apply (div_le_iff₀ hc).mpr
  calc
    ∑ j ∈ hiddenIndices n, f j ≤ ∑ j ∈ hiddenIndices n, f k := sum_le_sum hmax
    _ = f k * ((hiddenIndices n).card : ℝ) := by simp; ring

/-- Distributional lower bounds imply a lower bound on at least one actual
instance; this theorem proves the quantifier conversion explicitly. -/
theorem exists_hidden_expected_supply_ge_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (program : Ω → SupplyProgram (Fin n) ℝ)
    (hQ : ∀ k ∈ hiddenIndices n,
      Integrable (fun ω => ((execute n k (program ω)).2.count .response : ℝ)) μ) :
    ∃ k ∈ hiddenIndices n,
      (∫ ω, expectedSupplyCalls n (program ω) ∂μ) ≤
        ∫ ω, ((execute n k (program ω)).2.count .response : ℝ) ∂μ := by
  have hh := exists_hidden_at_least_mean hn
    (fun k => ∫ ω, ((execute n k (program ω)).2.count .response : ℝ) ∂μ)
  unfold expectedSupplyCalls
  rw [integral_hiddenMean μ n hQ]
  exact hh


private theorem exponential_bound_ennreal_of_score {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (program : (n : ℕ) → Ω → SupplyProgram (Fin n) ℝ) (score : ℕ → Ω → ℝ)
    (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hs : ∀ n, 2 ≤ n → Integrable (score n) μ)
    (hnonneg : ∀ n, 2 ≤ n → ∀ ω, 0 ≤ score n ω)
    (hscore : ∀ n, 2 ≤ n → ∀ ω, score n ω ≤ approximationProbability n (program n ω))
    (hgood : ∀ n, 2 ≤ n → δ ≤ ∫ ω, score n ω ∂μ)
    (hV : ∀ n, 2 ≤ n → Measurable (fun ω => expectedValueCalls n (program n ω)))
    (hpoly : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (expectedValueCalls n (program n ω)) ∂μ) ≤
        ENNReal.ofReal (C * ((n : ℝ) + 1) ^ d)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal ((3 / 2 : ℝ) ^ n) ≤
        ∫⁻ ω, ENNReal.ofReal (expectedSupplyCalls n (program n ω)) ∂μ := by
  apply eventually_exponential_supply_lower_bound_ennreal
    (fun n => ∫⁻ ω, ENNReal.ofReal (expectedSupplyCalls n (program n ω)) ∂μ)
    (fun n => ∫⁻ ω, ENNReal.ofReal (expectedValueCalls n (program n ω)) ∂μ) δ C d hδ ?_ hpoly
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hsuccess : ENNReal.ofReal δ ≤
      ∫⁻ ω, ENNReal.ofReal (approximationProbability n (program n ω)) ∂μ := by
    have hh := ENNReal.ofReal_le_ofReal (hgood n hn)
    rw [ofReal_integral_eq_lintegral_ofReal (hs n hn)
      (Filter.Eventually.of_forall (hnonneg n hn))] at hh
    exact hh.trans (lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hscore n hn ω)))
  have hh := (mul_le_mul_left' hsuccess ((2 : ℝ≥0∞) ^ (n - 1))).trans
    (randomized_high_accuracy_query_bound_lintegral μ hn (program n) (hV n hn))
  have hc : ENNReal.ofReal (8 * ((n : ℝ) + 1) ^ 2) =
      ((8 * (n + 1) ^ 2 : ℕ) : ℝ≥0∞) := by
    convert ENNReal.ofReal_natCast (8 * (n + 1) ^ 2) using 1 <;> push_cast <;> ring
  rw [ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_pow (by norm_num), hc]
  norm_num only [ENNReal.ofReal_ofNat]
  convert hh using 1 <;> push_cast <;> ring

/-- Theorem 8 with extended expectations. No finite expected supply-query
count is assumed; infinite expectations automatically satisfy the conclusion. -/
theorem theorem8_high_accuracy_ennreal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (program : (n : ℕ) → Ω → SupplyProgram (Fin n) ℝ)
    (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hs : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      Integrable (fun ω => approximationIndicator n (program n ω) k) μ)
    (hgood : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      δ ≤ ∫ ω, approximationIndicator n (program n ω) k ∂μ)
    (hV : ∀ n, 2 ≤ n → Measurable (fun ω => expectedValueCalls n (program n ω)))
    (hpoly : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (expectedValueCalls n (program n ω)) ∂μ) ≤
        ENNReal.ofReal (C * ((n : ℝ) + 1) ^ d)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal ((3 / 2 : ℝ) ^ n) ≤
        ∫⁻ ω, ENNReal.ofReal (expectedSupplyCalls n (program n ω)) ∂μ := by
  apply exponential_bound_ennreal_of_score μ program
    (fun n ω => approximationProbability n (program n ω)) δ C d hδ
  · intro n hn; exact integrable_hiddenMean μ n (hs n hn)
  · intro n hn ω; exact approximationProbability_nonneg n _
  · intro n hn ω; exact le_rfl
  · intro n hn
    exact average_success_of_each_instance μ (by omega) δ (hs n hn) (hgood n hn)
  · exact hV
  · exact hpoly

/-- Exact optimization has the same extended-expectation lower bound. -/
theorem corollary3_exact_lower_bound_ennreal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (program : (n : ℕ) → Ω → SupplyProgram (Fin n) ℝ)
    (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hs : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      Integrable (fun ω => exactIndicator n (program n ω) k) μ)
    (hgood : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      δ ≤ ∫ ω, exactIndicator n (program n ω) k ∂μ)
    (hV : ∀ n, 2 ≤ n → Measurable (fun ω => expectedValueCalls n (program n ω)))
    (hpoly : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (expectedValueCalls n (program n ω)) ∂μ) ≤
        ENNReal.ofReal (C * ((n : ℝ) + 1) ^ d)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal ((3 / 2 : ℝ) ^ n) ≤
        ∫⁻ ω, ENNReal.ofReal (expectedSupplyCalls n (program n ω)) ∂μ := by
  apply exponential_bound_ennreal_of_score μ program
    (fun n ω => exactProbability n (program n ω)) δ C d hδ
  · intro n hn; exact integrable_hiddenMean μ n (hs n hn)
  · intro n hn ω
    apply hiddenMean_nonneg
    intro k hk
    unfold exactIndicator
    split_ifs <;> norm_num
  · intro n hn ω; exact exactProbability_le_approximation n _
  · intro n hn
    exact average_success_of_each_instance μ (by omega) δ (hs n hn) (hgood n hn)
  · exact hV
  · exact hpoly


theorem lintegral_hiddenMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (hn : 0 < n) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ∈ hiddenIndices n, Measurable (f k))
    (hfn : ∀ k ∈ hiddenIndices n, ∀ ω, 0 ≤ f k ω) :
    (∫⁻ ω, ENNReal.ofReal (hiddenMean n (fun k => f k ω)) ∂μ) =
      (∑ k ∈ hiddenIndices n, ∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ) /
        ((hiddenIndices n).card : ℝ≥0∞) := by
  have hcard := (hiddenIndices_nonempty hn).card_pos
  have hc : (0 : ℝ) < (hiddenIndices n).card := by exact_mod_cast hcard
  have hc0 : ((hiddenIndices n).card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hcard.ne'
  have he ω : ENNReal.ofReal (hiddenMean n (fun k => f k ω)) =
      ((hiddenIndices n).card : ℝ≥0∞)⁻¹ * ∑ k ∈ hiddenIndices n, ENNReal.ofReal (f k ω) := by
    unfold hiddenMean
    rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_sum_of_nonneg (fun k hk => hfn k hk ω),
      ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [lintegral_congr he, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0),
    lintegral_finset_sum _ (fun k hk => (hf k hk).ennreal_ofReal), div_eq_mul_inv, mul_comm]

/-- The extended worst-instance extraction includes infinite expectations;
only measurability of the actual per-instance query counts is needed. -/
theorem exists_hidden_expected_supply_ge_average_ennreal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (program : Ω → SupplyProgram (Fin n) ℝ)
    (hQ : ∀ k ∈ hiddenIndices n,
      Measurable (fun ω => ((execute n k (program ω)).2.count .response : ℝ))) :
    ∃ k ∈ hiddenIndices n,
      (∫⁻ ω, ENNReal.ofReal (expectedSupplyCalls n (program ω)) ∂μ) ≤
        ∫⁻ ω, ((execute n k (program ω)).2.count .response : ℝ≥0∞) ∂μ := by
  let f (k : ℕ) : ℝ≥0∞ := ∫⁻ ω, ((execute n k (program ω)).2.count .response : ℝ≥0∞) ∂μ
  obtain ⟨k, hk, hmax⟩ := exists_max_image (hiddenIndices n) f (hiddenIndices_nonempty hn)
  refine ⟨k, hk, ?_⟩
  unfold expectedSupplyCalls
  rw [lintegral_hiddenMean μ hn hQ (fun _ _ _ => Nat.cast_nonneg _)]
  simp only [ENNReal.ofReal_natCast]
  have hc0 : ((hiddenIndices n).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (hiddenIndices_nonempty hn).card_pos.ne'
  apply (ENNReal.div_le_iff hc0 (ENNReal.natCast_ne_top _)).mpr
  calc
    ∑ j ∈ hiddenIndices n, f j ≤ ∑ j ∈ hiddenIndices n, f k := sum_le_sum hmax
    _ = f k * ((hiddenIndices n).card : ℝ≥0∞) := by simp [nsmul_eq_mul, mul_comm]

/-- The full worst-instance form of Theorem 8, allowing infinite expected
query counts at arbitrary problem sizes. The returned index belongs to the
concrete additive-reward, monotone-supermodular-cost family. -/
theorem theorem8_worst_instance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (program : (n : ℕ) → Ω → SupplyProgram (Fin n) ℝ)
    (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hs : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      Integrable (fun ω => approximationIndicator n (program n ω) k) μ)
    (hgood : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      δ ≤ ∫ ω, approximationIndicator n (program n ω) k ∂μ)
    (hQ : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      Measurable (fun ω => ((execute n k (program n ω)).2.count .response : ℝ)))
    (hV : ∀ n, 2 ≤ n → Measurable (fun ω => expectedValueCalls n (program n ω)))
    (hpoly : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (expectedValueCalls n (program n ω)) ∂μ) ≤
        ENNReal.ofReal (C * ((n : ℝ) + 1) ^ d)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ k ∈ hiddenIndices n,
      ENNReal.ofReal ((3 / 2 : ℝ) ^ n) ≤
        ∫⁻ ω, ((execute n k (program n ω)).2.count .response : ℝ≥0∞) ∂μ := by
  have hh := theorem8_high_accuracy_ennreal μ program δ C d hδ hs hgood hV hpoly
  filter_upwards [hh, Filter.eventually_ge_atTop 2] with n hn hn2
  obtain ⟨k, hk, hmax⟩ := exists_hidden_expected_supply_ge_average_ennreal μ
    (by omega) (program n) (hQ n hn2)
  exact ⟨k, hk, hn.trans hmax⟩

/-- Corollary 3's exact lower bound, including a worst actual hidden instance
and infinite-expectation algorithms. -/
theorem corollary3_exact_worst_instance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (program : (n : ℕ) → Ω → SupplyProgram (Fin n) ℝ)
    (δ C : ℝ) (d : ℕ) (hδ : 0 < δ)
    (hs : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      Integrable (fun ω => exactIndicator n (program n ω) k) μ)
    (hgood : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      δ ≤ ∫ ω, exactIndicator n (program n ω) k ∂μ)
    (hQ : ∀ n, 2 ≤ n → ∀ k ∈ hiddenIndices n,
      Measurable (fun ω => ((execute n k (program n ω)).2.count .response : ℝ)))
    (hV : ∀ n, 2 ≤ n → Measurable (fun ω => expectedValueCalls n (program n ω)))
    (hpoly : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (expectedValueCalls n (program n ω)) ∂μ) ≤
        ENNReal.ofReal (C * ((n : ℝ) + 1) ^ d)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ k ∈ hiddenIndices n,
      ENNReal.ofReal ((3 / 2 : ℝ) ^ n) ≤
        ∫⁻ ω, ((execute n k (program n ω)).2.count .response : ℝ≥0∞) ∂μ := by
  have hh := corollary3_exact_lower_bound_ennreal μ program δ C d hδ hs hgood hV hpoly
  filter_upwards [hh, Filter.eventually_ge_atTop 2] with n hn hn2
  obtain ⟨k, hk, hmax⟩ := exists_hidden_expected_supply_ge_average_ennreal μ
    (by omega) (program n) (hQ n hn2)
  exact ⟨k, hk, hn.trans hmax⟩

end
end CombinatorialContracts.LowerBounds
