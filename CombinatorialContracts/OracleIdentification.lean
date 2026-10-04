import Mathlib

/-!
# Adaptive hidden-index identification

A point probe only reveals whether its query is the hidden index.  Programs
below are genuine adaptive decision trees, including both answer branches and
an arbitrary final guess.  The proofs do not assume a fixed list of probes,
successful discovery before output, or a worst-case bound on the random seed.
-/
namespace CombinatorialContracts.OracleIdentification
noncomputable section
open Finset
open scoped ENNReal

/-- A terminating, fully adaptive point-oracle program. -/
inductive PointProgram (κ : Type*) (α : Type*) where
  | pure : α → PointProgram κ α
  | ask : κ → PointProgram κ α → PointProgram κ α → PointProgram κ α

namespace PointProgram
variable {κ α β : Type*}

def result (oracle : κ → Bool) : PointProgram κ α → α
  | .pure x => x
  | .ask q yes no => if oracle q then result oracle yes else result oracle no

def probes (oracle : κ → Bool) : PointProgram κ α → ℕ
  | .pure _ => 0
  | .ask q yes no => 1 + if oracle q then probes oracle yes else probes oracle no

def bind : PointProgram κ α → (α → PointProgram κ β) → PointProgram κ β
  | .pure x, f => f x
  | .ask q yes no, f => .ask q (bind yes f) (bind no f)

@[simp] theorem result_bind (oracle : κ → Bool) (p : PointProgram κ α)
    (f : α → PointProgram κ β) :
    result oracle (bind p f) = result oracle (f (result oracle p)) := by
  induction p with
  | pure x => rfl
  | ask q yes no iy ino => cases h : oracle q <;> simp [bind, result, h, iy, ino]

@[simp] theorem probes_bind (oracle : κ → Bool) (p : PointProgram κ α)
    (f : α → PointProgram κ β) :
    probes oracle (bind p f) = probes oracle p + probes oracle (f (result oracle p)) := by
  induction p with
  | pure x => simp [bind, probes, result]
  | ask q yes no iy ino =>
      cases h : oracle q <;> simp [bind, probes, result, h, iy, ino, Nat.add_assoc]
end PointProgram

variable {κ : Type*} [DecidableEq κ]

def pointOracle (hidden query : κ) : Bool := decide (query = hidden)

def correct (p : PointProgram κ κ) (hidden : κ) : ℝ :=
  if p.result (pointOracle hidden) = hidden then 1 else 0

def successSum (K : Finset κ) (p : PointProgram κ κ) : ℝ := ∑ k ∈ K, correct p k

def probeSum (K : Finset κ) (p : PointProgram κ κ) : ℝ :=
  ∑ k ∈ K, (p.probes (pointOracle k) : ℝ)

theorem correct_nonneg (p : PointProgram κ κ) (k : κ) : 0 ≤ correct p k := by
  unfold correct; split_ifs <;> norm_num

theorem correct_le_one (p : PointProgram κ κ) (k : κ) : correct p k ≤ 1 := by
  unfold correct; split_ifs <;> norm_num

theorem successSum_le_card (K : Finset κ) (p : PointProgram κ κ) :
    successSum K p ≤ K.card := by
  calc
    successSum K p ≤ ∑ _k ∈ K, (1 : ℝ) := sum_le_sum fun k _ => correct_le_one p k
    _ = K.card := by simp

theorem probeSum_nonneg (K : Finset κ) (p : PointProgram κ κ) : 0 ≤ probeSum K p := by
  exact sum_nonneg fun _ _ => Nat.cast_nonneg _

private theorem successSum_pure_le_one (K : Finset κ) (guess : κ) :
    successSum K (.pure guess) ≤ 1 := by
  classical
  simp only [successSum, correct, PointProgram.result]
  calc
    ∑ k ∈ K, (if guess = k then (1 : ℝ) else 0) = if guess ∈ K then 1 else 0 := by
      simp
    _ ≤ 1 := by split_ifs <;> norm_num

private theorem successSum_ask_of_mem (K : Finset κ) (q : κ)
    (yes no : PointProgram κ κ) (hq : q ∈ K) :
    successSum K (.ask q yes no) = correct yes q + successSum (K.erase q) no := by
  rw [successSum, ← sum_erase_add _ _ hq]
  have hsum : (∑ k ∈ K.erase q, correct (.ask q yes no) k) = successSum (K.erase q) no := by
    apply sum_congr rfl
    intro k hk
    have hqk : q ≠ k := Ne.symm (mem_erase.mp hk).1
    simp [correct, PointProgram.result, pointOracle, hqk]
  rw [hsum]
  simp [correct, PointProgram.result, pointOracle, add_comm]

private theorem probeSum_ask_of_mem (K : Finset κ) (q : κ)
    (yes no : PointProgram κ κ) (hq : q ∈ K) :
    probeSum K (.ask q yes no) = K.card +
      (yes.probes (pointOracle q) : ℝ) + probeSum (K.erase q) no := by
  have hstep : probeSum K (.ask q yes no) = (K.card : ℝ) +
      ∑ k ∈ K, (if q = k then (yes.probes (pointOracle k) : ℝ)
          else (no.probes (pointOracle k) : ℝ)) := by
    simp [probeSum, PointProgram.probes, pointOracle, Nat.cast_add, sum_add_distrib]
  rw [hstep, ← sum_erase_add _ _ hq]
  have hsum : (∑ k ∈ K.erase q,
      if q = k then (yes.probes (pointOracle k) : ℝ)
      else (no.probes (pointOracle k) : ℝ)) = probeSum (K.erase q) no := by
    apply sum_congr rfl
    intro k hk
    simp [Ne.symm (mem_erase.mp hk).1]
  rw [hsum]
  simp only [↓reduceIte]
  ring

/-- The main deterministic inequality.  The additive one accounts for a final
unqueried guess.  Query counts are averaged over the actual adaptive paths. -/
theorem adaptive_identification_sum (p : PointProgram κ κ) (K : Finset κ) :
    (K.card : ℝ) * (successSum K p - 1) ≤ 2 * probeSum K p := by
  induction p generalizing K with
  | pure guess =>
      have hs := successSum_pure_le_one K guess
      have hn : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
      simp only [probeSum, PointProgram.probes, Nat.cast_zero, sum_const_zero]
      nlinarith
  | ask q yes no iy ino =>
      by_cases hq : q ∈ K
      · rw [successSum_ask_of_mem K q yes no hq, probeSum_ask_of_mem K q yes no hq]
        have ih := ino (K.erase q)
        have hs := successSum_le_card (K.erase q) no
        have hc := correct_le_one yes q
        have hn : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
        have hp : (0 : ℝ) ≤ yes.probes (pointOracle q) := Nat.cast_nonneg _
        have he : (K.erase q).card + 1 = K.card := card_erase_add_one hq
        have her : ((K.erase q).card : ℝ) + 1 = K.card := by exact_mod_cast he
        nlinarith
      · have hs : successSum K (.ask q yes no) = successSum K no := by
          apply sum_congr rfl
          intro k hk
          have hqk : q ≠ k := by intro he; subst k; exact hq hk
          simp [correct, PointProgram.result, pointOracle, hqk]
        have hp : probeSum K (.ask q yes no) = (K.card : ℝ) + probeSum K no := by
          unfold probeSum
          simp only [PointProgram.probes, Nat.cast_add, Nat.cast_one]
          have hx : (∑ k ∈ K,
              ((if pointOracle k q = true then yes.probes (pointOracle k)
                else no.probes (pointOracle k) : ℕ) : ℝ)) =
              ∑ k ∈ K, (no.probes (pointOracle k) : ℝ) := by
            apply sum_congr rfl
            intro k hk
            have hqk : q ≠ k := by intro he; subst k; exact hq hk
            simp [pointOracle, hqk]
          rw [sum_add_distrib, hx]
          simp
        rw [hs, hp]
        have ih := ino K
        have hn : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
        linarith

/-- Uniform hidden-index success probability for one deterministic seed. -/
def successProbability (K : Finset κ) (p : PointProgram κ κ) : ℝ :=
  successSum K p / K.card

/-- Uniform hidden-index expected probe count for one deterministic seed. -/
def expectedProbes (K : Finset κ) (p : PointProgram κ κ) : ℝ :=
  probeSum K p / K.card

theorem adaptive_identification (K : Finset κ) (hK : K.Nonempty)
    (p : PointProgram κ κ) :
    (K.card : ℝ) * successProbability K p ≤ 2 * expectedProbes K p + 1 := by
  have hc : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  have hh := adaptive_identification_sum p K
  unfold successProbability expectedProbes
  apply (mul_le_mul_iff_left₀ hc).mp
  field_simp
  nlinarith

theorem expectedProbes_nonneg (K : Finset κ) (p : PointProgram κ κ) :
    0 ≤ expectedProbes K p := div_nonneg (probeSum_nonneg K p) (Nat.cast_nonneg _)

/-- Extended expectations also cover random algorithms of infinite expected
query complexity.  No finite-support or finite-expectation restriction is
needed.  For measurable randomized algorithms these are ordinary nonnegative
expectations; the inequality even holds for lower Lebesgue integrals. -/
theorem randomized_identification_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (K : Finset κ) (hK : K.Nonempty) (program : Ω → PointProgram κ κ) :
    (K.card : ℝ≥0∞) * (∫⁻ ω, ENNReal.ofReal (successProbability K (program ω)) ∂μ) ≤
      2 * (∫⁻ ω, ENNReal.ofReal (expectedProbes K (program ω)) ∂μ) + 1 := by
  have hp (ω : Ω) :
      (K.card : ℝ≥0∞) * ENNReal.ofReal (successProbability K (program ω)) ≤
        2 * ENNReal.ofReal (expectedProbes K (program ω)) + 1 := by
    have hh := ENNReal.ofReal_le_ofReal (adaptive_identification K hK (program ω))
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg K.card),
      ENNReal.ofReal_add (mul_nonneg (by norm_num) (expectedProbes_nonneg _ _)) (by norm_num),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
    simpa using hh
  have hh := MeasureTheory.lintegral_mono (μ := μ) hp
  rw [MeasureTheory.lintegral_const_mul' _ _ (by simp),
      MeasureTheory.lintegral_add_right _ measurable_const,
      MeasureTheory.lintegral_const_mul' _ _ (by norm_num)] at hh
  simpa using hh

/-- Randomized algorithms may use an arbitrary probability space of seeds;
the seed is independent of the uniformly distributed hidden index.  The only
analytic hypotheses are existence of the two displayed expectations. -/
theorem randomized_identification {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (K : Finset κ) (hK : K.Nonempty) (program : Ω → PointProgram κ κ)
    (hs : MeasureTheory.Integrable (fun ω => successProbability K (program ω)) μ)
    (hq : MeasureTheory.Integrable (fun ω => expectedProbes K (program ω)) μ) :
    (K.card : ℝ) * (∫ ω, successProbability K (program ω) ∂μ) ≤
      2 * (∫ ω, expectedProbes K (program ω) ∂μ) + 1 := by
  have hh := MeasureTheory.integral_mono (hs.const_mul (K.card : ℝ))
    ((hq.const_mul 2).add (MeasureTheory.integrable_const (1 : ℝ)))
    (fun ω => adaptive_identification K hK (program ω))
  simpa only [Pi.add_apply, MeasureTheory.integral_add (hq.const_mul 2)
      (MeasureTheory.integrable_const (1 : ℝ)), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const, MeasureTheory.measureReal_univ_eq_one, one_smul] using hh

/-- Constant success forces a linear expected number of point probes. -/
theorem randomized_expected_probes_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (K : Finset κ) (hK : K.Nonempty) (program : Ω → PointProgram κ κ)
    (hs : MeasureTheory.Integrable (fun ω => successProbability K (program ω)) μ)
    (hq : MeasureTheory.Integrable (fun ω => expectedProbes K (program ω)) μ)
    (δ : ℝ) (hsuccess : δ ≤ ∫ ω, successProbability K (program ω) ∂μ) :
    ((K.card : ℝ) * δ - 1) / 2 ≤ ∫ ω, expectedProbes K (program ω) ∂μ := by
  have hh := randomized_identification μ K hK program hs hq
  have hn : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
  nlinarith

/-- Elementary finite/discrete randomization, requiring no measure-theoretic
regularity hypotheses.  The probabilities need not be rational or uniform. -/
theorem finite_randomized_identification {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (hw : ∀ ω, 0 ≤ weight ω) (htotal : ∑ ω, weight ω = 1)
    (K : Finset κ) (hK : K.Nonempty) (program : Ω → PointProgram κ κ) :
    (K.card : ℝ) * (∑ ω, weight ω * successProbability K (program ω)) ≤
      2 * (∑ ω, weight ω * expectedProbes K (program ω)) + 1 := by
  have hh : (∑ ω, weight ω * ((K.card : ℝ) * successProbability K (program ω))) ≤
      ∑ ω, weight ω * (2 * expectedProbes K (program ω) + 1) := by
    exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
      (adaptive_identification K hK (program ω)) (hw ω)
  have hl : (∑ ω, weight ω * ((K.card : ℝ) * successProbability K (program ω))) =
      (K.card : ℝ) * (∑ ω, weight ω * successProbability K (program ω)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro ω _
    ring
  have hr : (∑ ω, weight ω * (2 * expectedProbes K (program ω) + 1)) =
      2 * (∑ ω, weight ω * expectedProbes K (program ω)) + 1 := by
    simp only [mul_add, mul_one, sum_add_distrib, htotal]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro ω _
    ring
  rwa [hl, hr] at hh

/-- Test a finite batch by actual sequential adaptive point probes.  Stopping
after the first hit is allowed, and can only reduce the query count. -/
def pointBatch : List κ → PointProgram κ (Option κ)
  | [] => .pure none
  | q :: qs => .ask q (.pure (some q)) (pointBatch qs)

def batchAnswer (queries : List κ) (hidden : κ) : Option κ :=
  if hidden ∈ queries then some hidden else none

@[simp] theorem pointBatch_result (queries : List κ) (hidden : κ) :
    (pointBatch queries).result (pointOracle hidden) = batchAnswer queries hidden := by
  induction queries with
  | nil => simp [pointBatch, PointProgram.result, batchAnswer]
  | cons q qs ih =>
      by_cases hq : q = hidden
      · subst q; simp [pointBatch, PointProgram.result, pointOracle, batchAnswer]
      · simp [pointBatch, PointProgram.result, pointOracle, hq, ih, batchAnswer, Ne.symm hq]

theorem pointBatch_probes (queries : List κ) (hidden : κ) :
    (pointBatch queries).probes (pointOracle hidden) ≤ queries.length := by
  induction queries with
  | nil => simp [pointBatch, PointProgram.probes]
  | cons q qs ih =>
      by_cases hq : q = hidden
      · simp [pointBatch, PointProgram.probes, pointOracle, hq]
      · simp [pointBatch, PointProgram.probes, pointOracle, hq]
        omega

/-- A genuine adaptive program for compound queries.  Each query label may
represent a supply call or a cost-value call; its finite candidate batch is
known from the public, unperturbed instance. -/
inductive BatchProgram (Q : Type*) (κ : Type*) (α : Type*) where
  | pure : α → BatchProgram Q κ α
  | ask : Q → (Option κ → BatchProgram Q κ α) → BatchProgram Q κ α

namespace BatchProgram
variable {Q α β : Type*}

def result (candidates : Q → List κ) (hidden : κ) : BatchProgram Q κ α → α
  | .pure x => x
  | .ask q next => result candidates hidden (next (batchAnswer (candidates q) hidden))

/-- Sum of charges on the actual answer-dependent path. -/
def callCost (weight : Q → ℕ) (candidates : Q → List κ) (hidden : κ) :
    BatchProgram Q κ α → ℕ
  | .pure _ => 0
  | .ask q next => weight q + callCost weight candidates hidden
      (next (batchAnswer (candidates q) hidden))

/-- Every adaptive compound program is compiled, not assumed equivalent, to
an adaptive point-query program. -/
def compile (candidates : Q → List κ) : BatchProgram Q κ α → PointProgram κ α
  | .pure x => .pure x
  | .ask q next => (pointBatch (candidates q)).bind (fun a => compile candidates (next a))

@[simp] theorem compile_result (candidates : Q → List κ) (hidden : κ)
    (p : BatchProgram Q κ α) :
    (compile candidates p).result (pointOracle hidden) = result candidates hidden p := by
  induction p with
  | pure x => rfl
  | ask q next ih => simp [compile, PointProgram.result_bind, pointBatch_result, ih, result]

theorem compile_probes_le (candidates : Q → List κ) (hidden : κ)
    (weight : Q → ℕ) (bound : ∀ q, (candidates q).length ≤ weight q)
    (p : BatchProgram Q κ α) :
    (compile candidates p).probes (pointOracle hidden) ≤ callCost weight candidates hidden p := by
  induction p with
  | pure x => simp [compile, PointProgram.probes, callCost]
  | ask q next ih =>
      simp only [compile, PointProgram.probes_bind, pointBatch_result, callCost]
      exact Nat.add_le_add ((pointBatch_probes _ _).trans (bound q)) (ih _)

/-- Change the output, including decoding a returned contract into its hidden
index, without making additional oracle calls. -/
def map (f : α → β) : BatchProgram Q κ α → BatchProgram Q κ β
  | .pure x => .pure (f x)
  | .ask q next => .ask q (fun a => map f (next a))

@[simp] theorem result_map (f : α → β) (candidates : Q → List κ) (hidden : κ)
    (p : BatchProgram Q κ α) :
    result candidates hidden (map f p) = f (result candidates hidden p) := by
  induction p with
  | pure x => rfl
  | ask q next ih => simp [map, result, ih]

@[simp] theorem callCost_map (f : α → β) (weight : Q → ℕ)
    (candidates : Q → List κ) (hidden : κ) (p : BatchProgram Q κ α) :
    callCost weight candidates hidden (map f p) = callCost weight candidates hidden p := by
  induction p with
  | pure x => rfl
  | ask q next ih => simp [map, callCost, ih]

@[simp] theorem callCost_add (w v : Q → ℕ) (candidates : Q → List κ)
    (hidden : κ) (p : BatchProgram Q κ α) :
    callCost (fun q => w q + v q) candidates hidden p =
      callCost w candidates hidden p + callCost v candidates hidden p := by
  induction p with
  | pure x => simp [callCost]
  | ask q next ih => simp [callCost, ih]; omega

@[simp] theorem callCost_mul (c : ℕ) (w : Q → ℕ) (candidates : Q → List κ)
    (hidden : κ) (p : BatchProgram Q κ α) :
    callCost (fun q => c * w q) candidates hidden p =
      c * callCost w candidates hidden p := by
  induction p with
  | pure x => simp [callCost]
  | ask q next ih => simp [callCost, ih, Nat.mul_add]

/-- If supply calls use at most B candidates and the other calls use at most
one, the compiled execution costs at most B times the number of supply calls,
plus the number of additional value calls, on every adaptive path. -/
theorem compile_supply_probes_le (candidates : Q → List κ) (hidden : κ)
    (isSupply : Q → Bool) (B : ℕ)
    (bound : ∀ q, (candidates q).length ≤ if isSupply q then B else 1)
    (p : BatchProgram Q κ α) :
    (compile candidates p).probes (pointOracle hidden) ≤
      B * callCost (fun q => if isSupply q then 1 else 0) candidates hidden p +
        callCost (fun q => if isSupply q then 0 else 1) candidates hidden p := by
  have hh := compile_probes_le candidates hidden (fun q => if isSupply q then B else 1) bound p
  have hw : (fun q => if isSupply q then B else 1) =
      (fun q => B * (if isSupply q then 1 else 0) + (if isSupply q then 0 else 1)) := by
    funext q
    cases isSupply q <;> simp
  rw [hw, callCost_add, callCost_mul] at hh
  exact hh

/-- Probability of identifying a uniformly drawn hidden index using the
compound program, including its final unqueried guess. -/
def successProbability (K : Finset κ) (candidates : Q → List κ)
    (p : BatchProgram Q κ κ) : ℝ :=
  OracleIdentification.successProbability K (compile candidates p)

/-- Expected charge on the actual adaptive path under a uniform hidden index. -/
def expectedCost (K : Finset κ) (weight : Q → ℕ) (candidates : Q → List κ)
    (p : BatchProgram Q κ α) : ℝ :=
  (∑ k ∈ K, (callCost weight candidates k p : ℝ)) / K.card

@[simp] theorem successProbability_eq (K : Finset κ) (candidates : Q → List κ)
    (p : BatchProgram Q κ κ) :
    successProbability K candidates p =
      (∑ k ∈ K, if result candidates k p = k then (1 : ℝ) else 0) / K.card := by
  simp [successProbability, OracleIdentification.successProbability, successSum, correct]

theorem expectedCost_nonneg (K : Finset κ) (weight : Q → ℕ)
    (candidates : Q → List κ) (p : BatchProgram Q κ α) :
    0 ≤ expectedCost K weight candidates p := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem compile_expectedProbes_le (K : Finset κ) (candidates : Q → List κ)
    (weight : Q → ℕ) (bound : ∀ q, (candidates q).length ≤ weight q)
    (p : BatchProgram Q κ κ) :
    expectedProbes K (compile candidates p) ≤ expectedCost K weight candidates p := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k _
  exact_mod_cast compile_probes_le candidates k weight bound p

/-- Compound queries inherit the search lower bound from their compiled
point-query implementation, with proved overhead rather than an assumed
identification lower bound. -/
theorem identification (K : Finset κ) (hK : K.Nonempty) (candidates : Q → List κ)
    (weight : Q → ℕ) (bound : ∀ q, (candidates q).length ≤ weight q)
    (p : BatchProgram Q κ κ) :
    (K.card : ℝ) * successProbability K candidates p ≤
      2 * expectedCost K weight candidates p + 1 := by
  have hi := adaptive_identification K hK (compile candidates p)
  have hc := compile_expectedProbes_le K candidates weight bound p
  unfold successProbability
  linarith

@[simp] theorem expectedCost_map (K : Finset κ) (f : α → β) (weight : Q → ℕ)
    (candidates : Q → List κ) (p : BatchProgram Q κ α) :
    expectedCost K weight candidates (map f p) = expectedCost K weight candidates p := by
  simp [expectedCost]

@[simp] theorem expectedCost_add (K : Finset κ) (w v : Q → ℕ)
    (candidates : Q → List κ) (p : BatchProgram Q κ α) :
    expectedCost K (fun q => w q + v q) candidates p =
      expectedCost K w candidates p + expectedCost K v candidates p := by
  simp only [expectedCost, callCost_add, Nat.cast_add, sum_add_distrib, add_div]

@[simp] theorem expectedCost_mul (K : Finset κ) (c : ℕ) (w : Q → ℕ)
    (candidates : Q → List κ) (p : BatchProgram Q κ α) :
    expectedCost K (fun q => c * w q) candidates p =
      (c : ℝ) * expectedCost K w candidates p := by
  simp only [expectedCost, callCost_mul, Nat.cast_mul, ← mul_sum]
  ring

/-- Decompose supply simulation cost into bounded-cost supply calls and
one-probe value calls, keeping the true answer-dependent call counts. -/
theorem expectedCost_supply (K : Finset κ) (candidates : Q → List κ)
    (isSupply : Q → Bool) (B : ℕ) (p : BatchProgram Q κ α) :
    expectedCost K (fun q => if isSupply q then B else 1) candidates p =
      (B : ℝ) * expectedCost K (fun q => if isSupply q then 1 else 0) candidates p +
        expectedCost K (fun q => if isSupply q then 0 else 1) candidates p := by
  have he : (fun q => if isSupply q then B else 1) =
      (fun q => B * (if isSupply q then 1 else 0) + (if isSupply q then 0 else 1)) := by
    funext q
    cases isSupply q <;> simp
  rw [he, expectedCost_add, expectedCost_mul]

/-- Real-valued expectation form for arbitrary probability-space seeds. -/
theorem randomized_identification {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (K : Finset κ) (hK : K.Nonempty) (candidates : Q → List κ)
    (weight : Q → ℕ) (bound : ∀ q, (candidates q).length ≤ weight q)
    (program : Ω → BatchProgram Q κ κ)
    (hs : MeasureTheory.Integrable (fun ω => successProbability K candidates (program ω)) μ)
    (hq : MeasureTheory.Integrable (fun ω => expectedCost K weight candidates (program ω)) μ) :
    (K.card : ℝ) * (∫ ω, successProbability K candidates (program ω) ∂μ) ≤
      2 * (∫ ω, expectedCost K weight candidates (program ω) ∂μ) + 1 := by
  have hh := MeasureTheory.integral_mono (hs.const_mul (K.card : ℝ))
    ((hq.const_mul 2).add (MeasureTheory.integrable_const (1 : ℝ)))
    (fun ω => identification K hK candidates weight bound (program ω))
  simpa only [Pi.add_apply, MeasureTheory.integral_add (hq.const_mul 2)
      (MeasureTheory.integrable_const (1 : ℝ)), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const, MeasureTheory.measureReal_univ_eq_one, one_smul] using hh

/-- The supply-query lower bound for arbitrary randomized seeds, expressed as
an exact finite-expectation inequality.  The additional value-query budget
can be any bound, including a polynomial in the instance size. -/
theorem randomized_supply_identification {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (K : Finset κ) (hK : K.Nonempty) (candidates : Q → List κ)
    (isSupply : Q → Bool) (B : ℕ)
    (bound : ∀ q, (candidates q).length ≤ if isSupply q then B else 1)
    (program : Ω → BatchProgram Q κ κ)
    (hs : MeasureTheory.Integrable (fun ω => successProbability K candidates (program ω)) μ)
    (hq : MeasureTheory.Integrable (fun ω => expectedCost K
      (fun q => if isSupply q then 1 else 0) candidates (program ω)) μ)
    (hv : MeasureTheory.Integrable (fun ω => expectedCost K
      (fun q => if isSupply q then 0 else 1) candidates (program ω)) μ) :
    (K.card : ℝ) * (∫ ω, successProbability K candidates (program ω) ∂μ) ≤
      2 * ((B : ℝ) * (∫ ω, expectedCost K
          (fun q => if isSupply q then 1 else 0) candidates (program ω) ∂μ) +
        (∫ ω, expectedCost K
          (fun q => if isSupply q then 0 else 1) candidates (program ω) ∂μ)) + 1 := by
  have hc : MeasureTheory.Integrable (fun ω => expectedCost K
      (fun q => if isSupply q then B else 1) candidates (program ω)) μ := by
    simpa only [expectedCost_supply K candidates isSupply B] using (hq.const_mul (B : ℝ)).add hv
  have hh := randomized_identification μ K hK candidates
    (fun q => if isSupply q then B else 1) bound program hs hc
  simpa only [expectedCost_supply K candidates isSupply B, MeasureTheory.integral_add (hq.const_mul (B : ℝ)) hv,
    MeasureTheory.integral_const_mul] using hh

/-- Arbitrary probability spaces and arbitrary expected compound-query cost,
including infinity.  The program can adapt every query and stopping decision
to all previous answers. -/
theorem randomized_identification_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (K : Finset κ) (hK : K.Nonempty) (candidates : Q → List κ)
    (weight : Q → ℕ) (bound : ∀ q, (candidates q).length ≤ weight q)
    (program : Ω → BatchProgram Q κ κ) :
    (K.card : ℝ≥0∞) *
        (∫⁻ ω, ENNReal.ofReal (successProbability K candidates (program ω)) ∂μ) ≤
      2 * (∫⁻ ω, ENNReal.ofReal (expectedCost K weight candidates (program ω)) ∂μ) + 1 := by
  have hp (ω : Ω) :
      (K.card : ℝ≥0∞) * ENNReal.ofReal (successProbability K candidates (program ω)) ≤
        2 * ENNReal.ofReal (expectedCost K weight candidates (program ω)) + 1 := by
    have hh := ENNReal.ofReal_le_ofReal (identification K hK candidates weight bound (program ω))
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg K.card),
      ENNReal.ofReal_add (mul_nonneg (by norm_num) (expectedCost_nonneg _ _ _ _)) (by norm_num),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
    simpa using hh
  have hh := MeasureTheory.lintegral_mono (μ := μ) hp
  rw [MeasureTheory.lintegral_const_mul' _ _ (by simp),
      MeasureTheory.lintegral_add_right _ measurable_const,
      MeasureTheory.lintegral_const_mul' _ _ (by norm_num)] at hh
  simpa using hh

theorem finite_randomized_identification {Ω : Type*} [Fintype Ω]
    (prob : Ω → ℝ) (hw : ∀ ω, 0 ≤ prob ω) (htotal : ∑ ω, prob ω = 1)
    (K : Finset κ) (hK : K.Nonempty) (candidates : Q → List κ)
    (weight : Q → ℕ) (bound : ∀ q, (candidates q).length ≤ weight q)
    (program : Ω → BatchProgram Q κ κ) :
    (K.card : ℝ) * (∑ ω, prob ω * successProbability K candidates (program ω)) ≤
      2 * (∑ ω, prob ω * expectedCost K weight candidates (program ω)) + 1 := by
  have hi := OracleIdentification.finite_randomized_identification prob hw htotal
    K hK (fun ω => compile candidates (program ω))
  have hc : (∑ ω, prob ω * expectedProbes K (compile candidates (program ω))) ≤
      ∑ ω, prob ω * expectedCost K weight candidates (program ω) := by
    exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
      (compile_expectedProbes_le K candidates weight bound (program ω)) (hw ω)
  unfold successProbability
  linarith

/-- Explicit supply/value-query tradeoff.  In the lower-bound family B is
quadratic in n and the additional value-call expectation may be polynomial.
This conclusion remains valid with arbitrary finite real seed probabilities. -/
theorem finite_randomized_supply_identification {Ω : Type*} [Fintype Ω]
    (prob : Ω → ℝ) (hw : ∀ ω, 0 ≤ prob ω) (htotal : ∑ ω, prob ω = 1)
    (K : Finset κ) (hK : K.Nonempty) (candidates : Q → List κ)
    (isSupply : Q → Bool) (B : ℕ)
    (bound : ∀ q, (candidates q).length ≤ if isSupply q then B else 1)
    (program : Ω → BatchProgram Q κ κ) :
    (K.card : ℝ) * (∑ ω, prob ω * successProbability K candidates (program ω)) ≤
      2 * ((B : ℝ) * (∑ ω, prob ω * expectedCost K
          (fun q => if isSupply q then 1 else 0) candidates (program ω)) +
        (∑ ω, prob ω * expectedCost K
          (fun q => if isSupply q then 0 else 1) candidates (program ω))) + 1 := by
  have hh := finite_randomized_identification prob hw htotal K hK candidates
    (fun q => if isSupply q then B else 1) bound program
  have he : (fun q => if isSupply q then B else 1) =
      (fun q => B * (if isSupply q then 1 else 0) + (if isSupply q then 0 else 1)) := by
    funext q
    cases isSupply q <;> simp
  rw [he] at hh
  simp only [expectedCost_add, expectedCost_mul, mul_add, sum_add_distrib] at hh
  have hm : (∑ ω, prob ω * ((B : ℝ) * expectedCost K
      (fun q => if isSupply q then 1 else 0) candidates (program ω))) =
      (B : ℝ) * (∑ ω, prob ω * expectedCost K
      (fun q => if isSupply q then 1 else 0) candidates (program ω)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro ω _
    ring
  rw [hm] at hh
  nlinarith

end BatchProgram

end
end CombinatorialContracts.OracleIdentification
