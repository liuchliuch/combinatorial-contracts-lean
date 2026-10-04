import CombinatorialContracts.LowerBoundProgram

/-!
# From operational strategies to finite oracle programs

A history-dependent strategy need not terminate on arbitrary oracle histories.
Termination only on the finite public hidden-instance family suffices: taking
a maximum of the actual termination times produces a finite unrolling with
exactly the same outputs and query traces on that family.  Thus the program
lower bound does not impose a uniform off-family termination requirement.
-/
namespace CombinatorialContracts.LowerBounds
noncomputable section
open Finset EqualRevenue
attribute [local instance] Classical.propDecidable

/-- Complete observations include both the query and its answer. -/
inductive StrategyObservation (ι : Type*) where
  | supply : (ι → ℝ) → Finset ι → StrategyObservation ι
  | reward : Finset ι → ℝ → StrategyObservation ι
  | cost : Finset ι → ℝ → StrategyObservation ι

/-- An unrestricted next-action rule, with no global termination condition. -/
inductive StrategyAction (ι α : Type*) where
  | halt : α → StrategyAction ι α
  | supply : (ι → ℝ) → StrategyAction ι α
  | reward : Finset ι → StrategyAction ι α
  | cost : Finset ι → StrategyAction ι α

abbrev HistoryStrategy (ι α : Type*) := List (StrategyObservation ι) → StrategyAction ι α

/-- Fuel is used only for finite observation of the operational strategy.
The history is newest-first; the returned trace is execution-order. -/
def runStrategyFuel {ι α : Type*} (strategy : HistoryStrategy ι α)
    (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ) :
    ℕ → List (StrategyObservation ι) → Option (α × List QueryKind)
  | 0, _ => none
  | fuel+1, history =>
      match strategy history with
      | .halt x => some (x, [])
      | .supply p =>
          (runStrategyFuel strategy supply value costValue fuel
            (.supply p (supply p) :: history)).map (fun r => (r.1, .response :: r.2))
      | .reward S =>
          (runStrategyFuel strategy supply value costValue fuel
            (.reward S (value S) :: history)).map (fun r => (r.1, .reward :: r.2))
      | .cost S =>
          (runStrategyFuel strategy supply value costValue fuel
            (.cost S (costValue S) :: history)).map (fun r => (r.1, .cost :: r.2))

/-- An actual terminating run, independently of any chosen fuel bound. -/
def StrategyTerminatesWith {ι α : Type*} (strategy : HistoryStrategy ι α)
    (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ)
    (history : List (StrategyObservation ι)) (result : α × List QueryKind) : Prop :=
  ∃ fuel, runStrategyFuel strategy supply value costValue fuel history = some result

/-- Once the strategy halts, increasing observation fuel changes nothing. -/
theorem runStrategyFuel_add {ι α : Type*} (strategy : HistoryStrategy ι α)
    (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ)
    {fuel : ℕ} {history : List (StrategyObservation ι)} {result : α × List QueryKind}
    (h : runStrategyFuel strategy supply value costValue fuel history = some result) (extra : ℕ) :
    runStrategyFuel strategy supply value costValue (fuel+extra) history = some result := by
  induction fuel generalizing history result with
  | zero => simp [runStrategyFuel] at h
  | succ fuel ih =>
      rw [show fuel+1+extra = (fuel+extra)+1 by omega]
      cases hs : strategy history with
      | halt x => simpa [runStrategyFuel, hs] using h
      | supply p =>
          simp only [runStrategyFuel, hs] at h ⊢
          obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
          rw [ih hr]
          simpa using he
      | reward S =>
          simp only [runStrategyFuel, hs] at h ⊢
          obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
          rw [ih hr]
          simpa using he
      | cost S =>
          simp only [runStrategyFuel, hs] at h ⊢
          obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
          rw [ih hr]
          simpa using he

theorem runStrategyFuel_mono {ι α : Type*} (strategy : HistoryStrategy ι α)
    (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ)
    {fuel cap : ℕ} (hcap : fuel ≤ cap) {history : List (StrategyObservation ι)}
    {result : α × List QueryKind}
    (h : runStrategyFuel strategy supply value costValue fuel history = some result) :
    runStrategyFuel strategy supply value costValue cap history = some result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hcap
  exact runStrategyFuel_add strategy supply value costValue h extra

theorem StrategyTerminatesWith.unique {ι α : Type*} {strategy : HistoryStrategy ι α}
    {supply : (ι → ℝ) → Finset ι} {value costValue : Finset ι → ℝ}
    {history : List (StrategyObservation ι)} {r s : α × List QueryKind}
    (hr : StrategyTerminatesWith strategy supply value costValue history r)
    (hs : StrategyTerminatesWith strategy supply value costValue history s) : r = s := by
  obtain ⟨f, hf⟩ := hr
  obtain ⟨g, hg⟩ := hs
  have hf' := runStrategyFuel_mono strategy supply value costValue (Nat.le_max_left f g) hf
  have hg' := runStrategyFuel_mono strategy supply value costValue (Nat.le_max_right f g) hg
  exact Option.some.inj (hf'.symm.trans hg')

/-- Finite unrolling truncates only paths that have not halted by the cap.
Its syntax is structurally terminating even when the original strategy is not. -/
def unrollStrategy {ι α : Type*} (strategy : HistoryStrategy ι α) (fallback : α) :
    ℕ → List (StrategyObservation ι) → SupplyProgram ι α
  | 0, _ => .pure fallback
  | fuel+1, history =>
      match strategy history with
      | .halt x => .pure x
      | .supply p => .supply p (fun S =>
          unrollStrategy strategy fallback fuel (.supply p S :: history))
      | .reward S => .reward S (fun v =>
          unrollStrategy strategy fallback fuel (.reward S v :: history))
      | .cost S => .cost S (fun v =>
          unrollStrategy strategy fallback fuel (.cost S v :: history))

/-- Any run that halts within the unrolling cap has exactly the same output
and full query trace in the finite program. -/
theorem unrollStrategy_exact {ι α : Type*} (strategy : HistoryStrategy ι α) (fallback : α)
    (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ)
    {fuel : ℕ} {history : List (StrategyObservation ι)} {result : α × List QueryKind}
    (h : runStrategyFuel strategy supply value costValue fuel history = some result) :
    SupplyProgram.eval supply value costValue (unrollStrategy strategy fallback fuel history) =
      result := by
  induction fuel generalizing history result with
  | zero => simp [runStrategyFuel] at h
  | succ fuel ih =>
      cases hs : strategy history with
      | halt x =>
          simpa [runStrategyFuel, hs, unrollStrategy, SupplyProgram.eval] using h
      | supply p =>
          simp only [runStrategyFuel, hs] at h
          obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
          simpa only [unrollStrategy, hs, SupplyProgram.eval, ih hr] using he
      | reward S =>
          simp only [runStrategyFuel, hs] at h
          obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
          simpa only [unrollStrategy, hs, SupplyProgram.eval, ih hr] using he
      | cost S =>
          simp only [runStrategyFuel, hs] at h
          obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
          simpa only [unrollStrategy, hs, SupplyProgram.eval, ih hr] using he

/-- Finite-family compactness for operational algorithms. Only actual runs
on `K` must terminate. No uniform cap or off-family termination is assumed. -/
theorem exists_finite_program_of_termination {ι α κ : Type*} [DecidableEq κ]
    (strategy : HistoryStrategy ι α) (fallback : α) (K : Finset κ)
    (supply : κ → (ι → ℝ) → Finset ι)
    (value costValue : κ → Finset ι → ℝ)
    (hterm : ∀ k ∈ K, ∃ result,
      StrategyTerminatesWith strategy (supply k) (value k) (costValue k) [] result) :
    ∃ program : SupplyProgram ι α, ∀ k ∈ K, ∀ result,
      StrategyTerminatesWith strategy (supply k) (value k) (costValue k) [] result →
      SupplyProgram.eval (supply k) (value k) (costValue k) program = result := by
  have htime : ∀ k ∈ K, ∃ fuel, ∃ result,
      runStrategyFuel strategy (supply k) (value k) (costValue k) fuel [] = some result := by
    intro k hk
    obtain ⟨result, fuel, hf⟩ := hterm k hk
    exact ⟨fuel, result, hf⟩
  let time : κ → ℕ := fun k => if hk : k ∈ K then Classical.choose (htime k hk) else 0
  let cap := K.sup time
  refine ⟨unrollStrategy strategy fallback cap [], ?_⟩
  intro k hk result hresult
  have ht : ∃ r, runStrategyFuel strategy (supply k) (value k) (costValue k) (time k) [] = some r := by
    simpa [time, hk] using Classical.choose_spec (htime k hk)
  obtain ⟨r, hr⟩ := ht
  have hcap : time k ≤ cap := Finset.le_sup hk
  have hrun := runStrategyFuel_mono strategy (supply k) (value k) (costValue k) hcap hr
  have heq : r = result := StrategyTerminatesWith.unique ⟨time k, hr⟩ hresult
  exact (unrollStrategy_exact strategy fallback (supply k) (value k) (costValue k) hrun).trans heq

/-- The actual hidden-family termination relation used by the lower bound. -/
def HiddenStrategyTerminatesWith {α : Type*} (n k : ℕ)
    (strategy : HistoryStrategy (Fin n) α) (result : α × List QueryKind) : Prop :=
  StrategyTerminatesWith strategy (supplyOracle n k) (fun S => binaryIndex S)
    (fun S => perturbedCost k (perturbation (2^n-1)) (binaryIndex S)) [] result

/-- Every operational algorithm terminating on each actual hidden instance
has an exact finite-program representative on the complete lower-bound family. -/
theorem exists_supplyProgram_of_hidden_termination {α : Type*} (n : ℕ)
    (strategy : HistoryStrategy (Fin n) α) (fallback : α)
    (hterm : ∀ k ∈ hiddenIndices n, ∃ result, HiddenStrategyTerminatesWith n k strategy result) :
    ∃ program : SupplyProgram (Fin n) α, ∀ k ∈ hiddenIndices n, ∀ result,
      HiddenStrategyTerminatesWith n k strategy result → execute n k program = result :=
  exists_finite_program_of_termination strategy fallback (hiddenIndices n)
    (supplyOracle n) (fun _ S => binaryIndex S)
    (fun k S => perturbedCost k (perturbation (2^n-1)) (binaryIndex S)) hterm


/-- A canonical representative can be selected independently for every
random seed; it uses a fallback only when the actual-family termination
condition fails. This selection makes no assumption on off-family histories. -/
def finiteStrategyProgram {α : Type*} (n : ℕ)
    (strategy : HistoryStrategy (Fin n) α) (fallback : α) : SupplyProgram (Fin n) α :=
  if hterm : ∀ k ∈ hiddenIndices n, ∃ result, HiddenStrategyTerminatesWith n k strategy result
  then Classical.choose (exists_supplyProgram_of_hidden_termination n strategy fallback hterm)
  else .pure fallback

theorem finiteStrategyProgram_exact {α : Type*} (n : ℕ)
    (strategy : HistoryStrategy (Fin n) α) (fallback : α)
    (hterm : ∀ k ∈ hiddenIndices n, ∃ result, HiddenStrategyTerminatesWith n k strategy result)
    {k : ℕ} (hk : k ∈ hiddenIndices n) {result : α × List QueryKind}
    (hr : HiddenStrategyTerminatesWith n k strategy result) :
    execute n k (finiteStrategyProgram n strategy fallback) = result := by
  rw [finiteStrategyProgram, dif_pos hterm]
  exact Classical.choose_spec (exists_supplyProgram_of_hidden_termination n strategy fallback hterm)
    k hk result hr

/-- Seed-by-seed representation introduces no uniform bound over seeds.
Each strategy's cap may differ, and every actual output and trace is preserved. -/
theorem randomized_strategy_program_exact {Ω α : Type*} (n : ℕ)
    (strategy : Ω → HistoryStrategy (Fin n) α) (fallback : α)
    (ω : Ω)
    (hterm : ∀ k ∈ hiddenIndices n, ∃ result, HiddenStrategyTerminatesWith n k (strategy ω) result)
    {k : ℕ} (hk : k ∈ hiddenIndices n) {result : α × List QueryKind}
    (hr : HiddenStrategyTerminatesWith n k (strategy ω) result) :
    execute n k (finiteStrategyProgram n (strategy ω) fallback) = result :=
  finiteStrategyProgram_exact n (strategy ω) fallback hterm hk hr

end
end CombinatorialContracts.LowerBounds
