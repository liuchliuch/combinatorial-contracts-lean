import CombinatorialContracts.OracleProgram

namespace CombinatorialContracts

/-- Supply programs send actual price vectors; singleton values are read into
a cache before any such vector is constructed. -/
inductive SupplyProgram (ι : Type*) (α : Type*) where
  | pure : α → SupplyProgram ι α
  | supply : (ι → ℝ) → (Finset ι → SupplyProgram ι α) → SupplyProgram ι α
  | reward : Finset ι → (ℝ → SupplyProgram ι α) → SupplyProgram ι α
  | cost : Finset ι → (ℝ → SupplyProgram ι α) → SupplyProgram ι α

namespace SupplyProgram
variable {ι α β : Type*}

def bind : SupplyProgram ι α → (α → SupplyProgram ι β) → SupplyProgram ι β
  | .pure x, f => f x
  | .supply p k, f => .supply p (fun s => bind (k s) f)
  | .reward s k, f => .reward s (fun v => bind (k v) f)
  | .cost s k, f => .cost s (fun v => bind (k v) f)

/-- The response trace tag counts supply calls in this interpreter. -/
def eval (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ) :
    SupplyProgram ι α → α × List QueryKind
  | .pure x => (x, [])
  | .supply p k =>
    let result := eval supply value costValue (k (supply p))
    (result.1, QueryKind.response :: result.2)
  | .reward s k =>
    let result := eval supply value costValue (k (value s))
    (result.1, QueryKind.reward :: result.2)
  | .cost s k =>
    let result := eval supply value costValue (k (costValue s))
    (result.1, QueryKind.cost :: result.2)

theorem eval_bind (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ)
    (p : SupplyProgram ι α) (f : α → SupplyProgram ι β) :
    eval supply value costValue (bind p f) =
      let first := eval supply value costValue p
      let second := eval supply value costValue (f first.1)
      (second.1, first.2 ++ second.2) := by
  induction p with
  | pure x => rfl
  | supply p k ih => simp [bind, eval, ih]
  | reward s k ih => simp [bind, eval, ih]
  | cost s k ih => simp [bind, eval, ih]

/-- Compile response calls into the stated vector-price supply calls. -/
def translate (prices : ℝ → ι → ℝ) : OracleProgram ι α → SupplyProgram ι α
  | .pure x => .pure x
  | .response a k => .supply (prices a) (fun S => translate prices (k S))
  | .reward S k => .reward S (fun v => translate prices (k v))
  | .cost S k => .cost S (fun v => translate prices (k v))

theorem eval_translate (prices : ℝ → ι → ℝ) (supply : (ι → ℝ) → Finset ι)
    (value costValue : Finset ι → ℝ) (p : OracleProgram ι α) :
    eval supply value costValue (translate prices p) =
      OracleProgram.eval (fun a => supply (prices a)) value costValue p := by
  induction p with
  | pure x => rfl
  | response a k ih => simp [translate, eval, OracleProgram.eval, ih]
  | reward S k ih => simp [translate, eval, OracleProgram.eval, ih]
  | cost S k ih => simp [translate, eval, OracleProgram.eval, ih]

/-- The fully operational additive algorithm. The prefix reads n singleton
values. Each subsequent price vector uses only the resulting cached table. -/
noncomputable def algorithm [Fintype ι] [DecidableEq ι] (ε : ℝ) :
    SupplyProgram ι (OracleRun ι) :=
  bind (translate (fun _ _ => 0) (OracleProgram.readTable Finset.univ.toList))
    (fun a => translate (fun α i => α * a i) (OracleProgram.cachedGeometricProgram a ε))

theorem eval_algorithm [Fintype ι] [DecidableEq ι]
    (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ) (ε : ℝ) :
    eval supply value costValue (algorithm ε) =
      (additiveAlgorithm1 (fun i => value {i}) supply costValue ε,
        List.replicate (Fintype.card ι) .reward ++
          OracleProgram.cachedTrace (fun i => value {i})
            (fun α => supply (fun i => α * value {i})) costValue ε) := by
  simp [algorithm, eval_bind, eval_translate, OracleProgram.eval_readTable,
    OracleProgram.tableValues_univ, OracleProgram.eval_cachedGeometricProgram,
    additiveAlgorithm1]

theorem algorithm_counts [Fintype ι] [DecidableEq ι]
    (supply : (ι → ℝ) → Finset ι) (value costValue : Finset ι → ℝ) (ε : ℝ) :
    let executed := eval supply value costValue (algorithm ε)
    executed.2.count .response = executed.1.responseQueries ∧
    executed.2.count .reward = Fintype.card ι ∧
    executed.2.count .cost = 1 := by
  rw [eval_algorithm]
  have hc := OracleProgram.cachedTrace_counts (fun i => value {i})
    (fun α => supply (fun i => α * value {i})) costValue ε
  simpa [List.count_append, List.count_replicate, additiveAlgorithm1] using hc

/-- Source Theorem 1's approximation guarantee for the executed supply program. -/
theorem algorithm_approximation [Fintype ι] [DecidableEq ι]
    (M : Model ι) (hadd : HasAdditiveReward M)
    (supply : (ι → ℝ) → Finset ι)
    (hsupply : ∀ p, (∀ i, 0 ≤ p i) → IsSupplyResponse M p (supply p))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (1-ε)*optimalValue M ≤
      (eval supply M.reward M.cost (algorithm ε)).1.output.utility := by
  rw [eval_algorithm]
  exact additiveAlgorithm1_approximation M hadd supply hsupply hε hε1

end SupplyProgram
end CombinatorialContracts
