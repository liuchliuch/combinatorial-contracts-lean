import CombinatorialContracts.Algorithm

namespace CombinatorialContracts

/-- Observable oracle-call kinds. Real arithmetic, comparisons, and local sums
are free in the exact-real query model, as stipulated by the source paper. -/
inductive QueryKind where
  | response | reward | cost
  deriving DecidableEq, Repr

/-- A finite oracle program. A node issues exactly one query before branching
on its answer. Queries cannot be duplicated by reusing a recorded answer. -/
inductive OracleProgram (ι : Type*) (α : Type*) where
  | pure : α → OracleProgram ι α
  | response : ℝ → (Finset ι → OracleProgram ι α) → OracleProgram ι α
  | reward : Finset ι → (ℝ → OracleProgram ι α) → OracleProgram ι α
  | cost : Finset ι → (ℝ → OracleProgram ι α) → OracleProgram ι α

namespace OracleProgram
variable {ι α β : Type*}

def bind : OracleProgram ι α → (α → OracleProgram ι β) → OracleProgram ι β
  | .pure x, f => f x
  | .response a k, f => .response a (fun s => bind (k s) f)
  | .reward s k, f => .reward s (fun v => bind (k v) f)
  | .cost s k, f => .cost s (fun v => bind (k v) f)

/-- Execute a program and retain the actual chronological call-kind trace. -/
def eval (oracle : ℝ → Finset ι) (value costValue : Finset ι → ℝ) :
    OracleProgram ι α → α × List QueryKind
  | .pure x => (x, [])
  | .response a k =>
    let result := eval oracle value costValue (k (oracle a))
    (result.1, QueryKind.response :: result.2)
  | .reward s k =>
    let result := eval oracle value costValue (k (value s))
    (result.1, QueryKind.reward :: result.2)
  | .cost s k =>
    let result := eval oracle value costValue (k (costValue s))
    (result.1, QueryKind.cost :: result.2)

theorem eval_bind (oracle : ℝ → Finset ι) (value costValue : Finset ι → ℝ)
    (p : OracleProgram ι α) (f : α → OracleProgram ι β) :
    eval oracle value costValue (bind p f) =
      let first := eval oracle value costValue p
      let second := eval oracle value costValue (f first.1)
      (second.1, first.2 ++ second.2) := by
  induction p with
  | pure x => rfl
  | response a k ih => simp [bind, eval, ih]
  | reward s k ih => simp [bind, eval, ih]
  | cost s k ih => simp [bind, eval, ih]

/-- One response followed by one reward-value query on its stored answer. -/
def queryRecord (a : ℝ) : OracleProgram ι (QueryRecord ι) :=
  .response a (fun s => .reward s (fun v => .pure ⟨a,s,v⟩))

@[simp] theorem eval_queryRecord (oracle : ℝ → Finset ι)
    (value costValue : Finset ι → ℝ) (a : ℝ) :
    eval oracle value costValue (queryRecord a) =
      (QueryRecord.query oracle value a, [.response, .reward]) := rfl

def queryRecords : List ℝ → OracleProgram ι (List (QueryRecord ι))
  | [] => .pure []
  | a :: as => bind (queryRecord a) (fun r =>
      bind (queryRecords as) (fun rs => .pure (r :: rs)))

def recordTrace : List ℝ → List QueryKind
  | [] => []
  | _ :: as => .response :: .reward :: recordTrace as

theorem eval_queryRecords (oracle : ℝ → Finset ι) (value costValue : Finset ι → ℝ)
    (as : List ℝ) :
    eval oracle value costValue (queryRecords as) =
      (as.map (QueryRecord.query oracle value), recordTrace as) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [queryRecords, eval_bind, ih, eval, recordTrace]

@[simp] theorem recordTrace_response (as : List ℝ) :
    (recordTrace as).count .response = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [recordTrace, ih]

@[simp] theorem recordTrace_reward (as : List ℝ) :
    (recordTrace as).count .reward = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [recordTrace, ih]

@[simp] theorem recordTrace_cost (as : List ℝ) :
    (recordTrace as).count .cost = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [recordTrace, ih]

def readSingletons [DecidableEq ι] : List ι → OracleProgram ι (List ℝ)
  | [] => .pure []
  | i :: is => .reward {i} (fun a => bind (readSingletons is)
      (fun as => .pure (a :: as)))

theorem eval_readSingletons [DecidableEq ι] (oracle : ℝ → Finset ι)
    (value costValue : Finset ι → ℝ) (is : List ι) :
    eval oracle value costValue (readSingletons is) =
      (is.map (fun i => value {i}), List.replicate is.length .reward) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [readSingletons, eval, eval_bind, ih, List.replicate_succ]

/-- Welfare query, one cost query, then the actual finite geometric schedule. -/
noncomputable def geometricProgram (anchors : List ℝ) (q : ℝ) (K offset : ℕ) :
    OracleProgram ι (OracleRun ι) :=
  bind (queryRecord 1) (fun initial =>
    .cost initial.response (fun c =>
      if initial.reward - c = 0 then .pure ⟨initial, []⟩ else
        bind (queryRecords (gridShares anchors (initial.reward-c) q K offset))
          (fun records => .pure ⟨initial, records⟩)))

noncomputable def geometricTrace (anchors : List ℝ) (oracle : ℝ → Finset ι)
    (value costValue : Finset ι → ℝ) (q : ℝ) (K offset : ℕ) : List QueryKind :=
  [.response, .reward, .cost] ++
    if value (oracle 1) - costValue (oracle 1) = 0 then [] else
      recordTrace (gridShares anchors (value (oracle 1)-costValue (oracle 1)) q K offset)

theorem eval_geometricProgram (anchors : List ℝ) (oracle : ℝ → Finset ι)
    (value costValue : Finset ι → ℝ) (q : ℝ) (K offset : ℕ) :
    eval oracle value costValue (geometricProgram anchors q K offset) =
      (geometricRun anchors oracle value costValue q K offset,
        geometricTrace anchors oracle value costValue q K offset) := by
  simp only [geometricProgram, eval_bind, eval_queryRecord]
  simp [eval, eval_bind, eval_queryRecords, geometricRun, geometricTrace, QueryRecord.query]
  split <;> simp [eval_bind, eval_queryRecords, eval]

/-- Algorithm 1 as a finite, value-dependent oracle-query program. -/
noncomputable def algorithm1Program [Fintype ι] [DecidableEq ι] (ε : ℝ) :
    OracleProgram ι (OracleRun ι) :=
  bind (readSingletons Finset.univ.toList) (fun anchors =>
    geometricProgram anchors (1-ε)
      (leastGridSteps (1-ε) ((Fintype.card ι : ℝ)^2)) 1)

theorem eval_algorithm1Program [Fintype ι] [DecidableEq ι]
    (oracle : ℝ → Finset ι) (value costValue : Finset ι → ℝ) (ε : ℝ) :
    (eval oracle value costValue (algorithm1Program ε)).1 =
      algorithm1 oracle value costValue ε := by
  simp [algorithm1Program, eval_bind, eval_readSingletons, eval_geometricProgram, algorithm1]

/-- The counts attached to the mathematical run equal the counts of actual
query nodes executed by the finite program, including singleton reads. -/
theorem algorithm1Program_counts [Fintype ι] [DecidableEq ι]
    (oracle : ℝ → Finset ι) (value costValue : Finset ι → ℝ) (ε : ℝ) :
    let executed := eval oracle value costValue (algorithm1Program ε)
    executed.2.count .response = executed.1.responseQueries ∧
    executed.2.count .reward = executed.1.rewardQueries ∧
    executed.2.count .cost = executed.1.costQueries := by
  simp only [algorithm1Program, eval_bind, eval_readSingletons, eval_geometricProgram]
  simp [geometricTrace, geometricRun, OracleRun.responseQueries, OracleRun.rewardQueries,
    OracleRun.costQueries, QueryRecord.query]
  split <;> simp [recordTrace_response, recordTrace_reward, recordTrace_cost, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc, List.count_replicate]

/-- Read every singleton into an explicit locally stored lookup table. -/
noncomputable def readTable [DecidableEq ι] : List ι → OracleProgram ι (ι → ℝ)
  | [] => .pure (fun _ => 0)
  | i :: is => .reward {i} (fun a => bind (readTable is)
      (fun tail => .pure (fun j => if j = i then a else tail j)))

noncomputable def tableValues [DecidableEq ι] (value : Finset ι → ℝ) :
    List ι → ι → ℝ
  | [], _ => 0
  | i :: is, j => if j = i then value {i} else tableValues value is j

theorem eval_readTable [DecidableEq ι] (oracle : ℝ → Finset ι)
    (value costValue : Finset ι → ℝ) (is : List ι) :
    eval oracle value costValue (readTable is) =
      (tableValues value is, List.replicate is.length .reward) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [readTable, eval, eval_bind, ih, tableValues, List.replicate_succ]

theorem tableValues_of_mem [DecidableEq ι] (value : Finset ι → ℝ)
    {is : List ι} {i : ι} (hi : i ∈ is) : tableValues value is i = value {i} := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
    simp only [tableValues]
    split
    · next h => subst i; rfl
    · next h => exact ih (by simpa [List.mem_cons, h] using hi)

/-- A supply/response query whose reward is computed locally from the cache. -/
noncomputable def cachedRecord [DecidableEq ι] (a : ι → ℝ) (α : ℝ) :
    OracleProgram ι (QueryRecord ι) :=
  .response α (fun S => .pure ⟨α,S,∑ i ∈ S, a i⟩)

@[simp] theorem eval_cachedRecord [DecidableEq ι] (a : ι → ℝ)
    (oracle : ℝ → Finset ι) (value costValue : Finset ι → ℝ) (α : ℝ) :
    eval oracle value costValue (cachedRecord a α) =
      (QueryRecord.query oracle (fun S => ∑ i ∈ S, a i) α, [.response]) := rfl

noncomputable def cachedRecords [DecidableEq ι] (a : ι → ℝ) :
    List ℝ → OracleProgram ι (List (QueryRecord ι))
  | [] => .pure []
  | α :: αs => bind (cachedRecord a α) (fun r =>
      bind (cachedRecords a αs) (fun rs => .pure (r :: rs)))

theorem eval_cachedRecords [DecidableEq ι] (a : ι → ℝ)
    (oracle : ℝ → Finset ι) (value costValue : Finset ι → ℝ) (as : List ℝ) :
    eval oracle value costValue (cachedRecords a as) =
      (as.map (QueryRecord.query oracle (fun S => ∑ i ∈ S, a i)),
        List.replicate as.length .response) := by
  induction as with
  | nil => rfl
  | cons α as ih => simp [cachedRecords, eval_bind, ih, eval, List.replicate_succ]

noncomputable def cachedGeometricProgram [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ε : ℝ) : OracleProgram ι (OracleRun ι) :=
  bind (cachedRecord a 1) (fun initial =>
    .cost initial.response (fun c =>
      if initial.reward-c = 0 then .pure ⟨initial,[]⟩ else
        bind (cachedRecords a (gridShares (Finset.univ.toList.map a)
          (initial.reward-c) (1-ε) (leastGridSteps (1-ε) ((Fintype.card ι : ℝ)^2)) 1))
          (fun records => .pure ⟨initial,records⟩)))

/-- Cached additive implementation: n reward queries up front, then no more. -/
noncomputable def additiveProgram [Fintype ι] [DecidableEq ι] (ε : ℝ) :
    OracleProgram ι (OracleRun ι) :=
  bind (readTable Finset.univ.toList) (fun a => cachedGeometricProgram a ε)

noncomputable def cachedTrace [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (oracle : ℝ → Finset ι) (costValue : Finset ι → ℝ) (ε : ℝ) : List QueryKind :=
  [.response, .cost] ++
    if (∑ i ∈ oracle 1, a i) - costValue (oracle 1) = 0 then [] else
      List.replicate (gridShares (Finset.univ.toList.map a)
        ((∑ i ∈ oracle 1, a i)-costValue (oracle 1)) (1-ε)
        (leastGridSteps (1-ε) ((Fintype.card ι : ℝ)^2)) 1).length .response

theorem eval_cachedGeometricProgram [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (oracle : ℝ → Finset ι) (value costValue : Finset ι → ℝ) (ε : ℝ) :
    eval oracle value costValue (cachedGeometricProgram a ε) =
      (geometricRun (Finset.univ.toList.map a) oracle (fun S => ∑ i ∈ S, a i)
        costValue (1-ε) (leastGridSteps (1-ε) ((Fintype.card ι : ℝ)^2)) 1,
        cachedTrace a oracle costValue ε) := by
  simp only [cachedGeometricProgram, eval_bind, eval_cachedRecord]
  simp [eval, geometricRun, cachedTrace, QueryRecord.query]
  split <;> simp [eval_bind, eval_cachedRecords, eval]

theorem tableValues_univ [Fintype ι] [DecidableEq ι] (value : Finset ι → ℝ) :
    tableValues value Finset.univ.toList = fun i => value {i} := by
  funext i
  exact tableValues_of_mem value (by simp)

theorem cachedTrace_counts [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (oracle : ℝ → Finset ι) (costValue : Finset ι → ℝ) (ε : ℝ) :
    let run := geometricRun (Finset.univ.toList.map a) oracle (fun S => ∑ i ∈ S, a i)
      costValue (1-ε) (leastGridSteps (1-ε) ((Fintype.card ι : ℝ)^2)) 1
    let trace := cachedTrace a oracle costValue ε
    trace.count .response = run.responseQueries ∧
    trace.count .reward = 0 ∧ trace.count .cost = 1 := by
  simp [cachedTrace, geometricRun, OracleRun.responseQueries, QueryRecord.query]
  split <;> simp [List.count_replicate, Nat.add_comm]

end OracleProgram
end CombinatorialContracts
