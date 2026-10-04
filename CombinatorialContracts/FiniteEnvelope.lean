import Mathlib

open scoped BigOperators

namespace CombinatorialContracts.FiniteEnvelope

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The utility of one member of a finite family of affine lines. -/
def line (r c : ι → ℝ) (x : ℝ) (i : ι) : ℝ := x * r i - c i

/-- An active line attains the upper envelope. -/
def IsActive (r c : ι → ℝ) (x : ℝ) (i : ι) : Prop :=
  ∀ j, line r c x j ≤ line r c x i

noncomputable def envelope (r c : ι → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (line r c x)

lemma exists_active (r c : ι → ℝ) (x : ℝ) : ∃ i, IsActive r c x i := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (line r c x) Finset.univ_nonempty
  exact ⟨i, fun j => hmax j (Finset.mem_univ j)⟩

lemma active_eq_envelope (r c : ι → ℝ) (x : ℝ) (i : ι)
    (hi : IsActive r c x i) : line r c x i = envelope r c x := by
  classical
  apply le_antisymm
  · exact Finset.le_sup' (line r c x) (Finset.mem_univ i)
  · exact Finset.sup'_le _ _ (fun j _ => hi j)

/-- All pairwise intersections, clipped to the interval of interest, together with its ends. -/
noncomputable def breakpoints (r c : ι → ℝ) : Finset ℝ := by
  classical
  exact insert 0 (insert 1 (((Finset.univ : Finset (ι × ι)).image
    (fun ij => (c ij.1 - c ij.2) / (r ij.1 - r ij.2))).filter
      (fun x => 0 ≤ x ∧ x ≤ 1)))

omit [Nonempty ι] in
lemma zero_mem_breakpoints (r c : ι → ℝ) : 0 ∈ breakpoints r c := by
  classical
  simp [breakpoints]

omit [Nonempty ι] in
lemma one_mem_breakpoints (r c : ι → ℝ) : 1 ∈ breakpoints r c := by
  classical
  simp [breakpoints]

omit [Nonempty ι] in
lemma mem_breakpoints_bounds (r c : ι → ℝ) {x : ℝ} (hx : x ∈ breakpoints r c) :
    0 ≤ x ∧ x ≤ 1 := by
  classical
  simp only [breakpoints, Finset.mem_insert, Finset.mem_filter] at hx
  rcases hx with rfl | rfl | ⟨_, hx⟩
  · norm_num
  · norm_num
  · exact hx

omit [Nonempty ι] in
lemma intersection_mem_breakpoints (r c : ι → ℝ) {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1)
    {i j : ι} (hne : r i ≠ r j) (heq : line r c x i = line r c x j) :
    x ∈ breakpoints r c := by
  classical
  have hden : r i - r j ≠ 0 := sub_ne_zero.mpr hne
  have hxq : x = (c i - c j) / (r i - r j) := by
    apply (eq_div_iff hden).mpr
    dsimp [line] at heq
    nlinarith
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨?_, hx⟩
  apply Finset.mem_image.mpr
  exact ⟨(i,j), Finset.mem_univ _, hxq.symm⟩

omit [Nonempty ι] in
/-- If there is no intersection in an open interval, a line active at its midpoint is
active on the whole closed interval. Endpoints may have ties. -/
lemma active_on_gap (r c : ι → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a < b) (hgap : ∀ x, a < x → x < b → x ∉ breakpoints r c)
    {i : ι} (hi : IsActive r c ((a+b)/2) i) :
    ∀ x ∈ Set.Icc a b, IsActive r c x i := by
  have ham : a < (a+b)/2 := by linarith
  have hmb : (a+b)/2 < b := by linarith
  have endpoint : IsActive r c a i ∧ IsActive r c b i := by
    constructor
    · intro j
      by_contra h
      have hj : line r c a i < line r c a j := lt_of_not_ge h
      let d : ℝ → ℝ := fun x => line r c x i - line r c x j
      have hd : Continuous d := by unfold d line; fun_prop
      obtain ⟨z, hz, heq⟩ := intermediate_value_Icc (le_of_lt ham) hd.continuousOn
        (show 0 ∈ Set.Icc (d a) (d ((a+b)/2)) by
          dsimp [d]; exact ⟨sub_nonpos.mpr hj.le, sub_nonneg.mpr (hi j)⟩)
      have hza : a < z := by
        have hza' := hz.1
        apply lt_of_le_of_ne hza'
        intro he
        subst z
        dsimp [d] at heq
        linarith
      have hzb : z < b := lt_of_le_of_lt hz.2 hmb
      apply hgap z hza hzb
      apply intersection_mem_breakpoints r c (i := i) (j := j) ⟨by linarith, by linarith⟩
      · intro hr
        dsimp [d, line] at heq hj
        rw [hr] at heq hj
        linarith
      · dsimp [d] at heq
        exact sub_eq_zero.mp heq
    · intro j
      by_contra h
      have hj : line r c b i < line r c b j := lt_of_not_ge h
      let d : ℝ → ℝ := fun x => line r c x i - line r c x j
      have hd : Continuous d := by unfold d line; fun_prop
      obtain ⟨z, hz, heq⟩ := intermediate_value_Icc' (le_of_lt hmb) hd.continuousOn
        (show 0 ∈ Set.Icc (d b) (d ((a+b)/2)) by
          dsimp [d]; exact ⟨sub_nonpos.mpr hj.le, sub_nonneg.mpr (hi j)⟩)
      have hza : a < z := lt_of_lt_of_le ham hz.1
      have hzb : z < b := by
        apply lt_of_le_of_ne hz.2
        intro he
        subst z
        dsimp [d] at heq
        linarith
      apply hgap z hza hzb
      apply intersection_mem_breakpoints r c (i := i) (j := j) ⟨by linarith, by linarith⟩
      · intro hr
        dsimp [d, line] at heq hj
        rw [hr] at heq hj
        linarith
      · dsimp [d] at heq
        exact sub_eq_zero.mp heq
  intro x hx j
  have ha' := endpoint.1 j
  have hb' := endpoint.2 j
  dsimp [line] at ha' hb' ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hb'),
    mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr ha')]

/-- Enumerate a finite subdivision of `[0,1]` in increasing order. -/
lemma exists_grid (B : Finset ℝ) (hzero : 0 ∈ B) (hone : 1 ∈ B)
    (hbound : ∀ x ∈ B, 0 ≤ x ∧ x ≤ 1) :
    ∃ (k : ℕ) (a : ℕ → ℝ), 0 < k ∧ a 0 = 0 ∧ a k = 1 ∧
      (∀ t < k, a t < a (t+1)) ∧
      (∀ t ≤ k, 0 ≤ a t ∧ a t ≤ 1) ∧
      (∀ t < k, ∀ x, a t < x → x < a (t+1) → x ∉ B) := by
  classical
  have htwo : 2 ≤ B.card := by
    have hsub : ({0, 1} : Finset ℝ) ⊆ B := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hh := Finset.card_le_card hsub
    norm_num at hh
    exact hh
  let k := B.card - 1
  have hk : 0 < k := by dsimp [k]; omega
  have hcard : k + 1 = B.card := by dsimp [k]; omega
  let e : Fin B.card ↪o ℝ := B.orderEmbOfFin rfl
  let a : ℕ → ℝ := fun t => if ht : t < B.card then e ⟨t, ht⟩ else 1
  have hea (t : ℕ) (ht : t ≤ k) : a t = e ⟨t, by omega⟩ := by
    dsimp [a]
    rw [dif_pos (show t < B.card by omega)]
  have hemem (t : Fin B.card) : e t ∈ B := B.orderEmbOfFin_mem rfl t
  have hesurj (x : ℝ) (hx : x ∈ B) : ∃ t : Fin B.card, e t = x := by
    have hr : x ∈ Set.range e := by
      rw [show Set.range e = (B : Set ℝ) from B.range_orderEmbOfFin rfl]
      exact hx
    exact hr
  have habound (t : ℕ) (ht : t ≤ k) : 0 ≤ a t ∧ a t ≤ 1 := by
    rw [hea t ht]
    exact hbound _ (hemem _)
  refine ⟨k, a, hk, ?_, ?_, ?_, habound, ?_⟩
  · apply le_antisymm _ (habound 0 (by omega)).1
    obtain ⟨j, hj⟩ := hesurj 0 hzero
    rw [hea 0 (by omega), ← hj]
    apply e.monotone
    change 0 ≤ j.val
    omega
  · apply le_antisymm (habound k le_rfl).2
    obtain ⟨j, hj⟩ := hesurj 1 hone
    rw [hea k le_rfl, ← hj]
    apply e.monotone
    change j.val ≤ k
    have := j.isLt
    omega
  · intro t ht
    rw [hea t (by omega), hea (t+1) (by omega)]
    apply e.strictMono
    change t < t + 1
    omega
  · intro t ht x hax hxa hx
    obtain ⟨j, rfl⟩ := hesurj x hx
    rw [hea t (by omega)] at hax
    rw [hea (t+1) (by omega)] at hxa
    have h₁ := e.lt_iff_lt.mp hax
    have h₂ := e.lt_iff_lt.mp hxa
    change t < j.val at h₁
    change j.val < t + 1 at h₂
    omega

/-- A finite affine envelope has a finite subdivision whose active slopes telescope
exactly to its total increase. Each selected line remains active on a closed subinterval,
so it is a valid best response at the left endpoint as well. -/
theorem exists_partition (r c : ι → ℝ) :
    ∃ (k : ℕ) (a : ℕ → ℝ) (s : ℕ → ι),
      0 < k ∧ a 0 = 0 ∧ a k = 1 ∧
      (∀ t < k, a t < a (t+1)) ∧
      (∀ t ≤ k, 0 ≤ a t ∧ a t ≤ 1) ∧
      (∀ t < k, ∀ x ∈ Set.Icc (a t) (a (t+1)), IsActive r c x (s t)) ∧
      (∑ t ∈ Finset.range k, (a (t+1) - a t) * r (s t)) =
        envelope r c 1 - envelope r c 0 := by
  classical
  obtain ⟨k, a, hk, ha0, hak, hainc, habound, hagap⟩ := exists_grid (breakpoints r c)
    (zero_mem_breakpoints r c) (one_mem_breakpoints r c)
    (fun _ hx => mem_breakpoints_bounds r c hx)
  choose s hs using (fun t : ℕ => exists_active r c ((a t + a (t+1))/2))
  have hactive : ∀ t < k, ∀ x ∈ Set.Icc (a t) (a (t+1)), IsActive r c x (s t) := by
    intro t ht
    exact active_on_gap r c (habound t (by omega)).1
      (habound (t+1) (by omega)).2 (hainc t ht) (hagap t ht) (hs t)
  refine ⟨k, a, s, hk, ha0, hak, hainc, habound, hactive, ?_⟩
  have hdiff : ∀ t < k, (a (t+1) - a t) * r (s t) =
      envelope r c (a (t+1)) - envelope r c (a t) := by
    intro t ht
    have hleft := active_eq_envelope r c (a t) (s t)
      (hactive t ht (a t) ⟨le_rfl, (hainc t ht).le⟩)
    have hright := active_eq_envelope r c (a (t+1)) (s t)
      (hactive t ht (a (t+1)) ⟨(hainc t ht).le, le_rfl⟩)
    rw [← hleft, ← hright]
    dsimp [line]
    ring
  calc
    (∑ t ∈ Finset.range k, (a (t+1) - a t) * r (s t)) =
        ∑ t ∈ Finset.range k, (envelope r c (a (t+1)) - envelope r c (a t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hdiff t (Finset.mem_range.mp ht)
    _ = envelope r c (a k) - envelope r c (a 0) := by
      exact Finset.sum_range_sub (fun t => envelope r c (a t)) k
    _ = envelope r c 1 - envelope r c 0 := by rw [ha0, hak]

omit [Fintype ι] [Nonempty ι] in
/-- Active slopes are ordered in the same direction as the parameter. -/
lemma active_slope_le {r c : ι → ℝ} {x y : ℝ} (hxy : x < y) {i j : ι}
    (hi : IsActive r c x i) (hj : IsActive r c y j) : r i ≤ r j := by
  have hx := hi j
  have hy := hj i
  dsimp [line] at hx hy
  by_contra h
  have hr : 0 < r i - r j := sub_pos.mpr (lt_of_not_ge h)
  have hp := mul_pos (sub_pos.mpr hxy) hr
  nlinarith

omit [Fintype ι] [Nonempty ι] in
/-- A line active throughout a right-hand interval has maximal slope among all ties
at its left endpoint. This supplies the standard principal-favorable tie-breaking rule. -/
lemma maximal_slope_of_active_right {r c : ι → ℝ} {x y : ℝ} (hxy : x < y)
    {i : ι} (hi : IsActive r c y i) :
    ∀ j, IsActive r c x j → r j ≤ r i := by
  intro j hj
  exact active_slope_le hxy hj hi

/-- The subdivision can moreover be chosen to use a maximal-slope active line at every
point of each left-closed, right-open interval. -/
theorem exists_partition_max_slope (r c : ι → ℝ) :
    ∃ (k : ℕ) (a : ℕ → ℝ) (s : ℕ → ι),
      0 < k ∧ a 0 = 0 ∧ a k = 1 ∧
      (∀ t < k, a t < a (t+1)) ∧
      (∀ t ≤ k, 0 ≤ a t ∧ a t ≤ 1) ∧
      (∀ t < k, ∀ x ∈ Set.Icc (a t) (a (t+1)), IsActive r c x (s t)) ∧
      (∀ t < k, ∀ x ∈ Set.Ico (a t) (a (t+1)),
        ∀ j, IsActive r c x j → r j ≤ r (s t)) ∧
      (∑ t ∈ Finset.range k, (a (t+1) - a t) * r (s t)) =
        envelope r c 1 - envelope r c 0 := by
  obtain ⟨k, a, s, hk, hzero, hone, hinc, hbounds, hactive, hsum⟩ :=
    exists_partition r c
  refine ⟨k, a, s, hk, hzero, hone, hinc, hbounds, hactive, ?_, hsum⟩
  intro t ht x hx
  apply maximal_slope_of_active_right hx.2
  exact hactive t ht (a (t+1)) ⟨(hinc t ht).le, le_rfl⟩

end CombinatorialContracts.FiniteEnvelope
