import CombinatorialContracts.Welfare

/-! # Reward-anchored scale certificate (Lemma 6) -/

namespace CombinatorialContracts

/-- The algebra behind the certificate, with all positivity requirements
explicit. Here `v` is the reward of an optimal response and `a` its largest
singleton reward. -/
theorem scale_certificate_algebra {n W P δ v a : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hP : 0 < P)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (heq : P = δ * v)
    (hav : a ≤ v) (hva : v ≤ n * a)
    (hPW : P ≤ W) (hWP : W ≤ n * P) :
    0 < W / (n ^ 2 * a) ∧
    W / (n ^ 2 * a) ≤ δ ∧
    δ ≤ min 1 (W / a) ∧
    min 1 (W / a) / (W / (n ^ 2 * a)) ≤ n ^ 2 := by
  have hW : 0 < W := hP.trans_le hPW
  have hden : 0 < n ^ 2 * a := mul_pos (sq_pos_of_pos hn) ha
  have hlo : 0 < W / (n ^ 2 * a) := div_pos hW hden
  have hbound : W ≤ δ * (n ^ 2 * a) := by
    calc
      W ≤ n * P := hWP
      _ = n * (δ * v) := by rw [heq]
      _ ≤ n * (δ * (n * a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hva hδ) hn.le
      _ = δ * (n ^ 2 * a) := by ring
  have hup : δ ≤ W / a := (le_div_iff₀ ha).mpr (by
    calc
      δ * a ≤ δ * v := mul_le_mul_of_nonneg_left hav hδ
      _ = P := heq.symm
      _ ≤ W := hPW)
  refine ⟨hlo, (div_le_iff₀ hden).mpr hbound, le_min hδ1 hup, ?_⟩
  apply (div_le_iff₀ hlo).mpr
  calc
    min 1 (W / a) ≤ W / a := min_le_right _ _
    _ = n ^ 2 * (W / (n ^ 2 * a)) := by
      field_simp

/-- The algorithm uses the smaller lower endpoint `b/n²`, where
`b = min 1 (W/a)`. The sharper certificate implies this form directly. -/
theorem grid_scale_algebra {n W P δ v a : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hP : 0 < P)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (heq : P = δ * v)
    (hav : a ≤ v) (hva : v ≤ n * a)
    (hPW : P ≤ W) (hWP : W ≤ n * P) :
    0 < min 1 (W / a) ∧
    min 1 (W / a) / n ^ 2 ≤ δ ∧ δ ≤ min 1 (W / a) := by
  obtain ⟨hlo, hl, hu, _⟩ :=
    scale_certificate_algebra hn ha hP hδ hδ1 heq hav hva hPW hWP
  refine ⟨lt_min (by norm_num) (div_pos (hP.trans_le hPW) ha), ?_, hu⟩
  calc
    min 1 (W / a) / n ^ 2 ≤ (W / a) / n ^ 2 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    _ = W / (n ^ 2 * a) := by ring
    _ ≤ δ := hl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A largest singleton in a positive-reward set provides an `n`-factor
reward approximation. This proves the existence and positivity of the anchor,
rather than assuming either. -/
theorem exists_reward_anchor (M : Model ι) (S : Finset ι)
    (hS : 0 < M.reward S) :
    ∃ j ∈ S, 0 < M.reward {j} ∧
      M.reward {j} ≤ M.reward S ∧
      M.reward S ≤ (Fintype.card ι : ℝ) * M.reward {j} ∧
      ∀ i ∈ S, M.reward {i} ≤ M.reward {j} := by
  classical
  have hne : S.Nonempty := by
    by_contra h
    have hE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hE, M.reward_empty] at hS
    exact lt_irrefl _ hS
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S (fun i => M.reward {i}) hne
  have hupper : M.reward S ≤ (Fintype.card ι : ℝ) * M.reward {j} := by
    calc
      M.reward S ≤ ∑ i ∈ S, M.reward {i} :=
        subadditive_le_sum_singletons M.reward M.reward_empty M.reward_subadditive S
      _ ≤ ∑ _i ∈ S, M.reward {j} := Finset.sum_le_sum hmax
      _ = (S.card : ℝ) * M.reward {j} := by simp
      _ ≤ (Fintype.card ι : ℝ) * M.reward {j} :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S)
          (M.reward_nonneg _)
  have hjpos : 0 < M.reward {j} := by
    by_contra h
    have hprod : (Fintype.card ι : ℝ) * M.reward {j} ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt h)
    linarith
  exact ⟨j, hj, hjpos, M.reward_mono (Finset.singleton_subset_iff.mpr hj), hupper, hmax⟩

/-- Positive optimal principal utility forces a positive reward and a nonempty
ground set, including the boundary case of zero available actions. -/
theorem optimal_reward_pos (M : Model ι) (hopt : 0 < optimalValue M) :
    0 < M.reward (response M (optimum M)) := by
  have hδ := sub_nonneg.mpr (optimum_mem M).2
  have hv := M.reward_nonneg (response M (optimum M))
  change 0 < (1 - optimum M) * M.reward (response M (optimum M)) at hopt
  nlinarith

theorem card_pos_of_optimalValue_pos (M : Model ι) (hopt : 0 < optimalValue M) :
    0 < Fintype.card ι := by
  obtain ⟨j, _, _, _, _, _⟩ := exists_reward_anchor M _ (optimal_reward_pos M hopt)
  exact Fintype.card_pos_iff.mpr ⟨j⟩

/-- Lemma 6: a positive singleton anchor always exists, and the exact retained
share belongs to the stated interval of endpoint ratio at most `n²`. -/
theorem reward_anchored_scale (M : Model ι) (hopt : 0 < optimalValue M) :
    ∃ j ∈ response M (optimum M), 0 < M.reward {j} ∧
      welfare M / ((Fintype.card ι : ℝ) ^ 2 * M.reward {j}) ≤ 1 - optimum M ∧
      1 - optimum M ≤ min 1 (welfare M / M.reward {j}) ∧
      min 1 (welfare M / M.reward {j}) /
          (welfare M / ((Fintype.card ι : ℝ) ^ 2 * M.reward {j})) ≤
        (Fintype.card ι : ℝ) ^ 2 := by
  obtain ⟨j, hj, ha, hav, hva, _⟩ :=
    exists_reward_anchor M _ (optimal_reward_pos M hopt)
  have hn : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast card_pos_of_optimalValue_pos M hopt
  obtain ⟨_, hl, hu, hratio⟩ := scale_certificate_algebra hn ha hopt
    (sub_nonneg.mpr (optimum_mem M).2) (by linarith [(optimum_mem M).1])
    (show optimalValue M = (1 - optimum M) * M.reward (response M (optimum M)) from rfl)
    hav hva (optimalValue_le_welfare M) (welfare_le_card_mul_optimalValue M)
  exact ⟨j, hj, ha, hl, hu, hratio⟩

/-- Algorithm-ready form: for one enumerated singleton, the interval
`[b/n²,b]`, with `b = min 1 (W/a)`, contains the optimal retained share. -/
theorem reward_anchored_grid_scale (M : Model ι) (hopt : 0 < optimalValue M) :
    ∃ j ∈ response M (optimum M), 0 < M.reward {j} ∧
      0 < min 1 (welfare M / M.reward {j}) ∧
      min 1 (welfare M / M.reward {j}) / (Fintype.card ι : ℝ) ^ 2 ≤
          1 - optimum M ∧
      1 - optimum M ≤ min 1 (welfare M / M.reward {j}) := by
  obtain ⟨j, hj, ha, hav, hva, _⟩ :=
    exists_reward_anchor M _ (optimal_reward_pos M hopt)
  have hn : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast card_pos_of_optimalValue_pos M hopt
  obtain ⟨hb, hl, hu⟩ := grid_scale_algebra hn ha hopt
    (sub_nonneg.mpr (optimum_mem M).2) (by linarith [(optimum_mem M).1])
    (show optimalValue M = (1 - optimum M) * M.reward (response M (optimum M)) from rfl)
    hav hva (optimalValue_le_welfare M) (welfare_le_card_mul_optimalValue M)
  exact ⟨j, hj, ha, hb, hl, hu⟩

end CombinatorialContracts
