import CombinatorialContracts.EqualRevenue

/-! # Polynomial sparse supply for the concrete binary equal-revenue cost.

The proof is uniform in the price vector.  Its combinatorial ingredient is a
finite-family counting theorem derived from the pairwise exclusion property.
-/
namespace CombinatorialContracts.EqualRevenue
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

private def lowBits {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :=
  S.filter (fun i => i.val < k)

private theorem binaryIndex_modEq_low {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    Nat.ModEq (2^k) (binaryIndex S) (binaryIndex (lowBits S k)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [lowBits, filter_empty, binaryIndex_empty]; rfl
  | @insert i S hi ih =>
    by_cases hik : i.val < k
    · have hil : i ∉ lowBits S k := by simp [lowBits, hi]
      simp only [lowBits, filter_insert, hik, ↓reduceIte]
      change Nat.ModEq (2^k) (binaryIndex (insert i S)) (binaryIndex (insert i (lowBits S k)))
      rw [binaryIndex_insert hi, binaryIndex_insert hil]
      exact (Nat.ModEq.refl (2^i.val)).add ih
    · have hid : 2^k ∣ 2^i.val := pow_dvd_pow 2 (by omega)
      simp only [lowBits, filter_insert, hik, ↓reduceIte]
      rw [binaryIndex_insert hi]
      simpa using (Nat.modEq_zero_iff_dvd.mpr hid).add ih


private def rightEnd {n : ℕ} (F : Finset (Finset (Fin n))) (i : Fin n) : ℕ :=
  F.sup (fun S => if i ∈ S then binaryIndex S else 0)

private def Ambiguous {n : ℕ} (F : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) (i : Fin n) : Prop :=
  binaryIndex S ≤ rightEnd F i ∧ rightEnd F i ≤ binaryIndex S + 2*2^i.val

private theorem exists_ambiguous_or_end {n : ℕ} (F : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : ∃ k : ℕ, k = n ∨ ∃ i : Fin n, i.val = k ∧ Ambiguous F S i :=
  ⟨n, Or.inl rfl⟩

private def minAmb {n : ℕ} (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  Nat.find (exists_ambiguous_or_end F S)

private theorem minAmb_le {n : ℕ} (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    minAmb F S ≤ n := Nat.find_min' _ (Or.inl rfl)

private theorem minAmb_spec {n : ℕ} (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    minAmb F S = n ∨ ∃ i : Fin n, i.val = minAmb F S ∧ Ambiguous F S i :=
  Nat.find_spec (exists_ambiguous_or_end F S)

private theorem not_ambiguous_below {n : ℕ} (F : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) {i : Fin n} (hi : i.val < minAmb F S) : ¬Ambiguous F S i := by
  intro ha
  have : minAmb F S ≤ i.val := Nat.find_min' _ (Or.inr ⟨i, rfl, ha⟩)
  omega

/-- The quantitative pairwise exclusion relation. -/
def PairBound {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ S ∈ F, ∀ T ∈ F, ∀ i : Fin n, i ∈ T → i ∉ S →
    binaryIndex T ≤ binaryIndex S + 2*2^i.val

private theorem rightEnd_of_mem {n : ℕ} {F : Finset (Finset (Fin n))}
    {S : Finset (Fin n)} (hS : S ∈ F) {i : Fin n} (hi : i ∈ S) :
    binaryIndex S ≤ rightEnd F i := by
  have h := Finset.le_sup (f := fun T => if i ∈ T then binaryIndex T else 0) hS
  simpa [rightEnd, hi] using h

private theorem rightEnd_of_not_mem {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : PairBound F) {S : Finset (Fin n)} (hS : S ∈ F) {i : Fin n} (hi : i ∉ S) :
    rightEnd F i ≤ binaryIndex S + 2*2^i.val := by
  apply Finset.sup_le
  intro T hT
  split_ifs with hit
  · exact hF S hS T hT i hit hi
  · omega

private theorem lowBits_antitone {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : PairBound F) {S T : Finset (Fin n)} (hS : S ∈ F) (hT : T ∈ F)
    (hst : binaryIndex S ≤ binaryIndex T) (hm : minAmb F S = minAmb F T) :
    lowBits T (minAmb F T) ⊆ lowBits S (minAmb F S) := by
  intro i hi
  obtain ⟨hiT, him⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨?_, by omega⟩
  by_contra hiS
  have hr1 := rightEnd_of_mem hT hiT
  have hr2 := rightEnd_of_not_mem hF hS hiS
  exact not_ambiguous_below F S (by omega) ⟨by omega, hr2⟩

private def bitAt {n : ℕ} (S : Finset (Fin n)) (k : ℕ) : Bool :=
  decide (∃ i ∈ S, i.val = k)

private theorem bitAt_eq_iff {n : ℕ} {S T : Finset (Fin n)} {k : ℕ}
    (h : bitAt S k = bitAt T k) (i : Fin n) (hi : i.val = k) :
    i ∈ S ↔ i ∈ T := by
  have hh : (∃ j ∈ S, j.val = k) ↔ (∃ j ∈ T, j.val = k) := by
    simpa only [bitAt, decide_eq_decide] using h
  constructor
  · intro his
    obtain ⟨j, hj, hjk⟩ := hh.mp ⟨i, his, hi⟩
    have : j = i := Fin.ext (by omega)
    simpa [this] using hj
  · intro hit
    obtain ⟨j, hj, hjk⟩ := hh.mpr ⟨i, hit, hi⟩
    have : j = i := Fin.ext (by omega)
    simpa [this] using hj

private theorem lowBits_extend_two {n : ℕ} {S T : Finset (Fin n)} {k : ℕ}
    (hlo : lowBits S k = lowBits T k)
    (hb0 : bitAt S k = bitAt T k) (hb1 : bitAt S (k+1) = bitAt T (k+1)) :
    lowBits S (k+2) = lowBits T (k+2) := by
  ext i
  simp only [lowBits, Finset.mem_filter]
  by_cases hi : i.val < k
  · have hmem := Finset.ext_iff.mp hlo i
    simp only [lowBits, Finset.mem_filter, hi, and_true] at hmem
    exact and_congr_left fun _ => hmem
  · by_cases hi0 : i.val = k
    · exact and_congr_left fun _ => bitAt_eq_iff hb0 i hi0
    · by_cases hi1 : i.val = k+1
      · exact and_congr_left fun _ => bitAt_eq_iff hb1 i hi1
      · have : ¬i.val < k+2 := by omega
        simp [this]

private theorem encoding_injective_ordered {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : PairBound F) {S T : Finset (Fin n)} (hS : S ∈ F) (hT : T ∈ F)
    (hst : binaryIndex S ≤ binaryIndex T) (hm : minAmb F S = minAmb F T)
    (hc : (lowBits S (minAmb F S)).card = (lowBits T (minAmb F T)).card)
    (hb0 : bitAt S (minAmb F S) = bitAt T (minAmb F T))
    (hb1 : bitAt S (minAmb F S+1) = bitAt T (minAmb F T+1)) : S = T := by
  have hlo : lowBits S (minAmb F S) = lowBits T (minAmb F S) := by
    simpa only [hm] using (Finset.eq_of_subset_of_card_le (lowBits_antitone hF hS hT hst hm)
      (by omega)).symm
  rcases minAmb_spec F S with hn | ⟨i, hi, haS⟩
  · have hall (U : Finset (Fin n)) : lowBits U n = U := by
      ext j
      simp [lowBits]
    rw [hn, hall, hall] at hlo
    exact hlo
  · have haT : Ambiguous F T i := by
      rcases minAmb_spec F T with hn | ⟨j, hj, hjA⟩
      · have := i.isLt
        omega
      · have : j = i := Fin.ext (by omega)
        simpa [this] using hjA
    have hlow2 : lowBits S (minAmb F S+2) = lowBits T (minAmb F S+2) :=
      lowBits_extend_two hlo (by simpa [hm] using hb0) (by simpa [hm] using hb1)
    have hmod : Nat.ModEq (2^(minAmb F S+2)) (binaryIndex T) (binaryIndex S) :=
      (binaryIndex_modEq_low T _).trans (hlow2 ▸ (binaryIndex_modEq_low S _).symm)
    have hp : 2*2^i.val < 2^(minAmb F S+2) := by
      rw [← hi, pow_add]
      have : 0 < 2^i.val := pow_pos (by omega) _
      norm_num
      omega
    have hdist : binaryIndex T < binaryIndex S + 2^(minAmb F S+2) := by
      obtain ⟨h1, h2⟩ := haS
      obtain ⟨h3, h4⟩ := haT
      omega
    exact binaryIndex_injective n (Nat.le_antisymm hst (hmod.le_of_lt_add hdist))

/-- Any binary family satisfying pairwise exclusion has quadratic size. -/
theorem card_le_of_pairBound {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : PairBound F) : F.card ≤ 4*(n+1)^2 := by
  classical
  let code : Finset (Fin n) → Fin (n+1) × Fin (n+1) × Bool × Bool := fun S =>
    (⟨minAmb F S, by have := minAmb_le F S; omega⟩,
     ⟨(lowBits S (minAmb F S)).card, by have := Finset.card_le_univ (lowBits S (minAmb F S)); simp at this; omega⟩,
     bitAt S (minAmb F S), bitAt S (minAmb F S+1))
  have hcard := Finset.card_le_card_of_injOn code (s := F) (t := Finset.univ) (by intro S hS; simp) (by
    intro S hS T hT heq
    have hm : minAmb F S = minAmb F T := congrArg (fun x => x.1.val) heq
    have hc : (lowBits S (minAmb F S)).card = (lowBits T (minAmb F T)).card :=
      congrArg (fun x => x.2.1.val) heq
    have hb0 : bitAt S (minAmb F S) = bitAt T (minAmb F T) := congrArg (fun x => x.2.2.1) heq
    have hb1 : bitAt S (minAmb F S+1) = bitAt T (minAmb F T+1) := congrArg (fun x => x.2.2.2) heq
    rcases le_total (binaryIndex S) (binaryIndex T) with hst | hts
    · exact encoding_injective_ordered hF hS hT hst hm hc hb0 hb1
    · exact (encoding_injective_ordered hF hT hS hts hm.symm hc.symm hb0.symm hb1.symm).symm)
  simpa [Fintype.card_prod, Fintype.card_bool, pow_two, mul_assoc, mul_comm, mul_left_comm] using hcard

/-- Approximate supply is defined against every action subset, with no
restriction on the signs or arithmetic description of prices. -/
def approxSupply (n : ℕ) (p : Fin n → ℝ) (ζ : ℝ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => ∀ T, supplyUtility (model n) p T ≤
    supplyUtility (model n) p S + ζ)

@[simp] theorem mem_approxSupply {n : ℕ} {p : Fin n → ℝ} {ζ : ℝ}
    {S : Finset (Fin n)} : S ∈ approxSupply n p ζ ↔
      ∀ T, supplyUtility (model n) p T ≤ supplyUtility (model n) p S + ζ := by
  simp [approxSupply]

private theorem cost_add_gap {x y a N : ℕ} (hxy : x < y)
    (ha : 0 < a) (hN : y+a ≤ N) :
    1/(N : ℝ)^2 ≤ (cost (y+a) - cost y) - (cost (x+a) - cost x) := by
  have hg : (a : ℝ) * (1/(N : ℝ)^2) ≤
      (cost (y+a) - cost y) - (cost (x+a) - cost x) := by
    calc
      (a : ℝ) * (1/(N : ℝ)^2) = ∑ j ∈ range a, (1/(N : ℝ)^2) := by simp
      _ ≤ ∑ j ∈ range a, (increment (y+j) - increment (x+j)) := by
        apply sum_le_sum
        intro j hj
        exact increment_gap (by omega) (by have := mem_range.mp hj; omega)
      _ = (cost (y+a) - cost y) - (cost (x+a) - cost x) := by
        rw [cost_add, cost_add, sum_sub_distrib]
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hnon : (0 : ℝ) ≤ 1/(N : ℝ)^2 := by positivity
  nlinarith

/-- Uniform approximate-supply exclusion, proved directly from the concrete
cost rather than assumed as an oracle property. -/
theorem approxSupply_pairBound {n : ℕ} {p : Fin n → ℝ} {ζ : ℝ}
    (hζ : 2*ζ < 1/((2^n-1 : ℕ) : ℝ)^2) : PairBound (approxSupply n p ζ) := by
  intro S hS T hT i hiT hiS
  by_contra hnot
  have hfar : binaryIndex S + 2*2^i.val < binaryIndex T := by omega
  let U := T.erase i
  have hiU : i ∉ U := by simp [U]
  have hTU : T = insert i U := by simp [U, hiT]
  have hidxT : binaryIndex T = 2^i.val + binaryIndex U := by
    rw [hTU, binaryIndex_insert hiU]
  have hidxS : binaryIndex (insert i S) = 2^i.val + binaryIndex S :=
    binaryIndex_insert hiS
  have hst : binaryIndex S < binaryIndex U := by omega
  have hN : binaryIndex U + 2^i.val ≤ 2^n-1 := by
    have := binaryIndex_lt T
    omega
  have hgap := cost_add_gap (a := 2^i.val) hst (by positivity) hN
  have hs := (mem_approxSupply.mp hS) (insert i S)
  have ht := (mem_approxSupply.mp hT) U
  have hpS : (∑ j ∈ insert i S, p j) = p i + ∑ j ∈ S, p j := sum_insert hiS
  have hpT : (∑ j ∈ T, p j) = p i + ∑ j ∈ U, p j := by
    rw [hTU, sum_insert hiU]
  change (∑ j ∈ insert i S, p j) - cost (binaryIndex (insert i S)) ≤
    (∑ j ∈ S, p j) - cost (binaryIndex S) + ζ at hs
  change (∑ j ∈ U, p j) - cost (binaryIndex U) ≤
    (∑ j ∈ T, p j) - cost (binaryIndex T) + ζ at ht
  rw [hpS, hidxS] at hs
  rw [hpT, hidxT] at ht
  simp only [add_comm (2^i.val)] at hs ht
  linarith

/-- A uniform quadratic bound for every price vector and every tolerance
below half the smallest explicit marginal-cost gap. -/
theorem approxSupply_card_le {n : ℕ} (p : Fin n → ℝ) {ζ : ℝ}
    (hζ : 2*ζ < 1/((2^n-1 : ℕ) : ℝ)^2) :
    (approxSupply n p ζ).card ≤ 4*(n+1)^2 :=
  card_le_of_pairBound (approxSupply_pairBound hζ)

/-- The explicit inverse-exponential tolerance required by the lower bound.
The theorem is stronger than nonnegative-price sparse supply: it permits
all real price vectors. -/
theorem approxSupply_card_explicit (n : ℕ) (p : Fin n → ℝ) :
    (approxSupply n p (1/(8*((2^n-1 : ℕ) : ℝ)^2))).card ≤ 4*(n+1)^2 := by
  by_cases hn : n = 0
  · subst n
    have h := Finset.card_le_univ (approxSupply 0 p (1/(8*((2^0-1 : ℕ) : ℝ)^2)))
    simp only [Fintype.card_finset, Fintype.card_fin] at h
    norm_num at h ⊢
    omega
  · apply approxSupply_card_le
    have hN : 0 < 2^n-1 := by
      have : 1 < 2^n := one_lt_pow₀ (by omega) (by omega)
      omega
    have hNr : (0 : ℝ) < ((2^n-1 : ℕ) : ℝ) := by exact_mod_cast hN
    have hp : (0 : ℝ) < ((2^n-1 : ℕ) : ℝ)^2 := sq_pos_of_pos hNr
    apply (lt_div_iff₀ hp).mpr
    field_simp
    norm_num

end
end CombinatorialContracts.EqualRevenue
