import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Deterministic threshold elimination and empirical upper-half padding

These are the deterministic parts of manuscript Lemma A.3, Remark A.4,
(D.11)--(D.12), and the counting argument used in (F.1).
No probability bound or algorithm correctness is asserted here.

The threshold-specific implications below are proved from the manuscript's exact constants.
-/

namespace GapEntropy.Elimination

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The raw threshold set in (A.5)/(D.7). -/
def raw (S : Finset ι) (x : ι → ℝ) (z d : ℝ) : Finset ι :=
  S.filter fun i => z - d / 2 ≤ x i

/-- Empirical descending ranking. Equal estimates are resolved by the input list order. -/
def ranking (S : Finset ι) (x : ι → ℝ) : List ι :=
  S.toList.mergeSort fun i j => decide (x j ≤ x i)

/-- The empirical upper `⌈|S|/2⌉` arms, including arbitrary resolution of equal estimates. -/
def upperHalf (S : Finset ι) (x : ι → ℝ) : Finset ι :=
  ((ranking S x).take ((S.card + 1) / 2)).toFinset

/-- Padding is completed before any singleton-output decision. -/
def padded (S : Finset ι) (x : ι → ℝ) (z d : ℝ) : Finset ι :=
  raw S x z d ∪ upperHalf S x

omit [DecidableEq ι] in
@[simp] theorem mem_raw {S : Finset ι} {x : ι → ℝ} {z d : ℝ} {i : ι} :
    i ∈ raw S x z d ↔ i ∈ S ∧ z - d / 2 ≤ x i := by
  simp [raw]

omit [DecidableEq ι] in
theorem raw_subset (S : Finset ι) (x : ι → ℝ) (z d : ℝ) : raw S x z d ⊆ S :=
  Finset.filter_subset _ _

omit [DecidableEq ι] in
@[simp] theorem mem_ranking {S : Finset ι} {x : ι → ℝ} {i : ι} :
    i ∈ ranking S x ↔ i ∈ S := by
  simp [ranking]

omit [DecidableEq ι] in
theorem ranking_nodup (S : Finset ι) (x : ι → ℝ) : (ranking S x).Nodup := by
  exact (List.mergeSort_perm _ _).nodup_iff.mpr S.nodup_toList

omit [DecidableEq ι] in
@[simp] theorem length_ranking (S : Finset ι) (x : ι → ℝ) :
    (ranking S x).length = S.card := by
  simp [ranking]

omit [DecidableEq ι] in
theorem ranking_pairwise (S : Finset ι) (x : ι → ℝ) :
    (ranking S x).Pairwise fun i j => x j ≤ x i := by
  have h := List.pairwise_mergeSort
    (le := fun i j => decide (x j ≤ x i))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at *
      exact le_trans hbc hab)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
    S.toList
  simpa only [ranking, decide_eq_true_eq] using h

theorem upperHalf_subset (S : Finset ι) (x : ι → ℝ) : upperHalf S x ⊆ S := by
  intro i hi
  apply mem_ranking.mp
  exact List.mem_of_mem_take (List.mem_toFinset.mp hi)

@[simp] theorem upperHalf_card (S : Finset ι) (x : ι → ℝ) :
    (upperHalf S x).card = (S.card + 1) / 2 := by
  rw [upperHalf, List.toFinset_card_of_nodup (ranking_nodup S x).take]
  rw [List.length_take, length_ranking, Nat.min_eq_left]
  omega

/-- Every upper-half arm outranks every omitted active arm, even when estimates tie. -/
theorem upperHalf_rank {S : Finset ι} {x : ι → ℝ} {i j : ι}
    (hi : i ∈ upperHalf S x) (hj : j ∈ S) (hju : j ∉ upperHalf S x) :
    x j ≤ x i := by
  have hi' : i ∈ (ranking S x).take ((S.card + 1) / 2) := List.mem_toFinset.mp hi
  have hj' : j ∈ (ranking S x).drop ((S.card + 1) / 2) := by
    have hm : j ∈ (ranking S x).take ((S.card + 1) / 2) ++
        (ranking S x).drop ((S.card + 1) / 2) := by
      simpa only [List.take_append_drop] using mem_ranking.mpr hj
    rcases List.mem_append.mp hm with h | h
    · exact False.elim (hju (List.mem_toFinset.mpr h))
    · exact h
  exact (ranking_pairwise S x).rel_of_mem_take_of_mem_drop hi' hj'

theorem raw_subset_padded (S : Finset ι) (x : ι → ℝ) (z d : ℝ) :
    raw S x z d ⊆ padded S x z d := Finset.subset_union_left

theorem upperHalf_subset_padded (S : Finset ι) (x : ι → ℝ) (z d : ℝ) :
    upperHalf S x ⊆ padded S x z d := Finset.subset_union_right

theorem padded_subset (S : Finset ι) (x : ι → ℝ) (z d : ℝ) :
    padded S x z d ⊆ S :=
  Finset.union_subset (raw_subset S x z d) (upperHalf_subset S x)

/-- A threshold set and the upper half are comparable by inclusion. -/
theorem raw_upperHalf_comparable (S : Finset ι) (x : ι → ℝ) (z d : ℝ) :
    raw S x z d ⊆ upperHalf S x ∨ upperHalf S x ⊆ raw S x z d := by
  classical
  by_cases h : raw S x z d ⊆ upperHalf S x
  · exact Or.inl h
  · right
    obtain ⟨j, hj, hju⟩ := Finset.not_subset.mp h
    intro i hi
    have hji := upperHalf_rank hi (mem_raw.mp hj).1 hju
    exact mem_raw.mpr ⟨upperHalf_subset S x hi, le_trans (mem_raw.mp hj).2 hji⟩

/-- Union padding is exactly the algorithm's “add arms until half remain” rule in size. -/
theorem padded_card (S : Finset ι) (x : ι → ℝ) (z d : ℝ) :
    (padded S x z d).card = max (raw S x z d).card ((S.card + 1) / 2) := by
  rcases raw_upperHalf_comparable S x z d with h | h
  · have hc := Finset.card_le_card h
    rw [upperHalf_card] at hc
    rw [padded, Finset.union_eq_right.mpr h, upperHalf_card, max_eq_right hc]
  · have hc := Finset.card_le_card h
    rw [upperHalf_card] at hc
    rw [padded, Finset.union_eq_left.mpr h, max_eq_left hc]

theorem padded_card_ge_half (S : Finset ι) (x : ι → ℝ) (z d : ℝ) :
    (S.card + 1) / 2 ≤ (padded S x z d).card := by
  rw [padded_card]
  exact le_max_right _ _

theorem padded_halves_of_raw_small {S : Finset ι} {x : ι → ℝ} {z d : ℝ}
    (h : (raw S x z d).card ≤ (S.card + 1) / 2) :
    (padded S x z d).card = (S.card + 1) / 2 := by
  rw [padded_card, max_eq_right h]

/-- In a nontrivial active set, a padded singleton can only follow a two-arm call. -/
theorem singleton_input_card {S : Finset ι} {x : ι → ℝ} {z d : ℝ}
    (hS : 2 ≤ S.card) (hR : (padded S x z d).card = 1) : S.card = 2 := by
  have h := padded_card_ge_half S x z d
  omega

/-- The exact rounded halving used in C.2, D.2 and F.2 contracts sizes ≥3 by 3/4. -/
theorem rounded_half_contracts {s : ℕ} (hs : 3 ≤ s) :
    4 * ((s + 1) / 2) ≤ 3 * s := by omega

/-- Upper-valid reference estimates remain bounded by the original best mean. -/
theorem reference_upper {z μa μstar d : ℝ} (hz : z ≤ μa + d / 16)
    (ha : μa ≤ μstar) : z - d / 2 ≤ μstar - 7 * d / 16 := by
  linarith

omit [DecidableEq ι] in
/-- Remark A.4/(D.12): removing a near arm requires a severe downward error. -/
theorem removed_near_severe {S : Finset ι} {x μ : ι → ℝ} {z d μstar : ℝ} {i : ι}
    (hi : i ∈ S) (hz : z ≤ μstar + d / 16) (hgap : μstar - μ i ≤ d / 8)
    (hremoved : i ∉ raw S x z d) : x i - μ i < -5 * d / 16 := by
  have hx : x i < z - d / 2 := by
    by_contra! h
    exact hremoved (mem_raw.mpr ⟨hi, h⟩)
  linarith

theorem padded_removed_near_severe {S : Finset ι} {x μ : ι → ℝ} {z d μstar : ℝ}
    {i : ι} (hi : i ∈ S) (hz : z ≤ μstar + d / 16)
    (hgap : μstar - μ i ≤ d / 8) (hremoved : i ∉ padded S x z d) :
    x i - μ i < -5 * d / 16 := by
  apply removed_near_severe hi hz hgap
  exact fun h => hremoved (raw_subset_padded S x z d h)

omit [DecidableEq ι] in
/-- The sufficient empirical estimate condition used to protect the best arm. -/
theorem best_mem_raw {S : Finset ι} {x : ι → ℝ} {z d μstar : ℝ} {best : ι}
    (hbest : best ∈ S) (hd : 0 ≤ d) (hz : z ≤ μstar + d / 16)
    (hx : μstar - d / 16 ≤ x best) : best ∈ raw S x z d := by
  apply mem_raw.mpr
  exact ⟨hbest, by linarith⟩

theorem best_mem_padded {S : Finset ι} {x : ι → ℝ} {z d μstar : ℝ} {best : ι}
    (hbest : best ∈ S) (hd : 0 ≤ d) (hz : z ≤ μstar + d / 16)
    (hx : μstar - d / 16 ≤ x best) : best ∈ padded S x z d :=
  raw_subset_padded S x z d (best_mem_raw hbest hd hz hx)

omit [DecidableEq ι] in
/-- A raw-retained far arm requires the manuscript's large upward error. -/
theorem far_retained_upward {S : Finset ι} {x μ : ι → ℝ} {z d μstar : ℝ} {i : ι}
    (hz : μstar - 3 * d / 16 ≤ z) (hgap : d ≤ μstar - μ i)
    (hi : i ∈ raw S x z d) : 5 * d / 16 ≤ x i - μ i := by
  have hx := (mem_raw.mp hi).2
  linarith

/-- Arms within one tolerance of the specified original best mean. -/
def near (S : Finset ι) (μ : ι → ℝ) (μstar d : ℝ) : Finset ι :=
  S.filter fun i => μstar - μ i < d

/-- Far arms with the upward error required for raw retention. -/
def farErrors (S : Finset ι) (x μ : ι → ℝ) (μstar d : ℝ) : Finset ι :=
  S.filter fun i => d ≤ μstar - μ i ∧ 5 * d / 16 ≤ x i - μ i

theorem raw_subset_near_union_errors {S : Finset ι} {x μ : ι → ℝ}
    {z d μstar : ℝ} (hz : μstar - 3 * d / 16 ≤ z) :
    raw S x z d ⊆ near S μ μstar d ∪ farErrors S x μ μstar d := by
  intro i hi
  have his := (mem_raw.mp hi).1
  by_cases hgap : μstar - μ i < d
  · exact Finset.mem_union_left _ (by simp [near, his, hgap])
  · have hge := le_of_not_gt hgap
    exact Finset.mem_union_right _ (by
      simp only [farErrors, Finset.mem_filter]
      exact ⟨his, hge, far_retained_upward hz hge hi⟩)

theorem raw_card_le_near_add_errors {S : Finset ι} {x μ : ι → ℝ}
    {z d μstar : ℝ} (hz : μstar - 3 * d / 16 ≤ z) :
    (raw S x z d).card ≤ (near S μ μstar d).card + (farErrors S x μ μstar d).card :=
  (Finset.card_le_card (raw_subset_near_union_errors hz)).trans (Finset.card_union_le _ _)

/-- The deterministic counting step preceding the Markov bound in A.3/F.1. -/
theorem large_raw_many_far_errors {S : Finset ι} {x μ : ι → ℝ}
    {z d μstar : ℝ} {N : ℕ} (hz : μstar - 3 * d / 16 ≤ z)
    (hnear : (near S μ μstar d).card ≤ N) (hS : 4 * N < S.card)
    (hraw : (S.card + 1) / 2 < (raw S x z d).card) :
    S.card < 4 * (farErrors S x μ μstar d).card := by
  have hc := raw_card_le_near_add_errors (S := S) (x := x) (μ := μ) hz
  omega

/-- If no suboptimal arm has the necessary upward error, the raw set is the best singleton.
The probabilistic small-set assumption `|S| ≤ 4` is needed only for the later union bound,
and hence is not imposed on this deterministic implication. -/
theorem raw_eq_best_singleton {S : Finset ι} {x μ : ι → ℝ} {z d μstar : ℝ}
    {best : ι} (hbest : best ∈ S) (hd : 0 ≤ d)
    (hzlo : μstar - 3 * d / 16 ≤ z) (hzhi : z ≤ μstar + d / 16)
    (hxbest : μstar - d / 16 ≤ x best)
    (hgaps : ∀ i ∈ S, i ≠ best → d ≤ μstar - μ i)
    (herrors : ∀ i ∈ S, i ≠ best → x i - μ i < 5 * d / 16) :
    raw S x z d = {best} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨best_mem_raw hbest hd hzhi hxbest, ?_⟩
  intro i hi
  by_contra hne
  have his := (mem_raw.mp hi).1
  have hu := far_retained_upward hzlo (hgaps i his hne) hi
  exact (not_lt_of_ge hu) (herrors i his hne)

/-- A padded omission supplies the rank comparison used in the batch-collapse proof. -/
theorem omitted_rank {S : Finset ι} {x : ι → ℝ} {z d : ℝ} {i j : ι}
    (hi : i ∈ S) (hremoved : i ∉ padded S x z d) (hj : j ∈ upperHalf S x) :
    x i ≤ x j :=
  upperHalf_rank hj hi (fun h => hremoved (upperHalf_subset_padded S x z d h))

/-- The cardinality part of the empirical-rank argument in E.2:
if the upper half contains at most one core arm and at most `s/8` exceptional
outside arms, at least `s/4` upper-half arms belong to neither category. -/
theorem upperHalf_many_outside {S B C : Finset ι} {x : ι → ℝ}
    (hS : 8 ≤ S.card) (hB : (upperHalf S x ∩ B).card ≤ 1)
    (hC : (upperHalf S x ∩ C).card ≤ S.card / 8) :
    S.card ≤ 4 * (upperHalf S x \ (B ∪ C)).card := by
  have hsplit := Finset.card_sdiff_add_card_inter (upperHalf S x) (B ∪ C)
  rw [Finset.inter_union_distrib_left] at hsplit
  have hle := Finset.card_union_le (upperHalf S x ∩ B) (upperHalf S x ∩ C)
  rw [upperHalf_card] at hsplit
  omega

end

end GapEntropy.Elimination
