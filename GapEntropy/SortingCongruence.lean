import GapEntropy.MedianElimination

/-!
# Sorting depends only on estimates of the input arms

The comparison is kept exactly, including the tie convention of `mergeSort`.
No assumption excluding equal empirical means is needed.
-/

namespace GapEntropy.SortingCongruence

theorem merge_congr_on {α : Type*} (xs ys : List α) {r s : α → α → Bool}
    (h : ∀ a ∈ xs, ∀ b ∈ ys, r a b = s a b) : xs.merge ys r = xs.merge ys s := by
  match xs, ys with
  | [], ys => simp
  | xs, [] => simp
  | a :: xs, b :: ys =>
      have hab := h a (by simp) b (by simp)
      simp only [List.merge, hab]
      split
      · congr 1
        exact merge_congr_on xs (b :: ys) (fun c hc d hd => h c (by simp [hc]) d hd)
      · congr 1
        exact merge_congr_on (a :: xs) ys (fun c hc d hd => h c hc d (by simp [hd]))
termination_by xs.length + ys.length

theorem mergeSort_congr_on {α : Type*} (xs : List α) {r s : α → α → Bool}
    (h : ∀ a ∈ xs, ∀ b ∈ xs, r a b = s a b) : xs.mergeSort r = xs.mergeSort s := by
  match xs with
  | [] => simp
  | [a] => simp
  | a :: b :: xs =>
      have hl : ∀ c ∈ (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1, c ∈ a :: b :: xs := by
        intro c hc
        simp only [List.MergeSort.Internal.splitInTwo_fst] at hc
        exact List.mem_of_mem_take hc
      have hr : ∀ c ∈ (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1, c ∈ a :: b :: xs := by
        intro c hc
        simp only [List.MergeSort.Internal.splitInTwo_snd] at hc
        exact List.mem_of_mem_drop hc
      rw [List.mergeSort, List.mergeSort,
        mergeSort_congr_on (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1
          (fun c hc d hd => h c (hl c hc) d (hl d hd)),
        mergeSort_congr_on (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1
          (fun c hc d hd => h c (hr c hc) d (hr d hd))]
      apply merge_congr_on
      intro c hc d hd
      exact h c (hl c (List.mem_mergeSort.mp hc)) d (hr d (List.mem_mergeSort.mp hd))
termination_by xs.length
decreasing_by all_goals simp [List.MergeSort.Internal.splitInTwo_fst, List.MergeSort.Internal.splitInTwo_snd]; omega

theorem ranking_congr_on {ι : Type*} [DecidableEq ι] (S : Finset ι) {x y : ι → ℝ}
    (hxy : ∀ i ∈ S, x i = y i) : Elimination.ranking S x = Elimination.ranking S y := by
  apply mergeSort_congr_on
  intro a ha b hb
  rw [hxy a (Finset.mem_toList.mp ha), hxy b (Finset.mem_toList.mp hb)]

theorem upperHalf_congr_on {ι : Type*} [DecidableEq ι] (S : Finset ι) {x y : ι → ℝ}
    (hxy : ∀ i ∈ S, x i = y i) : Elimination.upperHalf S x = Elimination.upperHalf S y := by
  unfold Elimination.upperHalf
  rw [ranking_congr_on S hxy]

theorem nextActive_congr_on {n : ℕ} (S : Finset (Fin n)) {x y : Fin n → ℝ}
    (hxy : ∀ i ∈ S, x i = y i) :
    MedianElimination.nextActive S x = MedianElimination.nextActive S y := by
  unfold MedianElimination.nextActive
  split_ifs
  · exact upperHalf_congr_on S hxy
  · rfl

end GapEntropy.SortingCongruence
