import GapEntropy.PermutationCounts
import GapEntropy.LowerBoundCore
import Mathlib.Data.Finset.Max

/-!
# Minimum-cost representatives of occupied gap buckets

The representative is an original arm identity, including when several arms
have equal means. Its cost is the minimum of the actual normalized permutation
costs in its bucket. Weighted averaging therefore charges only the original
instance's unconditional expected sample count.

The statistical confidence and scale-count bounds remain separate obligations.
-/

open scoped BigOperators Classical

namespace GapEntropy.Instance

variable {n : ℕ} (I : Instance n)

theorem gapGroup_nonempty_iff (k : ℕ) :
    (I.gapGroup k).Nonempty ↔ k ∈ I.occupiedBuckets := by
  simp only [gapGroup, occupiedBuckets, Finset.nonempty_def,
    Finset.mem_filter, Finset.mem_image]

noncomputable def costRepresentative (c : Fin n → ℝ) (k : ℕ)
    (hk : k ∈ I.occupiedBuckets) : Fin n :=
  Classical.choose ((I.gapGroup k).exists_min_image c ((I.gapGroup_nonempty_iff k).2 hk))

theorem costRepresentative_mem (c : Fin n → ℝ) (k : ℕ)
    (hk : k ∈ I.occupiedBuckets) : I.costRepresentative c k hk ∈ I.gapGroup k :=
  (Classical.choose_spec
    ((I.gapGroup k).exists_min_image c ((I.gapGroup_nonempty_iff k).2 hk))).1

theorem costRepresentative_min (c : Fin n → ℝ) (k : ℕ)
    (hk : k ∈ I.occupiedBuckets) {i : Fin n} (hi : i ∈ I.gapGroup k) :
    c (I.costRepresentative c k hk) ≤ c i :=
  (Classical.choose_spec
    ((I.gapGroup k).exists_min_image c ((I.gapGroup_nonempty_iff k).2 hk))).2 i hi

theorem costRepresentative_suboptimal (c : Fin n → ℝ) (k : ℕ)
    (hk : k ∈ I.occupiedBuckets) : I.costRepresentative c k hk ∈ I.suboptimal :=
  (Finset.mem_filter.1 (I.costRepresentative_mem c k hk)).1

@[simp] theorem bucket_costRepresentative (c : Fin n → ℝ) (k : ℕ)
    (hk : k ∈ I.occupiedBuckets) : I.bucket (I.costRepresentative c k hk) = k :=
  (Finset.mem_filter.1 (I.costRepresentative_mem c k hk)).2

theorem costRepresentative_ne (c : Fin n → ℝ) {k l : ℕ}
    (hk : k ∈ I.occupiedBuckets) (hl : l ∈ I.occupiedBuckets) (hkl : k ≠ l) :
    I.costRepresentative c k hk ≠ I.costRepresentative c l hl := by
  intro h
  apply hkl
  simpa only [I.bucket_costRepresentative] using congrArg I.bucket h

/-- Total version for finite sums and event families; only occupied buckets are
used in the lower bound. The arbitrary off-support value is the stored best arm. -/
noncomputable def representativeArm (c : Fin n → ℝ) (k : ℕ) : Fin n :=
  if hk : k ∈ I.occupiedBuckets then I.costRepresentative c k hk else I.best

@[simp] theorem representativeArm_of_mem (c : Fin n → ℝ) {k : ℕ}
    (hk : k ∈ I.occupiedBuckets) :
    I.representativeArm c k = I.costRepresentative c k hk := by
  simp [representativeArm, hk]

theorem representativeArm_suboptimal (c : Fin n → ℝ) {k : ℕ}
    (hk : k ∈ I.occupiedBuckets) : I.representativeArm c k ∈ I.suboptimal := by
  rw [I.representativeArm_of_mem c hk]
  exact I.costRepresentative_suboptimal c k hk

noncomputable def representativeCost (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k ∈ I.occupiedBuckets then c (I.costRepresentative c k hk) else 0

@[simp] theorem representativeCost_of_mem (c : Fin n → ℝ) {k : ℕ}
    (hk : k ∈ I.occupiedBuckets) :
    I.representativeCost c k = c (I.costRepresentative c k hk) := by
  simp [representativeCost, hk]

theorem representativeCost_eq_cost_arm (c : Fin n → ℝ) {k : ℕ}
    (hk : k ∈ I.occupiedBuckets) : I.representativeCost c k = c (I.representativeArm c k) := by
  rw [I.representativeCost_of_mem c hk, I.representativeArm_of_mem c hk]

theorem representativeCost_le (c : Fin n → ℝ) {k : ℕ} {i : Fin n}
    (hi : i ∈ I.gapGroup k) : I.representativeCost c k ≤ c i := by
  have hk := (I.gapGroup_nonempty_iff k).1 ⟨i, hi⟩
  rw [I.representativeCost_of_mem c hk]
  exact I.costRepresentative_min c k hk hi

theorem le_representativeCost (c : Fin n → ℝ) {L : ℝ} {k : ℕ}
    (hk : k ∈ I.occupiedBuckets) (hc : ∀ i ∈ I.gapGroup k, L ≤ c i) :
    L ≤ I.representativeCost c k := by
  rw [I.representativeCost_of_mem c hk]
  exact hc _ (I.costRepresentative_mem c k hk)

theorem representativeCost_nonneg (c : Fin n → ℝ)
    (hc : ∀ i ∈ I.suboptimal, 0 ≤ c i) (k : ℕ) : 0 ≤ I.representativeCost c k := by
  by_cases hk : k ∈ I.occupiedBuckets
  · exact I.le_representativeCost c hk (fun i hi => hc i (Finset.mem_filter.1 hi).1)
  · simp [representativeCost, hk]

theorem groupHardness_mul_representativeCost_le (c : Fin n → ℝ) (k : ℕ) :
    I.groupHardness k * I.representativeCost c k ≤
      ∑ i ∈ I.gapGroup k, I.weight i * c i := by
  rw [groupHardness, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (I.representativeCost_le c hi) (I.weight_nonneg i))

theorem hardness_mul_representativeCost_le (c : Fin n → ℝ) :
    I.hardness * (∑ k ∈ I.occupiedBuckets, I.bucketMass k * I.representativeCost c k) ≤
      ∑ i ∈ I.suboptimal, I.weight i * c i := by
  calc
    _ = ∑ k ∈ I.occupiedBuckets, I.groupHardness k * I.representativeCost c k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      unfold bucketMass
      field_simp [I.hardness_pos.ne']
    _ ≤ ∑ k ∈ I.occupiedBuckets, ∑ i ∈ I.gapGroup k, I.weight i * c i :=
      Finset.sum_le_sum (fun k _ => I.groupHardness_mul_representativeCost_le c k)
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem I.bucket hi) (fun i => I.weight i * c i)

/-- The representative-cost budget is now proved for the original algorithm's
actual permutation average, rather than assumed as an abstract cost inequality. -/
theorem normalized_representative_cost_le (A : Algorithm)
    (h : permutationAverage A I ≠ ⊤) :
    I.hardness * (∑ k ∈ I.occupiedBuckets,
      I.bucketMass k * I.representativeCost (normalizedArmCost A I h) k) ≤
      (permutationAverage A I).toReal :=
  (I.hardness_mul_representativeCost_le _).trans
    (sum_weight_mul_normalizedArmCost_le A I h)

/-- B.1 reduced to two statistical facts about these specified representatives.
Neither fact is an axiom or a claim that the full lower bound is already proved. -/
theorem permutation_lower_bound_of_scale_count (A : Algorithm)
    (h : permutationAverage A I ≠ ⊤) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10)
    (hconfidence : ∀ i ∈ I.suboptimal, Real.log δ⁻¹ ≤ normalizedArmCost A I h i)
    (hcount : ∀ x : ℝ, 1 ≤ x →
      ((I.occupiedBuckets.filter fun k =>
        I.representativeCost (normalizedArmCost A I h) k ≤ x).card : ℝ) ≤
        4 * δ * (Real.log (1600 * x) / Real.log 4 + 2) * Real.exp (2 * x)) :
    I.hardness * (Real.log δ⁻¹ + I.gapEntropy) / 5 ≤
      (permutationAverage A I).toReal := by
  apply I.lower_bound_of_scale_count _ hδ0 hδ1
  · intro k hk
    exact I.le_representativeCost _ hk
      (fun i hi => hconfidence i (Finset.mem_filter.1 hi).1)
  · exact I.normalized_representative_cost_le A h
  · exact hcount

end GapEntropy.Instance
