import GapEntropy.Problem
import GapEntropy.SamplingCounts

/-!
# Original-instance costs under uniform relabeling

The cost of original arm identity `i` is the average of the samples drawn from
its image `π i` when the original algorithm is run on `π I`. The identities below
justify the lower-bound argument directly for permutation averages, without
requiring a separate realization of a symmetrized randomized policy.
-/

open scoped ENNReal BigOperators

namespace GapEntropy

noncomputable def permutationArmSamples (A : Algorithm) {n : ℕ} (I : Instance n)
    (i : Fin n) : ℝ≥0∞ :=
  (∑ π : Equiv.Perm (Fin n), (A n).expectedArmSamples (I.permute π) (π i)) /
    (n.factorial : ℝ≥0∞)

theorem sum_permutationArmSamples (A : Algorithm) {n : ℕ} (I : Instance n) :
    ∑ i : Fin n, permutationArmSamples A I i = permutationAverage A I := by
  unfold permutationArmSamples permutationAverage
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  rw [Equiv.sum_comp π ((A n).expectedArmSamples (I.permute π)),
    Policy.sum_expectedArmSamples]

theorem permutationArmSamples_le_average (A : Algorithm) {n : ℕ} (I : Instance n) (i : Fin n) :
    permutationArmSamples A I i ≤ permutationAverage A I := by
  rw [← sum_permutationArmSamples A I]
  exact Finset.single_le_sum (s := Finset.univ) (f := permutationArmSamples A I)
    (fun _ _ => zero_le) (Finset.mem_univ i)

theorem permutationArmSamples_ne_top (A : Algorithm) {n : ℕ} (I : Instance n)
    (h : permutationAverage A I ≠ ⊤) (i : Fin n) : permutationArmSamples A I i ≠ ⊤ :=
  ne_top_of_le_ne_top h (permutationArmSamples_le_average A I i)

theorem sum_toReal_permutationArmSamples (A : Algorithm) {n : ℕ} (I : Instance n)
    (h : permutationAverage A I ≠ ⊤) :
    ∑ i : Fin n, (permutationArmSamples A I i).toReal = (permutationAverage A I).toReal := by
  rw [← ENNReal.toReal_sum (fun i _ => permutationArmSamples_ne_top A I h i),
    sum_permutationArmSamples]

/-- The normalized per-arm cost is defined only with evidence that the original
permutation average is finite. It therefore never encodes an infinite cost as zero. -/
noncomputable def normalizedArmCost (A : Algorithm) {n : ℕ} (I : Instance n)
    (_h : permutationAverage A I ≠ ⊤) (i : Fin n) : ℝ :=
  I.gap i ^ 2 * (permutationArmSamples A I i).toReal

theorem normalizedArmCost_nonneg (A : Algorithm) {n : ℕ} (I : Instance n)
    (h : permutationAverage A I ≠ ⊤) (i : Fin n) : 0 ≤ normalizedArmCost A I h i := by
  unfold normalizedArmCost
  positivity

theorem weight_mul_normalizedArmCost (A : Algorithm) {n : ℕ} (I : Instance n)
    (h : permutationAverage A I ≠ ⊤) {i : Fin n} (hi : i ∈ I.suboptimal) :
    I.weight i * normalizedArmCost A I h i = (permutationArmSamples A I i).toReal := by
  have hg : I.gap i ≠ 0 := (I.gap_pos ((I.mem_suboptimal i).1 hi)).ne'
  simp [Instance.weight, normalizedArmCost, hg]

theorem sum_weight_mul_normalizedArmCost_le (A : Algorithm) {n : ℕ} (I : Instance n)
    (h : permutationAverage A I ≠ ⊤) :
    ∑ i ∈ I.suboptimal, I.weight i * normalizedArmCost A I h i ≤
      (permutationAverage A I).toReal := by
  calc
    (∑ i ∈ I.suboptimal, I.weight i * normalizedArmCost A I h i) =
        ∑ i ∈ I.suboptimal, (permutationArmSamples A I i).toReal :=
      Finset.sum_congr rfl (fun i hi => weight_mul_normalizedArmCost A I h hi)
    _ ≤ ∑ i : Fin n, (permutationArmSamples A I i).toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => ENNReal.toReal_nonneg)
    _ = (permutationAverage A I).toReal := sum_toReal_permutationArmSamples A I h

end GapEntropy
