import GapEntropy.WindowProbability
import GapEntropy.ScalePacking

/-!
# The unconditional permutation-averaged gap-entropy lower bound

This closes Appendix B for the concrete nonanticipating Gaussian policies of
`Model.lean`. All statistical premises of `LowerBoundCore` are discharged:
global correctness gives the per-arm confidence cost, censoring and Markov give
the source stopping window, finite transcript KL transfers its probability to
one tied comparison law, and actual dyadic geometry supplies scale packing.

No assumption of algorithm symmetry, monotonicity, dyadic gaps, distinct means,
or termination at a tied comparison instance is used. Infinite original costs
are kept in extended nonnegative reals and handled before real conversion.
-/

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy

/-- B.13 for the specified minimum-cost representatives of a globally correct
algorithm on its original instance. Its statistical premises are now proved. -/
theorem representative_scale_count (A : Algorithm) {n : ℕ} (I : Instance n)
    {δ : ℝ} (hδ : ValidConfidence δ) (hA : DeltaCorrect A δ)
    (hfin : permutationAverage A I ≠ ⊤) (x : ℝ) (hx : 1 ≤ x) :
    ((I.occupiedBuckets.filter fun k =>
      I.representativeCost (normalizedArmCost A I hfin) k ≤ x).card : ℝ) ≤
      4 * δ * (Real.log (1600 * x) / Real.log 4 + 2) * Real.exp (2 * x) := by
  apply I.scale_count_of_windows (normalizedArmCost A I hfin)
    (fun i hi => (confidenceCost_pos hδ).trans_le
      (log_inv_le_normalizedArmCost A I hδ hA hfin i ((I.mem_suboptimal i).1 hi)))
    (fun a => markedSampleLaw (Coupling.raisedMean I.mean I.best a) a)
    (stoppingWindow A I hfin) ((A n).markedReturnedNotEvent I.two_le)
    (fun p => ((A n).markedArmSamples I.two_le p).toReal) hδ.1.le
    (fun i _ => measurableSet_stoppingWindow A I hfin i)
    ((A n).measurableSet_markedReturnedNotEvent I.two_le)
    (fun i _ => stoppingWindow_subset_returnedNotEvent A I hfin i) ?_ ?_ ?_ x hx
  · intro i hi p hp
    obtain ⟨hlo, hhi⟩ := stoppingWindow_count_bounds A I hfin i hp
    refine ⟨hlo, ?_⟩
    rw [mul_right_comm 16, mul_assoc, weight_mul_normalizedArmCost A I hfin hi]
    exact hhi
  · intro a ha
    exact marked_tied_returnedNotEvent_le A I a ((I.mem_suboptimal a).1 ha)
      (by have := hδ.2; linarith) hA
  · intro a _ d hd hgap
    exact stoppingWindow_transfer A I hfin d a hgap
      (stoppingWindow_source_prob_gt_half A I hδ hA hfin d ((I.mem_suboptimal d).1 hd))

/-- The finite-cost real form of B.1. The finiteness proof is explicit so the
conversion to `toReal` never turns an infinite expected runtime into zero. -/
theorem permutationAverage_entropy_lower_bound_real (A : Algorithm) {n : ℕ}
    (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) (hA : DeltaCorrect A δ)
    (hfin : permutationAverage A I ≠ ⊤) :
    I.hardness * (Real.log δ⁻¹ + I.gapEntropy) / 5 ≤
      (permutationAverage A I).toReal := by
  apply I.permutation_lower_bound_of_scale_count A hfin hδ.1 hδ.2
  · intro i hi
    exact log_inv_le_normalizedArmCost A I hδ hA hfin i ((I.mem_suboptimal i).1 hi)
  · exact representative_scale_count A I hδ hA hfin

/-- Every globally correct original algorithm pays the entropy lower bound on
average over all label permutations, including when its expected cost is infinite. -/
theorem permutationAverage_entropy_lower_bound (A : Algorithm) {n : ℕ}
    (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) (hA : DeltaCorrect A δ) :
    ENNReal.ofReal (entropyCost I δ / 5) ≤ permutationAverage A I := by
  by_cases hfin : permutationAverage A I = ⊤
  · simp [hfin]
  · rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal
      (permutationAverage_entropy_lower_bound_real A I hδ hA hfin)

/-- Manuscript Theorem B.1, with its exact universal coefficient `1/5`.
This is an unconditional theorem about the actual benchmark defined in Problem.lean. -/
theorem benchmark_entropy_lower_bound {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) :
    ENNReal.ofReal (I.hardness * (Real.log δ⁻¹ + I.gapEntropy) / 5) ≤ benchmark I δ := by
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  exact permutationAverage_entropy_lower_bound A I hδ hA

/-- The lower half of Chen–Li Conjecture 3.5 holds with the same constant for
every arm count, admissible instance, and confidence level. -/
theorem uniform_gap_entropy_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, ValidConfidence δ → ∀ (n : ℕ) (I : Instance n),
      ENNReal.ofReal (c * entropyCost I δ) ≤ benchmark I δ := by
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro δ hδ n I
  convert benchmark_entropy_lower_bound I hδ using 1
  congr 1
  unfold entropyCost confidenceCost
  ring

end GapEntropy
