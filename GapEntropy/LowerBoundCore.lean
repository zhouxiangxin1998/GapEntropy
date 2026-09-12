import GapEntropy.Profile
import GapEntropy.KraftCounting
import GapEntropy.IntervalPacking

/-!
# Deterministic conclusion of the original-instance lower-bound argument

This file composes the scale-counting bound (B.13), Kraft bound (B.14), Gibbs
step (B.15), and final `1/5` combination for the actual gap profile.

It is intentionally conditional on the representative costs and scale-counting
hypotheses. The algorithmic symmetrization, tied-law coupling and stopping-window
construction that must establish those hypotheses remain separate obligations.
Theorems here are not a proof of the benchmark lower bound by themselves.
-/

open scoped BigOperators Classical

namespace GapEntropy.Instance

variable {n : ℕ} (I : Instance n)

/-- The complete algebraic/counting end of Appendix B, with the statistical
representative-cost and scale-counting obligations stated explicitly. -/
theorem lower_bound_of_scale_count {T δ : ℝ} (a : ℕ → ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10)
    (hconfidence : ∀ k ∈ I.occupiedBuckets, Real.log δ⁻¹ ≤ a k)
    (hcost : I.hardness * (∑ k ∈ I.occupiedBuckets, I.bucketMass k * a k) ≤ T)
    (hcount : ∀ x : ℝ, 1 ≤ x →
      ((I.occupiedBuckets.filter fun k => a k ≤ x).card : ℝ) ≤
        4 * δ * (Real.log (1600 * x) / Real.log 4 + 2) * Real.exp (2 * x)) :
    I.hardness * (Real.log δ⁻¹ + I.gapEntropy) / 5 ≤ T := by
  have hkraft := kraft_sum_lt_one_of_scale_count I.occupiedBuckets a hδ0 hδ1 hconfidence hcount
  have hEntropy := I.gapEntropy_le_of_kraft a hkraft.le
  have hL : Real.log δ⁻¹ ≤ ∑ k ∈ I.occupiedBuckets, I.bucketMass k * a k := by
    calc
      Real.log δ⁻¹ = ∑ k ∈ I.occupiedBuckets, I.bucketMass k * Real.log δ⁻¹ := by
        rw [← Finset.sum_mul, I.sum_bucketMass, one_mul]
      _ ≤ ∑ k ∈ I.occupiedBuckets, I.bucketMass k * a k :=
        Finset.sum_le_sum (fun k hk =>
          mul_le_mul_of_nonneg_left (hconfidence k hk) (I.bucketMass_nonneg k))
  apply confidence_entropy_fifth
  · exact (mul_le_mul_of_nonneg_left hL I.hardness_pos.le).trans hcost
  · have hE := mul_le_mul_of_nonneg_left hEntropy I.hardness_pos.le
    linarith

end GapEntropy.Instance
