import GapEntropy.Instance
import GapEntropy.Entropy

/-!
# Entropy facts for the actual dyadic gap profile

This connects the finite entropy library to Definition 3.3 and the optimal
confidence-allocation calculation in §4 of the original open problem.
The Kraft hypothesis needed by the statistical lower bound remains explicit.
-/

open scoped BigOperators

namespace GapEntropy.Instance

variable {n : ℕ} (I : Instance n)

theorem gapEntropy_eq_finiteEntropy :
    I.gapEntropy = finiteEntropy I.occupiedBuckets I.bucketMass := rfl

theorem gapEntropy_le_log_bucket_count :
    I.gapEntropy ≤ Real.log I.occupiedBuckets.card :=
  finiteEntropy_le_log_card I.occupiedBuckets I.bucketMass
    (fun k _ => I.bucketMass_nonneg k) I.sum_bucketMass

theorem gapEntropy_zero_of_one_bucket (h : I.occupiedBuckets.card = 1) :
    I.gapEntropy = 0 := by
  have hb := I.gapEntropy_le_log_bucket_count
  rw [h] at hb
  simp only [Nat.cast_one, Real.log_one] at hb
  exact le_antisymm hb I.gapEntropy_nonneg

theorem confidence_allocation_sum (δ : ℝ) :
    ∑ k ∈ I.occupiedBuckets, δ * I.groupHardness k / I.hardness = δ := by
  simpa only [I.sum_groupHardness] using
    proportional_allocation_sum I.occupiedBuckets I.groupHardness δ
      (by rw [I.sum_groupHardness]; exact I.hardness_pos.ne')

theorem confidence_allocation_cost {δ : ℝ} (hδ : δ ≠ 0) :
    (∑ k ∈ I.occupiedBuckets,
      I.groupHardness k * Real.log (δ * I.groupHardness k / I.hardness)⁻¹) =
      I.hardness * (Real.log δ⁻¹ + I.gapEntropy) := by
  simpa only [I.sum_groupHardness, gapEntropy, finiteEntropy, bucketMass] using
    weighted_allocation_cost_identity I.occupiedBuckets I.groupHardness δ
      (by rw [I.sum_groupHardness]; exact I.hardness_pos.ne') hδ

theorem confidence_allocation_lower_bound {δ : ℝ} (hδ : 0 < δ) (α : ℕ → ℝ)
    (hα : ∀ k ∈ I.occupiedBuckets, 0 < α k)
    (hbudget : ∑ k ∈ I.occupiedBuckets, α k ≤ δ) :
    I.hardness * (Real.log δ⁻¹ + I.gapEntropy) ≤
      ∑ k ∈ I.occupiedBuckets, I.groupHardness k * Real.log (α k)⁻¹ := by
  simpa only [I.sum_groupHardness, gapEntropy, finiteEntropy, bucketMass] using
    weighted_allocation_cost_lower_bound I.occupiedBuckets I.groupHardness α δ
      (fun k _ => I.groupHardness_nonneg k) (by rw [I.sum_groupHardness]; exact I.hardness_pos)
      hδ hα hbudget

/-- Equation (B.15), conditional on the probabilistic scale-packing/Kraft bound. -/
theorem gapEntropy_le_of_kraft (a : ℕ → ℝ)
    (hkraft : ∑ k ∈ I.occupiedBuckets, Real.exp (-(4 * a k)) ≤ 1) :
    I.gapEntropy ≤ 4 * ∑ k ∈ I.occupiedBuckets, I.bucketMass k * a k :=
  finiteEntropy_le_of_kraft I.occupiedBuckets I.bucketMass a 4
    (fun k _ => I.bucketMass_nonneg k) I.sum_bucketMass hkraft

end GapEntropy.Instance
