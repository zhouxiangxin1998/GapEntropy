import GapEntropy.Entropy

/-!
# Finite pushforward entropy and the entropy of mixtures

The joint entropy chain rule is proved using mathlib's `Real.negMulLog_mul`.
The entropy inequality for a pushforward is proved fiberwise from log monotonicity.
Neither fact is assumed as an input to the later work-envelope proof.
-/

noncomputable section
open scoped BigOperators

namespace GapEntropy

variable {ι κ : Type*}

/-- Combining nonnegative masses into one atom cannot increase their entropy contribution. -/
theorem entropy_sum_le (s : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) :
    (∑ i ∈ s, p i) * Real.log (∑ i ∈ s, p i)⁻¹ ≤ finiteEntropy s p := by
  rw [Finset.sum_mul, finiteEntropy]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h0 : p i = 0
  · simp [h0]
  have hpos : 0 < p i := lt_of_le_of_ne (hp i hi) (Ne.symm h0)
  have hle : p i ≤ ∑ j ∈ s, p j := Finset.single_le_sum hp hi
  have hlog := Real.log_le_log hpos hle
  simp only [Real.log_inv]
  nlinarith

/-- The entropy of a finite deterministic pushforward is at most the original entropy.
The masses need not sum to one for this comparison. -/
theorem finiteEntropy_pushforward_le [DecidableEq κ] (s : Finset ι) (u : Finset κ)
    (f : ι → κ) (p : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hf : ∀ i ∈ s, f i ∈ u) :
    finiteEntropy u (fun k => ∑ i ∈ s.filter (fun i => f i = k), p i) ≤ finiteEntropy s p := by
  calc
    _ ≤ ∑ k ∈ u, finiteEntropy (s.filter (fun i => f i = k)) p := by
      apply Finset.sum_le_sum
      intro k _
      exact entropy_sum_le _ p (fun i hi => hp i (Finset.mem_filter.mp hi).1)
    _ = finiteEntropy s p := Finset.sum_fiberwise_of_maps_to hf
      (fun i => p i * Real.log (p i)⁻¹)

theorem finiteEntropy_filter (s : Finset ι) (p : ι → Prop) [DecidablePred p] (w : ι → ℝ) :
    finiteEntropy s (fun i => if p i then w i else 0) = finiteEntropy (s.filter p) w := by
  rw [finiteEntropy, finiteEntropy, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The chain decomposition of a finite joint distribution `r_i c_{i,k}`. -/
theorem finiteEntropy_joint_chain (s : Finset ι) (u : Finset κ)
    (r : ι → ℝ) (c : ι → κ → ℝ) (hc : ∀ i ∈ s, ∑ k ∈ u, c i k = 1) :
    (∑ i ∈ s, finiteEntropy u (fun k => r i * c i k)) =
      finiteEntropy s r + ∑ i ∈ s, r i * finiteEntropy u (c i) := by
  simp_rw [finiteEntropy_eq_sum_negMulLog, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i hi, one_mul]

/-- Mixing distributions costs at most source entropy plus average conditional entropy. -/
theorem finiteEntropy_mixture_le (s : Finset ι) (u : Finset κ)
    (r : ι → ℝ) (c : ι → κ → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (hc : ∀ i ∈ s, ∀ k ∈ u, 0 ≤ c i k)
    (hcsum : ∀ i ∈ s, ∑ k ∈ u, c i k = 1) :
    finiteEntropy u (fun k => ∑ i ∈ s, r i * c i k) ≤
      finiteEntropy s r + ∑ i ∈ s, r i * finiteEntropy u (c i) := by
  calc
    _ ≤ ∑ k ∈ u, finiteEntropy s (fun i => r i * c i k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact entropy_sum_le s _ (fun i hi => mul_nonneg (hr i hi) (hc i hi k hk))
    _ = ∑ i ∈ s, finiteEntropy u (fun k => r i * c i k) := Finset.sum_comm
    _ = _ := finiteEntropy_joint_chain s u r c hcsum

end GapEntropy
