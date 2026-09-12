import GapEntropy.RepresentativeCosts

/-!
# Logarithmic geometry of the actual stopping windows

The original dyadic bucket convention puts `log₄(Δ⁻²)` in `(k-1,k]`,
including the boundary gap one. The sample-count window
`Δ⁻²/100 ≤ N ≤ 16 α Δ⁻²` is contained in a closed logarithmic interval
of length `log₄(1600 α)`. These are the hypotheses used by the bounded
overlap proof of B.13.
-/

open scoped BigOperators Classical

namespace GapEntropy

theorem log_four_pos : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)

theorem log_four_eq_two_log_two : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
    Real.log_pow (2 : ℝ) 2

noncomputable def windowLength (x : ℝ) : ℝ := Real.log (1600 * x) / Real.log 4

theorem windowLength_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ windowLength x :=
  div_nonneg (Real.log_nonneg (by linarith)) log_four_pos.le

theorem windowLength_mono {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    windowLength a ≤ windowLength x := by
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (by positivity) (by linarith)) log_four_pos.le

theorem sample_window_implies_log_window {w α N : ℝ} (hw : 0 < w) (hα : 0 < α)
    (hlo : w / 100 ≤ N) (hhi : N ≤ 16 * α * w) :
    Real.log w / Real.log 4 ≤ Real.log (100 * N) / Real.log 4 ∧
      Real.log (100 * N) / Real.log 4 ≤ Real.log w / Real.log 4 + windowLength α := by
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hlo
  have hl := Real.log_le_log hw (show w ≤ 100 * N by linarith)
  have hu := Real.log_le_log (by positivity : 0 < 100 * N)
    (show 100 * N ≤ w * (1600 * α) by nlinarith)
  rw [Real.log_mul hw.ne' (by positivity : 1600 * α ≠ 0)] at hu
  refine ⟨div_le_div_of_nonneg_right hl log_four_pos.le, ?_⟩
  simpa only [windowLength, add_div] using
    div_le_div_of_nonneg_right hu log_four_pos.le

namespace Instance

variable {n : ℕ} (I : Instance n)

noncomputable def windowStart (i : Fin n) : ℝ := Real.log (I.weight i) / Real.log 4

theorem log_weight (i : Fin n) : Real.log (I.weight i) = -(2 * Real.log (I.gap i)) := by
  simp [weight, Real.log_inv, Real.log_pow]

theorem windowStart_in_bucket {i : Fin n} (hi : i ∈ I.suboptimal) :
    (I.bucket i : ℝ) - 1 < I.windowStart i ∧ I.windowStart i ≤ I.bucket i := by
  have hd := I.gap_pos ((I.mem_suboptimal i).1 hi)
  obtain ⟨hl, hu⟩ := I.bucket_bounds hi
  have hp : 0 < (1 / 2 : ℝ) ^ I.bucket i := by positivity
  have hll := Real.log_le_log hp hl
  have hlu := Real.log_lt_log hd hu
  have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [Real.log_pow, hh] at hll
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne', Real.log_pow, hh] at hlu
  unfold windowStart
  rw [I.log_weight]
  constructor
  · apply (lt_div_iff₀ log_four_pos).2
    rw [log_four_eq_two_log_two]
    nlinarith
  · apply (div_le_iff₀ log_four_pos).2
    rw [log_four_eq_two_log_two]
    nlinarith

theorem windowStart_costRepresentative (c : Fin n → ℝ) (k : ℕ)
    (hk : k ∈ I.occupiedBuckets) :
    (k : ℝ) - 1 < I.windowStart (I.costRepresentative c k hk) ∧
      I.windowStart (I.costRepresentative c k hk) ≤ k := by
  simpa only [I.bucket_costRepresentative] using
    I.windowStart_in_bucket (I.costRepresentative_suboptimal c k hk)

/-- Direct conversion of the normalized source-cost window to the exact
geometric interval used in the common-null packing argument. -/
theorem normalized_sample_window_implies_log_window (A : Algorithm)
    (h : permutationAverage A I ≠ ⊤) {i : Fin n} (hi : i ∈ I.suboptimal) {N : ℝ}
    (hα : 0 < normalizedArmCost A I h i)
    (hlo : I.weight i / 100 ≤ N)
    (hhi : N ≤ 16 * (permutationArmSamples A I i).toReal) :
    I.windowStart i ≤ Real.log (100 * N) / Real.log 4 ∧
      Real.log (100 * N) / Real.log 4 ≤
        I.windowStart i + windowLength (normalizedArmCost A I h i) := by
  apply sample_window_implies_log_window (I.weight_pos hi) hα hlo
  rw [mul_right_comm 16, mul_assoc, weight_mul_normalizedArmCost A I h hi]
  exact hhi

end Instance

end GapEntropy
