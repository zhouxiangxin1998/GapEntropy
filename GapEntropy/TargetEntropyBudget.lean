import GapEntropy.TargetProfile
import GapEntropy.MedianCost

/-!
# The A.5 entropy budget of the target profile

This module proves the elementary logarithmic estimates for the target's per-call confidences,
in particular `log(128 / (η · (1/2)^(r+1))) ≤ (r + 9) · log(1/η)` for `η ≤ 1/3`, and bounds the
series `Σ (r + 9) · (3/4)^r` by `48`. The weighted allocation identity of `WorkEntropy` rewrites
the sum of `scaleWork k · log(1/scaleConfidence ε k)` over scales as
`workEnvelope · (log(2/ε) + workEntropy)`. Absorbing the additive constant into `log(1/ε)` gives
the complete A.5 envelope: this sum is at most `200 · hardness · (log(1/ε) + gapEntropy)`.
-/

noncomputable section
open scoped BigOperators

namespace GapEntropy.TargetAttempt

theorem one_le_log_inv {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 1 / 3) : 1 ≤ Real.log a⁻¹ := by
  apply (Real.le_log_iff_exp_le (inv_pos.mpr ha)).mpr
  apply Real.exp_one_lt_three.le.trans
  rw [← one_div]
  exact (le_div_iff₀ ha).mpr (by linarith)

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h

theorem log_128_eq : Real.log (128 : ℝ) = 7 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 7
  norm_num at h
  exact h

theorem log_call_eq {η : ℝ} (hη : 0 < η) (r : ℕ) :
    Real.log (128 / (η * (1 / 2 : ℝ) ^ (r + 1))) =
      Real.log η⁻¹ + ((r : ℝ) + 8) * Real.log 2 := by
  rw [Real.log_div (by norm_num) (mul_ne_zero hη.ne' (pow_ne_zero _ (by norm_num))),
    Real.log_mul hη.ne' (pow_ne_zero _ (by norm_num)), Real.log_pow, log_128_eq]
  simp only [one_div, Real.log_inv, Nat.cast_add, Nat.cast_one]
  ring

theorem log_call_le {η : ℝ} (hη : 0 < η) (hη3 : η ≤ 1 / 3) (r : ℕ) :
    Real.log (128 / (η * (1 / 2 : ℝ) ^ (r + 1))) ≤
      ((r : ℝ) + 9) * Real.log η⁻¹ := by
  have hlog := one_le_log_inv hη hη3
  have htwo := log_two_le_one
  rw [log_call_eq hη]
  have hr : (0 : ℝ) ≤ r := by positivity
  nlinarith

theorem scale_series_le (R : ℕ) :
    (∑ r ∈ Finset.range R, ((r : ℝ) + 9) * (3 / 4 : ℝ) ^ r) ≤ 48 := by
  have hm := sum_le_hasSum (Finset.range R) (fun r _ => by positivity)
    (hasSum_coe_mul_geometric_of_norm_lt_one (r := (3 / 4 : ℝ)) (by norm_num))
  have hg := sum_le_hasSum (Finset.range R) (fun r _ => by positivity)
    (hasSum_geometric_of_norm_lt_one (ξ := (3 / 4 : ℝ)) (by norm_num))
  norm_num at hm hg
  simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

theorem entropyConstant_le_two : GapEntropy.WorkEnvelope.entropyConstant ≤ 2 := by
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  unfold GapEntropy.WorkEnvelope.entropyConstant
  linarith

variable {n : ℕ} (I : Instance n)

theorem scale_allocation_identity {ε : ℝ} (hε : 0 < ε) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹) =
      I.workEnvelope * (Real.log (ε / 2)⁻¹ + I.workEntropy) := by
  have h := GapEntropy.weighted_allocation_cost_identity
    (Finset.range (I.lastBucket + 1)) I.scaleWork (ε / 2)
    (by rw [← I.workEnvelope_eq_sum]; exact I.workEnvelope_pos.ne') (by positivity)
  rw [← I.workEnvelope_eq_sum] at h
  change _ = I.workEnvelope * (Real.log (ε / 2)⁻¹ + I.workEntropy) at h
  simpa only [Instance.scaleConfidence, Instance.workMass, mul_div_assoc] using h

/-- The complete A.5 entropy envelope, absorbing its additive constant into log(1/ε). -/
theorem profile_log_budget_le {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹) ≤
      200 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy) := by
  rw [scale_allocation_identity I hε]
  have hL := one_le_log_inv hε (by linarith)
  have hE := I.gapEntropy_nonneg
  have hH := I.hardness_pos
  have hW := I.hardness_le_workEnvelope_lt.2.le
  have hEnt := I.workEntropy_le
  have hC := entropyConstant_le_two
  have hlogeq : Real.log (ε / 2)⁻¹ = Real.log ε⁻¹ + Real.log 2 := by
    rw [inv_div, Real.log_div (by norm_num) hε.ne', Real.log_inv]
    ring
  rw [hlogeq]
  have hinside : Real.log ε⁻¹ + Real.log 2 + I.workEntropy ≤
      4 * Real.log ε⁻¹ + (32 / 3 : ℝ) * I.gapEntropy := by
    linarith [log_two_le_one]
  have hmul := mul_le_mul_of_nonneg_left hinside I.workEnvelope_pos.le
  have hmulW := mul_le_mul_of_nonneg_right hW
    (show 0 ≤ 4 * Real.log ε⁻¹ + (32 / 3 : ℝ) * I.gapEntropy by positivity)
  have hLE : 0 ≤ I.hardness * Real.log ε⁻¹ := by positivity
  have hHE : 0 ≤ I.hardness * I.gapEntropy := by positivity
  nlinarith

theorem final_log_le {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    Real.log (128 / (ε / 2)) ≤ 9 * Real.log ε⁻¹ := by
  have hL := one_le_log_inv hε (by linarith)
  have heq : (128 / (ε / 2) : ℝ) = 256 / ε := by ring
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 8
    norm_num at h
    exact h
  rw [heq, Real.log_div (by norm_num) hε.ne', h256, Real.log_inv]
  rw [Real.log_inv] at hL
  linarith [log_two_le_one]

end GapEntropy.TargetAttempt
