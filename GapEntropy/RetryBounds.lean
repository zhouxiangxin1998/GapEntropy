import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Unconditional costs of fresh-attempt streams

These integral identities count all trajectories, including errors and aborts.
Their reach-probability premises must be established by the actual algorithm's
fresh-attempt construction; no independence is inferred merely from the notation.
The exact arithmetic-geometric sum is the estimate used in Appendix C.3.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace GapEntropy

theorem geometric_reach_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : ℕ → Set Ω) (r : ℝ≥0∞)
    (hstep : ∀ t, μ (R (t + 1)) ≤ r * μ (R t)) :
    ∀ t, μ (R t) ≤ r ^ t := by
  intro t
  induction t with
  | zero => simpa only [pow_zero] using prob_le_one
  | succ t ih =>
      exact (hstep t).trans (by simpa only [pow_succ'] using mul_le_mul' le_rfl ih)

/-- Tonelli plus deterministic per-attempt caps; neither expected runtime nor
almost-sure termination is assumed in this inequality. -/
theorem expected_attempt_cost_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℕ → Set Ω) (hR : ∀ t, MeasurableSet (R t))
    (cost : ℕ → Ω → ℝ≥0∞) (hcost : ∀ t, Measurable (cost t))
    (cap : ℕ → ℝ≥0∞)
    (hzero : ∀ t ω, ω ∉ R t → cost t ω = 0)
    (hcap : ∀ t ω, ω ∈ R t → cost t ω ≤ cap t) :
    (∫⁻ ω, ∑' t, cost t ω ∂μ) ≤ ∑' t, cap t * μ (R t) := by
  rw [lintegral_tsum (fun t => (hcost t).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro t
  calc
    (∫⁻ ω, cost t ω ∂μ) ≤ ∫⁻ ω, (R t).indicator (fun _ => cap t) ω ∂μ := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ R t
      · simpa only [Set.indicator_of_mem hω] using hcap t ω hω
      · simp only [Set.indicator_of_notMem hω, hzero t ω hω]
        exact le_rfl
    _ = cap t * μ (R t) := lintegral_indicator_const (hR t) _

theorem hasSum_retry_weights (A B : ℝ) :
    HasSum (fun t : ℕ => (1 / 2 : ℝ) ^ t * (A + (t + 2) * B)) (2 * A + 6 * B) := by
  have h₀ := hasSum_geometric_two
  have h₁ : HasSum (fun t : ℕ => (t : ℝ) * (1 / 2 : ℝ) ^ t) 2 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) using 1
    norm_num
  have h := (h₀.mul_left A).add ((h₁.mul_right B).add (h₀.mul_left (2 * B)))
  convert! h using 1
  · ext t
    ring
  · ring

/-- Exact unconditional expectation bound for caps growing linearly in attempt
index and a geometric reach tail, as in the target-profile globalization. -/
theorem expected_retry_cost_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℕ → Set Ω) (hR : ∀ t, MeasurableSet (R t))
    (cost : ℕ → Ω → ℝ≥0∞) (hcost : ∀ t, Measurable (cost t))
    {C A B : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hzero : ∀ t ω, ω ∉ R t → cost t ω = 0)
    (hcap : ∀ t ω, ω ∈ R t → cost t ω ≤ ENNReal.ofReal (C * (A + (t + 2) * B)))
    (hreach : ∀ t, μ (R t) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ t)) :
    (∫⁻ ω, ∑' t, cost t ω ∂μ) ≤ ENNReal.ofReal (C * (2 * A + 6 * B)) := by
  apply (expected_attempt_cost_le μ R hR cost hcost _ hzero hcap).trans
  calc
    (∑' t : ℕ, ENNReal.ofReal (C * (A + (t + 2) * B)) * μ (R t)) ≤
        ∑' t : ℕ, ENNReal.ofReal (C * ((1 / 2 : ℝ) ^ t * (A + (t + 2) * B))) := by
      apply ENNReal.tsum_le_tsum
      intro t
      apply (mul_le_mul' le_rfl (hreach t)).trans_eq
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C * (A + ((t : ℝ) + 2) * B))]
      congr 1
      ring
    _ = ENNReal.ofReal C *
        ∑' t : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ t * (A + (t + 2) * B)) := by
      simp only [ENNReal.ofReal_mul hC, ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal C * ENNReal.ofReal (2 * A + 6 * B) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity)
        (hasSum_retry_weights A B).summable, (hasSum_retry_weights A B).tsum_eq]
    _ = _ := (ENNReal.ofReal_mul hC).symm

noncomputable def retryConfidence (δ : ℝ) (t : ℕ) : ℝ := δ * (1 / 2 : ℝ) ^ (t + 2)

theorem retryConfidence_pos {δ : ℝ} (hδ : 0 < δ) (t : ℕ) : 0 < retryConfidence δ t := by
  unfold retryConfidence
  positivity

theorem log_inv_retryConfidence {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    Real.log (retryConfidence δ t)⁻¹ = Real.log δ⁻¹ + (t + 2) * Real.log 2 := by
  rw [retryConfidence, Real.log_inv,
    Real.log_mul hδ.ne' (by positivity : (1 / 2 : ℝ) ^ (t + 2) ≠ 0), Real.log_pow,
    one_div, Real.log_inv, Real.log_inv]
  push_cast
  ring

theorem hasSum_retryConfidence (δ : ℝ) : HasSum (retryConfidence δ) (δ / 2) := by
  have h := hasSum_geometric_two.mul_left (δ / 4)
  convert! h using 1
  · ext t
    simp only [retryConfidence, pow_add]
    ring
  · ring

theorem sum_retryConfidence (δ : ℝ) : ∑' t, retryConfidence δ t = δ / 2 :=
  (hasSum_retryConfidence δ).tsum_eq

end GapEntropy
