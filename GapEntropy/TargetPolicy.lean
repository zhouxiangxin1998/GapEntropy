import GapEntropy.ActualAttemptProbability
import GapEntropy.TargetRetry
import GapEntropy.FixedCapRetryBounds
import GapEntropy.Globalize

/-!
# The actual target-profile algorithm

The algorithm repeats padded finite target-profile attempts and interleaves the
result with the globally terminating fallback. Other arm counts use the fallback.
The construction and final correctness/complexity theorems are unconditional.
The intermediate composition lemmas are discharged by ActualAttemptProbability.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.TargetPolicy
variable {n : ℕ}

def attempts (I : Instance n) (δ : ℝ) (j : ℕ) : BoundedProcedure n (Option (Fin n)) :=
  AttemptProcedure.procedure I (retryConfidence δ j)

theorem attempt_budget_pos (I : Instance n) (δ : ℝ) (j : ℕ) :
    0 < (attempts I δ j).budget := AttemptProcedure.cap_pos I _

def stream (I : Instance n) (δ : ℝ) : Policy n :=
  FixedCapRetry.policy (attempts I δ) (attempt_budget_pos I δ)

def localPolicy (I : Instance n) (δ : ℝ) : Policy n :=
  Interleave.policy (stream I δ) (Fallback.policy n δ)

/-- The target appears only as a fixed algorithm parameter; the actual unknown
input means never enter a request rule. Other input sizes use the fallback. -/
def algorithm (I : Instance n) (δ : ℝ) : Algorithm := fun m =>
  if hm : m = n then hm.symm ▸ localPolicy I δ else Fallback.policy m δ

@[simp] theorem algorithm_at_target (I : Instance n) (δ : ℝ) :
    algorithm I δ n = localPolicy I δ := by simp [algorithm]

theorem local_expectedSamples_ne_top (I J : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (localPolicy I δ).expectedSamples J ≠ ⊤ :=
  Interleave.expectedSamples_ne_top_of_right _ _ J (Fallback.expectedSamples_ne_top J hδ hδ1)

theorem local_almostSurelyTerminates (I J : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (localPolicy I δ).AlmostSurelyTerminates J :=
  (localPolicy I δ).almostSurelyTerminates_of_expectedSamples_ne_top J
    (local_expectedSamples_ne_top I J hδ hδ1)

theorem local_success_of_stream_wrong_bound (I J : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbad : sampleLaw J ((stream I δ).returnedNotEvent J.two_le J.best) ≤ ENNReal.ofReal (δ / 2)) :
    ENNReal.ofReal (1 - δ) ≤ (localPolicy I δ).successProb J := by
  apply (localPolicy I δ).successProb_ge_of_wrong_return_le_of_almostSurelyTerminates
    J hδ.le (local_almostSurelyTerminates I J hδ hδ1)
  have h := Interleave.returnedNotEvent_measure_le (stream I δ) (Fallback.policy n δ) J hbad
    (Fallback.wrong_return_measure_le J hδ hδ1)
  have he : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  simpa only [localPolicy, he] using h

/-- Exact globalization step from actual per-attempt block error bounds. -/
theorem deltaCorrect_of_attempt_bounds (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (hbad : ∀ (J : Instance n) j,
      GaussianBlocks.blockLaw J.mean (attempts I δ j).budget
        {x | (attempts I δ j).evaluate x ≠ none ∧
          (attempts I δ j).evaluate x ≠ some J.best} ≤ ENNReal.ofReal (retryConfidence δ j)) :
    DeltaCorrect (algorithm I δ) δ := by
  intro m J
  have hδ1 : δ ≤ 1 := by have := hδ.2; linarith
  by_cases hm : m = n
  · subst m
    rw [algorithm_at_target]
    apply local_success_of_stream_wrong_bound I J hδ.1 hδ1
    exact FixedCapRetry.wrong_return_retryConfidence_le _ _ J hδ.1 (hbad J)
  · simp only [algorithm, dif_neg hm]
    exact (ENNReal.ofReal_le_ofReal (by linarith [hδ.1] : 1 - δ ≤ 1 - δ / 2)).trans
      (Fallback.successProb_ge J hδ.1 hδ1)

theorem algorithm_finite_expectation (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (m : ℕ) (J : Instance m) : (algorithm I δ m).expectedSamples J < ⊤ := by
  have hδ1 : δ ≤ 1 := by have := hδ.2; linarith
  by_cases hm : m = n
  · subst m
    rw [algorithm_at_target]
    exact (local_expectedSamples_ne_top I J hδ.1 hδ1).lt_top
  · simp only [algorithm, dif_neg hm]
    exact (Fallback.expectedSamples_ne_top J hδ.1 hδ1).lt_top

theorem attempt_budget_le (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) (j : ℕ) :
    ((attempts I δ j).budget : ℝ) ≤ (2000000000000 * I.hardness) *
      ((Real.log δ⁻¹ + I.gapEntropy) + (j + 2) * Real.log 2) := by
  have h := AttemptProcedure.cap_le_twice_realCap I (retryConfidence_pos hδ.1 j)
    (TargetRetry.confidence_le_tenth hδ.1 hδ.2.le j)
  rw [AttemptProcedure.realCap, log_inv_retryConfidence hδ.1] at h
  change (AttemptProcedure.cap I (retryConfidence δ j) : ℝ) ≤ _
  nlinarith

theorem stream_expectedSamples_le_of_abort_bounds (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (π : Equiv.Perm (Fin n))
    (habort : ∀ j, GaussianBlocks.blockLaw (I.permute π).mean (attempts I δ j).budget
      {x | (attempts I δ j).evaluate x = none} ≤ 1 / 2) :
    (stream I δ).expectedSamples (I.permute π) ≤
      ENNReal.ofReal (16000000000000 * entropyCost I δ) := by
  have hL : 1 ≤ Real.log δ⁻¹ := TargetAttempt.one_le_log_inv hδ.1 (by have := hδ.2; linarith)
  have hE := I.gapEntropy_nonneg
  have hB : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB1 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := FixedCapRetry.expectedSamples_le_geometric (attempts I δ) (attempt_budget_pos I δ)
    (I.permute π) (C := 2000000000000 * I.hardness)
    (A := Real.log δ⁻¹ + I.gapEntropy) (B := Real.log 2)
    (by positivity [I.hardness_pos]) (by linarith) hB (attempt_budget_le I hδ) habort
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hm := mul_le_mul_of_nonneg_left (show
      2 * (Real.log δ⁻¹ + I.gapEntropy) + 6 * Real.log 2 ≤
        8 * (Real.log δ⁻¹ + I.gapEntropy) by linarith)
    (show 0 ≤ 2000000000000 * I.hardness by positivity [I.hardness_pos])
  unfold entropyCost confidenceCost
  nlinarith

theorem one_le_entropyCost (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    1 ≤ entropyCost I δ := by
  have hH := I.one_le_twoArmHardness.trans I.twoArmHardness_le_hardness
  have hL : 1 ≤ Real.log δ⁻¹ := TargetAttempt.one_le_log_inv hδ.1 (by have := hδ.2; linarith)
  have hE := I.gapEntropy_nonneg
  change 1 ≤ I.hardness * (Real.log δ⁻¹ + I.gapEntropy)
  nlinarith

theorem target_expectedSamples_le_of_abort_bounds (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (π : Equiv.Perm (Fin n))
    (habort : ∀ j, GaussianBlocks.blockLaw (I.permute π).mean (attempts I δ j).budget
      {x | (attempts I δ j).evaluate x = none} ≤ 1 / 2) :
    (algorithm I δ n).expectedSamples (I.permute π) ≤
      ENNReal.ofReal (64000000000000 * entropyCost I δ) := by
  rw [algorithm_at_target]
  have h := Interleave.expectedSamples_le_left (stream I δ) (Fallback.policy n δ) (I.permute π)
  apply h.trans
  have hcost := stream_expectedSamples_le_of_abort_bounds I hδ π habort
  apply (add_le_add (mul_le_mul' le_rfl hcost) le_rfl).trans
  have hX := one_le_entropyCost I hδ
  have hX0 := (entropyCost_pos hδ I).le
  calc
    2 * ENNReal.ofReal (16000000000000 * entropyCost I δ) + 1 =
        ENNReal.ofReal (32000000000000 * entropyCost I δ + 1) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num),
        show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num,
        ← ENNReal.ofReal_add (by positivity) (by norm_num)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- The concrete target-profile algorithm is correct on every legal instance,
including all off-target profiles and arm counts. -/
theorem deltaCorrect (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    DeltaCorrect (algorithm I δ) δ := by
  apply deltaCorrect_of_attempt_bounds I hδ
  intro J j
  exact ActualAttempt.procedure_incorrect_le I J (retryConfidence_pos hδ.1 j)
    (TargetRetry.confidence_le_tenth hδ.1 hδ.2.le j)

/-- Proposition C.1: every labeling of the target has the uniform entropy bound
under the same concrete globally correct algorithm. All execution paths count. -/
theorem target_expectedSamples_le (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (π : Equiv.Perm (Fin n)) :
    (algorithm I δ n).expectedSamples (I.permute π) ≤
      ENNReal.ofReal (64000000000000 * entropyCost I δ) := by
  apply target_expectedSamples_le_of_abort_bounds I hδ π
  intro j
  apply (ActualAttempt.procedure_abort_le I π (retryConfidence_pos hδ.1 j)
    (TargetRetry.confidence_le_tenth hδ.1 hδ.2.le j)).trans
  have h : retryConfidence δ j ≤ (1 / 2 : ℝ) :=
    (TargetRetry.confidence_le_tenth hδ.1 hδ.2.le j).trans (by norm_num)
  simpa using ENNReal.ofReal_le_ofReal h

/-- Complete actual-algorithm witness for C.1. -/
theorem proposition_C1 (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    DeltaCorrect (algorithm I δ) δ ∧
      (∀ (m : ℕ) (J : Instance m), (algorithm I δ m).AlmostSurelyTerminates J ∧
        (algorithm I δ m).expectedSamples J < ⊤) ∧
      (∀ π : Equiv.Perm (Fin n), (algorithm I δ n).expectedSamples (I.permute π) ≤
        ENNReal.ofReal (64000000000000 * entropyCost I δ)) := by
  refine ⟨deltaCorrect I hδ, ?_, target_expectedSamples_le I hδ⟩
  intro m J
  have hfin := algorithm_finite_expectation I hδ m J
  exact ⟨(algorithm I δ m).almostSurelyTerminates_of_expectedSamples_ne_top J hfin.ne, hfin⟩

end GapEntropy.TargetPolicy
