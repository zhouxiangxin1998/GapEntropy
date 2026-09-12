import GapEntropy.AttemptProbability
import GapEntropy.RetryExperiment

/-!
# Canonical target-profile retry experiment (C.3)

Each attempt is the actual finite fresh Gaussian experiment of C.2. The outer
product provides fresh attempts. Costs are charged on the actual reach events,
including aborts and errors. This is a statistical experiment; its `Policy`
embedding is a separate obligation.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace GapEntropy

instance optionFinMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (Option (Fin n)) :=
  ⟨fun _ => trivial⟩

namespace AttemptExperiment
open TargetAttempt
variable {n : ℕ}

theorem totalCost_measurable (I J : Instance n) (ε : ℝ) :
    Measurable (fun ω : Space I ε => totalCost I ε (loopOracle I J ε ω)) := by
  have hlo (k r : ℕ) : Measurable (fun ω : Space I ε => loopCost I ε (loopOracle I J ε ω) k r) := by
    let charge : Option (Finset (Fin n)) → ℕ := fun st => match st with
      | none => 0
      | some S => EliminationTape.declaredCost S.card (I.targetTolerance k) (I.callConfidence ε k r)
    exact (measurable_of_finite charge).comp (request_measurable I J ε (.loop k r))
  have hfi : Measurable (fun ω : Space I ε => finalCost I ε (loopOracle I J ε ω)) := by
    let charge : Option (Finset (Fin n)) → ℕ := fun st => match st with
      | none => 0
      | some S => EliminationTape.declaredCost S.card (I.targetTolerance I.lastBucket) (ε / 2)
    exact (measurable_of_finite charge).comp (request_measurable I J ε .final)
  exact (Finset.measurable_sum _ (fun k _ => Finset.measurable_sum _ (fun r _ => hlo k r))).add hfi

theorem universal_incorrect_measure_le (I J : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    law I J ε {ω | response I J ε ω ≠ none ∧ response I J ε ω ≠ some J.best} ≤
      ENNReal.ofReal ε := by
  have he : {ω | response I J ε ω ≠ none ∧ response I J ε ω ≠ some J.best} =
      {ω | ∃ a, response I J ε ω = some a ∧ a ≠ J.best} := by
    ext ω
    cases h : response I J ε ω <;> simp [h]
  rw [he, ← ofReal_measureReal (μ := law I J ε)]
  exact ENNReal.ofReal_le_ofReal (universal_incorrect_le I J hε hε10)

theorem target_abort_measure_le (I : Instance n) (π : Equiv.Perm (Fin n)) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    law I (I.permute π) ε {ω | response I (I.permute π) ε ω = none} ≤ ENNReal.ofReal ε := by
  apply (measure_mono (t := {ω | response I (I.permute π) ε ω ≠ some (I.permute π).best}) ?_).trans
  · rw [← ofReal_measureReal (μ := law I (I.permute π) ε)]
    exact ENNReal.ofReal_le_ofReal (target_failure_le I π hε hε10)
  · intro ω hω
    change response I (I.permute π) ε ω = none at hω
    simp only [Set.mem_ofPred_eq, hω, ne_eq, reduceCtorEq, not_false_eq_true]

end AttemptExperiment

namespace TargetRetry
variable {n : ℕ}

abbrev AttemptSpace (I : Instance n) (δ : ℝ) (t : ℕ) :=
  AttemptExperiment.Space I (retryConfidence δ t)

abbrev Space (I : Instance n) (δ : ℝ) := ∀ t, AttemptSpace I δ t

def attemptLaw (I J : Instance n) (δ : ℝ) (t : ℕ) : Measure (AttemptSpace I δ t) :=
  AttemptExperiment.law I J (retryConfidence δ t)

instance (I J : Instance n) (δ : ℝ) (t : ℕ) : IsProbabilityMeasure (attemptLaw I J δ t) := by
  unfold attemptLaw
  infer_instance

def answer (I J : Instance n) (δ : ℝ) (t : ℕ) : AttemptSpace I δ t → Option (Fin n) :=
  AttemptExperiment.response I J (retryConfidence δ t)

theorem answer_measurable (I J : Instance n) (δ : ℝ) (t : ℕ) : Measurable (answer I J δ t) :=
  AttemptExperiment.response_measurable I J _

def law (I J : Instance n) (δ : ℝ) : Measure (Space I δ) := RetryExperiment.law (attemptLaw I J δ)

instance (I J : Instance n) (δ : ℝ) : IsProbabilityMeasure (law I J δ) := by
  unfold law
  infer_instance

def incorrect (I J : Instance n) (δ : ℝ) : Set (Space I δ) :=
  RetryExperiment.incorrect (answer I J δ) J.best

def terminates (I J : Instance n) (δ : ℝ) : Set (Space I δ) :=
  RetryExperiment.terminates (answer I J δ)

def cost (I J : Instance n) (δ : ℝ) (t : ℕ) (ω : AttemptSpace I δ t) : ℝ≥0∞ :=
  (TargetAttempt.totalCost I (retryConfidence δ t)
    (AttemptExperiment.loopOracle I J (retryConfidence δ t) ω) : ℝ≥0∞)

theorem cost_measurable (I J : Instance n) (δ : ℝ) (t : ℕ) : Measurable (cost I J δ t) :=
  (measurable_of_countable (fun x : ℕ => (x : ℝ≥0∞))).comp
    (AttemptExperiment.totalCost_measurable I J _)

def totalCost (I J : Instance n) (δ : ℝ) (ω : Space I δ) : ℝ≥0∞ :=
  ∑' t, RetryExperiment.chargedCost (answer I J δ) (cost I J δ) t ω

theorem totalCost_measurable (I J : Instance n) (δ : ℝ) : Measurable (totalCost I J δ) :=
  Measurable.tsum (fun t => RetryExperiment.measurable_chargedCost
    (answer I J δ) (answer_measurable I J δ) (cost I J δ) (cost_measurable I J δ) t)

theorem confidence_le {δ : ℝ} (hδ : 0 < δ) (t : ℕ) : retryConfidence δ t ≤ δ := by
  unfold retryConfidence
  exact mul_le_of_le_one_right hδ.le (pow_le_one₀ (by norm_num) (by norm_num))

theorem confidence_le_tenth {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ ≤ 1 / 10) (t : ℕ) :
    retryConfidence δ t ≤ 1 / 10 := (confidence_le hδ t).trans hδ10

/-- C.3: every actual input has stream wrong-return probability at most δ/2. -/
theorem incorrect_le (I J : Instance n) {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ ≤ 1 / 10) :
    law I J δ (incorrect I J δ) ≤ ENNReal.ofReal (δ / 2) := by
  exact RetryExperiment.measure_incorrect_le_retryConfidence (attemptLaw I J δ)
    (answer I J δ) (answer_measurable I J δ) J.best hδ (fun t =>
      AttemptExperiment.universal_incorrect_measure_le I J (retryConfidence_pos hδ t)
        (confidence_le_tenth hδ hδ10 t))

theorem target_abort_le_half (I : Instance n) (π : Equiv.Perm (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ ≤ 1 / 10) (t : ℕ) :
    attemptLaw I (I.permute π) δ t {x | answer I (I.permute π) δ t x = none} ≤ 1 / 2 := by
  apply (AttemptExperiment.target_abort_measure_le I π (retryConfidence_pos hδ t)
    (confidence_le_tenth hδ hδ10 t)).trans
  have h : retryConfidence δ t ≤ (1 / 2 : ℝ) := (confidence_le_tenth hδ hδ10 t).trans (by norm_num)
  simpa using ENNReal.ofReal_le_ofReal h

/-- The target-labeling stream answers almost surely, proved from its independent
attempt coordinates and the actual C.2 abort bound. -/
theorem target_almostSurely_terminates (I : Instance n) (π : Equiv.Perm (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ ≤ 1 / 10) :
    ∀ᵐ ω ∂law I (I.permute π) δ, ω ∈ terminates I (I.permute π) δ :=
  RetryExperiment.almostSurely_terminates (attemptLaw I (I.permute π) δ)
    (answer I (I.permute π) δ) (answer_measurable I (I.permute π) δ)
    (by norm_num : (1 / 2 : ℝ≥0∞) < 1) (target_abort_le_half I π hδ hδ10)

theorem cost_le_cap (I J : Instance n) {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ ≤ 1 / 10)
    (t : ℕ) (ω : AttemptSpace I δ t) :
    cost I J δ t ω ≤ ENNReal.ofReal
      ((1000000000000 * I.hardness) *
        ((Real.log δ⁻¹ + I.gapEntropy) + (t + 2) * Real.log 2)) := by
  have h := AttemptExperiment.declaredCost_le I J (retryConfidence_pos hδ t)
    (confidence_le_tenth hδ hδ10 t) ω
  rw [log_inv_retryConfidence hδ] at h
  have he : Real.log δ⁻¹ + ((t : ℝ) + 2) * Real.log 2 + I.gapEntropy =
      Real.log δ⁻¹ + I.gapEntropy + ((t : ℝ) + 2) * Real.log 2 := by ring
  rw [he] at h
  simpa only [cost, ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h

/-- Unconditional expected declared samples, including all aborts and errors. -/
theorem target_expected_cost_le (I : Instance n) (π : Equiv.Perm (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (hδ10 : δ ≤ 1 / 10) :
    (∫⁻ ω, totalCost I (I.permute π) δ ω ∂law I (I.permute π) δ) ≤
      ENNReal.ofReal (8000000000000 * I.hardness * (Real.log δ⁻¹ + I.gapEntropy)) := by
  have hL : 1 ≤ Real.log δ⁻¹ := TargetAttempt.one_le_log_inv hδ (by linarith)
  have hE := I.gapEntropy_nonneg
  have hB : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB1 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := RetryExperiment.expected_cost_le_geometric (attemptLaw I (I.permute π) δ)
    (answer I (I.permute π) δ) (answer_measurable I (I.permute π) δ)
    (cost I (I.permute π) δ) (cost_measurable I (I.permute π) δ)
    (C := 1000000000000 * I.hardness) (A := Real.log δ⁻¹ + I.gapEntropy) (B := Real.log 2)
    (by positivity [I.hardness_pos]) (by linarith) hB
    (cost_le_cap I (I.permute π) hδ hδ10) (target_abort_le_half I π hδ hδ10)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hm := mul_le_mul_of_nonneg_left (show
      2 * (Real.log δ⁻¹ + I.gapEntropy) + 6 * Real.log 2 ≤
        8 * (Real.log δ⁻¹ + I.gapEntropy) by linarith)
    (show 0 ≤ 1000000000000 * I.hardness by positivity [I.hardness_pos])
  nlinarith

end TargetRetry
end GapEntropy
