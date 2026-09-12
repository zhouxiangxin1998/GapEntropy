import GapEntropy.FixedCapRetryCost

/-!
# Genuine Gaussian error and expectation bounds for the retry policy

The premises are properties of the supplied finite interactive procedures under
their actual Gaussian block laws. The stream itself is a constructed Policy;
its reach probabilities, output origin, and full sample accounting are proved.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.FixedCapRetry
variable {n : ℕ} (R : ℕ → BoundedProcedure n (Option (Fin n)))
  (hpos : ∀ j, 0 < (R j).budget)

local instance : MeasurableSingletonClass (Option (Fin n)) := ⟨fun _ => trivial⟩

theorem measure_reach_le_pow (mean : Fin n → ℝ) {r : ℝ≥0∞}
    (habort : ∀ j, GaussianBlocks.blockLaw mean (R j).budget
      {x | (R j).evaluate x = none} ≤ r) (j : ℕ) :
    sampleLawOfMeans mean (reach R hpos j) ≤ r ^ j := by
  rw [measure_reach_eq_prod, ← RetryExperiment.measure_reach
    (fun k => GaussianBlocks.blockLaw mean (R k).budget)
    (fun k => (R k).evaluate) (fun k => (R k).measurable_evaluate) j]
  exact RetryExperiment.measure_reach_le_pow _ _ (fun k => (R k).measurable_evaluate) habort j

/-- Global correctness needs only an incorrect-answer budget for each attempt;
there is no abort or termination requirement on an off-target input. -/
theorem wrong_return_measure_le (I : Instance n) (ε : ℕ → ℝ≥0∞)
    (hbad : ∀ j, GaussianBlocks.blockLaw I.mean (R j).budget
      {x | (R j).evaluate x ≠ none ∧ (R j).evaluate x ≠ some I.best} ≤ ε j) :
    sampleLaw I ((policy R hpos).returnedNotEvent I.two_le I.best) ≤ ∑' j, ε j := by
  have hsub : (policy R hpos).returnedNotEvent I.two_le I.best ⊆
      ⋃ j, {ω | answer R hpos j ω ≠ none ∧ answer R hpos j ω ≠ some I.best} := by
    rintro ω ⟨t, i, hi, ht⟩
    obtain ⟨j, hj⟩ := returned_imp_answer R hpos I.two_le ω i ⟨t, ht⟩
    exact Set.mem_iUnion.mpr ⟨j, by simp [hj], by simpa [hj] using hi⟩
  apply (measure_mono hsub).trans ((measure_iUnion_le _).trans _)
  apply ENNReal.tsum_le_tsum
  intro j
  have hm := GaussianBlocks.measurePreserving_rewardBlock I.mean ((schedule R hpos).start j)
    (R j).budget
  have hset : MeasurableSet {x | (R j).evaluate x ≠ none ∧ (R j).evaluate x ≠ some I.best} :=
    (((R j).measurable_evaluate.eq_const none).not.and
      ((R j).measurable_evaluate.eq_const (some I.best)).not).setOf
  change sampleLawOfMeans I.mean ((GaussianBlocks.rewardBlock ((schedule R hpos).start j)
    (R j).budget) ⁻¹' {x | (R j).evaluate x ≠ none ∧ (R j).evaluate x ≠ some I.best}) ≤ ε j
  rw [hm.measure_preimage hset.nullMeasurableSet]
  exact hbad j

/-- The source's geometric confidence schedule gives the actual Policy's δ/2
incorrect-return bound on every supplied instance. -/
theorem wrong_return_retryConfidence_le (I : Instance n) {δ : ℝ} (hδ : 0 < δ)
    (hbad : ∀ j, GaussianBlocks.blockLaw I.mean (R j).budget
      {x | (R j).evaluate x ≠ none ∧ (R j).evaluate x ≠ some I.best} ≤
        ENNReal.ofReal (retryConfidence δ j)) :
    sampleLaw I ((policy R hpos).returnedNotEvent I.two_le I.best) ≤ ENNReal.ofReal (δ / 2) := by
  apply (wrong_return_measure_le R hpos I _ hbad).trans_eq
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (retryConfidence_pos hδ j).le)
    (hasSum_retryConfidence δ).summable, sum_retryConfidence]

/-- Exact arithmetic-geometric expectation estimate for the actual retry Policy. -/
theorem expectedSamples_le_geometric (I : Instance n) {C A B : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcap : ∀ j, ((R j).budget : ℝ) ≤ C * (A + (j + 2) * B))
    (habort : ∀ j, GaussianBlocks.blockLaw I.mean (R j).budget
      {x | (R j).evaluate x = none} ≤ 1 / 2) :
    (policy R hpos).expectedSamples I ≤ ENNReal.ofReal (C * (2 * A + 6 * B)) := by
  apply (lintegral_mono (sampleCount_le_charges R hpos I.two_le)).trans
  apply expected_retry_cost_le (sampleLaw I) (reach R hpos) (measurableSet_reach R hpos)
    (cappedCharge R hpos) (measurable_cappedCharge R hpos) hC hA hB
  · intro j ω hω
    exact Set.indicator_of_notMem hω _
  · intro j ω hω
    simp only [cappedCharge, Set.indicator_of_mem hω]
    have h := ENNReal.ofReal_le_ofReal (hcap j)
    simpa only [ENNReal.ofReal_natCast] using h
  · intro j
    have h := measure_reach_le_pow R hpos I.mean habort j
    have he : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by simp
    rw [ENNReal.ofReal_pow (by positivity), he]
    exact h

theorem expectedSamples_ne_top (I : Instance n) {C A B : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcap : ∀ j, ((R j).budget : ℝ) ≤ C * (A + (j + 2) * B))
    (habort : ∀ j, GaussianBlocks.blockLaw I.mean (R j).budget
      {x | (R j).evaluate x = none} ≤ 1 / 2) :
    (policy R hpos).expectedSamples I ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (expectedSamples_le_geometric R hpos I hC hA hB hcap habort)

end GapEntropy.FixedCapRetry
