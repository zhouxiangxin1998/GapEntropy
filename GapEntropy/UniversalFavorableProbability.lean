import GapEntropy.UniversalFavorableAggregation
import GapEntropy.UniversalReferenceHazard
import GapEntropy.UniversalFavorableTermination
import GapEntropy.UniversalPolicy

/-! Actual favorable-path probability and the unconditional large-attempt
abort bound. The controller, its real stored reference, and its fresh data are
all the actual procedures already constructed in the sampling model. -/
noncomputable section
open MeasureTheory
open scoped Classical ENNReal BigOperators
namespace GapEntropy.UniversalAttempt
open UniversalSevereProcess GaussianBlocks UniversalCapAnalysis
variable {n : ℕ}

theorem riskRate_eq_charges (c : Config) (r : ℕ) (ω : SampleSpace n) :
    riskRate c (choice c r ω) = ENNReal.ofReal
      (confidenceCharge c (stage c ω.2 r) / 4 + referenceCharge c (stage c ω.2 r)) := by
  unfold choice
  cases hs : stage c ω.2 r with
  | inl result => simp [choiceFromStage, riskRate, confidenceCharge, referenceCharge]
  | inr st =>
    rcases st with ⟨a, z⟩
    by_cases ha : a.Allowed c
    · by_cases he : a.entry = true
      · simp [choiceFromStage, ha, riskRate, callRisk, confidenceCharge, referenceCharge, he]
      · simp [choiceFromStage, ha, riskRate, callRisk, confidenceCharge, referenceCharge, he]
    · simp [choiceFromStage, ha, riskRate, confidenceCharge, referenceCharge]

theorem riskRate_sum_le (c : Config) (hδ : ValidConfidence c.confidence)
    (ω : SampleSpace n) (T : ℕ) :
    (∑ r ∈ Finset.range T, riskRate c (choice c r ω)) ≤
      ENNReal.ofReal (c.errorBudget + c.confidence / 16) := by
  simp_rw [riskRate_eq_charges]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => add_nonneg
    (div_nonneg (confidenceCharge_nonneg c hδ.1.le _) (by norm_num))
    (referenceCharge_nonneg c hδ.1.le _))]
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
  have hα := stage_confidence_sum_le c hδ.1.le ω.2 T
  have hβ := stage_reference_sum_le c hδ.1.le ω.2 T
  have hγ : 0 ≤ c.errorBudget := div_nonneg hδ.1.le (by norm_num)
  linarith

/-- Probability of any first favorable failure in the actual capped attempt.
Entry β is paid only once at its scale; later calls reuse the suitable z. -/
theorem measure_bad_union_le (I : Instance n) (c : Config) (hδ : ValidConfidence c.confidence)
    (T : ℕ) :
    sampleLawOfMeans I.mean (⋃ r ∈ Finset.range T, {ω | BadAt I c r ω}) ≤
      ENNReal.ofReal (c.errorBudget + c.confidence / 16) := by
  apply (finite_bad_union_le_lintegralRisk I c hδ T).trans
  calc
    _ ≤ ∫⁻ _ω : SampleSpace n, ENNReal.ofReal (c.errorBudget + c.confidence / 16)
        ∂sampleLawOfMeans I.mean := lintegral_mono (fun ω => riskRate_sum_le c hδ ω T)
    _ = _ := by simp

theorem unfavorable_probability_le (I : Instance n) (c : Config) (hδ : ValidConfidence c.confidence)
    (T : ℕ) :
    sampleLawOfMeans I.mean {ω | ¬ FavorableThrough I c ω.2 T} ≤
      ENNReal.ofReal (c.errorBudget + c.confidence / 16) :=
  (measure_mono (unfavorable_subset_bad_union I c T)).trans (measure_bad_union_le I c hδ T)

/-- The actual favorable event has probability at least 1−γ−δ/16 for every
attempt index, whether or not its caps are large enough to return an answer. -/
theorem favorable_probability_ge (I : Instance n) (c : Config) (hδ : ValidConfidence c.confidence)
    (T : ℕ) :
    1 - c.errorBudget - c.confidence / 16 ≤
      (sampleLawOfMeans I.mean).real {ω | FavorableThrough I c ω.2 T} := by
  let B : Set (SampleSpace n) := ⋃ r ∈ Finset.range T, {ω | BadAt I c r ω}
  have hB : MeasurableSet B := MeasurableSet.iUnion (fun r => MeasurableSet.iUnion (fun _ =>
    measurableSet_badAt I c r))
  have hb : (sampleLawOfMeans I.mean).real B ≤ c.errorBudget + c.confidence / 16 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (measure_bad_union_le I c hδ T)
    have hp : 0 ≤ c.errorBudget + c.confidence / 16 := by
      have hδ0 := hδ.1.le
      unfold Config.errorBudget
      positivity
    simpa only [Measure.real_def, B, ENNReal.toReal_ofReal hp] using h
  have hsub : Bᶜ ⊆ {ω | FavorableThrough I c ω.2 T} := by
    intro ω hω
    by_contra hf
    exact hω (unfavorable_subset_bad_union I c T hf)
  have hh := measureReal_mono (μ := sampleLawOfMeans I.mean) hsub (measure_ne_top _ _)
  rw [measureReal_compl hB] at hh
  simp only [probReal_univ] at hh
  linarith

theorem favorable_probability_three_quarters (I : Instance n) (c : Config)
    (hδ : ValidConfidence c.confidence) (T : ℕ) :
    (3 : ℝ) / 4 ≤ (sampleLawOfMeans I.mean).real {ω | FavorableThrough I c ω.2 T} := by
  have h := favorable_probability_ge I c hδ T
  unfold Config.errorBudget at h
  have hδ1 := hδ.2
  linarith

theorem actual_abort_le_quarter (I : Instance n) (c : Config) (hδ : ValidConfidence c.confidence)
    (hfit : complexityTarget I c.confidence ≤ (2 : ℝ) ^ c.attempt * confidenceCost c.confidence)
    (hC : c.sampleConstant = UniversalCallCost.sampleCapConstant) :
    sampleLawOfMeans I.mean {ω | (procedure c I.two_le).actualOutput ω = none} ≤ 1 / 4 := by
  have hH : I.hardness ≤ (2 : ℝ) ^ c.attempt :=
    (hardness_le_target_div I hδ).trans ((div_le_iff₀ (confidenceCost_pos hδ)).mpr hfit)
  have hsub : {ω | (procedure c I.two_le).actualOutput ω = none} ⊆
      {ω | ¬ FavorableThrough I c ω.2 c.fuel} := by
    intro ω hnone hgood
    have he := favorable_actualOutput_eq_best I c ω hgood hδ hH hfit hC
    rw [hnone] at he
    cases he
  apply ((measure_mono hsub).trans (unfavorable_probability_le I c hδ c.fuel)).trans
  have hreal : c.errorBudget + c.confidence / 16 ≤ (1 : ℝ) / 4 := by
    unfold Config.errorBudget
    linarith [hδ.2]
  exact (ENNReal.ofReal_le_ofReal hreal).trans_eq (by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num)

/-- The actual finite reward-block evaluator has the same abort bound; this is
ready for the real fixed-cap retry policy's large-attempt assumption. -/
theorem block_abort_le_quarter (I : Instance n) (c : Config) (hδ : ValidConfidence c.confidence)
    (hfit : complexityTarget I c.confidence ≤ (2 : ℝ) ^ c.attempt * confidenceCost c.confidence)
    (hC : c.sampleConstant = UniversalCallCost.sampleCapConstant) :
    blockLaw I.mean (procedure c I.two_le).budget {v | (procedure c I.two_le).evaluate v = none} ≤ 1 / 4 := by
  have he := (procedure c I.two_le).actualOutput_event I.mean {none} (measurableSet_singleton none)
  change blockLaw I.mean (procedure c I.two_le).budget
    ((procedure c I.two_le).evaluate ⁻¹' {none}) ≤ 1 / 4
  rw [← he]
  exact actual_abort_le_quarter I c hδ hfit hC

end GapEntropy.UniversalAttempt

namespace GapEntropy.UniversalPolicy
variable {n : ℕ}

/-- The runtime-side probability obligation of the actual universal algorithm
is discharged for every normalized instance and valid confidence. -/
theorem largeAttemptAbortBound (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    LargeAttemptAbortBound I δ := by
  intro j hfit
  exact UniversalAttempt.block_abort_le_quarter I (config δ j) hδ hfit rfl

end GapEntropy.UniversalPolicy
