import GapEntropy.UniversalReferenceFailure
import GapEntropy.UniversalPolicy

/-! Error events on the actual deterministic blocks of the universal retry policy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}

/-- The complete suffix at any fixed absolute row has the original joint
seed/reward law. The seed is retained, and the universal calls are seed-free. -/
theorem measurePreserving_shiftedSample (mean : Fin n → ℝ) (m : ℕ) :
    MeasurePreserving (shiftedSample m) (sampleLawOfMeans mean) (sampleLawOfMeans mean) := by
  have hm : MeasurePreserving (shiftValues m) (rewardLaw mean) (rewardLaw mean) := by
    refine ⟨shiftValues_measurable m, ?_⟩
    exact Measure.map_infinitePi_infinitePi_of_inj (fun i j hij => Nat.add_left_cancel hij)
  exact (MeasurePreserving.id seedLaw).prod hm

/-- Outer-measure inequality for arbitrary events; no measurability premise is
needed by the terminal-core cover. -/
theorem measure_shiftedSample_preimage_le (mean : Fin n → ℝ) (m : ℕ) (E : Set (SampleSpace n)) :
    sampleLawOfMeans mean ((shiftedSample m) ⁻¹' E) ≤ sampleLawOfMeans mean E := by
  have hm := measurePreserving_shiftedSample mean m
  simpa only [hm.map_eq] using Measure.le_map_apply (μ := sampleLawOfMeans mean) hm.measurable.aemeasurable E

end GapEntropy.UniversalAttempt

namespace GapEntropy.FixedCapRetry
variable {n : ℕ} (R : ℕ → BoundedProcedure n (Option (Fin n))) (hpos : ∀ j, 0 < (R j).budget)

/-- Lift local execution events to the actual retry policy's deterministic
sample blocks. Dropping the condition that an attempt is reached only enlarges
this error event. -/
def streamEvent (E : ℕ → Set (SampleSpace n)) : Set (SampleSpace n) :=
  ⋃ j, (UniversalAttempt.shiftedSample ((schedule R hpos).start j)) ⁻¹' E j

theorem measurableSet_streamEvent (E : ℕ → Set (SampleSpace n)) (hE : ∀ j, MeasurableSet (E j)) :
    MeasurableSet (streamEvent R hpos E) := by
  apply MeasurableSet.iUnion
  intro j
  exact (UniversalAttempt.measurePreserving_shiftedSample (fun _ => 0) _).measurable (hE j)

theorem streamEvent_measure_le (mean : Fin n → ℝ) (E : ℕ → Set (SampleSpace n))
    (hE : ∀ j, MeasurableSet (E j)) (ε : ℕ → ℝ≥0∞)
    (hε : ∀ j, sampleLawOfMeans mean (E j) ≤ ε j) :
    sampleLawOfMeans mean (streamEvent R hpos E) ≤ ∑' j, ε j := by
  apply (measure_iUnion_le _).trans
  apply ENNReal.tsum_le_tsum
  intro j
  rw [(UniversalAttempt.measurePreserving_shiftedSample mean _).measure_preimage (hE j).nullMeasurableSet]
  exact hε j

/-- Local actualOutput on a shifted sample is exactly the private finite
attempt readout used by the real retry policy. -/
theorem actualOutput_shifted_eq_answer (j : ℕ) (ω : SampleSpace n) :
    (R j).actualOutput (UniversalAttempt.shiftedSample ((schedule R hpos).start j) ω) =
      answer R hpos j ω := by
  unfold BoundedProcedure.actualOutput
  rw [UniversalAttempt.rewardBlock_shiftedSample]
  rfl

end GapEntropy.FixedCapRetry

namespace GapEntropy.UniversalPolicy
open UniversalAttempt UniversalCall UniversalErrorBudget
variable {n : ℕ}

def ReferenceFailure (I : Instance n) (δ : ℝ) (hδ : ValidConfidence δ) : Set (SampleSpace n) :=
  FixedCapRetry.streamEvent (attempts n I.two_le δ) (attempt_budget_pos n I.two_le hδ)
    (fun j => UniversalAttempt.ReferenceFailure (config δ j) (I.mean I.best))


theorem measurableSet_referenceFailure (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    MeasurableSet (ReferenceFailure I δ hδ) :=
  FixedCapRetry.measurableSet_streamEvent _ _ _ (fun _ => UniversalAttempt.measurableSet_referenceFailure _ _)

/-- D.10 for the actual universal retry stream, including all attempts whether
reached or not. Each local call reads the actual corresponding global rows. -/
theorem referenceFailure_measure_le (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    sampleLaw I (ReferenceFailure I δ hδ) ≤ ENNReal.ofReal (δ / 16) := by
  have hh := FixedCapRetry.streamEvent_measure_le (attempts n I.two_le δ) (attempt_budget_pos n I.two_le hδ)
    I.mean (fun j => UniversalAttempt.ReferenceFailure (config δ j) (I.mean I.best))
    (fun _ => UniversalAttempt.measurableSet_referenceFailure _ _)
    (fun j => ∑' k, ENNReal.ofReal (referenceError δ j k))
    (fun j => UniversalAttempt.referenceFailure_measure_le (config δ j) hδ I.two_le I.mean (I.mean I.best)
      (fun i => sub_nonneg.mp (I.gap_nonneg i)))
  apply hh.trans
  have he := tsum_referenceConfidence_le hδ.1.le
  rw [ENNReal.tsum_prod (f := fun j k => ENNReal.ofReal (referenceConfidence δ j k))] at he
  exact he

/-- Outside the global reference-failure event every actual accepted call,
including later calls reusing an old numerical z, has an upper-valid reference. -/
theorem callReference_le_of_not_stream (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (ω : SampleSpace n) (hno : ω ∉ ReferenceFailure I δ hδ) (j r : ℕ)
    (a : Metadata n) (z : ℝ)
    (hs : stage (config δ j)
      (shiftedSample ((FixedCapRetry.schedule (attempts n I.two_le δ) (attempt_budget_pos n I.two_le hδ)).start j) ω).2 r =
      .inr (a, z)) (ha : a.Allowed (config δ j)) :
    (callResult (config δ j)
      (shiftedSample ((FixedCapRetry.schedule (attempts n I.two_le δ) (attempt_budget_pos n I.two_le hδ)).start j) ω).2
      a ha z).1 ≤ I.mean I.best + a.tolerance / 16 := by
  apply callReference_le_of_not_referenceFailure (config δ j) (I.mean I.best) _ _ r a z hs ha
  intro hb
  exact hno (Set.mem_iUnion.mpr ⟨j, hb⟩)

end GapEntropy.UniversalPolicy
