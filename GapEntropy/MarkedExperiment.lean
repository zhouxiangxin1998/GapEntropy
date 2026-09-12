import GapEntropy.MarkedTranscript
import GapEntropy.PermutationCounts
import GapEntropy.ReturnedEvents

/-!
# One marked raw experiment for full paths and all finite transcripts

The raw sample law is independent of the policy. A fixed policy's marked
transcripts, arm counts and return events are measurable observations on it.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy

section UniformMixture

variable {ι α β : Type*} [Fintype ι] [MeasurableSpace α] [MeasurableSpace β]

theorem uniformMixture_apply (F : ι → Measure α) (s : Set α) (_hs : MeasurableSet s) :
    uniformMixture F s = (∑ i, F i s) / Fintype.card ι := by
  simp only [uniformMixture, finiteMixture, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem uniformMixture_map (F : ι → Measure α) (f : α → β) (hf : Measurable f) :
    (uniformMixture F).map f = uniformMixture (fun i ↦ (F i).map f) := by
  ext s hs
  rw [Measure.map_apply hf hs, uniformMixture_apply F _ (hf hs),
    uniformMixture_apply _ _ hs]
  simp only [Measure.map_apply hf hs]

theorem lintegral_uniformMixture (F : ι → Measure α) (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂uniformMixture F) = (∑ i, ∫⁻ x, f x ∂F i) / Fintype.card ι := by
  simp only [uniformMixture, finiteMixture, lintegral_finsetSum_measure,
    lintegral_smul_measure, smul_eq_mul]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

end UniformMixture

abbrev MarkedSampleSpace (n : ℕ) := SampleSpace n × Fin n

/-- A raw Gaussian experiment with a fixed external tag. -/
def taggedSampleLaw {n : ℕ} (mean : Fin n → ℝ) (tag : Fin n) :
    Measure (MarkedSampleSpace n) :=
  (sampleLawOfMeans mean).map (fun ω ↦ (ω, tag))

instance isProbabilityMeasure_taggedSampleLaw {n : ℕ} (mean : Fin n → ℝ) (tag : Fin n) :
    IsProbabilityMeasure (taggedSampleLaw mean tag) :=
  Measure.isProbabilityMeasure_map (measurable_id.prodMk measurable_const).aemeasurable

/-- The common raw probability space, before applying any sampling policy. -/
def markedSampleLaw {n : ℕ} (mean : Fin n → ℝ) (d : Fin n) :
    Measure (MarkedSampleSpace n) :=
  uniformMixture (fun π : Equiv.Perm (Fin n) ↦
    taggedSampleLaw (Coupling.relabelMean mean π) (π d))

instance isProbabilityMeasure_markedSampleLaw {n : ℕ} (mean : Fin n → ℝ) (d : Fin n) :
    IsProbabilityMeasure (markedSampleLaw mean d) := uniformMixture_isProbability _

theorem markedSampleLaw_eq_markedAverage {n : ℕ} (mean : Fin n → ℝ) (d : Fin n) :
    markedSampleLaw mean d = Coupling.markedAverage taggedSampleLaw mean d := by
  simp only [markedSampleLaw, uniformMixture, finiteMixture,
    Coupling.markedAverage, Finset.smul_sum]

theorem markedSampleLaw_twoCoordinate_eq {n : ℕ} (mean : Fin n → ℝ)
    (best a d : Fin n) (had : a ≠ d) :
    markedSampleLaw (Coupling.twoCoordinateMean mean best a d) d =
      markedSampleLaw (Coupling.raisedMean mean best a) a := by
  simp only [markedSampleLaw_eq_markedAverage]
  exact Coupling.marked_twoCoordinate_average _ mean best a d had

/-- Event probabilities are the uniform average of the actual tagged components. -/
theorem markedSampleLaw_apply {n : ℕ} (mean : Fin n → ℝ) (d : Fin n)
    (E : Set (MarkedSampleSpace n)) (hE : MeasurableSet E) :
    markedSampleLaw mean d E =
      (∑ π : Equiv.Perm (Fin n), sampleLawOfMeans (Coupling.relabelMean mean π)
        {ω | (ω, π d) ∈ E}) / Fintype.card (Equiv.Perm (Fin n)) := by
  rw [markedSampleLaw, uniformMixture_apply _ _ hE]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  exact Measure.map_apply (measurable_id.prodMk measurable_const) hE

/-- Nonnegative observations are integrated on the same raw marked law. -/
theorem lintegral_markedSampleLaw {n : ℕ} (mean : Fin n → ℝ) (d : Fin n)
    (f : MarkedSampleSpace n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂markedSampleLaw mean d) =
      (∑ π : Equiv.Perm (Fin n),
        ∫⁻ ω, f (ω, π d) ∂sampleLawOfMeans (Coupling.relabelMean mean π)) /
          Fintype.card (Equiv.Perm (Fin n)) := by
  rw [markedSampleLaw, lintegral_uniformMixture]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  exact lintegral_map hf (measurable_id.prodMk measurable_const)

namespace Policy

variable {n : ℕ} (A : Policy n)

def markedTranscriptFromSample (hn : 2 ≤ n) (T : ℕ) (p : MarkedSampleSpace n) :
    MarkedTranscript n T := (A.transcript hn p.1 T, p.2)

theorem measurable_markedTranscriptFromSample (hn : 2 ≤ n) (T : ℕ) :
    Measurable (A.markedTranscriptFromSample hn T) :=
  ((A.measurable_transcript hn T).comp measurable_fst).prodMk measurable_snd

/-- The finite marked law is exactly the pushforward of the common raw law. -/
theorem markedSampleLaw_map_transcript (hn : 2 ≤ n) (mean : Fin n → ℝ)
    (T : ℕ) (d : Fin n) :
    (markedSampleLaw mean d).map (A.markedTranscriptFromSample hn T) =
      A.markedTranscriptLaw hn mean T d := by
  rw [markedSampleLaw, uniformMixture_map _ _ (A.measurable_markedTranscriptFromSample hn T)]
  unfold markedTranscriptLaw
  congr 1
  funext π
  unfold taggedSampleLaw taggedTranscriptLaw transcriptLaw
  have htag : Measurable (fun ω : SampleSpace n ↦ (ω, π d)) :=
    measurable_id.prodMk measurable_const
  have htag' : Measurable (fun p : Transcript n T ↦ (p, π d)) :=
    measurable_id.prodMk measurable_const
  rw [Measure.map_map (A.measurable_markedTranscriptFromSample hn T) htag,
    Measure.map_map htag' (A.measurable_transcript hn T)]
  rfl

/-- The full sample count of the externally marked label. -/
def markedArmSamples (hn : 2 ≤ n) (p : MarkedSampleSpace n) : ℝ≥0∞ :=
  A.armSamples hn p.2 p.1

theorem measurable_markedArmSamples (hn : 2 ≤ n) : Measurable (A.markedArmSamples hn) :=
  measurable_from_prod_countable_left (fun tag ↦ A.measurable_armSamples hn tag)

theorem lintegral_markedArmSamples (hn : 2 ≤ n) (mean : Fin n → ℝ) (d : Fin n) :
    (∫⁻ p, A.markedArmSamples hn p ∂markedSampleLaw mean d) =
      (∑ π : Equiv.Perm (Fin n),
        ∫⁻ ω, A.armSamples hn (π d) ω ∂sampleLawOfMeans (Coupling.relabelMean mean π)) /
          Fintype.card (Equiv.Perm (Fin n)) :=
  lintegral_markedSampleLaw mean d _ (A.measurable_markedArmSamples hn)

def markedReturnedNotAt (hn : 2 ≤ n) (T : ℕ) : Set (MarkedSampleSpace n) :=
  {p | p.1 ∈ A.returnedNotAt hn p.2 T}

def markedReturnedNotEvent (hn : 2 ≤ n) : Set (MarkedSampleSpace n) :=
  {p | p.1 ∈ A.returnedNotEvent hn p.2}

theorem measurableSet_markedReturnedNotAt (hn : 2 ≤ n) (T : ℕ) :
    MeasurableSet (A.markedReturnedNotAt hn T) :=
  (measurable_from_prod_countable_left
    (fun tag ↦ (A.measurableSet_returnedNotAt hn tag T).mem)).setOf

theorem measurableSet_markedReturnedNotEvent (hn : 2 ≤ n) :
    MeasurableSet (A.markedReturnedNotEvent hn) :=
  (measurable_from_prod_countable_left
    (fun tag ↦ (A.measurableSet_returnedNotEvent hn tag).mem)).setOf

theorem measure_markedReturnedNotAt (hn : 2 ≤ n) (mean : Fin n → ℝ) (d : Fin n) (T : ℕ) :
    markedSampleLaw mean d (A.markedReturnedNotAt hn T) =
      (∑ π : Equiv.Perm (Fin n), sampleLawOfMeans (Coupling.relabelMean mean π)
        (A.returnedNotAt hn (π d) T)) / Fintype.card (Equiv.Perm (Fin n)) :=
  markedSampleLaw_apply mean d _ (A.measurableSet_markedReturnedNotAt hn T)

theorem measure_markedReturnedNotEvent (hn : 2 ≤ n) (mean : Fin n → ℝ) (d : Fin n) :
    markedSampleLaw mean d (A.markedReturnedNotEvent hn) =
      (∑ π : Equiv.Perm (Fin n), sampleLawOfMeans (Coupling.relabelMean mean π)
        (A.returnedNotEvent hn (π d))) / Fintype.card (Equiv.Perm (Fin n)) :=
  markedSampleLaw_apply mean d _ (A.measurableSet_markedReturnedNotEvent hn)

theorem markedReturnedNotAt_mono (hn : 2 ≤ n) : Monotone (A.markedReturnedNotAt hn) := by
  intro s t hst p hp
  exact A.returnedNotAt_mono hn p.2 hst hp

theorem markedReturnedNotEvent_eq_iUnion (hn : 2 ≤ n) :
    A.markedReturnedNotEvent hn = ⋃ T, A.markedReturnedNotAt hn T := by
  ext p
  simp [markedReturnedNotEvent, markedReturnedNotAt, returnedNotEvent]

/-- The eventual probability is the increasing limit under this same measure. -/
theorem measure_markedReturnedNotEvent_eq_iSup (hn : 2 ≤ n)
    (μ : Measure (MarkedSampleSpace n)) :
    μ (A.markedReturnedNotEvent hn) = ⨆ T, μ (A.markedReturnedNotAt hn T) := by
  rw [A.markedReturnedNotEvent_eq_iUnion]
  exact (A.markedReturnedNotAt_mono hn).measure_iUnion

end Policy

/-- The unified raw-law count is exactly the benchmark's per-identity average. -/
theorem lintegral_markedArmSamples_eq_permutationArmSamples (A : Algorithm) {n : ℕ}
    (I : Instance n) (d : Fin n) :
    (∫⁻ p, (A n).markedArmSamples I.two_le p ∂markedSampleLaw I.mean d) =
      permutationArmSamples A I d := by
  rw [Policy.lintegral_markedArmSamples]
  simp only [permutationArmSamples, Policy.expectedArmSamples, sampleLaw,
    Instance.permute, Fintype.card_perm, Fintype.card_fin]
  rfl

end GapEntropy
