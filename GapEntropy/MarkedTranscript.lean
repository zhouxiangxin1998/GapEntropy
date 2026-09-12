import GapEntropy.Transcript
import GapEntropy.FiniteMixture
import GapEntropy.Coupling

/-!
# Actual marked transcript laws under uniform relabeling

Every component runs the same policy. The externally visible mark is the label
of a fixed original arm identity under the sampled permutation. Averaging KL
charges source expected counts, and the two-coordinate comparison law is
independent of which designated source identity was used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy

abbrev MarkedTranscript (n T : ℕ) := Transcript n T × Fin n

namespace Policy

variable {n : ℕ} (A : Policy n)

/-- Add an external fixed mark to the true finite transcript law. -/
def taggedTranscriptLaw (hn : 2 ≤ n) (mean : Fin n → ℝ) (T : ℕ) (tag : Fin n) :
    Measure (MarkedTranscript n T) :=
  (A.transcriptLaw hn mean T).map (fun p ↦ (p, tag))

instance isProbabilityMeasure_taggedTranscriptLaw (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (T : ℕ) (tag : Fin n) :
    IsProbabilityMeasure (A.taggedTranscriptLaw hn mean T tag) :=
  Measure.isProbabilityMeasure_map (measurable_id.prodMk measurable_const).aemeasurable

/-- Adding the same constant mark to both laws preserves their actual KL. -/
theorem klDiv_taggedTranscriptLaw (hn : 2 ≤ n) (mean mean' : Fin n → ℝ)
    (T : ℕ) (tag : Fin n) :
    InformationTheory.klDiv (A.taggedTranscriptLaw hn mean T tag)
      (A.taggedTranscriptLaw hn mean' T tag) =
      InformationTheory.klDiv (A.transcriptLaw hn mean T) (A.transcriptLaw hn mean' T) := by
  apply le_antisymm
  · exact InformationTheory.klDiv_map_le _ _ (measurable_id.prodMk measurable_const)
  · have h := InformationTheory.klDiv_map_le
      (A.taggedTranscriptLaw hn mean T tag) (A.taggedTranscriptLaw hn mean' T tag)
      measurable_fst
    have hmap (m : Measure (Transcript n T)) :
        (m.map (fun p ↦ (p, tag))).map Prod.fst = m := by
      have hf : Measurable (fun p : Transcript n T ↦ (p, tag)) :=
        measurable_id.prodMk measurable_const
      rw [Measure.map_map measurable_fst hf]
      exact Measure.map_id
    simpa only [taggedTranscriptLaw, hmap] using h

/-- The same original policy run under a uniform relabeling, with the relabeled
identity `d` recorded externally as an additional observable. -/
def markedTranscriptLaw (hn : 2 ≤ n) (mean : Fin n → ℝ) (T : ℕ) (d : Fin n) :
    Measure (MarkedTranscript n T) :=
  uniformMixture (fun π : Equiv.Perm (Fin n) ↦
    A.taggedTranscriptLaw hn (Coupling.relabelMean mean π) T (π d))

instance isProbabilityMeasure_markedTranscriptLaw (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (T : ℕ) (d : Fin n) :
    IsProbabilityMeasure (A.markedTranscriptLaw hn mean T d) :=
  uniformMixture_isProbability _

theorem markedTranscriptLaw_eq_markedAverage (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (T : ℕ) (d : Fin n) :
    A.markedTranscriptLaw hn mean T d =
      Coupling.markedAverage (fun m tag ↦ A.taggedTranscriptLaw hn m T tag) mean d := by
  simp only [markedTranscriptLaw, uniformMixture, finiteMixture,
    Coupling.markedAverage, Finset.smul_sum]

/-- The actual common comparison law in the two-coordinate change of measure. -/
theorem markedTranscriptLaw_twoCoordinate_eq (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (T : ℕ) (best a d : Fin n) (had : a ≠ d) :
    A.markedTranscriptLaw hn (Coupling.twoCoordinateMean mean best a d) T d =
      A.markedTranscriptLaw hn (Coupling.raisedMean mean best a) T a := by
  simp only [A.markedTranscriptLaw_eq_markedAverage]
  exact Coupling.marked_twoCoordinate_average _ mean best a d had

/-- Average expected samples of the original identity `i` through time `T`.
Every expectation is under the original source means, relabeled by `π`. -/
def permutationTruncatedArmSamples (hn : 2 ≤ n) (mean : Fin n → ℝ) (T : ℕ)
    (i : Fin n) : ℝ≥0∞ :=
  (∑ π : Equiv.Perm (Fin n),
    ∫⁻ ω, A.truncatedArmSamples hn T (π i) ω ∂sampleLawOfMeans (Coupling.relabelMean mean π)) /
      Fintype.card (Equiv.Perm (Fin n))

/-- A finite-horizon average arm count is bounded by the horizon, independently
of eventual stopping or finite expected total runtime. -/
theorem permutationTruncatedArmSamples_le_time (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (T : ℕ) (i : Fin n) :
    A.permutationTruncatedArmSamples hn mean T i ≤ T := by
  have hπ (π : Equiv.Perm (Fin n)) :
      (∫⁻ ω, A.truncatedArmSamples hn T (π i) ω
        ∂sampleLawOfMeans (Coupling.relabelMean mean π)) ≤ T := by
    calc
      _ ≤ ∫⁻ _ω, (T : ℝ≥0∞) ∂sampleLawOfMeans (Coupling.relabelMean mean π) := by
        apply lintegral_mono
        intro ω
        calc
          A.truncatedArmSamples hn T (π i) ω ≤
              ∑ j : Fin n, A.truncatedArmSamples hn T j ω :=
            Finset.single_le_sum (s := Finset.univ)
              (f := fun j : Fin n ↦ A.truncatedArmSamples hn T j ω)
              (fun _ _ ↦ zero_le) (Finset.mem_univ (π i))
          _ = A.truncatedSamples hn T ω := A.sum_truncatedArmSamples hn T ω
          _ ≤ T := A.truncatedSamples_le_time hn T ω
      _ = T := by simp
  unfold permutationTruncatedArmSamples
  calc
    _ ≤ (∑ _π : Equiv.Perm (Fin n), (T : ℝ≥0∞)) /
        Fintype.card (Equiv.Perm (Fin n)) :=
      ENNReal.div_le_div_right (Finset.sum_le_sum (fun π _ ↦ hπ π)) _
    _ = T := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_comm]
      exact ENNReal.mul_div_cancel_right (by simp) (by simp)

theorem permutationTruncatedArmSamples_ne_top (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (T : ℕ) (i : Fin n) :
    A.permutationTruncatedArmSamples hn mean T i ≠ ∞ :=
  ne_top_of_le_ne_top (by simp) (A.permutationTruncatedArmSamples_le_time hn mean T i)

/-- Mixing the exact A.1 transcript identities gives the average information bound. -/
theorem klDiv_markedTranscriptLaw_le_average_information (hn : 2 ≤ n)
    (mean mean' : Fin n → ℝ) (T : ℕ) (d : Fin n) :
    InformationTheory.klDiv (A.markedTranscriptLaw hn mean T d)
      (A.markedTranscriptLaw hn mean' T d) ≤
      (∑ π : Equiv.Perm (Fin n), ∑ i : Fin n,
        ENNReal.ofReal (((Coupling.relabelMean mean π) i -
          (Coupling.relabelMean mean' π) i) ^ 2 / 2) *
        ∫⁻ ω, A.truncatedArmSamples hn T i ω ∂sampleLawOfMeans (Coupling.relabelMean mean π)) /
          Fintype.card (Equiv.Perm (Fin n)) := by
  have h := klDiv_uniformMixture_le
    (fun π : Equiv.Perm (Fin n) ↦ A.taggedTranscriptLaw hn (Coupling.relabelMean mean π) T (π d))
    (fun π : Equiv.Perm (Fin n) ↦ A.taggedTranscriptLaw hn (Coupling.relabelMean mean' π) T (π d))
  simpa only [markedTranscriptLaw, A.klDiv_taggedTranscriptLaw,
    A.klDiv_transcriptLaw_eq_source_counts] using h

/-- The marked-mixture KL is bounded by the Gaussian coordinate costs times
permutation-averaged truncated counts of the original arm identities. -/
theorem klDiv_markedTranscriptLaw_le_source_counts (hn : 2 ≤ n)
    (mean mean' : Fin n → ℝ) (T : ℕ) (d : Fin n) :
    InformationTheory.klDiv (A.markedTranscriptLaw hn mean T d)
      (A.markedTranscriptLaw hn mean' T d) ≤
      ∑ i : Fin n, ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) *
        A.permutationTruncatedArmSamples hn mean T i := by
  have h := A.klDiv_markedTranscriptLaw_le_average_information hn mean mean' T d
  have hreindex (π : Equiv.Perm (Fin n)) :
      (∑ i : Fin n, ENNReal.ofReal (((Coupling.relabelMean mean π) i -
          (Coupling.relabelMean mean' π) i) ^ 2 / 2) *
        ∫⁻ ω, A.truncatedArmSamples hn T i ω ∂sampleLawOfMeans (Coupling.relabelMean mean π)) =
      ∑ i : Fin n, ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) *
        ∫⁻ ω, A.truncatedArmSamples hn T (π i) ω ∂sampleLawOfMeans (Coupling.relabelMean mean π) := by
    conv_lhs => rw [← Equiv.sum_comp π]
    simp [Coupling.relabelMean]
  simp_rw [hreindex] at h
  rw [Finset.sum_comm] at h
  simpa only [permutationTruncatedArmSamples, div_eq_mul_inv,
    Finset.sum_mul, Finset.mul_sum, mul_assoc] using h

/-- Only the two changed source identities contribute to the information cost. -/
theorem klDiv_markedTranscriptLaw_twoCoordinate_le (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (T : ℕ) (best a d : Fin n) (had : a ≠ d) :
    InformationTheory.klDiv (A.markedTranscriptLaw hn mean T d)
      (A.markedTranscriptLaw hn (Coupling.raisedMean mean best a) T a) ≤
      ENNReal.ofReal ((mean best - mean d) ^ 2 / 2) *
          A.permutationTruncatedArmSamples hn mean T d +
        ENNReal.ofReal ((mean a - mean d) ^ 2 / 2) *
          A.permutationTruncatedArmSamples hn mean T a := by
  rw [← A.markedTranscriptLaw_twoCoordinate_eq hn mean T best a d had]
  apply (A.klDiv_markedTranscriptLaw_le_source_counts hn mean
    (Coupling.twoCoordinateMean mean best a d) T d).trans_eq
  rw [Finset.sum_eq_add_of_mem d a (Finset.mem_univ d) (Finset.mem_univ a) had.symm]
  · rw [Coupling.twoCoordinate_at_designated mean best a d had,
      Coupling.twoCoordinate_at_pivot]
    congr 2
    exact congrArg ENNReal.ofReal (by ring)
  · intro i _ hi
    rw [Coupling.twoCoordinate_unchanged mean best a d i hi.2 hi.1]
    simp

/-- Gap notation for the actual two-coordinate marked comparison, specialized
to a valid original instance; the comparison itself may have a best-arm tie. -/
theorem klDiv_markedTranscriptLaw_twoCoordinate_le_gaps (I : Instance n)
    (T : ℕ) (a d : Fin n) (had : a ≠ d) :
    InformationTheory.klDiv (A.markedTranscriptLaw I.two_le I.mean T d)
      (A.markedTranscriptLaw I.two_le (Coupling.raisedMean I.mean I.best a) T a) ≤
      ENNReal.ofReal (I.gap d ^ 2 / 2) *
          A.permutationTruncatedArmSamples I.two_le I.mean T d +
        ENNReal.ofReal ((I.gap d - I.gap a) ^ 2 / 2) *
          A.permutationTruncatedArmSamples I.two_le I.mean T a := by
  have h := A.klDiv_markedTranscriptLaw_twoCoordinate_le I.two_le I.mean T I.best a d had
  have hgap : I.gap d - I.gap a = I.mean a - I.mean d := by
    simp only [Instance.gap]
    ring
  rw [hgap]
  exact h

end Policy

end GapEntropy
