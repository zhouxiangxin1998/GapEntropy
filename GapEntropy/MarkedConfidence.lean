import GapEntropy.MarkedExperiment
import GapEntropy.MarkedInformation
import GapEntropy.TiedNull
import GapEntropy.FiniteHorizonLimits

/-!
# B.9 for the original policy and its actual marked experiments

Correctness on each relabeling makes the source return away from any designated
suboptimal identity with probability at least `1-δ`. The raised-arm tied law
returns away from its mark with probability at most `δ`, by the proved tied-null
limit. Finite transcript information therefore charges `log(1/δ)` to the
designated identity's original normalized sampling cost.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy

private theorem average_const {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ≥0∞) :
    (∑ _i : ι, c) / Fintype.card ι = c := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right (by simp) (by simp)

namespace Coupling

/-- Raising one identity commutes with relabeling, including repeated means. -/
theorem relabel_raisedMean {n : ℕ} (mean : Fin n → ℝ) (best a : Fin n)
    (π : Equiv.Perm (Fin n)) :
    relabelMean (raisedMean mean best a) π =
      raisedMean (relabelMean mean π) (π best) (π a) := by
  ext i
  by_cases hi : i = π a
  · subst i
    simp [relabelMean, raisedMean]
  · have hia : π.symm i ≠ a := by
      intro h
      exact hi ((π.apply_symm_apply i).symm.trans (congrArg π h))
    simp [relabelMean, raisedMean, hi, hia]

end Coupling

namespace Policy

variable {n : ℕ} (A : Policy n)

/-- The finite test visible in the marked transcript: the last state has
returned some label other than the external mark. -/
def markedReturnedNotTranscript (T : ℕ) : Set (MarkedTranscript n T) :=
  {p | transcriptLast T p.1 ∈ returnedNotState p.2 T}

theorem measurableSet_markedReturnedNotTranscript (T : ℕ) :
    MeasurableSet (markedReturnedNotTranscript (n := n) T) :=
  (measurable_from_prod_countable_left (fun tag ↦
    ((measurableSet_returnedNotState tag T).preimage (measurable_transcriptLast T)).mem)).setOf

theorem markedReturnedNotTranscript_preimage (hn : 2 ≤ n) (T : ℕ) :
    A.markedTranscriptFromSample hn T ⁻¹' markedReturnedNotTranscript T =
      A.markedReturnedNotAt hn T := by
  ext p
  change transcriptLast T (A.transcript hn p.1 T) ∈ returnedNotState p.2 T ↔
    p.1 ∈ A.returnedNotAt hn p.2 T
  rw [A.transcriptLast_transcript]
  exact Set.ext_iff.mp (A.returnedNotState_preimage_run hn p.2 T) p.1

/-- Finite test probabilities are measured on the unified raw experiment. -/
theorem markedTranscriptLaw_returnedNot_eq_raw (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (d : Fin n) (T : ℕ) :
    A.markedTranscriptLaw hn mean T d (markedReturnedNotTranscript T) =
      markedSampleLaw mean d (A.markedReturnedNotAt hn T) := by
  rw [← A.markedSampleLaw_map_transcript,
    Measure.map_apply (A.measurable_markedTranscriptFromSample hn T)
      (measurableSet_markedReturnedNotTranscript T), A.markedReturnedNotTranscript_preimage]

/-- Supremum of the observable finite tests is exactly the actual full return event. -/
theorem iSup_markedTranscriptLaw_returnedNot (hn : 2 ≤ n)
    (mean : Fin n → ℝ) (d : Fin n) :
    (⨆ T, A.markedTranscriptLaw hn mean T d (markedReturnedNotTranscript T)) =
      markedSampleLaw mean d (A.markedReturnedNotEvent hn) := by
  simp_rw [A.markedTranscriptLaw_returnedNot_eq_raw]
  exact (A.measure_markedReturnedNotEvent_eq_iSup hn _).symm

end Policy

/-- The original source returns away from a designated suboptimal identity with
probability at least `1-δ`. Correctness alone suffices; runtime need not be finite. -/
theorem marked_source_returnedNotEvent_ge_correct (A : Algorithm) {n : ℕ}
    (I : Instance n) (d : Fin n) (hd : d ≠ I.best) {δ : ℝ} (hA : DeltaCorrect A δ) :
    ENNReal.ofReal (1 - δ) ≤
      markedSampleLaw I.mean d ((A n).markedReturnedNotEvent I.two_le) := by
  rw [Policy.measure_markedReturnedNotEvent]
  rw [← average_const (ι := Equiv.Perm (Fin n)) (ENNReal.ofReal (1 - δ))]
  apply ENNReal.div_le_div_right
  apply Finset.sum_le_sum
  intro π _
  apply (hA n (I.permute π)).trans
  apply measure_mono
  rintro ω ⟨T, hT⟩
  refine ⟨T, (I.permute π).best, ?_, hT⟩
  exact fun h ↦ hd (π.injective h.symm)

/-- Uniformly averaging the proved tied-null limits controls the full marked
comparison event; no correctness or stopping assumption is made at the tie. -/
theorem marked_tied_returnedNotEvent_le (A : Algorithm) {n : ℕ}
    (I : Instance n) (a : Fin n) (ha : a ≠ I.best) {δ : ℝ}
    (hδ : δ ≤ 1) (hA : DeltaCorrect A δ) :
    markedSampleLaw (Coupling.raisedMean I.mean I.best a) a
      ((A n).markedReturnedNotEvent I.two_le) ≤ ENNReal.ofReal δ := by
  rw [Policy.measure_markedReturnedNotEvent]
  rw [← average_const (ι := Equiv.Perm (Fin n)) (ENNReal.ofReal δ)]
  apply ENNReal.div_le_div_right
  apply Finset.sum_le_sum
  intro π _
  rw [Coupling.relabel_raisedMean]
  exact (A n).tied_returnedNotEvent_measure_le (I.permute π) (π a)
    (fun h ↦ ha (π.injective h)) hδ (hA n)

theorem marked_tied_returnedNotAt_le (A : Algorithm) {n : ℕ}
    (I : Instance n) (a : Fin n) (ha : a ≠ I.best) {δ : ℝ}
    (hδ : δ ≤ 1) (hA : DeltaCorrect A δ) (T : ℕ) :
    (A n).markedTranscriptLaw I.two_le (Coupling.raisedMean I.mean I.best a) T a
      (Policy.markedReturnedNotTranscript T) ≤ ENNReal.ofReal δ := by
  rw [Policy.markedTranscriptLaw_returnedNot_eq_raw]
  apply le_trans _ (marked_tied_returnedNotEvent_le A I a ha hδ hA)
  apply measure_mono
  exact fun _ h ↦ ⟨T, h⟩

/-- B.9: every original suboptimal identity pays at least `log(1/δ)` in
normalized permutation-averaged source sampling cost. -/
theorem log_inv_le_normalizedArmCost (A : Algorithm) {n : ℕ} (I : Instance n)
    {δ : ℝ} (hδ : ValidConfidence δ) (hA : DeltaCorrect A δ)
    (hfin : permutationAverage A I ≠ ⊤) (d : Fin n) (hd : d ≠ I.best) :
    Real.log δ⁻¹ ≤ normalizedArmCost A I hfin d := by
  apply confidence_lower_bound_of_finite_horizons
    (fun T ↦ (A n).markedTranscriptLaw I.two_le I.mean T d)
    (fun T ↦ (A n).markedTranscriptLaw I.two_le (Coupling.raisedMean I.mean I.best d) T d)
    (fun T ↦ Policy.markedReturnedNotTranscript T)
    (fun T ↦ Policy.measurableSet_markedReturnedNotTranscript T)
    hδ.1 hδ.2 (normalizedArmCost_nonneg A I hfin d)
  · rw [Policy.iSup_markedTranscriptLaw_returnedNot]
    exact marked_source_returnedNotEvent_ge_correct A I d hd hA
  · exact marked_tied_returnedNotAt_le A I d hd (by have := hδ.2; linarith) hA
  · exact fun T ↦ klDiv_markedTranscriptLaw_raised_le A I hfin T d

end GapEntropy
