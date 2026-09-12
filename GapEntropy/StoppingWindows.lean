import GapEntropy.MarkedConfidence
import GapEntropy.ReturnedCounts

/-!
# Stopping-count windows on the actual marked experiment

The full-count window becomes visible whenever the policy returns. Counts
reconstructed from the full retained transcript equal these frozen counts.
Finite observable windows increase to the full event on one raw measure.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy
namespace Policy

variable {n : ℕ} (A : Policy n)

/-- Full marked return and count window. -/
def markedWindow (hn : 2 ≤ n) (lo hi : ℝ≥0∞) : Set (MarkedSampleSpace n) :=
  {p | p ∈ A.markedReturnedNotEvent hn ∧
    lo ≤ A.markedArmSamples hn p ∧ A.markedArmSamples hn p ≤ hi}

/-- Same count window, with return already witnessed at horizon `T`. -/
def markedWindowAt (hn : 2 ≤ n) (lo hi : ℝ≥0∞) (T : ℕ) : Set (MarkedSampleSpace n) :=
  {p | p ∈ A.markedReturnedNotAt hn T ∧
    lo ≤ A.markedArmSamples hn p ∧ A.markedArmSamples hn p ≤ hi}

theorem measurableSet_markedWindow (hn : 2 ≤ n) (lo hi : ℝ≥0∞) :
    MeasurableSet (A.markedWindow hn lo hi) :=
  (A.measurableSet_markedReturnedNotEvent hn).inter
    ((measurableSet_le measurable_const (A.measurable_markedArmSamples hn)).inter
      (measurableSet_le (A.measurable_markedArmSamples hn) measurable_const))

theorem measurableSet_markedWindowAt (hn : 2 ≤ n) (lo hi : ℝ≥0∞) (T : ℕ) :
    MeasurableSet (A.markedWindowAt hn lo hi T) :=
  (A.measurableSet_markedReturnedNotAt hn T).inter
    ((measurableSet_le measurable_const (A.measurable_markedArmSamples hn)).inter
      (measurableSet_le (A.measurable_markedArmSamples hn) measurable_const))

/-- Reconstruct all requests to an arm from the retained sequence of states. -/
def transcriptArmCount (hn : 2 ≤ n) : (T : ℕ) → Fin n → Transcript n T → ℝ≥0∞
  | 0, _, _ => 0
  | T + 1, i, p => transcriptArmCount hn T i p.1 +
      if A.requestedArmFromTranscript hn T p.1 = some i then 1 else 0

theorem measurable_transcriptArmCount (hn : 2 ≤ n) (T : ℕ) (i : Fin n) :
    Measurable (A.transcriptArmCount hn T i) := by
  induction T with
  | zero => exact measurable_const
  | succ T ih =>
    exact (ih.comp measurable_fst).add
      (Measurable.ite (((A.measurable_requestedArmFromTranscript hn T).comp
        measurable_fst).eq_const (some i)).setOf measurable_const measurable_const)

@[simp] theorem transcriptArmCount_actual (hn : 2 ≤ n) (T : ℕ) (i : Fin n)
    (ω : SampleSpace n) :
    A.transcriptArmCount hn T i (A.transcript hn ω T) = A.truncatedArmSamples hn T i ω := by
  induction T with
  | zero => simp [transcriptArmCount, truncatedArmSamples]
  | succ T ih =>
    simp only [transcriptArmCount, transcript_succ_fst, ih, requestedArmFromTranscript_actual]
    simp only [truncatedArmSamples, Finset.sum_range_succ]

def markedTranscriptArmCount (hn : 2 ≤ n) (T : ℕ) (p : MarkedTranscript n T) : ℝ≥0∞ :=
  A.transcriptArmCount hn T p.2 p.1

theorem measurable_markedTranscriptArmCount (hn : 2 ≤ n) (T : ℕ) :
    Measurable (A.markedTranscriptArmCount hn T) :=
  measurable_from_prod_countable_left (fun tag ↦ A.measurable_transcriptArmCount hn T tag)

/-- At a witnessed return, the finite observable count equals the full count. -/
theorem markedTranscriptArmCount_eq_full_of_returned (hn : 2 ≤ n) (T : ℕ)
    (p : MarkedSampleSpace n) (hp : p ∈ A.markedReturnedNotAt hn T) :
    A.markedTranscriptArmCount hn T (A.markedTranscriptFromSample hn T p) =
      A.markedArmSamples hn p := by
  obtain ⟨i, _, hret⟩ := hp
  exact (A.transcriptArmCount_actual hn T p.2 p.1).trans
    (A.armSamples_eq_truncatedArmSamples_of_returned hn p.1 T hret p.2).symm

/-- The window as an actual finite marked-transcript event. -/
def markedWindowTranscript (hn : 2 ≤ n) (lo hi : ℝ≥0∞) (T : ℕ) :
    Set (MarkedTranscript n T) :=
  {p | p ∈ markedReturnedNotTranscript T ∧
    lo ≤ A.markedTranscriptArmCount hn T p ∧ A.markedTranscriptArmCount hn T p ≤ hi}

theorem measurableSet_markedWindowTranscript (hn : 2 ≤ n) (lo hi : ℝ≥0∞) (T : ℕ) :
    MeasurableSet (A.markedWindowTranscript hn lo hi T) :=
  (measurableSet_markedReturnedNotTranscript T).inter
    ((measurableSet_le measurable_const (A.measurable_markedTranscriptArmCount hn T)).inter
      (measurableSet_le (A.measurable_markedTranscriptArmCount hn T) measurable_const))

theorem markedWindowTranscript_preimage (hn : 2 ≤ n) (lo hi : ℝ≥0∞) (T : ℕ) :
    A.markedTranscriptFromSample hn T ⁻¹' A.markedWindowTranscript hn lo hi T =
      A.markedWindowAt hn lo hi T := by
  ext p
  have hr := Set.ext_iff.mp (A.markedReturnedNotTranscript_preimage hn T) p
  constructor
  · rintro ⟨hret, hlo, hhi⟩
    have hp := hr.mp hret
    have hc := A.markedTranscriptArmCount_eq_full_of_returned hn T p hp
    exact ⟨hp, hc ▸ hlo, hc ▸ hhi⟩
  · rintro ⟨hret, hlo, hhi⟩
    have hc := A.markedTranscriptArmCount_eq_full_of_returned hn T p hret
    exact ⟨hr.mpr hret, hc.symm ▸ hlo, hc.symm ▸ hhi⟩

theorem markedWindowAt_mono (hn : 2 ≤ n) (lo hi : ℝ≥0∞) :
    Monotone (A.markedWindowAt hn lo hi) := by
  intro s t hst p hp
  exact ⟨A.markedReturnedNotAt_mono hn hst hp.1, hp.2⟩

theorem markedWindowAt_subset (hn : 2 ≤ n) (lo hi : ℝ≥0∞) (T : ℕ) :
    A.markedWindowAt hn lo hi T ⊆ A.markedWindow hn lo hi := by
  rintro p ⟨hret, hlo, hhi⟩
  exact ⟨⟨T, hret⟩, hlo, hhi⟩

theorem markedWindow_eq_iUnion (hn : 2 ≤ n) (lo hi : ℝ≥0∞) :
    A.markedWindow hn lo hi = ⋃ T, A.markedWindowAt hn lo hi T := by
  ext p
  constructor
  · rintro ⟨⟨T, hret⟩, hlo, hhi⟩
    exact Set.mem_iUnion.mpr ⟨T, hret, hlo, hhi⟩
  · intro hp
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hp
    exact A.markedWindowAt_subset hn lo hi T hT

theorem measure_markedWindow_eq_iSup (hn : 2 ≤ n) (lo hi : ℝ≥0∞)
    (μ : Measure (MarkedSampleSpace n)) :
    μ (A.markedWindow hn lo hi) = ⨆ T, μ (A.markedWindowAt hn lo hi T) := by
  rw [A.markedWindow_eq_iUnion]
  exact (A.markedWindowAt_mono hn lo hi).measure_iUnion

theorem markedTranscriptLaw_window_eq_raw (hn : 2 ≤ n) (mean : Fin n → ℝ)
    (d : Fin n) (lo hi : ℝ≥0∞) (T : ℕ) :
    A.markedTranscriptLaw hn mean T d (A.markedWindowTranscript hn lo hi T) =
      markedSampleLaw mean d (A.markedWindowAt hn lo hi T) := by
  rw [← A.markedSampleLaw_map_transcript,
    Measure.map_apply (A.measurable_markedTranscriptFromSample hn T)
      (A.measurableSet_markedWindowTranscript hn lo hi T), A.markedWindowTranscript_preimage]

theorem iSup_markedTranscriptLaw_window (hn : 2 ≤ n) (mean : Fin n → ℝ)
    (d : Fin n) (lo hi : ℝ≥0∞) :
    (⨆ T, A.markedTranscriptLaw hn mean T d (A.markedWindowTranscript hn lo hi T)) =
      markedSampleLaw mean d (A.markedWindow hn lo hi) := by
  simp_rw [A.markedTranscriptLaw_window_eq_raw]
  exact (A.measure_markedWindow_eq_iSup hn lo hi _).symm

end Policy

/-- The manuscript's window, whose thresholds use the original source identity. -/
def stoppingWindow (A : Algorithm) {n : ℕ} (I : Instance n)
    (_hfin : permutationAverage A I ≠ ⊤) (d : Fin n) : Set (MarkedSampleSpace n) :=
  (A n).markedWindow I.two_le (ENNReal.ofReal (I.weight d / 100))
    (ENNReal.ofReal (16 * (permutationArmSamples A I d).toReal))

theorem measurableSet_stoppingWindow (A : Algorithm) {n : ℕ} (I : Instance n)
    (hfin : permutationAverage A I ≠ ⊤) (d : Fin n) :
    MeasurableSet (stoppingWindow A I hfin d) := (A n).measurableSet_markedWindow _ _ _

/-- B.12 transfer for any count interval. All information is charged to the
original source costs; the target is the single common raised-pivot law. -/
theorem markedWindow_transfer (A : Algorithm) {n : ℕ} (I : Instance n)
    (hfin : permutationAverage A I ≠ ⊤) (d a : Fin n) (hgap : I.gap d ≤ I.gap a)
    (lo hi : ℝ≥0∞)
    (hp : ENNReal.ofReal (1 / 2 : ℝ) < markedSampleLaw I.mean d
      ((A n).markedWindow I.two_le lo hi)) :
    ENNReal.ofReal (Real.exp (-(normalizedArmCost A I hfin d +
      normalizedArmCost A I hfin a)) / 4) ≤
      markedSampleLaw (Coupling.raisedMean I.mean I.best a) a
        ((A n).markedWindow I.two_le lo hi) := by
  apply event_transfer_of_finite_horizons
    (fun T ↦ (A n).markedTranscriptLaw I.two_le I.mean T d)
    (fun T ↦ (A n).markedTranscriptLaw I.two_le (Coupling.raisedMean I.mean I.best a) T a)
    (fun T ↦ (A n).markedWindowTranscript I.two_le lo hi T)
    (fun T ↦ (A n).measurableSet_markedWindowTranscript I.two_le lo hi T)
    (add_nonneg (normalizedArmCost_nonneg A I hfin d) (normalizedArmCost_nonneg A I hfin a))
  · rwa [Policy.iSup_markedTranscriptLaw_window]
  · intro T
    rw [Policy.markedTranscriptLaw_window_eq_raw]
    exact measure_mono ((A n).markedWindowAt_subset I.two_le lo hi T)
  · exact fun T ↦ klDiv_markedTranscriptLaw_le_normalized_pair A I hfin T a d hgap

theorem stoppingWindow_transfer (A : Algorithm) {n : ℕ} (I : Instance n)
    (hfin : permutationAverage A I ≠ ⊤) (d a : Fin n) (hgap : I.gap d ≤ I.gap a)
    (hp : ENNReal.ofReal (1 / 2 : ℝ) < markedSampleLaw I.mean d (stoppingWindow A I hfin d)) :
    ENNReal.ofReal (Real.exp (-(normalizedArmCost A I hfin d +
      normalizedArmCost A I hfin a)) / 4) ≤
      markedSampleLaw (Coupling.raisedMean I.mean I.best a) a (stoppingWindow A I hfin d) :=
  markedWindow_transfer A I hfin d a hgap _ _ hp

/-- Exponential transfer in the exact subtraction notation used in scale packing. -/
theorem stoppingWindow_target_lower_bound (A : Algorithm) {n : ℕ} (I : Instance n)
    (hfin : permutationAverage A I ≠ ⊤) (d a : Fin n) (hgap : I.gap d ≤ I.gap a)
    (hp : ENNReal.ofReal (1 / 2 : ℝ) < markedSampleLaw I.mean d (stoppingWindow A I hfin d)) :
    ENNReal.ofReal (Real.exp (-normalizedArmCost A I hfin d -
      normalizedArmCost A I hfin a) / 4) ≤
      markedSampleLaw (Coupling.raisedMean I.mean I.best a) a (stoppingWindow A I hfin d) := by
  rw [show -normalizedArmCost A I hfin d - normalizedArmCost A I hfin a =
      -(normalizedArmCost A I hfin d + normalizedArmCost A I hfin a) by ring]
  exact stoppingWindow_transfer A I hfin d a hgap hp

theorem stoppingWindow_subset_returnedNotEvent (A : Algorithm) {n : ℕ} (I : Instance n)
    (hfin : permutationAverage A I ≠ ⊤) (d : Fin n) :
    stoppingWindow A I hfin d ⊆ (A n).markedReturnedNotEvent I.two_le :=
  fun _ hp ↦ hp.1

/-- Real-valued window inequalities are extracted only after the finite upper
threshold proves that the marked full count is not infinite on the window. -/
theorem stoppingWindow_count_bounds (A : Algorithm) {n : ℕ} (I : Instance n)
    (hfin : permutationAverage A I ≠ ⊤) (d : Fin n) {p : MarkedSampleSpace n}
    (hp : p ∈ stoppingWindow A I hfin d) :
    I.weight d / 100 ≤ ((A n).markedArmSamples I.two_le p).toReal ∧
      ((A n).markedArmSamples I.two_le p).toReal ≤
        16 * (permutationArmSamples A I d).toReal := by
  have hc : (A n).markedArmSamples I.two_le p ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp.2.2
  constructor
  · have h := ENNReal.toReal_mono hc hp.2.1
    have hlo : 0 ≤ I.weight d / 100 := div_nonneg (I.weight_nonneg d) (by norm_num)
    simpa only [ENNReal.toReal_ofReal hlo] using h
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp.2.2
    simpa only [ENNReal.toReal_ofReal (by positivity :
      0 ≤ 16 * (permutationArmSamples A I d).toReal)] using h

end GapEntropy
