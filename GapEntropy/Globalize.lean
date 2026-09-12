import GapEntropy.InterleaveCost
import GapEntropy.FallbackGuarantees

/-!
# Actual fallback globalization

The attempt stream may abort forever on an off-target input. Alternating it with
the proved fallback produces a globally correct, finite-expectation Policy once
the stream's incorrect-return budget has been established. The target cost is
charged to the attempt stream, while finite expectation on every input is charged
to the fallback. Both comparisons concern the same concrete alternating policy.
-/

open MeasureTheory
open scoped ENNReal

namespace GapEntropy

noncomputable def globalize (stream : Algorithm) (δ : ℝ) : Algorithm :=
  fun n => Interleave.policy (stream n) (Fallback.policy n δ)

theorem globalize_expectedSamples_le_stream (stream : Algorithm) (δ : ℝ)
    {n : ℕ} (I : Instance n) :
    (globalize stream δ n).expectedSamples I ≤ 2 * (stream n).expectedSamples I + 1 :=
  Interleave.expectedSamples_le_left _ _ I

theorem globalize_expectedSamples_ne_top (stream : Algorithm) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (I : Instance n) :
    (globalize stream δ n).expectedSamples I ≠ ⊤ :=
  Interleave.expectedSamples_ne_top_of_right _ _ I (Fallback.expectedSamples_ne_top I hδ hδ1)

theorem globalize_almostSurelyTerminates (stream : Algorithm) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (I : Instance n) :
    (globalize stream δ n).AlmostSurelyTerminates I :=
  (globalize stream δ n).almostSurelyTerminates_of_expectedSamples_ne_top I
    (globalize_expectedSamples_ne_top stream hδ hδ1 I)

/-- C.3's correctness step uses only an incorrect-return bound for the stream;
neither stream termination nor an off-target sample-cost bound is required. -/
theorem globalize_deltaCorrect (stream : Algorithm) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstream : ∀ (n : ℕ) (I : Instance n),
      sampleLaw I ((stream n).returnedNotEvent I.two_le I.best) ≤ ENNReal.ofReal (δ / 2)) :
    DeltaCorrect (globalize stream δ) δ := by
  intro n I
  apply (globalize stream δ n).successProb_ge_of_wrong_return_le_of_almostSurelyTerminates
    I hδ.le (globalize_almostSurelyTerminates stream hδ hδ1 I)
  have h := Interleave.returnedNotEvent_measure_le (stream n) (Fallback.policy n δ) I
    (hstream n I) (Fallback.wrong_return_measure_le I hδ hδ1)
  have he : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  simpa only [he, globalize] using h

theorem globalize_guarantees (stream : Algorithm) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstream : ∀ (n : ℕ) (I : Instance n),
      sampleLaw I ((stream n).returnedNotEvent I.two_le I.best) ≤ ENNReal.ofReal (δ / 2)) :
    DeltaCorrect (globalize stream δ) δ ∧
      ∀ (n : ℕ) (I : Instance n), (globalize stream δ n).AlmostSurelyTerminates I ∧
        (globalize stream δ n).expectedSamples I < ⊤ ∧
        (globalize stream δ n).expectedSamples I ≤ 2 * (stream n).expectedSamples I + 1 := by
  refine ⟨globalize_deltaCorrect stream hδ hδ1 hstream, ?_⟩
  intro n I
  exact ⟨globalize_almostSurelyTerminates stream hδ hδ1 I,
    (globalize_expectedSamples_ne_top stream hδ hδ1 I).lt_top,
    globalize_expectedSamples_le_stream stream δ I⟩

end GapEntropy
