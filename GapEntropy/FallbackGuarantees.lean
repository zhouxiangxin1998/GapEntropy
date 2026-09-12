import GapEntropy.FallbackTermination
import GapEntropy.Problem

/-!
# The manuscript C.2 fallback guarantees

The policy is defined for every arm count without access to the input means.
Its operational Gaussian analysis proves both finite unconditional expectation
on every valid input and the required `δ/2` success guarantee.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Classical

namespace GapEntropy.Policy

theorem successProb_ge_of_wrong_return_le_of_almostSurelyTerminates
    {n : ℕ} (A : Policy n) (I : Instance n) {ε : ℝ} (hε : 0 ≤ ε)
    (hterm : A.AlmostSurelyTerminates I)
    (hwrong : sampleLaw I (A.returnedNotEvent I.two_le I.best) ≤ ENNReal.ofReal ε) :
    ENNReal.ofReal (1 - ε) ≤ A.successProb I := by
  have hae : A.successEvent I =ᵐ[sampleLaw I] (A.returnedNotEvent I.two_le I.best)ᶜ := by
    filter_upwards [hterm] with ω hω
    obtain ⟨T, i, hi⟩ := hω
    apply propext
    constructor
    · intro hs hw
      exact A.returnedNotEvent_subset_success_compl I hw hs
    · intro hw
      have hib : i = I.best := by
        by_contra hib
        exact hw ⟨T, i, hib, hi⟩
      exact ⟨T, by simpa only [hib] using hi⟩
  have hm : (sampleLaw I).real (A.successEvent I) =
      1 - (sampleLaw I).real (A.returnedNotEvent I.two_le I.best) := by
    calc
      _ = (sampleLaw I).real ((A.returnedNotEvent I.two_le I.best)ᶜ) :=
        congrArg ENNReal.toReal (measure_congr hae)
      _ = _ := probReal_compl_eq_one_sub (A.measurableSet_returnedNotEvent I.two_le I.best)
  have hw : (sampleLaw I).real (A.returnedNotEvent I.two_le I.best) ≤ ε := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal hε] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hwrong
  have hp : 1 - ε ≤ (sampleLaw I).real (A.successEvent I) := by linarith
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top (sampleLaw I) _),
    successProb] using ENNReal.ofReal_le_ofReal hp

end GapEntropy.Policy

namespace GapEntropy.Fallback

/-- The actual fallback returns the unique best arm with probability at least
`1 - δ/2`, including finite return in the event. -/
theorem successProb_ge {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - δ / 2) ≤ (policy n δ).successProb I :=
  (policy n δ).successProb_ge_of_wrong_return_le_of_almostSurelyTerminates I
    (by positivity) (almostSurelyTerminates I hδ hδ1) (wrong_return_measure_le I hδ hδ1)

/-- One mean-independent fallback policy for every input size. -/
def algorithm (δ : ℝ) : Algorithm := fun n => policy n δ

theorem deltaCorrect {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    DeltaCorrect (algorithm δ) (δ / 2) := fun _ I => successProb_ge I hδ hδ1

/-- All three C.2 guarantees refer to the same concrete policy. -/
theorem guarantees {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    DeltaCorrect (algorithm δ) (δ / 2) ∧
      ∀ (n : ℕ) (I : Instance n), (algorithm δ n).AlmostSurelyTerminates I ∧
        (algorithm δ n).expectedSamples I < ⊤ := by
  refine ⟨deltaCorrect hδ hδ1, ?_⟩
  intro n I
  exact ⟨almostSurelyTerminates I hδ hδ1, (expectedSamples_ne_top I hδ hδ1).lt_top⟩

end GapEntropy.Fallback
