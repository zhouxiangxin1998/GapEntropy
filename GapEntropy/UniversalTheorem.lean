import GapEntropy.UniversalSoundness
import GapEntropy.UniversalFavorableProbability
import GapEntropy.GapEntropyTheorem
import GapEntropy.IteratedLogConvention

/-!
Theorem 2.2 and almost instance-wise optimality for the operational Gaussian
model. The single algorithm receives only confidence and the arm count. Its
actual global error and abort probabilities have been proved, so no execution
or statistical assumptions remain in these endpoints.
-/
noncomputable section
namespace GapEntropy

namespace UniversalPolicy
variable {n : ℕ}

theorem deltaCorrect {δ : ℝ} (hδ : ValidConfidence δ) : DeltaCorrect (algorithm δ) δ := by
  intro n I
  exact successProb_ge_of_execution_bounds I hδ (wrongReturnBound I hδ) (largeAttemptAbortBound I hδ)

theorem expectedSamples_le (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    (algorithm δ n).expectedSamples I ≤
      ENNReal.ofReal (12000000000012 * (entropyCost I δ + twoArmCost I)) :=
  expectedSamples_le_of_abort_bound I hδ (largeAttemptAbortBound I hδ)

theorem expectedSamples_lt_top (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    (algorithm δ n).expectedSamples I < ⊤ :=
  expectedSamples_lt_top_of_abort_bound I hδ (largeAttemptAbortBound I hδ)

theorem almostSurelyTerminates (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    (algorithm δ n).AlmostSurelyTerminates I :=
  almostSurelyTerminates_of_abort_bound I hδ (largeAttemptAbortBound I hδ)

end UniversalPolicy

/-- Manuscript Theorem 2.2, with the actual universal policy and an explicit constant. -/
theorem universalEntropyUpperBound : UniversalEntropyUpperBound :=
  UniversalPolicy.universalEntropyUpperBound_of_execution_bounds
    (fun _ hδ _ I => UniversalPolicy.wrongReturnBound I hδ)
    (fun _ hδ _ I => UniversalPolicy.largeAttemptAbortBound I hδ)

/-- The two proved main theorems imply Conjecture 3.2 under the stated smooth
positive iterated-log convention. The same globally correct algorithm serves
all unknown instances. -/
theorem almostInstanceWiseOptimality : AlmostInstanceWiseOptimality :=
  almostInstanceWiseOptimality_of_main_claims gapEntropyConjecture universalEntropyUpperBound

/-- The explicit positive truncation of the source iterated logarithm gives
an equivalent almost-optimality statement. -/
theorem positiveSourceAlmostInstanceWiseOptimality : PositiveSourceAlmostInstanceWiseOptimality :=
  almostInstanceWiseOptimality_iff_positiveTruncation.mp almostInstanceWiseOptimality

end GapEntropy
