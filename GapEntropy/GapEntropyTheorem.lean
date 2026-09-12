import GapEntropy.TargetPolicy
import GapEntropy.BenchmarkUpper
import GapEntropy.LowerBound

/-!
# The gap-entropy conjecture for the operational Gaussian model

The lower bound applies to every globally correct policy. The upper bound uses
the actual globally correct target-profile algorithm constructed in TargetPolicy,
with real Gaussian subroutines, abort/retry execution, and fallback interleaving.
No statistical success or runtime hypotheses remain in the final theorem.
-/

open scoped ENNReal
namespace GapEntropy

/-- The upper half of manuscript Theorem 2.1 with an explicit universal constant. -/
theorem benchmark_entropy_upper_bound {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) :
    benchmark I δ ≤ ENNReal.ofReal (64000000000000 * entropyCost I δ) :=
  benchmark_le_of_each (TargetPolicy.algorithm I δ) (TargetPolicy.deltaCorrect I hδ) I _
    (TargetPolicy.target_expectedSamples_le I hδ)

/-- Chen–Li gap-entropy Conjecture 3.5 / manuscript Theorem 2.1, in the explicitly
specified measurable Gaussian-tape Policy model. -/
theorem gapEntropyConjecture : GapEntropyConjecture := by
  refine ⟨1 / 5, 64000000000000, by norm_num, by norm_num, ?_⟩
  intro δ hδ n I
  refine ⟨?_, benchmark_entropy_upper_bound I hδ⟩
  convert benchmark_entropy_lower_bound I hδ using 1
  congr 1
  unfold entropyCost confidenceCost
  ring

end GapEntropy
