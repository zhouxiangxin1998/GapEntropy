import GapEntropy.PolicyRepresentations.Abandonment
import GapEntropy.PolicyRepresentations.StandardAlgorithms

/-!
# Explicit abandonment in arbitrary standard Borel private spaces

The same instance-independent normalization works on every input. It preserves
unconditional sample cost and global correctness, so the original lower bounds
also cover competitors that may explicitly stop without returning a label.
-/

noncomputable section
open GapEntropy MeasureTheory
open scoped ENNReal

namespace GapEntropy.PolicyRepresentations
namespace AbandonPolicy

variable {S : Type} [MeasurableSpace S] [StandardBorelSpace S]
  (μ : Measure S) [IsProbabilityMeasure μ] {n : ℕ} (A : AbandonPolicy S n)

def toPolicy : Policy n :=
  A.complete.toPolicy (seedSampler μ) (measurePreserving_seedSampler μ).measurable

theorem expectedSamples_toPolicy (I : Instance n) :
    (A.toPolicy μ).expectedSamples I = A.expectedSamples μ I := by
  rw [toPolicy, A.complete.expectedSamples_toPolicy μ (seedSampler μ)
    (measurePreserving_seedSampler μ) I, A.expectedSamples_complete μ I]

theorem successProb_le_toPolicy (I : Instance n) :
    A.successProb μ I ≤ (A.toPolicy μ).successProb I := by
  rw [toPolicy, A.complete.successProb_toPolicy μ (seedSampler μ)
    (measurePreserving_seedSampler μ) I]
  exact A.successProb_le_complete μ I

end AbandonPolicy

/-- The transformed family is chosen before the unknown instance. The private
space and its law can differ at every arm count. No termination or finite-cost
hypothesis is needed. -/
theorem explicitAbandonment_global_transport
    (S : ℕ → Type) [∀ n, MeasurableSpace (S n)] [∀ n, StandardBorelSpace (S n)]
    (μ : ∀ n, Measure (S n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, AbandonPolicy (S n) n) (δ : ℝ)
    (hA : ∀ n (I : Instance n), ENNReal.ofReal (1 - δ) ≤ (A n).successProb (μ n) I) :
    ∃ P : Algorithm, DeltaCorrect P δ ∧
      ∀ n (I : Instance n), (P n).expectedSamples I = (A n).expectedSamples (μ n) I := by
  refine ⟨fun n => (A n).toPolicy (μ n), ?_, ?_⟩
  · intro n I
    exact (hA n I).trans ((A n).successProb_le_toPolicy (μ n) I)
  · intro n I
    exact (A n).expectedSamples_toPolicy (μ n) I

end GapEntropy.PolicyRepresentations
