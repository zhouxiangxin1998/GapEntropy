import Verification.Statements
import GapEntropy.UniversalTheorem

/-!
The expected types live in `Statements.lean`; they are not inferred from the
proofs under review. Every declaration below is kernel checked against those
types. This file supplies no extra axiom and no statistical/runtime premise.
-/

namespace GapEntropy.StatementChecks

/-- This also verifies the independently transcribed admissibility predicate. -/
theorem referenceCorrect_eq (A : (n : ℕ) → Policy n) (δ : ℝ) :
    ReferenceCorrect A δ = DeltaCorrect A δ := rfl

theorem referenceCost_eq {n : ℕ} (P : Policy n) (I : Instance n) :
    ReferenceCost P I = P.expectedSamples I := rfl

theorem referenceBenchmark_eq {n : ℕ} (I : Instance n) (δ : ℝ) :
    ReferenceBenchmark I δ = benchmark I δ := rfl

theorem checkedGapEntropy : GapEntropyStatement := by
  intro δ hδpos hδsmall n I
  exact ⟨benchmark_entropy_lower_bound I ⟨hδpos, hδsmall⟩,
    benchmark_entropy_upper_bound I ⟨hδpos, hδsmall⟩⟩

theorem checkedUniversal : UniversalStatement := by
  refine ⟨UniversalPolicy.algorithm, ?_⟩
  intro δ hδpos hδsmall
  have hδ : ValidConfidence δ := ⟨hδpos, hδsmall⟩
  exact ⟨UniversalPolicy.deltaCorrect hδ, fun n I =>
    ⟨UniversalPolicy.almostSurelyTerminates I hδ,
      UniversalPolicy.expectedSamples_lt_top I hδ,
      UniversalPolicy.expectedSamples_le I hδ⟩⟩

theorem checkedAlmostOptimal : AlmostOptimalStatement :=
  almostInstanceWiseOptimality

theorem checkedPositiveAlmostOptimal : PositiveAlmostOptimalStatement :=
  positiveSourceAlmostInstanceWiseOptimality

#print axioms checkedGapEntropy
#print axioms checkedUniversal
#print axioms checkedAlmostOptimal
#print axioms checkedPositiveAlmostOptimal

end GapEntropy.StatementChecks
