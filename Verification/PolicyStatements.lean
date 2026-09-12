import GapEntropy.PolicyRepresentations.StandardAlgorithms

/-!
# Expanded statements for the policy-class supplement

The examples below expand the benchmark over arbitrary standard Borel private
probability spaces down to its operational definition, check that the concrete
upper-bound witnesses use one-point seed spaces, and restate manuscript
Theorem 2.2 for the universal witness in the broader class. The axioms of the
supplement's main declarations are printed.
-/

open GapEntropy GapEntropy.PolicyRepresentations MeasureTheory
open scoped ENNReal BigOperators

namespace GapEntropy.PolicyRepresentations.StatementChecks

/-- Global admissibility and every permutation cost are expanded to the
arbitrary-seed operational quantities; the result is the Gaussian-tape benchmark. -/
example {n : ℕ} (I : Instance n) (δ : ℝ) :
    (⨅ A : StandardAlgorithm,
      ⨅ (_ : ∀ (m : ℕ) (J : Instance m), ENNReal.ofReal (1 - δ) ≤
        (A m).rule.successProb (A m).law J),
      (∑ π : Equiv.Perm (Fin n),
        (A n).rule.expectedSamples (A n).law (I.permute π)) / (n.factorial : ℝ≥0∞)) =
      benchmark I δ :=
  standardBenchmark_eq I δ

/-- The concrete witnesses use one-point seed spaces. -/
example (δ : ℝ) (n : ℕ) : (standardUniversal δ n).SeedSpace = Unit := rfl
example {n : ℕ} (I : Instance n) (δ : ℝ) (m : ℕ) :
    (standardTarget I δ m).SeedSpace = Unit := rfl

/-- Manuscript Theorem 2.2 for the universal witness in the standard Borel class. -/
example : ∀ (δ : ℝ), (0 < δ ∧ δ < 1 / 10) →
    (∀ (n : ℕ) (I : Instance n), ENNReal.ofReal (1 - δ) ≤
      (standardUniversal δ n).rule.successProb (standardUniversal δ n).law I) ∧
    ∀ (n : ℕ) (I : Instance n),
      (standardUniversal δ n).rule.AlmostSurelyTerminates (standardUniversal δ n).law I ∧
      (standardUniversal δ n).rule.expectedSamples (standardUniversal δ n).law I < ⊤ ∧
      (standardUniversal δ n).rule.expectedSamples (standardUniversal δ n).law I ≤
        ENNReal.ofReal (12000000000012 *
          (I.hardness * (Real.log δ⁻¹ + I.gapEntropy) +
            I.twoArmHardness * Real.log
              (Real.exp 1 + Real.log (Real.exp 1 + I.twoArmHardness)))) :=
  fun _ hδ => standardUniversal_spec hδ

example : StandardGapEntropyConjecture := standardGapEntropyConjecture
example : StandardUniversalEntropyUpperBound := standardUniversalEntropyUpperBound
example : StandardAlmostInstanceWiseOptimality := standardAlmostInstanceWiseOptimality
example : StandardPositiveAlmostInstanceWiseOptimality :=
  standardPositiveAlmostInstanceWiseOptimality

#print axioms standardBenchmark_eq
#print axioms standardGapEntropyConjecture
#print axioms standardUniversalEntropyUpperBound
#print axioms standardAlmostInstanceWiseOptimality
#print axioms standardPositiveAlmostInstanceWiseOptimality

end GapEntropy.PolicyRepresentations.StatementChecks
