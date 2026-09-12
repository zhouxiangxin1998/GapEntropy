import GapEntropy.PolicyRepresentations.KernelPolicy
import GapEntropy.PolicyRepresentations.StandardAlgorithms

/-!
# Global correctness and benchmark transport for history-kernel algorithms

The source success probability and expected cost are defined by the direct
kernel recursion. Their equality with the implemented policy's quantities is a
theorem. The same policy transformation works for every mean vector and instance.
-/

open GapEntropy MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace GapEntropy.PolicyRepresentations

namespace KernelPolicy
variable {n : ℕ}

def toStandard (K : KernelPolicy n) : StandardPolicy n where
  SeedSpace := UniformSeed
  law := freshnessUniformLaw
  rule := K.toSeeded

theorem toStandard_successProb (K : KernelPolicy n) (I : Instance n) :
    K.toStandard.successProb I = K.successProb I :=
  K.toSeeded_successProb_eq I

theorem toStandard_expectedSamples (K : KernelPolicy n) (I : Instance n) :
    K.toStandard.expectedSamples I = K.expectedSamples I :=
  K.toSeeded_expectedSamples_eq I

theorem toStandard_terminates_iff (K : KernelPolicy n) (I : Instance n) :
    K.toStandard.AlmostSurelyTerminates I ↔ K.AlmostSurelyTerminates I :=
  K.toSeeded_terminates_iff I

def toPolicy (K : KernelPolicy n) : Policy n := K.toStandard.toPolicy

theorem toPolicy_successProb (K : KernelPolicy n) (I : Instance n) :
    K.toPolicy.successProb I = K.successProb I := by
  rw [toPolicy, StandardPolicy.successProb_toPolicy, toStandard_successProb]

theorem toPolicy_expectedSamples (K : KernelPolicy n) (I : Instance n) :
    K.toPolicy.expectedSamples I = K.expectedSamples I := by
  rw [toPolicy, StandardPolicy.expectedSamples_toPolicy, toStandard_expectedSamples]

theorem toPolicy_terminates_iff (K : KernelPolicy n) (I : Instance n) :
    K.toPolicy.AlmostSurelyTerminates I ↔ K.AlmostSurelyTerminates I := by
  rw [toPolicy, StandardPolicy.terminates_toPolicy_iff, toStandard_terminates_iff]

end KernelPolicy

abbrev KernelAlgorithm := (n : ℕ) → KernelPolicy n

namespace KernelAlgorithm

def GlobalCorrect (K : KernelAlgorithm) (δ : ℝ) : Prop :=
  ∀ (n : ℕ) (I : Instance n), ENNReal.ofReal (1 - δ) ≤ (K n).successProb I

def permutationAverage (K : KernelAlgorithm) {n : ℕ} (I : Instance n) : ℝ≥0∞ :=
  (∑ π : Equiv.Perm (Fin n), (K n).expectedSamples (I.permute π)) /
    (n.factorial : ℝ≥0∞)

def toStandard (K : KernelAlgorithm) : StandardAlgorithm := fun n => (K n).toStandard

def toAlgorithm (K : KernelAlgorithm) : Algorithm := fun n => (K n).toPolicy

theorem toStandard_globalCorrect_iff (K : KernelAlgorithm) (δ : ℝ) :
    K.toStandard.GlobalCorrect δ ↔ K.GlobalCorrect δ := by
  unfold StandardAlgorithm.GlobalCorrect GlobalCorrect toStandard
  simp only [KernelPolicy.toStandard_successProb]

theorem toStandard_permutationAverage (K : KernelAlgorithm) {n : ℕ} (I : Instance n) :
    K.toStandard.permutationAverage I = K.permutationAverage I := by
  unfold StandardAlgorithm.permutationAverage permutationAverage toStandard
  simp only [KernelPolicy.toStandard_expectedSamples]

theorem toAlgorithm_globalCorrect_iff (K : KernelAlgorithm) (δ : ℝ) :
    DeltaCorrect K.toAlgorithm δ ↔ K.GlobalCorrect δ := by
  unfold DeltaCorrect GlobalCorrect toAlgorithm
  simp only [KernelPolicy.toPolicy_successProb]

theorem toAlgorithm_permutationAverage (K : KernelAlgorithm) {n : ℕ} (I : Instance n) :
    GapEntropy.permutationAverage K.toAlgorithm I = K.permutationAverage I := by
  unfold GapEntropy.permutationAverage permutationAverage toAlgorithm
  simp only [KernelPolicy.toPolicy_expectedSamples]

/-- Every globally correct kernel algorithm is a valid original-benchmark competitor. -/
theorem benchmark_le_permutationAverage (K : KernelAlgorithm) {δ : ℝ}
    (hK : K.GlobalCorrect δ) {n : ℕ} (I : Instance n) :
    benchmark I δ ≤ K.permutationAverage I := by
  have h := GapEntropy.benchmark_le_permutationAverage K.toAlgorithm
    ((K.toAlgorithm_globalCorrect_iff δ).mpr hK) I
  simpa only [K.toAlgorithm_permutationAverage] using h

theorem entropy_lower_bound (K : KernelAlgorithm) {δ : ℝ}
    (hK : K.GlobalCorrect δ) {n : ℕ} (I : Instance n) (hδ : ValidConfidence δ) :
    ENNReal.ofReal (I.hardness * (Real.log δ⁻¹ + I.gapEntropy) / 5) ≤
      K.permutationAverage I :=
  (benchmark_entropy_lower_bound I hδ).trans (K.benchmark_le_permutationAverage hK I)

end KernelAlgorithm
end GapEntropy.PolicyRepresentations
