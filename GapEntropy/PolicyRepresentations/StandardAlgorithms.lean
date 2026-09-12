import GapEntropy.PolicyRepresentations.Randomization
import GapEntropy.PolicyRepresentations.SeededTransport
import GapEntropy.PolicyRepresentations.DeterministicWitnesses

/-!
# The benchmark over arbitrary standard Borel private probability spaces

A bundled competitor below supplies its own standard Borel seed space and
probability law, separately at each arm count, and a measurable history/tape
policy. Representability by a Gaussian tape is not a field or an assumption.
It is derived from `measurePreserving_seedSampler` and exact execution transport.

The resulting benchmark is equal to the Gaussian-tape benchmark `GapEntropy.benchmark`, even
when competitor expectations are infinite. The explicit upper-bound witnesses
can in fact use a one-point seed space: their decisions are deterministic
functions of observations, as proved in `DeterministicWitnesses`.
-/

open GapEntropy MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace GapEntropy.PolicyRepresentations

/-- A competitor chooses an arbitrary standard Borel private probability space.
There is no simulation, correctness, finite-cost, or termination field. -/
structure StandardPolicy (n : ℕ) where
  SeedSpace : Type
  [instMeasurable : MeasurableSpace SeedSpace]
  [instStandardBorel : StandardBorelSpace SeedSpace]
  law : Measure SeedSpace
  [instProbability : IsProbabilityMeasure law]
  rule : SeededPolicy SeedSpace n

attribute [instance] StandardPolicy.instMeasurable
  StandardPolicy.instStandardBorel StandardPolicy.instProbability

namespace StandardPolicy
variable {n : ℕ}

def successProb (A : StandardPolicy n) (I : Instance n) : ℝ≥0∞ :=
  A.rule.successProb A.law I

def expectedSamples (A : StandardPolicy n) (I : Instance n) : ℝ≥0∞ :=
  A.rule.expectedSamples A.law I

def AlmostSurelyTerminates (A : StandardPolicy n) (I : Instance n) : Prop :=
  A.rule.AlmostSurelyTerminates A.law I

/-- The seed sampler depends on the competitor's law, never on unknown means. -/
def toPolicy (A : StandardPolicy n) : Policy n :=
  A.rule.toPolicy (seedSampler A.law) (measurePreserving_seedSampler A.law).measurable

theorem successProb_toPolicy (A : StandardPolicy n) (I : Instance n) :
    A.toPolicy.successProb I = A.successProb I :=
  A.rule.successProb_toPolicy A.law (seedSampler A.law) (measurePreserving_seedSampler A.law) I

theorem expectedSamples_toPolicy (A : StandardPolicy n) (I : Instance n) :
    A.toPolicy.expectedSamples I = A.expectedSamples I :=
  A.rule.expectedSamples_toPolicy A.law (seedSampler A.law)
    (measurePreserving_seedSampler A.law) I

theorem terminates_toPolicy_iff (A : StandardPolicy n) (I : Instance n) :
    A.toPolicy.AlmostSurelyTerminates I ↔ A.AlmostSurelyTerminates I :=
  A.rule.terminates_toPolicy_iff A.law (seedSampler A.law)
    (measurePreserving_seedSampler A.law) I

/-- Every original Gaussian-tape policy is an admissible member of this class. -/
def ofPolicy (P : Policy n) : StandardPolicy n where
  SeedSpace := Seed
  law := seedLaw
  rule := SeededPolicy.ofPolicy P

@[simp] theorem ofPolicy_successProb (P : Policy n) (I : Instance n) :
    (ofPolicy P).successProb I = P.successProb I :=
  SeededPolicy.ofPolicy_successProb P I

@[simp] theorem ofPolicy_expectedSamples (P : Policy n) (I : Instance n) :
    (ofPolicy P).expectedSamples I = P.expectedSamples I :=
  SeededPolicy.ofPolicy_expectedSamples P I

@[simp] theorem ofPolicy_terminates_iff (P : Policy n) (I : Instance n) :
    (ofPolicy P).AlmostSurelyTerminates I ↔ P.AlmostSurelyTerminates I :=
  SeededPolicy.ofPolicy_terminates_iff P I

/-- A deterministic witness needs no auxiliary randomness: its private law is
the Dirac probability on a one-point standard Borel space. -/
def ofDeterministic (D : DeterministicPolicy n) : StandardPolicy n where
  SeedSpace := Unit
  law := Measure.dirac ()
  rule := {
    choose := fun hn t p => D.choose hn t p.2
    measurable_choose := fun hn t => (D.measurable_choose hn t).comp measurable_snd }

@[simp] theorem ofDeterministic_toPolicy (D : DeterministicPolicy n) :
    (ofDeterministic D).toPolicy = D.toPolicy := rfl

@[simp] theorem ofDeterministic_successProb (D : DeterministicPolicy n) (I : Instance n) :
    (ofDeterministic D).successProb I = D.toPolicy.successProb I := by
  rw [← successProb_toPolicy, ofDeterministic_toPolicy]

@[simp] theorem ofDeterministic_expectedSamples (D : DeterministicPolicy n) (I : Instance n) :
    (ofDeterministic D).expectedSamples I = D.toPolicy.expectedSamples I := by
  rw [← expectedSamples_toPolicy, ofDeterministic_toPolicy]

@[simp] theorem ofDeterministic_terminates_iff (D : DeterministicPolicy n) (I : Instance n) :
    (ofDeterministic D).AlmostSurelyTerminates I ↔ D.toPolicy.AlmostSurelyTerminates I := by
  rw [← terminates_toPolicy_iff, ofDeterministic_toPolicy]

end StandardPolicy

/-- The private space and law may vary with arm count. -/
abbrev StandardAlgorithm := (n : ℕ) → StandardPolicy n

namespace StandardAlgorithm

/-- Global correctness uses the independently defined arbitrary-seed execution. -/
def GlobalCorrect (A : StandardAlgorithm) (δ : ℝ) : Prop :=
  ∀ (n : ℕ) (I : Instance n), ENNReal.ofReal (1 - δ) ≤ (A n).successProb I

def permutationAverage (A : StandardAlgorithm) {n : ℕ} (I : Instance n) : ℝ≥0∞ :=
  (∑ π : Equiv.Perm (Fin n), (A n).expectedSamples (I.permute π)) /
    (n.factorial : ℝ≥0∞)

def toAlgorithm (A : StandardAlgorithm) : Algorithm := fun n => (A n).toPolicy

def ofAlgorithm (A : Algorithm) : StandardAlgorithm := fun n => StandardPolicy.ofPolicy (A n)

theorem toAlgorithm_globalCorrect_iff (A : StandardAlgorithm) (δ : ℝ) :
    DeltaCorrect A.toAlgorithm δ ↔ A.GlobalCorrect δ := by
  unfold DeltaCorrect GlobalCorrect toAlgorithm
  simp only [StandardPolicy.successProb_toPolicy]

theorem toAlgorithm_permutationAverage (A : StandardAlgorithm) {n : ℕ} (I : Instance n) :
    GapEntropy.permutationAverage A.toAlgorithm I = A.permutationAverage I := by
  unfold GapEntropy.permutationAverage permutationAverage toAlgorithm
  simp only [StandardPolicy.expectedSamples_toPolicy]

@[simp] theorem ofAlgorithm_globalCorrect_iff (A : Algorithm) (δ : ℝ) :
    (ofAlgorithm A).GlobalCorrect δ ↔ DeltaCorrect A δ := by
  unfold GlobalCorrect DeltaCorrect ofAlgorithm
  simp only [StandardPolicy.ofPolicy_successProb]

@[simp] theorem ofAlgorithm_permutationAverage (A : Algorithm) {n : ℕ} (I : Instance n) :
    (ofAlgorithm A).permutationAverage I = GapEntropy.permutationAverage A I := by
  unfold permutationAverage GapEntropy.permutationAverage ofAlgorithm
  simp only [StandardPolicy.ofPolicy_expectedSamples]

end StandardAlgorithm

/-- A new benchmark, defined directly over arbitrary standard Borel private laws.
Costs are unconditional ENNReal expectations, and correctness is global. -/
def standardBenchmark {n : ℕ} (I : Instance n) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ A : StandardAlgorithm, ⨅ (_ : A.GlobalCorrect δ), A.permutationAverage I

theorem standardBenchmark_le_permutationAverage (A : StandardAlgorithm) {δ : ℝ}
    (hA : A.GlobalCorrect δ) {n : ℕ} (I : Instance n) :
    standardBenchmark I δ ≤ A.permutationAverage I :=
  iInf_le_of_le A (iInf_le_of_le hA le_rfl)

/-- Both directions preserve all instance laws with the same transformed
algorithm. No finiteness or confidence hypothesis is required for equality. -/
theorem standardBenchmark_eq {n : ℕ} (I : Instance n) (δ : ℝ) :
    standardBenchmark I δ = benchmark I δ := by
  apply le_antisymm
  · apply le_iInf
    intro A
    apply le_iInf
    intro hA
    have h := standardBenchmark_le_permutationAverage (StandardAlgorithm.ofAlgorithm A)
      ((StandardAlgorithm.ofAlgorithm_globalCorrect_iff A δ).mpr hA) I
    simpa only [StandardAlgorithm.ofAlgorithm_permutationAverage] using h
  · unfold standardBenchmark
    apply le_iInf
    intro A
    apply le_iInf
    intro hA
    have h := benchmark_le_permutationAverage A.toAlgorithm
      ((A.toAlgorithm_globalCorrect_iff δ).mpr hA) I
    simpa only [StandardAlgorithm.toAlgorithm_permutationAverage] using h

theorem standardBenchmark_entropy_lower_bound {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) :
    ENNReal.ofReal (I.hardness * (Real.log δ⁻¹ + I.gapEntropy) / 5) ≤
      standardBenchmark I δ := by
  rw [standardBenchmark_eq]
  exact benchmark_entropy_lower_bound I hδ

theorem standardBenchmark_entropy_upper_bound {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) :
    standardBenchmark I δ ≤ ENNReal.ofReal (64000000000000 * entropyCost I δ) := by
  rw [standardBenchmark_eq]
  exact benchmark_entropy_upper_bound I hδ

/-- Existing C.1 witness, now with a one-point private seed space at every n. -/
def standardTarget {n : ℕ} (I : Instance n) (δ : ℝ) : StandardAlgorithm :=
  fun m => StandardPolicy.ofDeterministic (targetWitness I δ m)

/-- Existing universal witness, with a one-point private seed space. -/
def standardUniversal (δ : ℝ) : StandardAlgorithm :=
  fun n => StandardPolicy.ofDeterministic (universalWitness δ n)

@[simp] theorem standardTarget_toAlgorithm {n : ℕ} (I : Instance n) (δ : ℝ) :
    (standardTarget I δ).toAlgorithm = TargetPolicy.algorithm I δ := by
  funext m
  exact targetWitness_toPolicy I δ m

@[simp] theorem standardUniversal_toAlgorithm (δ : ℝ) :
    (standardUniversal δ).toAlgorithm = UniversalPolicy.algorithm δ := by
  funext n
  exact universalWitness_toPolicy δ n

theorem standardTarget_spec {n : ℕ} (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    (standardTarget I δ).GlobalCorrect δ ∧
      (∀ (m : ℕ) (J : Instance m), (standardTarget I δ m).AlmostSurelyTerminates J ∧
        (standardTarget I δ m).expectedSamples J < ⊤) ∧
      (∀ π : Equiv.Perm (Fin n), (standardTarget I δ n).expectedSamples (I.permute π) ≤
        ENNReal.ofReal (64000000000000 * entropyCost I δ)) := by
  constructor
  · apply ((standardTarget I δ).toAlgorithm_globalCorrect_iff δ).mp
    simpa only [standardTarget_toAlgorithm] using TargetPolicy.deltaCorrect I hδ
  · simpa only [standardTarget, StandardPolicy.ofDeterministic_terminates_iff,
      StandardPolicy.ofDeterministic_expectedSamples] using (targetWitness_spec I hδ).2

theorem standardUniversal_spec {δ : ℝ} (hδ : ValidConfidence δ) :
    (standardUniversal δ).GlobalCorrect δ ∧ ∀ (n : ℕ) (I : Instance n),
      (standardUniversal δ n).AlmostSurelyTerminates I ∧
      (standardUniversal δ n).expectedSamples I < ⊤ ∧
      (standardUniversal δ n).expectedSamples I ≤
        ENNReal.ofReal (12000000000012 * (entropyCost I δ + twoArmCost I)) := by
  constructor
  · apply ((standardUniversal δ).toAlgorithm_globalCorrect_iff δ).mp
    simpa only [standardUniversal_toAlgorithm] using UniversalPolicy.deltaCorrect hδ
  · simpa only [standardUniversal, StandardPolicy.ofDeterministic_terminates_iff,
      StandardPolicy.ofDeterministic_expectedSamples] using (universalWitness_spec hδ).2

def StandardGapEntropyConjecture : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ δ : ℝ, ValidConfidence δ → ∀ (n : ℕ) (I : Instance n),
      ENNReal.ofReal (c * entropyCost I δ) ≤ standardBenchmark I δ ∧
      standardBenchmark I δ ≤ ENNReal.ofReal (C * entropyCost I δ)

def StandardUniversalEntropyUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → StandardAlgorithm,
    ∀ δ : ℝ, ValidConfidence δ → (A δ).GlobalCorrect δ ∧
      ∀ (n : ℕ) (I : Instance n), (A δ n).AlmostSurelyTerminates I ∧
        (A δ n).expectedSamples I < ⊤ ∧
        (A δ n).expectedSamples I ≤
          ENNReal.ofReal (C * (entropyCost I δ + twoArmCost I))

def StandardAlmostInstanceWiseOptimality : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → StandardAlgorithm,
    ∀ δ : ℝ, ValidConfidence δ → (A δ).GlobalCorrect δ ∧
      ∀ (n : ℕ) (I : Instance n), (A δ n).expectedSamples I ≤
        ENNReal.ofReal C * (standardBenchmark I δ + ENNReal.ofReal (twoArmCost I))

def StandardPositiveAlmostInstanceWiseOptimality : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → StandardAlgorithm,
    ∀ δ : ℝ, ValidConfidence δ → (A δ).GlobalCorrect δ ∧
      ∀ (n : ℕ) (I : Instance n), (A δ n).expectedSamples I ≤
        ENNReal.ofReal C *
          (standardBenchmark I δ + ENNReal.ofReal (positiveSourceTwoArmCost I))

/-- Theorem 2.1 now ranges over the independently bundled standard Borel class. -/
theorem standardGapEntropyConjecture : StandardGapEntropyConjecture := by
  simpa only [StandardGapEntropyConjecture, GapEntropyConjecture, standardBenchmark_eq]
    using gapEntropyConjecture

/-- Theorem 2.2 uses the explicit deterministic witness in the broader class. -/
theorem standardUniversalEntropyUpperBound : StandardUniversalEntropyUpperBound := by
  exact ⟨12000000000012, by norm_num, standardUniversal, fun _ hδ => standardUniversal_spec hδ⟩

theorem standardAlmostInstanceWiseOptimality : StandardAlmostInstanceWiseOptimality := by
  obtain ⟨C, hC, A, hA⟩ := almostInstanceWiseOptimality
  refine ⟨C, hC, fun δ => StandardAlgorithm.ofAlgorithm (A δ), ?_⟩
  intro δ hδ
  obtain ⟨hcorrect, hcost⟩ := hA δ hδ
  constructor
  · exact (StandardAlgorithm.ofAlgorithm_globalCorrect_iff _ _).mpr hcorrect
  · intro n I
    simpa only [StandardAlgorithm.ofAlgorithm, StandardPolicy.ofPolicy_expectedSamples,
      standardBenchmark_eq] using hcost n I

theorem standardPositiveAlmostInstanceWiseOptimality :
    StandardPositiveAlmostInstanceWiseOptimality := by
  obtain ⟨C, hC, A, hA⟩ := positiveSourceAlmostInstanceWiseOptimality
  refine ⟨C, hC, fun δ => StandardAlgorithm.ofAlgorithm (A δ), ?_⟩
  intro δ hδ
  obtain ⟨hcorrect, hcost⟩ := hA δ hδ
  constructor
  · exact (StandardAlgorithm.ofAlgorithm_globalCorrect_iff _ _).mpr hcorrect
  · intro n I
    simpa only [StandardAlgorithm.ofAlgorithm, StandardPolicy.ofPolicy_expectedSamples,
      standardBenchmark_eq] using hcost n I

end GapEntropy.PolicyRepresentations
