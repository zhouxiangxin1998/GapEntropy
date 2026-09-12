import GapEntropy.MedianGaussian
import Mathlib.Probability.Independence.InfinitePi

/-!
# A canonical independent Gaussian sample tape for median elimination

The measure is explicitly constructed as a nested product over rounds, arms, and
within-round sample positions. Consequently A.2 has an instance with no unproved
sampling-law or independence premises. This is a statistical procedure and sample
count theorem; embedding it into the repository's interactive `Policy` remains a
separate task.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MeasureTheory.Measure

namespace GapEntropy.MedianTape
open GapEntropy.MedianElimination

def Tape (n : ℕ) (ε β : ℝ) := (r : ℕ) → Fin n → Fin (roundSamples ε β r) → ℝ

instance {n : ℕ} {ε β : ℝ} : MeasurableSpace (Tape n ε β) :=
  inferInstanceAs (MeasurableSpace ((r : ℕ) → Fin n → Fin (roundSamples ε β r) → ℝ))

def armLaw {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) (r : ℕ) (i : Fin n) :
    Measure (Fin (roundSamples ε β r) → ℝ) :=
  infinitePi (fun _ => gaussianReal (μ i) 1)

instance {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) (r : ℕ) (i : Fin n) :
    IsProbabilityMeasure (armLaw μ ε β r i) := by unfold armLaw; infer_instance

def roundLaw {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) (r : ℕ) :
    Measure (Fin n → Fin (roundSamples ε β r) → ℝ) := infinitePi (armLaw μ ε β r)

instance {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) (r : ℕ) :
    IsProbabilityMeasure (roundLaw μ ε β r) := by unfold roundLaw; infer_instance

def law {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) : Measure (Tape n ε β) :=
  infinitePi (roundLaw μ ε β)

instance {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) :
    IsProbabilityMeasure (law μ ε β) := by
  constructor
  change (infinitePi (roundLaw μ ε β)) Set.univ = 1
  exact measure_univ

def observation {n : ℕ} {ε β : ℝ} (r : ℕ) (i : Fin n)
    (j : Fin (roundSamples ε β r)) (ω : Tape n ε β) : ℝ := ω r i j

theorem observation_measurable {n : ℕ} {ε β : ℝ} (r : ℕ) (i : Fin n)
    (j : Fin (roundSamples ε β r)) : Measurable (observation r i j) := by
  unfold observation
  fun_prop

theorem arm_preserving {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) (r : ℕ) (i : Fin n) :
    MeasurePreserving (fun ω : Tape n ε β => ω r i)
      (law μ ε β) (armLaw μ ε β r i) := by
  exact (measurePreserving_eval_infinitePi (armLaw μ ε β r) i).comp
    (measurePreserving_eval_infinitePi (roundLaw μ ε β) r)

theorem observation_law {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) (r : ℕ) (i : Fin n)
    (j : Fin (roundSamples ε β r)) :
    HasLaw (observation r i j) (gaussianReal (μ i) 1) (law μ ε β) := by
  have h := (measurePreserving_eval_infinitePi
    (fun _ : Fin (roundSamples ε β r) => gaussianReal (μ i) 1) j).comp
      (arm_preserving μ ε β r i)
  exact ⟨h.measurable.aemeasurable, h.map_eq⟩

theorem rounds_independent {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) :
    iIndepFun (fun r (ω : Tape n ε β) i j => observation r i j ω) (law μ ε β) :=
  iIndepFun_infinitePi (P := roundLaw μ ε β) (X := fun _ x => x) (fun _ => measurable_id)

theorem within_independent {n : ℕ} (μ : Fin n → ℝ) (ε β : ℝ) (r : ℕ) (i : Fin n) :
    iIndepFun (observation r i) (law μ ε β) := by
  apply (iIndepFun_iff_hasLaw_Pi_infinitePi (observation_law μ ε β r i)
    ((measurable_pi_lambda _ (fun j => observation_measurable r i j)).aemeasurable)).mpr
  have h := arm_preserving μ ε β r i
  exact ⟨h.measurable.aemeasurable, h.map_eq⟩

def output {n : ℕ} {ε β : ℝ} (S : Finset (Fin n)) (hS : S.Nonempty) (ω : Tape n ε β) : Fin n :=
  medianEliminate S hS (fun r => empiricalVectors observation r ω)

/-- Canonical product-measure instance of A.2, requiring only the input set, means,
and accuracy/confidence parameters. This does not claim a `Policy` embedding. -/
theorem medianElimination_A2 {n : ℕ} (μ : Fin n → ℝ) {ε β : ℝ}
    {S : Finset (Fin n)} (hS : S.Nonempty)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Measurable (output (ε := ε) (β := β) S hS) ∧
    (∀ ω : Tape n ε β, output S hS ω ∈ S) ∧
    (1 - β ≤ (law μ ε β).real {ω : Tape n ε β | ∀ i ∈ S, μ i - ε ≤ μ (output S hS ω)}) ∧
    (∀ ω : Tape n ε β, trajectoryCost S (fun r => empiricalVectors observation r ω) ε β =
      declaredCost S.card ε β) ∧
    (declaredCost S.card ε β : ℝ) ≤
      100000 * (S.card : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β) :=
  GapEntropy.MedianElimination.medianElimination_A2 hS hε hε1 hβ hβ1
    observation_measurable (rounds_independent μ ε β) (within_independent μ ε β)
    (observation_law μ ε β)

end GapEntropy.MedianTape
