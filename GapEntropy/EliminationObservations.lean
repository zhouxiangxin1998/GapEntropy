import GapEntropy.EliminationTape

/-!
# Observation laws on the A.3 elimination tape

The reference and active observations are the arm means plus the corresponding fresh noise
coordinates of the elimination tape. The reference and active estimates of `EliminationTape` are
the sample means of these observations. For each active arm the observations are independent
unit-variance Gaussians centred at its mean, and for a fixed reference arm each reference
observation has the unit-variance Gaussian law centred at that arm's mean.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open scoped BigOperators

namespace GapEntropy.EliminationTape
variable {n : ℕ} {d α : ℝ}

def referenceObservation (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    (j : Fin (referenceSamples d α)) (ω : Tape n d α) : ℝ :=
  μ (referenceArm S hS ω) + ω.2.1 j

def activeObservation (μ : Fin n → ℝ) (i : Fin n)
    (j : Fin (activeSamples d α)) (ω : Tape n d α) : ℝ := μ i + ω.2.2 i j

theorem referenceEstimate_eq_sampleMean (μ : Fin n → ℝ) (S : Finset (Fin n))
    (hS : S.Nonempty) (hm : 0 < referenceSamples d α) (ω : Tape n d α) :
    referenceEstimate μ S hS ω =
      GapEntropy.Gaussian.sampleMean (referenceObservation μ S hS) ω := by
  have hm0 : (referenceSamples d α : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [referenceEstimate, referenceObservation, GapEntropy.GaussianNoise.mean,
    GapEntropy.Gaussian.sampleMean, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem activeEstimate_eq_sampleMean (μ : Fin n → ℝ) (i : Fin n)
    (hm : 0 < activeSamples d α) (ω : Tape n d α) :
    activeEstimate μ i ω = GapEntropy.Gaussian.sampleMean (activeObservation μ i) ω := by
  have hm0 : (activeSamples d α : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [activeEstimate, activeObservation, GapEntropy.GaussianNoise.mean,
    GapEntropy.Gaussian.sampleMean, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem activeObservation_law (μ : Fin n → ℝ) (i : Fin n) (j : Fin (activeSamples d α)) :
    HasLaw (activeObservation μ i j) (gaussianReal (μ i) 1) (law μ d α) := by
  have hp := (measurePreserving_eval_infinitePi
    (fun _ : Fin (activeSamples d α) => gaussianReal 0 1) j).comp (activeNoise_preserving μ i)
  have hl : HasLaw (fun ω : Tape n d α => ω.2.2 i j) (gaussianReal 0 1) (law μ d α) :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  change HasLaw (fun ω : Tape n d α => μ i + ω.2.2 i j) (gaussianReal (μ i) 1) (law μ d α)
  simpa only [zero_add] using gaussianReal_const_add hl (μ i)

theorem activeObservations_independent (μ : Fin n → ℝ) (i : Fin n) :
    iIndepFun (activeObservation (d := d) (α := α) μ i) (law μ d α) := by
  have hp := activeNoise_preserving (d := d) (α := α) μ i
  have hl (j : Fin (activeSamples d α)) :
      HasLaw (fun ω : Tape n d α => ω.2.2 i j) (gaussianReal 0 1) (law μ d α) := by
    have hh := (measurePreserving_eval_infinitePi
      (fun _ : Fin (activeSamples d α) => gaussianReal 0 1) j).comp hp
    exact ⟨hh.measurable.aemeasurable, hh.map_eq⟩
  have hind : iIndepFun (fun j (ω : Tape n d α) => ω.2.2 i j) (law μ d α) := by
    apply (iIndepFun_iff_hasLaw_Pi_infinitePi hl hp.measurable.aemeasurable).mpr
    exact ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  exact hind.comp (fun _ x => μ i + x) (fun _ => by fun_prop)

/-- Fixing the selected reference arm gives the unit-variance Gaussian observation law.
The reference noises themselves are independent of the complete PAC tape. -/
theorem fixed_referenceObservation_law (μ : Fin n → ℝ) (a : Fin n)
    (j : Fin (referenceSamples d α)) :
    HasLaw (fun ω : Tape n d α => μ a + ω.2.1 j)
      (gaussianReal (μ a) 1) (law μ d α) := by
  have hp := (measurePreserving_eval_infinitePi
    (fun _ : Fin (referenceSamples d α) => gaussianReal 0 1) j).comp (referenceNoise_preserving μ)
  have hl : HasLaw (fun ω : Tape n d α => ω.2.1 j) (gaussianReal 0 1) (law μ d α) :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  simpa only [zero_add] using gaussianReal_const_add hl (μ a)

end GapEntropy.EliminationTape
