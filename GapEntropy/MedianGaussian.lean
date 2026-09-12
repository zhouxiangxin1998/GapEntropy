import GapEntropy.MedianProbability
import GapEntropy.MedianCost

/-!
# The complete Gaussian median-elimination guarantee (A.2)

Observations have their genuine unit-variance Gaussian laws. Samples within each arm
block are independent, and the whole blocks from distinct rounds are independent.
The fresh-round property of the adaptive active sets is derived, not assumed.
Unused potential observations in eliminated arms are never charged by `trajectoryCost`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GapEntropy.MedianElimination

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ}

theorem gaussian_badNext_le {S : Finset (Fin n)} {μ : Fin n → ℝ} {m : ℕ}
    (hm : 0 < m) {X : Fin n → Fin m → Ω → ℝ} {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hbudget : 8 * (ε ^ 2)⁻¹ * Real.log (8 / β) ≤ (m : ℝ))
    (hX : ∀ i j, Measurable (X i j))
    (hind : ∀ i, iIndepFun (X i) P)
    (hlaw : ∀ i j, HasLaw (X i j) (gaussianReal (μ i) 1) P) :
    P.real ((fun ω i => GapEntropy.Gaussian.sampleMean (X i) ω) ⁻¹' badNext μ ε S) ≤ β := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image S μ hS
    have hsubset : ((fun ω i => GapEntropy.Gaussian.sampleMean (X i) ω) ⁻¹' badNext μ ε S) ⊆
        GapEntropy.PACRound.failureEvent S μ (fun i => GapEntropy.Gaussian.sampleMean (X i)) a ε := by
      intro ω hω
      exact badNext_subset_failure hε.le ha hmax hω
    exact (measureReal_mono hsubset).trans
      (GapEntropy.PACRound.gaussian_failure_le_beta hm ha hε hβ hβ1 hbudget
        (fun i _ j => hX i j) (fun i _ => hind i) (fun i _ j => hlaw i j))
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [he, badNext_empty, Set.preimage_empty, measureReal_empty]
    exact hβ.le

def empiricalVectors {ε β : ℝ}
    (X : (r : ℕ) → Fin n → Fin (roundSamples ε β r) → Ω → ℝ)
    (r : ℕ) (ω : Ω) (i : Fin n) : ℝ := GapEntropy.Gaussian.sampleMean (X r i) ω

theorem empiricalVectors_measurable {ε β : ℝ}
    {X : (r : ℕ) → Fin n → Fin (roundSamples ε β r) → Ω → ℝ}
    (hX : ∀ r i j, Measurable (X r i j)) (r : ℕ) :
    Measurable (empiricalVectors X r) := by
  apply measurable_pi_lambda
  intro i
  unfold empiricalVectors GapEntropy.Gaussian.sampleMean
  fun_prop

omit [IsProbabilityMeasure P] in
theorem empiricalVectors_independent {ε β : ℝ}
    {X : (r : ℕ) → Fin n → Fin (roundSamples ε β r) → Ω → ℝ}
    (hind : iIndepFun (fun r ω i j => X r i j ω) P) :
    iIndepFun (empiricalVectors X) P := by
  let G := fun r (v : Fin n → Fin (roundSamples ε β r) → ℝ) (i : Fin n) =>
    (∑ j, v i j) / (roundSamples ε β r : ℝ)
  have hG : ∀ r, Measurable (G r) := by
    intro r
    apply measurable_pi_lambda
    intro i
    dsimp [G]
    fun_prop
  exact hind.comp G hG

/-- The full multi-round A.2 error guarantee for the actual empirical upper-half algorithm.
All hypotheses describe sample measurability, Gaussian laws, or independence; no
concentration, one-round success, or final PAC guarantee is an assumption. -/
theorem gaussian_medianEliminate_failure_le
    {S : Finset (Fin n)} (hS : S.Nonempty) {μ : Fin n → ℝ} {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {X : (r : ℕ) → Fin n → Fin (roundSamples ε β r) → Ω → ℝ}
    (hX : ∀ r i j, Measurable (X r i j))
    (hrounds : iIndepFun (fun r ω i j => X r i j ω) P)
    (hwithin : ∀ r i, iIndepFun (X r i) P)
    (hlaw : ∀ r i j, HasLaw (X r i j) (gaussianReal (μ i) 1) P) :
    P.real {ω | ¬ ∀ i ∈ S,
      μ i - ε ≤ μ (medianEliminate S hS (fun r => empiricalVectors X r ω))} ≤ β := by
  apply medianEliminate_failure_le_of_independent_rounds hS hε.le hβ.le
    (empiricalVectors_measurable hX) (empiricalVectors_independent hrounds)
  intro r _ T
  exact gaussian_badNext_le (roundSamples_pos hε hβ hβ1 r)
    (roundEpsilon_pos hε r) (roundBeta_pos hβ r) ((roundBeta_le hβ.le r).trans hβ1)
    (roundSamples_budget ε β r) (hX r) (hwithin r) (hlaw r)

/-- Success-probability form of the complete PAC guarantee. -/
theorem gaussian_medianEliminate_success_ge
    {S : Finset (Fin n)} (hS : S.Nonempty) {μ : Fin n → ℝ} {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {X : (r : ℕ) → Fin n → Fin (roundSamples ε β r) → Ω → ℝ}
    (hX : ∀ r i j, Measurable (X r i j))
    (hrounds : iIndepFun (fun r ω i j => X r i j ω) P)
    (hwithin : ∀ r i, iIndepFun (X r i) P)
    (hlaw : ∀ r i j, HasLaw (X r i j) (gaussianReal (μ i) 1) P) :
    1 - β ≤ P.real {ω | ∀ i ∈ S,
      μ i - ε ≤ μ (medianEliminate S hS (fun r => empiricalVectors X r ω))} := by
  have hout := medianEliminate_measurable S hS
    (fun r i => (measurable_pi_apply i).comp (empiricalVectors_measurable hX r))
  have hgood : MeasurableSet {ω | ∀ i ∈ S,
      μ i - ε ≤ μ (medianEliminate S hS (fun r => empiricalVectors X r ω))} :=
    hout (Set.toFinite {a : Fin n | ∀ i ∈ S, μ i - ε ≤ μ a}).measurableSet
  have hf := gaussian_medianEliminate_failure_le hS hε hβ hβ1 hX hrounds hwithin hlaw
  have hc := measureReal_compl (μ := P) hgood
  rw [probReal_univ] at hc
  change P.real {ω | ¬ ∀ i ∈ S,
    μ i - ε ≤ μ (medianEliminate S hS (fun r => empiricalVectors X r ω))} = _ at hc
  linarith

theorem declaredCost_singleton (ε β : ℝ) : declaredCost 1 ε β = 0 := by
  simp [declaredCost, cardinalSchedule]

/-- Lemma A.2, including measurable output, membership in the input set, probability
of ε-optimality, deterministic sample count, and the manuscript's sample bound.
The universal constant is instantiated as 100000. -/
theorem medianElimination_A2
    {S : Finset (Fin n)} (hS : S.Nonempty) {μ : Fin n → ℝ} {ε β : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {X : (r : ℕ) → Fin n → Fin (roundSamples ε β r) → Ω → ℝ}
    (hX : ∀ r i j, Measurable (X r i j))
    (hrounds : iIndepFun (fun r ω i j => X r i j ω) P)
    (hwithin : ∀ r i, iIndepFun (X r i) P)
    (hlaw : ∀ r i j, HasLaw (X r i j) (gaussianReal (μ i) 1) P) :
    let output := fun ω => medianEliminate S hS (fun r => empiricalVectors X r ω)
    Measurable output ∧
    (∀ ω, output ω ∈ S) ∧
    (1 - β ≤ P.real {ω | ∀ i ∈ S, μ i - ε ≤ μ (output ω)}) ∧
    (∀ ω, trajectoryCost S (fun r => empiricalVectors X r ω) ε β = declaredCost S.card ε β) ∧
    (declaredCost S.card ε β : ℝ) ≤
      100000 * (S.card : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact medianEliminate_measurable S hS
      (fun r i => (measurable_pi_apply i).comp (empiricalVectors_measurable hX r))
  · intro ω
    exact activeSets_subset S _ _ (medianEliminate_mem_terminal hS _)
  · exact gaussian_medianEliminate_success_ge hS hε hβ hβ1 hX hrounds hwithin hlaw
  · intro ω
    exact trajectoryCost_eq_declaredCost S _ ε β
  · exact declaredCost_le hS.card_pos hε hε1 hβ hβ1

end GapEntropy.MedianElimination
