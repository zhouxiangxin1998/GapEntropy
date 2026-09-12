import GapEntropy.EliminationPolicyTrace

/-! # Gaussian error bounds of the actual elimination sampler -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.EliminationPolicy
open EliminationTape EliminationProbability GaussianBlocks

theorem referenceArm_eq_fromPrefix {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    referenceArm S hS d α hn ω = referenceArm S hS d α hn
      (extendPrefix (medianBudget S.card d α) (seedPrefix (medianBudget S.card d α) ω)) := by
  rw [referenceArm_eq_median_output, referenceArm_eq_median_output]
  unfold MedianPolicy.output MedianPolicy.completedHistory MedianPolicy.historyAt
  rw [(MedianPolicy.policy S hS (d / 8) (α / 16)).run_eq_runFromPrefix hn
    (MedianElimination.declaredCost S.card (d / 8) (α / 16)) ω]
  rfl

theorem indepFun_referenceArm_block {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (mean : Fin n → ℝ) (m : ℕ) :
    IndepFun (referenceArm S hS d α hn) (rewardBlock (medianBudget S.card d α) m)
      (sampleLawOfMeans mean) := by
  have h := (indepFun_seedPrefix_rewardBlock mean (medianBudget S.card d α) m).comp
    ((measurable_referenceArm S hS d α hn).comp (measurable_extendPrefix _)) measurable_id
  convert! h using 1
  funext ω
  exact referenceArm_eq_fromPrefix S hS d α hn ω

def rawReferenceMean {n m : ℕ} (v : Fin m → Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ j : Fin m, v j i) / (m : ℝ)

theorem measurable_rawReferenceMean {n m : ℕ} (i : Fin n) :
    Measurable (fun v : Fin m → Fin n → ℝ => rawReferenceMean v i) := by
  unfold rawReferenceMean
  fun_prop

theorem fixed_reference_deviation_le {n : ℕ} (S : Finset (Fin n)) (mean : Fin n → ℝ)
    {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) :
    (sampleLawOfMeans mean).real {ω | d / 16 ≤
      |rawReferenceMean (rewardBlock (medianBudget S.card d α) (referenceSamples d α) ω) i - mean i|}
      ≤ α / 16 := by
  let X := fun j : Fin (referenceSamples d α) => fun ω : SampleSpace n =>
    ω.2 (medianBudget S.card d α + j) i
  have hlaw (j : Fin (referenceSamples d α)) :
      HasLaw (X j) (gaussianReal (mean i) 1) (sampleLawOfMeans mean) :=
    ⟨(by dsimp [X]; fun_prop), sampleLawOfMeans_map_reward mean _ _⟩
  have h := Gaussian.sampleMean_two_sided (referenceSamples_pos hd hα hα1)
    (observations_independent mean i (medianBudget S.card d α)) hlaw (show 0 ≤ d / 16 by positivity)
  have ht := GaussianNoise.two_tail_of_budget hd hα (by norm_num : (0 : ℝ) < 32)
    (show 512 * (d ^ 2)⁻¹ * Real.log (32 / α) ≤ (referenceSamples d α : ℝ) from Nat.le_ceil _)
  have hc : 2 * α / 32 = α / 16 := by ring
  simpa only [rawReferenceMean, rewardBlock, Gaussian.sampleMean, X, hc] using h.trans ht

theorem reference_deviation_le {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) :
    (sampleLawOfMeans mean).real {ω | d / 16 ≤
      |referenceEstimate S hS d α hn ω - mean (referenceArm S hS d α hn ω)|} ≤ α / 16 := by
  let bad : Fin n → Set (Fin (referenceSamples d α) → Fin n → ℝ) :=
    fun i => {v | d / 16 ≤ |rawReferenceMean v i - mean i|}
  have hb := FiniteAdaptivity.measure_adaptive_event_le (measurable_referenceArm S hS d α hn)
    (indepFun_referenceArm_block S hS d α hn mean (referenceSamples d α)) (bad := bad)
    (fun i => measurableSet_le measurable_const ((measurable_rawReferenceMean i).sub_const (mean i)).abs)
    (fun i => fixed_reference_deviation_le S mean hd hα hα1 i)
  have he : {ω | d / 16 ≤ |referenceEstimate S hS d α hn ω - mean (referenceArm S hS d α hn ω)|} =
      {ω | rewardBlock (medianBudget S.card d α) (referenceSamples d α) ω ∈
        bad (referenceArm S hS d α hn ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, referenceEstimate_eq_rawMean, bad, rawReferenceMean, rewardBlock]
  rwa [he]

theorem active_deviation_le {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) (hi : i ∈ S) :
    (sampleLawOfMeans mean).real (deviation mean d (activeEstimate S hS d α hn) i) ≤ α / 64 := by
  have h := Gaussian.sampleMean_two_sided (activeSamples_pos hd hα hα1)
    (MedianPolicy.fixedObservation_independent S (activeStart S.card d α) mean i)
    (MedianPolicy.fixedObservation_hasLaw S (activeStart S.card d α) mean i)
    (show 0 ≤ d / 16 by positivity)
  have ht := GaussianNoise.two_tail_of_budget hd hα (by norm_num : (0 : ℝ) < 128)
    (show 512 * (d ^ 2)⁻¹ * Real.log (128 / α) ≤ (activeSamples d α : ℝ) from Nat.le_ceil _)
  have he : deviation mean d (activeEstimate S hS d α hn) i =
      {ω | d / 16 ≤ |Gaussian.sampleMean (MedianPolicy.fixedObservation
        (m := activeSamples d α) S (activeStart S.card d α) i) ω - mean i|} := by
    ext ω
    simp only [deviation, Set.mem_ofPred_eq, activeEstimate_eq_sampleMean S hS d α hn ω i hi]
  rw [he]
  simpa only [show 2 * α / 128 = α / 64 by ring] using h.trans ht

theorem pac_failure_le {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) :
    (sampleLawOfMeans mean).real {ω | ¬ ∀ i ∈ S,
      mean i - d / 8 ≤ mean (referenceArm S hS d α hn ω)} ≤ α / 16 := by
  have he : referenceArm S hS d α hn = MedianPolicy.output S hS (d / 8) (α / 16) hn :=
    funext (referenceArm_eq_median_output S hS d α hn)
  rw [he]
  exact MedianPolicy.output_failure_le S hS hn mean (by positivity) (by positivity) (by linarith)

theorem reference_bad_le {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {best : Fin n}
    (hbest : best ∈ S) (hmax : ∀ i ∈ S, mean i ≤ mean best) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) :
    (sampleLawOfMeans mean).real (referenceBad (mean best) d (referenceEstimate S hS d α hn)) ≤ α / 8 := by
  let B : Set (SampleSpace n) := {ω | ¬ ∀ i ∈ S, mean i - d / 8 ≤ mean (referenceArm S hS d α hn ω)}
  let E : Set (SampleSpace n) := {ω | d / 16 ≤
    |referenceEstimate S hS d α hn ω - mean (referenceArm S hS d α hn ω)|}
  have hsub : referenceBad (mean best) d (referenceEstimate S hS d α hn) ⊆ B ∪ E := by
    intro ω hω
    by_contra! h
    simp only [Set.mem_union, not_or] at h
    have hp : ∀ i ∈ S, mean i - d / 8 ≤ mean (referenceArm S hS d α hn ω) := not_not.mp h.1
    have he : |referenceEstimate S hS d α hn ω - mean (referenceArm S hS d α hn ω)| < d / 16 :=
      lt_of_not_ge h.2
    have hu := hmax _ (referenceArm_mem S hS d α hn ω)
    have hl := hp best hbest
    have ha := abs_lt.mp he
    apply hω
    constructor <;> linarith
  have hu := (measureReal_mono (μ := sampleLawOfMeans mean) hsub
    (measure_ne_top (sampleLawOfMeans mean) _)).trans (measureReal_union_le _ _)
  have hp := pac_failure_le S hS hn mean hd hα hα1
  have he := reference_deviation_le S hS hn mean hd hα hα1
  change (sampleLawOfMeans mean).real B ≤ α / 16 at hp
  change (sampleLawOfMeans mean).real E ≤ α / 16 at he
  linarith

end GapEntropy.EliminationPolicy
