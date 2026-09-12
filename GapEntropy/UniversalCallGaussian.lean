import GapEntropy.UniversalCallTrace
import GapEntropy.BatchCollapse

/-! # Gaussian laws and conditional fresh-data bounds for universal calls -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape GaussianBlocks
variable {n : ℕ}

theorem indepFun_referenceArm_block (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) (m : ℕ) :
    IndepFun (referenceArm S hS d α β) (rewardBlock (medianBudget S.card d α) m)
      (sampleLawOfMeans mean) := by
  have he : referenceArm S hS d α β = EliminationPolicy.referenceArm S hS d α hn :=
    funext (referenceArm_eq_median S hS d α β hn)
  rw [he]
  exact EliminationPolicy.indepFun_referenceArm_block S hS d α hn mean m

theorem fixed_reference_deviation_le (S : Finset (Fin n)) (mean : Fin n → ℝ)
    {d α β : ℝ} (hd : 0 < d) (hβ : 0 < β) (hβ1 : β ≤ 1) (i : Fin n) :
    (sampleLawOfMeans mean).real {ω | d / 16 ≤
      |EliminationPolicy.rawReferenceMean
        (rewardBlock (medianBudget S.card d α) (referenceBudget d β) ω) i - mean i|} ≤ β := by
  let X := fun j : Fin (referenceBudget d β) => fun ω : SampleSpace n =>
    ω.2 (medianBudget S.card d α + j) i
  have hlaw (j : Fin (referenceBudget d β)) :
      HasLaw (X j) (gaussianReal (mean i) 1) (sampleLawOfMeans mean) :=
    ⟨(by dsimp [X]; fun_prop), sampleLawOfMeans_map_reward mean _ _⟩
  have h := Gaussian.sampleMean_two_sided (referenceBudget_pos hd hβ hβ1)
    (observations_independent mean i (medianBudget S.card d α)) hlaw (show 0 ≤ d / 16 by positivity)
  have ht := GaussianNoise.two_tail_of_budget hd hβ (by norm_num : (0 : ℝ) < 2)
    (show 512 * (d ^ 2)⁻¹ * Real.log (2 / β) ≤ (referenceBudget d β : ℝ) from Nat.le_ceil _)
  simpa only [EliminationPolicy.rawReferenceMean, rewardBlock, Gaussian.sampleMean, X,
    show 2 * β / 2 = β by ring] using h.trans ht

theorem reference_deviation_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α β : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (sampleLawOfMeans mean).real {ω | d / 16 ≤
      |referenceEstimate S hS d α β ω - mean (referenceArm S hS d α β ω)|} ≤ β := by
  let bad : Fin n → Set (Fin (referenceBudget d β) → Fin n → ℝ) :=
    fun i => {v | d / 16 ≤ |EliminationPolicy.rawReferenceMean v i - mean i|}
  have hb := FiniteAdaptivity.measure_adaptive_event_le (measurable_referenceArm S hS d α β)
    (indepFun_referenceArm_block S hS d α β hn mean (referenceBudget d β)) (bad := bad)
    (fun i => measurableSet_le measurable_const
      ((EliminationPolicy.measurable_rawReferenceMean i).sub_const (mean i)).abs)
    (fun i => fixed_reference_deviation_le S mean hd hβ hβ1 i)
  convert! hb using 1
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, referenceEstimate_eq_mean, bad]

/-- Upper validity needs no PAC success and remains valid if the original best
has already disappeared from the active set. -/
theorem reference_upper_failure_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α β : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (sampleLawOfMeans mean).real {ω |
      mean (referenceArm S hS d α β ω) + d / 16 < referenceEstimate S hS d α β ω} ≤ β := by
  have hsub : {ω : SampleSpace n |
      mean (referenceArm S hS d α β ω) + d / 16 < referenceEstimate S hS d α β ω} ⊆
      {ω | d / 16 ≤ |referenceEstimate S hS d α β ω - mean (referenceArm S hS d α β ω)|} := by
    intro ω hω
    change mean (referenceArm S hS d α β ω) + d / 16 < referenceEstimate S hS d α β ω at hω
    exact (by linarith : d / 16 ≤ referenceEstimate S hS d α β ω -
      mean (referenceArm S hS d α β ω)).trans (le_abs_self _)
  exact (measureReal_mono hsub (measure_ne_top (sampleLawOfMeans mean) _)).trans
    (reference_deviation_le S hS hn mean hd hβ hβ1)

theorem schedule_severe_le (S : Finset (Fin n)) (start : ℕ) (mean : Fin n → ℝ)
    {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) :
    (sampleLawOfMeans mean).real {ω |
      scheduleEstimate S start (activeSamples d α) ω i - mean i < -(5 * d / 16)} ≤ (α / 128) ^ 25 := by
  have h := Gaussian.sampleMean_lower_tail (activeSamples_pos hd hα hα1)
    (MedianPolicy.fixedObservation_independent S start mean i)
    (MedianPolicy.fixedObservation_hasLaw S start mean i) (show 0 ≤ 5 * d / 16 by positivity)
  have hb : 512 * (d ^ 2)⁻¹ * Real.log (1 / (α / 128)) ≤ (activeSamples d α : ℝ) := by
    simpa only [one_div, inv_div, one_mul, activeSamples] using
      (Nat.le_ceil (512 * (d ^ 2)⁻¹ * Real.log (128 / α)))
  have ht := BatchCollapse.severe_tail_of_budget hd (show 0 < α / 128 by positivity) hb
  apply (measureReal_mono (μ := sampleLawOfMeans mean) (h₂ := measure_ne_top _ _) ?_).trans (h.trans ht)
  intro ω hω
  exact (show scheduleEstimate S start (activeSamples d α) ω i - mean i < -(5 * d / 16) from hω).le

theorem schedule_upward_le (S : Finset (Fin n)) (start : ℕ) (mean : Fin n → ℝ)
    {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) :
    (sampleLawOfMeans mean).real {ω |
      d / 16 ≤ scheduleEstimate S start (activeSamples d α) ω i - mean i} ≤ α / 128 := by
  have h := Gaussian.sampleMean_upper_tail (activeSamples_pos hd hα hα1)
    (MedianPolicy.fixedObservation_independent S start mean i)
    (MedianPolicy.fixedObservation_hasLaw S start mean i) (show 0 ≤ d / 16 by positivity)
  have ht := GaussianNoise.two_tail_of_budget hd hα (by norm_num : (0 : ℝ) < 128)
    (show 512 * (d ^ 2)⁻¹ * Real.log (128 / α) ≤ (activeSamples d α : ℝ) from Nat.le_ceil _)
  change (sampleLawOfMeans mean).real
    {ω | d / 16 ≤ Gaussian.sampleMean (MedianPolicy.fixedObservation (m := activeSamples d α) S start i) ω - mean i} ≤ _
  linarith

theorem entry_severe_le (S : Finset (Fin n)) (hS : S.Nonempty) (mean : Fin n → ℝ)
    {d α β : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) (hi : i ∈ S) :
    (sampleLawOfMeans mean).real {ω |
      entryEstimate S hS d α β ω i - mean i < -(5 * d / 16)} ≤ (α / 128) ^ 25 := by
  simp_rw [entryEstimate_eq_schedule S hS d α β _ i hi]
  exact schedule_severe_le S _ mean hd hα hα1 i

theorem later_severe_le (S : Finset (Fin n)) (hS : S.Nonempty) (mean : Fin n → ℝ)
    {d α z : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) (hi : i ∈ S) :
    (sampleLawOfMeans mean).real {ω |
      laterEstimate S hS d α z ω i - mean i < -(5 * d / 16)} ≤ (α / 128) ^ 25 := by
  simp_rw [laterEstimate_eq_schedule S hS d α z _ i hi]
  exact schedule_severe_le S _ mean hd hα hα1 i

end GapEntropy.UniversalCall
