import GapEntropy.UniversalCallReference

/-! # Public block-law guarantees of the universal primitives -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape GaussianBlocks
variable {n : ℕ}

theorem referenceError_pos {δ : ℝ} (hδ : 0 < δ) (j k : ℕ) : 0 < referenceError δ j k := by
  unfold referenceError
  positivity

theorem referenceError_le_one {δ : ℝ} (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (j k : ℕ) :
    referenceError δ j k ≤ 1 := by
  have hj : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg' (α := ℝ) j]
  have hk : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg' (α := ℝ) k]
  unfold referenceError
  apply (div_le_one (by positivity : (0 : ℝ) < 64 * ((j : ℝ) + 1) ^ 2 * ((k : ℝ) + 1) ^ 2)).mpr
  nlinarith [mul_le_mul hj hk (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg ((j : ℝ) + 1))]

theorem reference_pac_failure_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α β : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) :
    (sampleLawOfMeans mean).real {ω | ¬ ∀ i ∈ S,
      mean i - d / 8 ≤ mean (referenceArm S hS d α β ω)} ≤ α / 16 := by
  simp_rw [referenceArm_eq_median S hS d α β hn]
  exact EliminationPolicy.pac_failure_le S hS hn mean hd hα hα1

theorem reference_above_max_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α β μstar : ℝ}
    (hmax : ∀ i ∈ S, mean i ≤ μstar) (hd : 0 < d) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (sampleLawOfMeans mean).real {ω | μstar + d / 16 < referenceEstimate S hS d α β ω} ≤ β := by
  have hs : {ω : SampleSpace n | μstar + d / 16 < referenceEstimate S hS d α β ω} ⊆
      {ω | mean (referenceArm S hS d α β ω) + d / 16 < referenceEstimate S hS d α β ω} := by
    intro ω hω
    have hm := hmax _ (referenceArm_mem S hS d α β ω)
    change μstar + d / 16 < referenceEstimate S hS d α β ω at hω
    change mean (referenceArm S hS d α β ω) + d / 16 < referenceEstimate S hS d α β ω
    linarith
  exact (measureReal_mono hs (measure_ne_top (sampleLawOfMeans mean) _)).trans
    (reference_upper_failure_le S hS hn mean hd hβ hβ1)

theorem reference_below_max_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {best : Fin n} (hbest : best ∈ S) {d α β : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (sampleLawOfMeans mean).real {ω | referenceEstimate S hS d α β ω < mean best - 3 * d / 16} ≤
      α / 16 + β := by
  let B : Set (SampleSpace n) := {ω | ¬ ∀ i ∈ S, mean i - d / 8 ≤ mean (referenceArm S hS d α β ω)}
  let E : Set (SampleSpace n) := {ω | d / 16 ≤
    |referenceEstimate S hS d α β ω - mean (referenceArm S hS d α β ω)|}
  have hs : {ω | referenceEstimate S hS d α β ω < mean best - 3 * d / 16} ⊆ B ∪ E := by
    intro ω hω
    by_contra! h
    simp only [Set.mem_union, not_or] at h
    have hp : ∀ i ∈ S, mean i - d / 8 ≤ mean (referenceArm S hS d α β ω) := not_not.mp h.1
    have he : |referenceEstimate S hS d α β ω - mean (referenceArm S hS d α β ω)| < d / 16 :=
      lt_of_not_ge h.2
    have hh := hp best hbest
    have ha := (abs_lt.mp he).1
    change referenceEstimate S hS d α β ω < mean best - 3 * d / 16 at hω
    linarith
  have hu := (measureReal_mono hs (measure_ne_top (sampleLawOfMeans mean) _)).trans
    (measureReal_union_le _ _)
  exact hu.trans (add_le_add (reference_pac_failure_le S hS hn mean hd hα hα1)
    (reference_deviation_le S hS hn mean hd hβ hβ1))

/-- Entry z has its required one-sided validity bound under the finite-tape law. -/
theorem entry_reference_upper_block_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α β μstar : ℝ}
    (hmax : ∀ i ∈ S, mean i ≤ μstar) (hd : 0 < d) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (blockLaw mean (entryBudget S.card d α β)).real
      {v | μstar + d / 16 < ((entryProcedure S hS d α β).evaluate v).1} ≤ β := by
  have he := (entryProcedure S hS d α β).actualOutput_event mean
    {p : ℝ × Finset (Fin n) | μstar + d / 16 < p.1}
    (measurableSet_lt measurable_const measurable_fst)
  exact (congrArg ENNReal.toReal he).symm.trans_le
    (reference_above_max_le S hS hn mean hmax hd hβ hβ1)

theorem entry_reference_lower_block_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {best : Fin n} (hbest : best ∈ S) {d α β : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (blockLaw mean (entryBudget S.card d α β)).real
      {v | ((entryProcedure S hS d α β).evaluate v).1 < mean best - 3 * d / 16} ≤ α / 16 + β := by
  have he := (entryProcedure S hS d α β).actualOutput_event mean
    {p : ℝ × Finset (Fin n) | p.1 < mean best - 3 * d / 16}
    (measurableSet_lt measurable_fst measurable_const)
  exact (congrArg ENNReal.toReal he).symm.trans_le
    (reference_below_max_le S hS hn mean hbest hd hα hα1 hβ hβ1)

theorem blockEstimates_event_real_eq (S : Finset (Fin n)) (hS : S.Nonempty)
    (mean : Fin n → ℝ) (m : ℕ) (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    (blockLaw mean (S.card * m)).real ((blockEstimates S hS m) ⁻¹' B) =
      (sampleLawOfMeans mean).real ((scheduleEstimate S 0 m) ⁻¹' B) := by
  have he := (measurePreserving_rewardBlock mean 0 (S.card * m)).measure_preimage
    ((measurable_blockEstimates S hS m) hB).nullMeasurableSet
  have hs : rewardBlock 0 (S.card * m) ⁻¹' ((blockEstimates S hS m) ⁻¹' B) =
      (scheduleEstimate S 0 m) ⁻¹' B := by
    ext ω
    simp only [Set.mem_preimage, blockEstimates_rewardBlock]
  rw [hs] at he
  exact (congrArg ENNReal.toReal he).symm

theorem block_severe_le (S : Finset (Fin n)) (hS : S.Nonempty) (mean : Fin n → ℝ)
    {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) :
    (blockLaw mean (laterBudget S.card d α)).real {v |
      blockEstimates S hS (activeSamples d α) v i - mean i < -(5 * d / 16)} ≤ (α / 128) ^ 25 :=
  (blockEstimates_event_real_eq S hS mean (activeSamples d α)
    {x | x i - mean i < -(5 * d / 16)}
    (measurableSet_lt ((measurable_pi_apply i).sub_const _) measurable_const)).trans_le
      (schedule_severe_le S 0 mean hd hα hα1 i)

theorem block_upward_le (S : Finset (Fin n)) (hS : S.Nonempty) (mean : Fin n → ℝ)
    {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) :
    (blockLaw mean (laterBudget S.card d α)).real {v |
      d / 16 ≤ blockEstimates S hS (activeSamples d α) v i - mean i} ≤ α / 128 :=
  (blockEstimates_event_real_eq S hS mean (activeSamples d α)
    {x | d / 16 ≤ x i - mean i}
    (measurableSet_le measurable_const ((measurable_pi_apply i).sub_const _))).trans_le
      (schedule_upward_le S 0 mean hd hα hα1 i)

theorem entry_severe_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (mean : Fin n → ℝ) {d α β : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)
    (i : Fin n) (hi : i ∈ S) (E : Set (SeedPrefix n (activeStart S.card d α β)))
    (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω | seedPrefix (activeStart S.card d α β) ω ∈ E ∧
      entryEstimate S hS d α β ω i - mean i < -(5 * d / 16)} ≤
      (sampleLawOfMeans mean).real ((seedPrefix (activeStart S.card d α β)) ⁻¹' E) * (α / 128) ^ 25 := by
  simp_rw [entryEstimate_eq_schedule S hS d α β _ i hi]
  exact schedule_severe_on_past_le S hS _ mean hd hα hα1 i E hE

theorem entry_upward_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (mean : Fin n → ℝ) {d α β : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)
    (i : Fin n) (hi : i ∈ S) (E : Set (SeedPrefix n (activeStart S.card d α β)))
    (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω | seedPrefix (activeStart S.card d α β) ω ∈ E ∧
      d / 16 ≤ entryEstimate S hS d α β ω i - mean i} ≤
      (sampleLawOfMeans mean).real ((seedPrefix (activeStart S.card d α β)) ⁻¹' E) * (α / 128) := by
  simp_rw [entryEstimate_eq_schedule S hS d α β _ i hi]
  exact schedule_upward_on_past_le S hS _ mean hd hα hα1 i E hE

end GapEntropy.UniversalCall
