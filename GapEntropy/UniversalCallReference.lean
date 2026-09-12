import GapEntropy.UniversalCallReadout

/-! # The selected reference and its data precede all fresh active estimates -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape GaussianBlocks
variable {n : ℕ}

theorem measurable_referenceEstimate (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ) :
    Measurable (referenceEstimate S hS d α β) :=
  (measurable_referenceEstimateFromHistory S d α β).comp (measurable_completedHistory _)

theorem referenceArm_eq_fromPrefix (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (hn : 2 ≤ n) (T : ℕ) (hT : medianBudget S.card d α ≤ T) (ω : SampleSpace n) :
    referenceArm S hS d α β ω =
      referenceArm S hS d α β (extendPrefix T (seedPrefix T ω)) := by
  have hp : seedPrefix (medianBudget S.card d α) ω =
      seedPrefix (medianBudget S.card d α) (extendPrefix T (seedPrefix T ω)) := by
    apply Prod.ext
    · rfl
    · funext s
      simp only [seedPrefix, extendPrefix, dif_pos (s.isLt.trans_le hT)]
  rw [referenceArm_eq_median S hS d α β hn ω,
    referenceArm_eq_median S hS d α β hn (extendPrefix T (seedPrefix T ω)),
    EliminationPolicy.referenceArm_eq_fromPrefix S hS d α hn ω,
    EliminationPolicy.referenceArm_eq_fromPrefix S hS d α hn (extendPrefix T (seedPrefix T ω))]
  exact congrArg (fun p => EliminationPolicy.referenceArm S hS d α hn
    (extendPrefix (medianBudget S.card d α) p)) hp

theorem referenceEstimate_eq_fromPrefix (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (hn : 2 ≤ n) (ω : SampleSpace n) :
    referenceEstimate S hS d α β ω = referenceEstimate S hS d α β
      (extendPrefix (activeStart S.card d α β) (seedPrefix (activeStart S.card d α β) ω)) := by
  rw [referenceEstimate_eq_mean, referenceEstimate_eq_mean,
    ← referenceArm_eq_fromPrefix S hS d α β hn (activeStart S.card d α β) (Nat.le_add_right _ _) ω]
  unfold EliminationPolicy.rawReferenceMean rewardBlock
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hj : medianBudget S.card d α + j < activeStart S.card d α β := Nat.add_lt_add_left j.isLt _
  simp only [extendPrefix, seedPrefix, dif_pos hj]

/-- The reference label and the numerical z jointly depend only on the data
before the active-estimation boundary, hence are independent of fresh estimates. -/
theorem indepFun_referenceInfo_estimates (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) :
    IndepFun (fun ω => (referenceArm S hS d α β ω, referenceEstimate S hS d α β ω))
      (scheduleEstimate S (activeStart S.card d α β) (activeSamples d α))
      (sampleLawOfMeans mean) := by
  have h := (indepFun_prefix_scheduleEstimate S hS (activeStart S.card d α β)
    (activeSamples d α) mean).comp
      (((measurable_referenceArm S hS d α β).prodMk
        (measurable_referenceEstimate S hS d α β)).comp (measurable_extendPrefix _)) measurable_id
  convert! h using 1
  funext ω
  exact Prod.ext (referenceArm_eq_fromPrefix S hS d α β hn _ (Nat.le_add_right _ _) ω)
    (referenceEstimate_eq_fromPrefix S hS d α β hn ω)

/-- Severe flags obey their bound even after arbitrary measurable restrictions
on the reference data. No reference-validity event is assumed. -/
theorem entry_severe_on_reference_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α β : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) (hi : i ∈ S)
    (E : Set (Fin n × ℝ)) (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω |
      (referenceArm S hS d α β ω, referenceEstimate S hS d α β ω) ∈ E ∧
      entryEstimate S hS d α β ω i - mean i < -(5 * d / 16)} ≤
    (sampleLawOfMeans mean).real
      {ω | (referenceArm S hS d α β ω, referenceEstimate S hS d α β ω) ∈ E} * (α / 128) ^ 25 := by
  have hf := (indepFun_referenceInfo_estimates S hS d α β hn mean).measure_inter_preimage_eq_mul
    E {x : Fin n → ℝ | x i - mean i < -(5 * d / 16)} hE
    (measurableSet_lt ((measurable_pi_apply i).sub_const _) measurable_const)
  have hr := (congrArg ENNReal.toReal hf).trans ENNReal.toReal_mul
  simp_rw [entryEstimate_eq_schedule S hS d α β _ i hi]
  exact hr.trans_le (mul_le_mul_of_nonneg_left
    (schedule_severe_le S _ mean hd hα hα1 i) measureReal_nonneg)

/-- A fresh estimate of an adaptively selected reference remains accurate on
every measurable pre-estimation event with that selected label. -/
theorem reference_deviation_on_past_arm_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {d α β : ℝ}
    (hd : 0 < d) (hβ : 0 < β) (hβ1 : β ≤ 1) (i : Fin n)
    (E : Set (SeedPrefix n (medianBudget S.card d α))) (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω | seedPrefix (medianBudget S.card d α) ω ∈ E ∧
      referenceArm S hS d α β ω = i ∧
      d / 16 ≤ |referenceEstimate S hS d α β ω - mean i|} ≤
    (sampleLawOfMeans mean).real {ω | seedPrefix (medianBudget S.card d α) ω ∈ E ∧
      referenceArm S hS d α β ω = i} * β := by
  let E' : Set (SeedPrefix n (medianBudget S.card d α)) :=
    {p | p ∈ E ∧ referenceArm S hS d α β (extendPrefix (medianBudget S.card d α) p) = i}
  have hE' : MeasurableSet E' := hE.inter
    (measurableSet_eq_fun ((measurable_referenceArm S hS d α β).comp (measurable_extendPrefix _)) measurable_const)
  let B : Set (Fin (referenceBudget d β) → Fin n → ℝ) :=
    {v | d / 16 ≤ |EliminationPolicy.rawReferenceMean v i - mean i|}
  have hB : MeasurableSet B := measurableSet_le measurable_const
    ((EliminationPolicy.measurable_rawReferenceMean i).sub_const _).abs
  have hf := (indepFun_seedPrefix_rewardBlock mean (medianBudget S.card d α)
    (referenceBudget d β)).measure_inter_preimage_eq_mul E' B hE' hB
  have hr := (congrArg ENNReal.toReal hf).trans ENNReal.toReal_mul
  have hp : (seedPrefix (medianBudget S.card d α)) ⁻¹' E' =
      {ω | seedPrefix (medianBudget S.card d α) ω ∈ E ∧ referenceArm S hS d α β ω = i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, E',
      ← referenceArm_eq_fromPrefix S hS d α β hn _ le_rfl ω]
  have he : {ω | seedPrefix (medianBudget S.card d α) ω ∈ E ∧
      referenceArm S hS d α β ω = i ∧ d / 16 ≤ |referenceEstimate S hS d α β ω - mean i|} =
      (seedPrefix (medianBudget S.card d α)) ⁻¹' E' ∩
        (rewardBlock (medianBudget S.card d α) (referenceBudget d β)) ⁻¹' B := by
    rw [hp]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, B, referenceEstimate_eq_mean]
    constructor
    · rintro ⟨he, hi, hb⟩
      exact ⟨⟨he, hi⟩, by simpa only [hi] using hb⟩
    · rintro ⟨⟨he, hi⟩, hb⟩
      exact ⟨he, hi, by simpa only [hi] using hb⟩
  rw [he]
  have hb := fixed_reference_deviation_le (α := α) S mean hd hβ hβ1 i
  have hh := hr.trans_le (mul_le_mul_of_nonneg_left hb measureReal_nonneg)
  rw [hp] at hh ⊢
  exact hh

end GapEntropy.UniversalCall
