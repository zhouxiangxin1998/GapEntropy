import GapEntropy.UniversalCallGaussian

/-!
# Joint observations and past-event factorization

The coordinate law is proved from the actual reward table. The vector includes
unused coordinates for inactive labels only to give a uniform product law;
on every active label it is exactly the procedure's observed sample block.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape GaussianBlocks
variable {n : ℕ}

theorem reward_coordinates_independent (mean : Fin n → ℝ) :
    iIndepFun (fun p : ℕ × Fin n => fun ω : SampleSpace n => ω.2 p.1 p.2)
      (sampleLawOfMeans mean) := by
  apply iIndepFun_uncurry' (fun _ _ => by fun_prop) (rows_independent mean)
  intro t
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    (show Measurable (fun ω : SampleSpace n => ω.2 t i) by fun_prop).aemeasurable)).mpr
  have hp := (measurePreserving_eval_infinitePi
    (fun _ : ℕ => Measure.pi (fun i => gaussianReal (mean i) 1)) t).comp
      (measurePreserving_snd (μ := seedLaw) (ν := rewardLaw mean))
  simp_rw [sampleLawOfMeans_map_reward]
  exact hp.map_eq

theorem schedule_observations_independent (S : Finset (Fin n)) (start m : ℕ)
    (mean : Fin n → ℝ) :
    iIndepFun (fun p : Fin n × Fin m =>
      MedianPolicy.fixedObservation S start p.1 p.2) (sampleLawOfMeans mean) := by
  have hinj : Function.Injective (fun p : Fin n × Fin m =>
      (start + MedianPolicy.armRank S p.1 * m + p.2, p.1)) := by
    intro p q hpq
    have hi : p.1 = q.1 := congrArg Prod.snd hpq
    have hj := congrArg Prod.fst hpq
    apply Prod.ext hi
    apply Fin.ext
    change start + MedianPolicy.armRank S p.1 * m + p.2 =
      start + MedianPolicy.armRank S q.1 * m + q.2 at hj
    rw [hi] at hj
    exact Nat.add_left_cancel hj
  exact (reward_coordinates_independent mean).precomp hinj

/-- The entire observation array has the genuine independent Gaussian product law. -/
theorem schedule_observations_hasLaw (S : Finset (Fin n)) (start m : ℕ)
    (mean : Fin n → ℝ) :
    HasLaw (fun ω : SampleSpace n => fun p : Fin n × Fin m =>
      MedianPolicy.fixedObservation S start p.1 p.2 ω)
      (Measure.pi (fun p : Fin n × Fin m => gaussianReal (mean p.1) 1))
      (sampleLawOfMeans mean) :=
  (schedule_observations_independent S start m mean).hasLaw_pi
    (fun p => MedianPolicy.fixedObservation_hasLaw S start mean p.1 p.2)

/-- Centering yields the full standard-normal product, with no law hypothesis. -/
theorem schedule_noises_hasLaw (S : Finset (Fin n)) (start m : ℕ)
    (mean : Fin n → ℝ) :
    HasLaw (fun ω : SampleSpace n => fun p : Fin n × Fin m =>
      MedianPolicy.fixedObservation S start p.1 p.2 ω - mean p.1)
      (Measure.pi (fun _ : Fin n × Fin m => gaussianReal 0 1))
      (sampleLawOfMeans mean) := by
  have hi := (schedule_observations_independent S start m mean).comp
    (fun p x => x - mean p.1) (fun _ => measurable_id.sub_const _)
  apply hi.hasLaw_pi
  intro p
  simpa only [sub_self, Function.comp_def] using gaussianReal_sub_const
    (MedianPolicy.fixedObservation_hasLaw S start mean p.1 p.2) (mean p.1)

def blockEstimates (S : Finset (Fin n)) (hS : S.Nonempty) (m : ℕ)
    (v : Fin (S.card * m) → Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ j : Fin m, v ⟨MedianPolicy.armRank S i * m + j,
    by simpa only [Nat.zero_add] using active_index_lt S hS 0 m i j⟩ i) / (m : ℝ)

theorem measurable_blockEstimates (S : Finset (Fin n)) (hS : S.Nonempty) (m : ℕ) :
    Measurable (blockEstimates S hS m) := by
  unfold blockEstimates
  fun_prop

theorem blockEstimates_rewardBlock (S : Finset (Fin n)) (hS : S.Nonempty)
    (start m : ℕ) (ω : SampleSpace n) :
    blockEstimates S hS m (rewardBlock start (S.card * m) ω) = scheduleEstimate S start m ω := by
  funext i
  simp only [blockEstimates, rewardBlock, scheduleEstimate, Gaussian.sampleMean,
    MedianPolicy.fixedObservation, Nat.add_assoc]

/-- All active sample means are jointly independent of the entire past,
including the chosen reference and all reference observations. -/
theorem indepFun_prefix_scheduleEstimate (S : Finset (Fin n)) (hS : S.Nonempty)
    (start m : ℕ) (mean : Fin n → ℝ) :
    IndepFun (seedPrefix (n := n) start) (scheduleEstimate S start m) (sampleLawOfMeans mean) := by
  have h := (indepFun_seedPrefix_rewardBlock mean start (S.card * m)).comp
    measurable_id (measurable_blockEstimates S hS m)
  convert! h using 1
  funext ω
  exact (blockEstimates_rewardBlock S hS start m ω).symm

/-- Exact event form of the conditional fresh-data law. -/
theorem schedule_event_factor (S : Finset (Fin n)) (hS : S.Nonempty)
    (start m : ℕ) (mean : Fin n → ℝ) (E : Set (SeedPrefix n start)) (hE : MeasurableSet E)
    (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    (sampleLawOfMeans mean).real {ω | seedPrefix start ω ∈ E ∧ scheduleEstimate S start m ω ∈ B} =
      (sampleLawOfMeans mean).real ((seedPrefix start) ⁻¹' E) *
        (sampleLawOfMeans mean).real ((scheduleEstimate S start m) ⁻¹' B) := by
  have he := (indepFun_prefix_scheduleEstimate S hS start m mean).measure_inter_preimage_eq_mul E B hE hB
  exact (congrArg ENNReal.toReal he).trans ENNReal.toReal_mul

theorem schedule_severe_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (start : ℕ) (mean : Fin n → ℝ) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n)
    (E : Set (SeedPrefix n start)) (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω | seedPrefix start ω ∈ E ∧
      scheduleEstimate S start (activeSamples d α) ω i - mean i < -(5 * d / 16)} ≤
      (sampleLawOfMeans mean).real ((seedPrefix start) ⁻¹' E) * (α / 128) ^ 25 := by
  exact (schedule_event_factor S hS start (activeSamples d α) mean E hE
    {x | x i - mean i < -(5 * d / 16)}
    (measurableSet_lt ((measurable_pi_apply i).sub_const _) measurable_const)).trans_le
    (mul_le_mul_of_nonneg_left (schedule_severe_le S start mean hd hα hα1 i) measureReal_nonneg)

theorem schedule_upward_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (start : ℕ) (mean : Fin n → ℝ) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n)
    (E : Set (SeedPrefix n start)) (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω | seedPrefix start ω ∈ E ∧
      d / 16 ≤ scheduleEstimate S start (activeSamples d α) ω i - mean i} ≤
      (sampleLawOfMeans mean).real ((seedPrefix start) ⁻¹' E) * (α / 128) := by
  exact (schedule_event_factor S hS start (activeSamples d α) mean E hE
    {x | d / 16 ≤ x i - mean i}
    (measurableSet_le measurable_const ((measurable_pi_apply i).sub_const _))).trans_le
    (mul_le_mul_of_nonneg_left (schedule_upward_le S start mean hd hα hα1 i) measureReal_nonneg)

end GapEntropy.UniversalCall
