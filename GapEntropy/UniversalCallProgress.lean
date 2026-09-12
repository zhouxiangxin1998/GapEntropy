import GapEntropy.UniversalProgressEvents

/-!
# Actual local progress at a suitable reused reference

All deviation probabilities here are derived from the actual Gaussian reward
rows or their exact finite-block law. Past-event versions support adaptive calls.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape GaussianBlocks Elimination EliminationProbability
variable {n : ℕ}

theorem measurable_scheduleEstimate (S : Finset (Fin n)) (start m : ℕ) :
    Measurable (scheduleEstimate S start m) := by
  unfold scheduleEstimate Gaussian.sampleMean MedianPolicy.fixedObservation
  fun_prop

theorem schedule_deviation_le (S : Finset (Fin n)) (start : ℕ) (mean : Fin n → ℝ)
    {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) :
    (sampleLawOfMeans mean).real {ω |
      d / 16 ≤ |scheduleEstimate S start (activeSamples d α) ω i - mean i|} ≤ α / 64 := by
  have h := Gaussian.sampleMean_two_sided (activeSamples_pos hd hα hα1)
    (MedianPolicy.fixedObservation_independent S start mean i)
    (MedianPolicy.fixedObservation_hasLaw S start mean i) (show 0 ≤ d / 16 by positivity)
  have hb := GaussianNoise.two_tail_of_budget hd hα (by norm_num : (0 : ℝ) < 128)
    (show 512 * (d ^ 2)⁻¹ * Real.log (128 / α) ≤ (activeSamples d α : ℝ) from Nat.le_ceil _)
  simpa only [scheduleEstimate, show 2 * α / 128 = α / 64 by ring] using h.trans hb

theorem schedule_deviation_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (start : ℕ) (mean : Fin n → ℝ) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n)
    (E : Set (SeedPrefix n start)) (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω | seedPrefix start ω ∈ E ∧
      d / 16 ≤ |scheduleEstimate S start (activeSamples d α) ω i - mean i|} ≤
      (sampleLawOfMeans mean).real ((seedPrefix start) ⁻¹' E) * (α / 64) :=
  (schedule_event_factor S hS start (activeSamples d α) mean E hE
    {x | d / 16 ≤ |x i - mean i|}
    (measurableSet_le measurable_const ((measurable_pi_apply i).sub_const _).abs)).trans_le
      (mul_le_mul_of_nonneg_left (schedule_deviation_le S start mean hd hα hα1 i) measureReal_nonneg)

/-- Actual best protection, weighted by any pre-estimation history event. -/
theorem progress_best_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (start : ℕ) (mean : Fin n → ℝ) {best : Fin n} (hbest : best ∈ S) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (Z : SampleSpace n → ℝ)
    (E : Set (SeedPrefix n start)) (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω | seedPrefix start ω ∈ E ∧ Suitable (mean best) d (Z ω) ∧
      best ∉ padded S (scheduleEstimate S start (activeSamples d α) ω) (Z ω) d} ≤
      (sampleLawOfMeans mean).real ((seedPrefix start) ⁻¹' E) * (α / 64) :=
  protected_failure_of_deviation hbest hd.le (schedule_deviation_on_past_le S hS start mean hd hα hα1 best E hE)

/-- Large-set nonhalving has its sharper α/16 allocation. -/
theorem progress_halving_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (start : ℕ) (mean : Fin n → ℝ) {best : Fin n} {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (Z : SampleSpace n → ℝ)
    (E : Set (SeedPrefix n start)) (hE : MeasurableSet E)
    {N : ℕ} (hnear : (near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (sampleLawOfMeans mean).real {ω | seedPrefix start ω ∈ E ∧ Suitable (mean best) d (Z ω) ∧
      (padded S (scheduleEstimate S start (activeSamples d α) ω) (Z ω) d).card ≠ (S.card + 1) / 2} ≤
      (sampleLawOfMeans mean).real ((seedPrefix start) ⁻¹' E) * (α / 16) :=
  halving_failure_of_deviations hS hd.le ((measurable_prefix start) hE)
    (fun i => (measurable_pi_apply i).comp (measurable_scheduleEstimate S start _))
    (fun i _ => schedule_deviation_on_past_le S hS start mean hd hα hα1 i E hE) hnear hs

/-- Small-set raw isolation, preserving the distinction from its padded output. -/
theorem progress_isolation_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (start : ℕ) (mean : Fin n → ℝ) {best : Fin n} (hbest : best ∈ S) {d α : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (Z : SampleSpace n → ℝ)
    (E : Set (SeedPrefix n start)) (hE : MeasurableSet E)
    (hs : S.card ≤ 4) (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (sampleLawOfMeans mean).real {ω | seedPrefix start ω ∈ E ∧ Suitable (mean best) d (Z ω) ∧
      raw S (scheduleEstimate S start (activeSamples d α) ω) (Z ω) d ≠ {best}} ≤
      (sampleLawOfMeans mean).real ((seedPrefix start) ⁻¹' E) * (α / 16) :=
  isolation_failure_of_deviations hbest hd.le (by positivity)
    (fun i _ => schedule_deviation_on_past_le S hS start mean hd hα hα1 i E hE) hs hgaps

theorem block_deviation_le (S : Finset (Fin n)) (hS : S.Nonempty) (mean : Fin n → ℝ)
    {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (i : Fin n) :
    (blockLaw mean (laterBudget S.card d α)).real {v |
      d / 16 ≤ |blockEstimates S hS (activeSamples d α) v i - mean i|} ≤ α / 64 :=
  (blockEstimates_event_real_eq S hS mean (activeSamples d α) {x | d / 16 ≤ |x i - mean i|}
    (measurableSet_le measurable_const ((measurable_pi_apply i).sub_const _).abs)).trans_le
      (schedule_deviation_le S 0 mean hd hα hα1 i)

theorem later_best_failure_le (S : Finset (Fin n)) (hS : S.Nonempty) (mean : Fin n → ℝ)
    {best : Fin n} (hbest : best ∈ S) {d α z : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (hz : Suitable (mean best) d z) :
    (blockLaw mean (laterBudget S.card d α)).real
      {v | best ∉ (laterProcedure S hS d α z).evaluate v} ≤ α / 64 := by
  have hh := protected_failure_of_deviation (P := blockLaw mean (laterBudget S.card d α))
    (X := fun i v => blockEstimates S hS (activeSamples d α) v i) (Z := fun _ => z)
    (R := Set.univ) (p := 1) (α := α) hbest hd.le
    (by simpa only [Set.univ_inter, one_mul, deviation] using block_deviation_le S hS mean hd hα hα1 best)
  have he : {v : Fin (laterBudget S.card d α) → Fin n → ℝ |
      best ∉ (laterProcedure S hS d α z).evaluate v} =
      {v | best ∉ padded S (blockEstimates S hS (activeSamples d α) v) z d} := by
    ext v
    exact (congrArg (fun U => best ∉ U) (later_evaluate_eq S hS d α z v)).to_iff
  exact (congrArg (fun E => (blockLaw mean (laterBudget S.card d α)).real E) he).trans_le
    (by
      simp only [Set.mem_univ, hz, true_and, one_mul] at hh
      convert! hh using 1)

theorem later_halving_failure_le (S : Finset (Fin n)) (hS : S.Nonempty) (mean : Fin n → ℝ)
    {best : Fin n} {d α z : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)
    (hz : Suitable (mean best) d z) {N : ℕ}
    (hnear : (near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (blockLaw mean (laterBudget S.card d α)).real
      {v | ((laterProcedure S hS d α z).evaluate v).card ≠ (S.card + 1) / 2} ≤ α / 16 := by
  have hh := halving_failure_of_deviations (P := blockLaw mean (laterBudget S.card d α))
    (X := fun i v => blockEstimates S hS (activeSamples d α) v i) (Z := fun _ => z)
    (R := Set.univ) (p := 1) (α := α) hS hd.le MeasurableSet.univ
    (fun i => (measurable_pi_apply i).comp (measurable_blockEstimates S hS _))
    (fun i _ => by simpa only [Set.univ_inter, one_mul, deviation] using block_deviation_le S hS mean hd hα hα1 i) hnear hs
  have he : {v : Fin (laterBudget S.card d α) → Fin n → ℝ |
      ((laterProcedure S hS d α z).evaluate v).card ≠ (S.card + 1) / 2} =
      {v | (padded S (blockEstimates S hS (activeSamples d α) v) z d).card ≠ (S.card + 1) / 2} := by
    ext v
    exact (congrArg (fun U => U.card ≠ (S.card + 1) / 2)
      (later_evaluate_eq S hS d α z v)).to_iff
  exact (congrArg (fun E => (blockLaw mean (laterBudget S.card d α)).real E) he).trans_le
    (by
      simp only [Set.mem_univ, hz, true_and, one_mul] at hh
      convert! hh using 1)

theorem later_raw_isolation_failure_le (S : Finset (Fin n)) (hS : S.Nonempty) (mean : Fin n → ℝ)
    {best : Fin n} (hbest : best ∈ S) {d α z : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (hz : Suitable (mean best) d z)
    (hs : S.card ≤ 4) (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (blockLaw mean (laterBudget S.card d α)).real
      {v | raw S (blockEstimates S hS (activeSamples d α) v) z d ≠ {best}} ≤ α / 16 := by
  have hh := isolation_failure_of_deviations (P := blockLaw mean (laterBudget S.card d α))
    (X := fun i v => blockEstimates S hS (activeSamples d α) v i) (Z := fun _ => z)
    (R := Set.univ) (p := 1) (α := α) hbest hd.le (by positivity)
    (fun i _ => by simpa only [Set.univ_inter, one_mul, deviation] using block_deviation_le S hS mean hd hα hα1 i) hs hgaps
  simpa only [Set.mem_univ, hz, true_and, one_mul] using hh

/-- The entry PAC failure and the absolute reference-estimation failure are each
charged once; upper and lower invalidity do not duplicate β. -/
theorem reference_unsuitable_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {best : Fin n} (hbest : best ∈ S)
    (hmax : ∀ i ∈ S, mean i ≤ mean best) {d α β : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (sampleLawOfMeans mean).real {ω | ¬ Suitable (mean best) d (referenceEstimate S hS d α β ω)} ≤
      α / 16 + β := by
  let B : Set (SampleSpace n) := {ω | ¬ ∀ i ∈ S, mean i - d / 8 ≤ mean (referenceArm S hS d α β ω)}
  let E : Set (SampleSpace n) := {ω | d / 16 ≤
    |referenceEstimate S hS d α β ω - mean (referenceArm S hS d α β ω)|}
  have hs : {ω | ¬ Suitable (mean best) d (referenceEstimate S hS d α β ω)} ⊆ B ∪ E := by
    intro ω hω
    by_contra! h
    simp only [Set.mem_union, not_or] at h
    have hp : ∀ i ∈ S, mean i - d / 8 ≤ mean (referenceArm S hS d α β ω) := not_not.mp h.1
    have he : |referenceEstimate S hS d α β ω - mean (referenceArm S hS d α β ω)| < d / 16 :=
      lt_of_not_ge h.2
    have hlo := hp best hbest
    have hhi := hmax _ (referenceArm_mem S hS d α β ω)
    have ha := abs_lt.mp he
    apply hω
    constructor <;> linarith
  exact ((measureReal_mono hs (measure_ne_top (sampleLawOfMeans mean) _)).trans
    (measureReal_union_le _ _)).trans
      (add_le_add (reference_pac_failure_le S hS hn mean hd hα hα1)
        (reference_deviation_le S hS hn mean hd hβ hβ1))

end GapEntropy.UniversalCall
