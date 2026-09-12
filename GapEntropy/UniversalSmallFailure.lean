import GapEntropy.UniversalSmallHazard
import GapEntropy.UniversalFailureStream

/-! Actual small-set severe failures, from the complete conditional Gaussian flag law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace GapEntropy.UniversalSevereProcess
open UniversalAttempt
variable {n : ℕ}

def smallPayoff (S : Finset (Fin n)) (v : Fin n → Bool) : ℝ :=
  if S.card ≤ 7 ∧ ∃ i ∈ S, v i = true then 1 else 0

theorem smallPayoff_norm_le (S : Finset (Fin n)) (v : Fin n → Bool) : ‖smallPayoff S v‖ ≤ 1 := by
  unfold smallPayoff
  split_ifs <;> norm_num

theorem bernoulli_true_real (p : Fin n → unitInterval) (i : Fin n) :
    (bernoulliFlagLaw p).real {v | v i = true} = (p i : ℝ) := by
  have hm := (measurePreserving_eval (fun j => bernoulliMeasure true false (p j)) i).measure_preimage
    (measurableSet_singleton true).nullMeasurableSet
  have hh := congrArg ENNReal.toReal hm
  change (bernoulliFlagLaw p).real {v | v i = true} = (bernoulliMeasure true false (p i)).real {true} at hh
  simpa using hh

theorem bernoulli_any_real_le (p : Fin n → unitInterval) (S : Finset (Fin n)) :
    (bernoulliFlagLaw p).real {v | ∃ i ∈ S, v i = true} ≤ ∑ i ∈ S, (p i : ℝ) := by
  have he : {v : Fin n → Bool | ∃ i ∈ S, v i = true} = ⋃ i ∈ S, {v | v i = true} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [he]
  have hh := measureReal_biUnion_finset_le (μ := bernoulliFlagLaw p) S (fun i => {v | v i = true})
  simpa only [bernoulli_true_real] using hh

theorem smallPayoff_expectation_le (p : Fin n → unitInterval) (S : Finset (Fin n)) {q : ℝ}
    (hq : 0 ≤ q) (hp : ∀ i, (p i : ℝ) ≤ q) :
    (∑ v : Fin n → Bool, smallPayoff S v * (bernoulliFlagLaw p).real {v}) ≤
      if S.card ≤ 7 then 7 * q else 0 := by
  have he : (∑ v : Fin n → Bool, smallPayoff S v * (bernoulliFlagLaw p).real {v}) =
      (bernoulliFlagLaw p).real {v | S.card ≤ 7 ∧ ∃ i ∈ S, v i = true} := by
    have hi := integral_indicator_const (μ := bernoulliFlagLaw p) (1 : ℝ)
      (MeasurableSet.of_discrete : MeasurableSet {v : Fin n → Bool | S.card ≤ 7 ∧ ∃ i ∈ S, v i = true})
    rw [integral_fintype Integrable.of_finite] at hi
    simpa only [Set.indicator, Set.mem_ofPred_eq, smul_eq_mul, mul_one, one_mul, smallPayoff, mul_comm] using hi
  rw [he]
  by_cases hs : S.card ≤ 7
  · simp only [hs, true_and, if_true]
    calc
      _ ≤ ∑ i ∈ S, (p i : ℝ) := bernoulli_any_real_le p S
      _ ≤ ∑ _i ∈ S, q := Finset.sum_le_sum (fun i _ => hp i)
      _ ≤ 7 * q := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hq
  · simp [hs]

def SmallFailureAt (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ) (r : ℕ) :
    Set (SampleSpace n) :=
  {ω | (active c r ω).card ≤ 7 ∧ ∃ i ∈ active c r ω, fresh c hδ mean r ω i = true}

def SmallFailure (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ) :
    Set (SampleSpace n) := ⋃ r ∈ Finset.range c.fuel, SmallFailureAt c hδ mean r

theorem measurableSet_smallFailureAt (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (r : ℕ) : MeasurableSet (SmallFailureAt c hδ mean r) := by
  have hm := ((active_adapted c r).mono ((callFiltration c).le r) le_rfl).prodMk (fresh_measurable c hδ mean r)
  exact hm (MeasurableSet.of_discrete : MeasurableSet {p : Finset (Fin n) × (Fin n → Bool) |
    p.1.card ≤ 7 ∧ ∃ i ∈ p.1, p.2 i = true})

theorem measurableSet_smallFailure (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ) :
    MeasurableSet (SmallFailure c hδ mean) := by
  exact MeasurableSet.biUnion (Set.to_countable _) (fun r _ => measurableSet_smallFailureAt c hδ mean r)

/-- The complete actual conditional Bernoulli law bounds the chance of any
small-set flag by seven times the actual predictable severe-tail charge. -/
theorem condExp_smallPayoff_le (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (r : ℕ) :
    (sampleLawOfMeans mean)[fun ω => smallPayoff (active c r ω) (fresh c hδ mean r ω) | callPast c r] ≤ᵐ[sampleLawOfMeans mean]
      fun ω => 7 * smallRho c r ω ^ 25 := by
  have hg (v : Fin n → Bool) : StronglyMeasurable[callPast c r] (fun ω => smallPayoff (active c r ω) v) :=
    ((measurable_of_finite (fun S : Finset (Fin n) => smallPayoff S v)).comp (active_adapted c r)).stronglyMeasurable
  have hc := condExp_finite_random_payoff ((callFiltration c).le r) (fresh c hδ mean r)
    (fresh_measurable c hδ mean r) (fun ω => bernoulliFlagLaw (parameters c hδ r ω))
    (fun v ω => smallPayoff (active c r ω) v) hg 1 (by norm_num)
    (fun v ω => smallPayoff_norm_le _ _) (conditional_joint_law c hδ mean r)
  filter_upwards [hc] with ω hω
  apply hω.trans_le
  have hb := smallPayoff_expectation_le (parameters c hδ r ω) (active c r ω)
    (pow_nonneg (rho_nonneg c hδ.1.le r ω) 25) (parameters_le_rho_pow c hδ r ω)
  apply hb.trans_eq
  unfold smallRho
  split_ifs <;> norm_num

theorem smallFailureAt_real_le (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (r : ℕ) :
    (sampleLawOfMeans mean).real (SmallFailureAt c hδ mean r) ≤
      7 * ∫ ω, smallRho c r ω ^ 25 ∂sampleLawOfMeans mean := by
  have hh := integral_mono_ae (integrable_condExp (μ := sampleLawOfMeans mean))
    ((integrable_smallRho_pow c hδ.1.le mean r).const_mul 7) (condExp_smallPayoff_le c hδ mean r)
  have hm : callPast (n := n) c r ≤ (inferInstance : MeasurableSpace (SampleSpace n)) := (callFiltration c).le r
  let : IsFiniteMeasure ((sampleLawOfMeans mean).trim hm) := isFiniteMeasure_trim hm
  rw [integral_condExp (μ := sampleLawOfMeans mean) (m := callPast c r) hm, integral_const_mul] at hh
  have he : (∫ ω, smallPayoff (active c r ω) (fresh c hδ mean r ω) ∂sampleLawOfMeans mean) =
      (sampleLawOfMeans mean).real (SmallFailureAt c hδ mean r) := by
    have hi := integral_indicator_const (μ := sampleLawOfMeans mean) (1 : ℝ) (measurableSet_smallFailureAt c hδ mean r)
    simp only [Set.indicator, smul_eq_mul, mul_one] at hi
    convert! hi using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      simp only [smallPayoff, SmallFailureAt, Set.mem_ofPred_eq]
      split_ifs with h
      · exact (if_pos h).symm
      · exact (if_neg h).symm
  rwa [he] at hh

/-- E.4 within one actual attempt: random sample sizes, active sets and all
previous errors are covered by the derived chronological conditional law. -/
theorem smallFailure_real_le (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ) :
    (sampleLawOfMeans mean).real (SmallFailure c hδ mean) ≤
      7 * eta c ^ 25 * UniversalErrorBudget.indexWeight 50 c.attempt := by
  have hu := measureReal_biUnion_finset_le (μ := sampleLawOfMeans mean) (Finset.range c.fuel)
    (SmallFailureAt c hδ mean)
  have hh := hu.trans (Finset.sum_le_sum (fun r _ => smallFailureAt_real_le c hδ mean r))
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun r _ => integrable_smallRho_pow c hδ.1.le mean r)] at hh
  have hi := integral_mono_ae
    (integrable_finsetSum _ (fun r _ => integrable_smallRho_pow c hδ.1.le mean r))
    (integrable_const (smallEta c ^ 25)) (Filter.Eventually.of_forall (sum_smallRho_pow_le c hδ.1.le c.fuel))
  simp only [integral_const, probReal_univ, one_smul] at hi
  exact hh.trans (by simpa only [smallEta_pow_eq, mul_assoc] using mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ 7 by norm_num))

theorem smallFailure_measure_le (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ) :
    sampleLawOfMeans mean (SmallFailure c hδ mean) ≤
      ENNReal.ofReal (7 * eta c ^ 25 * UniversalErrorBudget.indexWeight 50 c.attempt) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (sampleLawOfMeans mean) _)]
  exact ENNReal.ofReal_le_ofReal (smallFailure_real_le c hδ mean)

end GapEntropy.UniversalSevereProcess

namespace GapEntropy.UniversalPolicy
open UniversalAttempt UniversalSevereProcess UniversalErrorBudget
variable {n : ℕ}

def SmallFailure (I : Instance n) (δ : ℝ) (hδ : ValidConfidence δ) : Set (SampleSpace n) :=
  FixedCapRetry.streamEvent (attempts n I.two_le δ) (attempt_budget_pos n I.two_le hδ)
    (fun j => UniversalSevereProcess.SmallFailure (config δ j) hδ I.mean)

theorem measurableSet_smallFailure (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    MeasurableSet (SmallFailure I δ hδ) :=
  FixedCapRetry.measurableSet_streamEvent _ _ _ (fun _ => UniversalSevereProcess.measurableSet_smallFailure _ _ _)

/-- E.4 for the actual complete retry stream. The summation charges even
unreached attempts, so no conditioning on reach or success is being assumed. -/
theorem smallFailure_measure_le (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    sampleLaw I (SmallFailure I δ hδ) ≤ ENNReal.ofReal (14 * (δ / 131072) ^ 25) := by
  have hη (j : ℕ) : eta (config δ j) = δ / 131072 := by
    unfold eta Config.errorBudget config
    ring
  have hh := FixedCapRetry.streamEvent_measure_le (attempts n I.two_le δ) (attempt_budget_pos n I.two_le hδ)
    I.mean (fun j => UniversalSevereProcess.SmallFailure (config δ j) hδ I.mean)
    (fun _ => UniversalSevereProcess.measurableSet_smallFailure _ _ _)
    (fun j => ENNReal.ofReal (7 * (δ / 131072) ^ 25 * indexWeight 50 j))
    (fun j => by
      have hx := UniversalSevereProcess.smallFailure_measure_le (config δ j) hδ I.mean
      rw [hη j] at hx
      exact hx)
  exact hh.trans (tsum_small_error_le (by linarith [hδ.1]))

/-- On every local call in every actual retry block, absence of the global
small failure event excludes an active severe flag when the active size is ≤7. -/
theorem not_smallAt_of_not_stream (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (ω : SampleSpace n) (hno : ω ∉ SmallFailure I δ hδ) (j r : ℕ) (hr : r < (config δ j).fuel) :
    shiftedSample ((FixedCapRetry.schedule (attempts n I.two_le δ) (attempt_budget_pos n I.two_le hδ)).start j) ω ∉
      SmallFailureAt (config δ j) hδ I.mean r := by
  intro hb
  apply hno
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hr, hb⟩⟩

end GapEntropy.UniversalPolicy
