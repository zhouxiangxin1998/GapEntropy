import GapEntropy.Transcript
import GapEntropy.Coupling
import GapEntropy.BinaryTesting
import GapEntropy.ReturnedEvents
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tied comparison means as limits of valid unique-best instances

The tied vector raises `a` to the original best mean. Lowering the original best
coordinate by a positive amount produces a valid instance whose unique best is
`a`. Finite-horizon continuity is derived from the actual transcript KL identity
and the proved event version of Pinsker's inequality.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace GapEntropy

namespace Instance

variable {n : ℕ} (I : Instance n)

theorem mean_best_pos : 0 < I.mean I.best := by
  obtain ⟨a, ha⟩ := I.suboptimal_nonempty
  exact lt_of_le_of_lt (I.mean_mem a).1 (I.best_unique a ((I.mem_suboptimal a).mp ha))

def tiedPerturbMean (a : Fin n) (ε : ℝ) : Fin n → ℝ :=
  Function.update (Coupling.raisedMean I.mean I.best a) I.best (I.mean I.best - ε)

def tiedPerturbInstance (a : Fin n) (ha : a ≠ I.best) (ε : ℝ) (hε : 0 < ε)
    (hεle : ε ≤ I.mean I.best) : Instance n where
  mean := I.tiedPerturbMean a ε
  mean_mem i := by
    by_cases hib : i = I.best
    · subst i
      simp only [tiedPerturbMean, Function.update_self, Set.mem_Icc]
      constructor
      · linarith
      · linarith [(I.mean_mem I.best).2]
    · by_cases hia : i = a
      · subst i
        simpa [tiedPerturbMean, Coupling.raisedMean, ha] using I.mean_mem I.best
      · simpa [tiedPerturbMean, Coupling.raisedMean, hib, hia] using I.mean_mem i
  best := a
  best_unique i hia := by
    by_cases hib : i = I.best
    · subst i
      simp [tiedPerturbMean, Coupling.raisedMean, ha, hε]
    · simpa [tiedPerturbMean, Coupling.raisedMean, ha, hib, hia] using I.best_unique i hib
  two_le := I.two_le

@[simp] theorem tiedPerturbInstance_mean (a : Fin n) (ha : a ≠ I.best)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ I.mean I.best) :
    (I.tiedPerturbInstance a ha ε hε hεle).mean = I.tiedPerturbMean a ε := rfl

@[simp] theorem tiedPerturbInstance_best (a : Fin n) (ha : a ≠ I.best)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ I.mean I.best) :
    (I.tiedPerturbInstance a ha ε hε hεle).best = a := rfl

end Instance

namespace Policy

variable {n : ℕ} (A : Policy n)

def returnedNotState (tag : Fin n) (T : ℕ) : Set (RunState n T) :=
  {s | s.elim (fun i => i ≠ tag) (fun _ => False)}

theorem measurableSet_returnedNotState (tag : Fin n) (T : ℕ) :
    MeasurableSet (returnedNotState tag T) :=
  ((measurable_of_finite (fun i : Fin n => i ≠ tag)).sumElim measurable_const).setOf

theorem returnedNotState_preimage_run (hn : 2 ≤ n) (tag : Fin n) (T : ℕ) :
    (fun ω => A.run hn ω T) ⁻¹' returnedNotState tag T = A.returnedNotAt hn tag T := by
  ext ω
  cases hr : A.run hn ω T with
  | inl i => simp [returnedNotState, returnedNotAt, returnedAt, hr, eq_comm]
  | inr h => simp [returnedNotState, returnedNotAt, returnedAt, hr]

theorem map_run_returnedNotState_real (hn : 2 ≤ n) (tag : Fin n) (T : ℕ)
    (μ : Measure (SampleSpace n)) :
    (μ.map (fun ω => A.run hn ω T)).real (returnedNotState tag T) =
      μ.real (A.returnedNotAt hn tag T) := by
  rw [measureReal_def, Measure.map_apply (A.measurable_run hn T)
    (measurableSet_returnedNotState tag T), A.returnedNotState_preimage_run]
  rfl

theorem truncatedArmSamples_le_time (hn : 2 ≤ n) (T : ℕ) (i : Fin n)
    (ω : SampleSpace n) : A.truncatedArmSamples hn T i ω ≤ T := by
  apply le_trans _ (A.truncatedSamples_le_time hn T ω)
  rw [← A.sum_truncatedArmSamples]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin n => A.truncatedArmSamples hn T j ω)
    (fun _ _ => zero_le) (Finset.mem_univ i)

theorem lintegral_truncatedArmSamples_le_time (hn : 2 ≤ n) (T : ℕ) (i : Fin n)
    (μ : Measure (SampleSpace n)) [IsProbabilityMeasure μ] :
    ∫⁻ ω, A.truncatedArmSamples hn T i ω ∂μ ≤ T := by
  calc
    _ ≤ ∫⁻ _ω, (T : ℝ≥0∞) ∂μ := lintegral_mono (A.truncatedArmSamples_le_time hn T i)
    _ = T := by simp

/-- A finite-horizon information bound for an arbitrary one-coordinate shift.
Neither vector needs a unique best arm. -/
theorem klDiv_transcriptLaw_update_le (hn : 2 ≤ n) (mean : Fin n → ℝ)
    (i : Fin n) (ε : ℝ) (T : ℕ) :
    InformationTheory.klDiv (A.transcriptLaw hn mean T)
      (A.transcriptLaw hn (Function.update mean i (mean i - ε)) T) ≤
      ENNReal.ofReal ((T : ℝ) * ε ^ 2 / 2) := by
  have hc (j : Fin n) : ENNReal.ofReal ((mean j - Function.update mean i (mean i - ε) j)^2 / 2) =
      if j = i then ENNReal.ofReal (ε ^ 2 / 2) else 0 := by
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  rw [A.klDiv_transcriptLaw_eq_source_counts]
  simp_rw [hc]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc
    _ ≤ ENNReal.ofReal (ε ^ 2 / 2) * T := mul_le_mul_right
      (A.lintegral_truncatedArmSamples_le_time hn T i (sampleLawOfMeans mean)) _
    _ = ENNReal.ofReal ((T : ℝ) * ε ^ 2 / 2) := by
      rw [show (T : ℝ≥0∞) = ENNReal.ofReal (T : ℝ) by simp,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ ε ^ 2 / 2)]
      congr 1
      ring

theorem klDiv_run_update_le (hn : 2 ≤ n) (mean : Fin n → ℝ)
    (i : Fin n) (ε : ℝ) (T : ℕ) :
    InformationTheory.klDiv
      ((sampleLawOfMeans mean).map (fun ω => A.run hn ω T))
      ((sampleLawOfMeans (Function.update mean i (mean i - ε))).map (fun ω => A.run hn ω T)) ≤
      ENNReal.ofReal ((T : ℝ) * ε ^ 2 / 2) :=
  (A.klDiv_run_le_transcript hn mean _ T).trans (A.klDiv_transcriptLaw_update_le hn mean i ε T)

theorem run_event_update_abs_sub_le (hn : 2 ≤ n) (mean : Fin n → ℝ)
    (i : Fin n) (ε : ℝ) (T : ℕ) {E : Set (RunState n T)} (hE : MeasurableSet E) :
    |((sampleLawOfMeans mean).map (fun ω => A.run hn ω T)).real E -
      ((sampleLawOfMeans (Function.update mean i (mean i - ε))).map
        (fun ω => A.run hn ω T)).real E| ≤ Real.sqrt (((T : ℝ) * ε ^ 2 / 2) / 2) := by
  let μ := (sampleLawOfMeans mean).map (fun ω => A.run hn ω T)
  let ν := (sampleLawOfMeans (Function.update mean i (mean i - ε))).map (fun ω => A.run hn ω T)
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (A.measurable_run hn T).aemeasurable
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (A.measurable_run hn T).aemeasurable
  exact measure_event_abs_sub_le_sqrt μ ν hE _ (by positivity) (A.klDiv_run_update_le hn mean i ε T)

theorem tied_returnedNotAt_real_le_add (I : Instance n) (a : Fin n) (ha : a ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ I.mean I.best) (T : ℕ) :
    (sampleLawOfMeans (Coupling.raisedMean I.mean I.best a)).real
      (A.returnedNotAt I.two_le a T) ≤ δ + Real.sqrt (((T : ℝ) * ε ^ 2 / 2) / 2) := by
  let J := I.tiedPerturbInstance a ha ε hε hεle
  have hq : (sampleLawOfMeans (I.tiedPerturbMean a ε)).real
      (A.returnedNotAt I.two_le a T) ≤ δ := by
    have he := A.returnedNotEvent_real_le_of_correct J hδ (hcorrect J)
    have hs : A.returnedNotAt I.two_le a T ⊆ A.returnedNotEvent I.two_le a :=
      fun _ h => ⟨T, h⟩
    exact (measureReal_mono hs).trans he
  have hv := A.run_event_update_abs_sub_le I.two_le (Coupling.raisedMean I.mean I.best a)
    I.best ε T (measurableSet_returnedNotState a T)
  rw [A.map_run_returnedNotState_real, A.map_run_returnedNotState_real] at hv
  have hm : Function.update (Coupling.raisedMean I.mean I.best a) I.best
      (Coupling.raisedMean I.mean I.best a I.best - ε) = I.tiedPerturbMean a ε := by
    simp [Instance.tiedPerturbMean, Coupling.raisedMean, ha.symm]
  rw [hm] at hv
  linarith [le_abs_self ((sampleLawOfMeans (Coupling.raisedMean I.mean I.best a)).real
    (A.returnedNotAt I.two_le a T) - (sampleLawOfMeans (I.tiedPerturbMean a ε)).real
      (A.returnedNotAt I.two_le a T))]

/-- Correctness on actual unique-best instances controls every finite wrong
return event at the tied comparison means, by vanishing one-coordinate shifts. -/
theorem tied_returnedNotAt_real_le (I : Instance n) (a : Fin n) (ha : a ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J) (T : ℕ) :
    (sampleLawOfMeans (Coupling.raisedMean I.mean I.best a)).real
      (A.returnedNotAt I.two_le a T) ≤ δ := by
  let ε : ℕ → ℝ := fun k => I.mean I.best / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := div_pos I.mean_best_pos (by positivity)
  have hεle (k : ℕ) : ε k ≤ I.mean I.best := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
    nlinarith [I.mean_best_pos, Nat.cast_nonneg (α := ℝ) k]
  have heps : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (I.mean I.best)
    simpa only [mul_zero, mul_one_div] using h
  have hterm : Tendsto (fun k => (((T : ℝ) * ε k ^ 2 / 2) / 2)) atTop (𝓝 0) := by
    simpa using (((heps.pow 2).const_mul (T : ℝ)).div_const 2).div_const 2
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hterm
  have hlim : Tendsto (fun k => δ + Real.sqrt (((T : ℝ) * ε k ^ 2 / 2) / 2))
      atTop (𝓝 δ) := by
    simpa using tendsto_const_nhds.add hsqrt
  exact ge_of_tendsto' hlim (fun k =>
    A.tied_returnedNotAt_real_le_add I a ha hδ hcorrect (ε k) (hεpos k) (hεle k) T)

theorem tied_returnedNotAt_measure_le (I : Instance n) (a : Fin n) (ha : a ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J) (T : ℕ) :
    sampleLawOfMeans (Coupling.raisedMean I.mean I.best a)
      (A.returnedNotAt I.two_le a T) ≤ ENNReal.ofReal δ := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (sampleLawOfMeans _) _)]
  exact ENNReal.ofReal_le_ofReal (A.tied_returnedNotAt_real_le I a ha hδ hcorrect T)

/-- The full finite-return event is an increasing union of the finite-horizon
events. No almost-sure termination at the tied means is required. -/
theorem tied_returnedNotEvent_measure_le (I : Instance n) (a : Fin n) (ha : a ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J) :
    sampleLawOfMeans (Coupling.raisedMean I.mean I.best a)
      (A.returnedNotEvent I.two_le a) ≤ ENNReal.ofReal δ := by
  exact A.measure_returnedNotEvent_le_of_finite I.two_le a _ _
    (A.tied_returnedNotAt_measure_le I a ha hδ hcorrect)

theorem tied_returnedNotEvent_real_le (I : Instance n) (a : Fin n) (ha : a ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J) :
    (sampleLawOfMeans (Coupling.raisedMean I.mean I.best a)).real
      (A.returnedNotEvent I.two_le a) ≤ δ := by
  have hδnonneg : 0 ≤ δ := measureReal_nonneg.trans
    (A.returnedNotEvent_real_le_of_correct I hδ (hcorrect I))
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (A.tied_returnedNotEvent_measure_le I a ha hδ hcorrect)
  simpa only [ENNReal.toReal_ofReal hδnonneg, measureReal_def] using h

end Policy
end GapEntropy
