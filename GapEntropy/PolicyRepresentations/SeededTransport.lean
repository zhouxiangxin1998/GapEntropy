import GapEntropy.PolicyRepresentations.SeededModel
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Exact transport of executions under a change of private seed

The seed map is independent of unknown means. The coupling is pointwise on every
reward table, including incorrect and infinite paths. Measure preservation then
gives equality of the entire trace law, success probabilities, and unconditional
extended-nonnegative sample expectations.
-/

open MeasureTheory ProbabilityTheory GapEntropy
open scoped ENNReal BigOperators

namespace GapEntropy.PolicyRepresentations.SeededPolicy

variable {S : Type*} [MeasurableSpace S] {n : ℕ} (A : SeededPolicy S n)

def toPolicy (f : Seed → S) (hf : Measurable f) : Policy n where
  choose hn t p := A.choose hn t (f p.1, p.2)
  measurable_choose hn t := (A.measurable_choose hn t).comp
    ((hf.comp measurable_fst).prodMk measurable_snd)

def mapSample (f : Seed → S) (ω : SampleSpace n) : SeededSampleSpace S n :=
  (f ω.1, ω.2)

theorem measurable_mapSample (f : Seed → S) (hf : Measurable f) :
    Measurable (mapSample (n := n) f) :=
  (hf.comp measurable_fst).prodMk measurable_snd

theorem mapSample_measurePreserving (μ : Measure S) [IsProbabilityMeasure μ]
    (f : Seed → S) (hf : MeasurePreserving f seedLaw μ) (mean : Fin n → ℝ) :
    MeasurePreserving (mapSample (n := n) f) (sampleLawOfMeans mean)
      (μ.prod (rewardLaw mean)) :=
  hf.prod (MeasurePreserving.id (rewardLaw mean))

theorem run_toPolicy (f : Seed → S) (hf : Measurable f) (hn : 2 ≤ n)
    (ω : SampleSpace n) (t : ℕ) :
    (A.toPolicy f hf).run hn ω t = A.run hn (mapSample f ω) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Policy.run_succ, run, ih]
    unfold Policy.step step
    cases A.run hn (mapSample f ω) t <;> rfl

theorem returnedAt_toPolicy (f : Seed → S) (hf : Measurable f) (hn : 2 ≤ n)
    (t : ℕ) (ω : SampleSpace n) :
    (A.toPolicy f hf).returnedAt hn t ω = A.returnedAt hn t (mapSample f ω) := by
  simp only [Policy.returnedAt, returnedAt, run_toPolicy]

theorem requestedArm_toPolicy (f : Seed → S) (hf : Measurable f) (hn : 2 ≤ n)
    (t : ℕ) (ω : SampleSpace n) :
    (A.toPolicy f hf).requestedArm hn t ω = A.requestedArm hn t (mapSample f ω) := by
  simp only [Policy.requestedArm, requestedArm, run_toPolicy]
  rfl

theorem sampleCount_toPolicy (f : Seed → S) (hf : Measurable f) (hn : 2 ≤ n)
    (ω : SampleSpace n) :
    (A.toPolicy f hf).sampleCount hn ω = A.sampleCount hn (mapSample f ω) := by
  unfold Policy.sampleCount sampleCount
  apply tsum_congr
  intro t
  simp only [Policy.sampleIndicator, Policy.sampleRequested, sampleIndicator, requestedArm_toPolicy]

theorem successEvent_toPolicy (f : Seed → S) (hf : Measurable f) (I : Instance n) :
    (A.toPolicy f hf).successEvent I = mapSample f ⁻¹' A.successEvent I := by
  ext ω
  simp only [Policy.successEvent, successEvent, Set.mem_ofPred_eq, Set.mem_preimage,
    returnedAt_toPolicy]

theorem traceLaw_toPolicy (μ : Measure S) [IsProbabilityMeasure μ]
    (f : Seed → S) (hf : MeasurePreserving f seedLaw μ) (I : Instance n) :
    (sampleLaw I).map (fun ω => (A.toPolicy f hf.measurable).run I.two_le ω) =
      (μ.prod (rewardLaw I.mean)).map (fun ω => A.run I.two_le ω) := by
  have hm := mapSample_measurePreserving μ f hf I.mean
  have ht : Measurable (fun ω => A.run I.two_le ω) :=
    measurable_pi_lambda _ (fun t => A.measurable_run I.two_le t)
  rw [← hm.map_eq, Measure.map_map ht hm.measurable]
  congr 1
  funext ω t
  exact A.run_toPolicy f hf.measurable I.two_le ω t

theorem successProb_toPolicy (μ : Measure S) [IsProbabilityMeasure μ]
    (f : Seed → S) (hf : MeasurePreserving f seedLaw μ) (I : Instance n) :
    (A.toPolicy f hf.measurable).successProb I = A.successProb μ I := by
  unfold Policy.successProb successProb
  rw [successEvent_toPolicy]
  exact (mapSample_measurePreserving μ f hf I.mean).measure_preimage
    (A.measurableSet_successEvent I).nullMeasurableSet

theorem expectedSamples_toPolicy (μ : Measure S) [IsProbabilityMeasure μ]
    (f : Seed → S) (hf : MeasurePreserving f seedLaw μ) (I : Instance n) :
    (A.toPolicy f hf.measurable).expectedSamples I = A.expectedSamples μ I := by
  unfold Policy.expectedSamples expectedSamples
  simp_rw [sampleCount_toPolicy]
  exact (mapSample_measurePreserving μ f hf I.mean).lintegral_comp
    (A.measurable_sampleCount I.two_le)

theorem terminates_toPolicy_iff (μ : Measure S) [IsProbabilityMeasure μ]
    (f : Seed → S) (hf : MeasurePreserving f seedLaw μ) (I : Instance n) :
    (A.toPolicy f hf.measurable).AlmostSurelyTerminates I ↔ A.AlmostSurelyTerminates μ I := by
  unfold Policy.AlmostSurelyTerminates AlmostSurelyTerminates
  simp_rw [returnedAt_toPolicy]
  have hm := mapSample_measurePreserving μ f hf I.mean
  have hp : MeasurableSet {ω : SeededSampleSpace S n |
      ∃ t i, A.returnedAt I.two_le t ω = some i} := by
    exact (Measurable.exists fun t => Measurable.exists fun i =>
      (A.measurable_returnedAt I.two_le t).eq_const (some i)).setOf
  rw [← hm.map_eq]
  exact (ae_map_iff hm.measurable.aemeasurable hp).symm

def ofPolicy (P : Policy n) : SeededPolicy Seed n where
  choose := P.choose
  measurable_choose := P.measurable_choose

@[simp] theorem toPolicy_ofPolicy (P : Policy n) :
    (ofPolicy P).toPolicy id measurable_id = P := rfl

@[simp] theorem ofPolicy_successProb (P : Policy n) (I : Instance n) :
    (ofPolicy P).successProb seedLaw I = P.successProb I := by
  exact ((ofPolicy P).successProb_toPolicy seedLaw id (MeasurePreserving.id seedLaw) I).symm

@[simp] theorem ofPolicy_expectedSamples (P : Policy n) (I : Instance n) :
    (ofPolicy P).expectedSamples seedLaw I = P.expectedSamples I := by
  exact ((ofPolicy P).expectedSamples_toPolicy seedLaw id (MeasurePreserving.id seedLaw) I).symm

@[simp] theorem ofPolicy_terminates_iff (P : Policy n) (I : Instance n) :
    (ofPolicy P).AlmostSurelyTerminates seedLaw I ↔ P.AlmostSurelyTerminates I := by
  exact ((ofPolicy P).terminates_toPolicy_iff seedLaw id (MeasurePreserving.id seedLaw) I).symm

end GapEntropy.PolicyRepresentations.SeededPolicy
