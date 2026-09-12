import GapEntropy.PolicyRepresentations.SeededModel
import GapEntropy.PolicyRepresentations.Randomization
import GapEntropy.PolicyRepresentations.PairedFreshness
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Policies specified by history-dependent transition kernels

The policy input is a genuine Markov kernel, with no sampler field. The direct
state law below uses only that kernel and the independent Gaussian reward law.
The implementation obtains a measurable sampler from the randomization theorem
and uses a fresh uniform coordinate at each time.
-/

open MeasureTheory ProbabilityTheory GapEntropy
open scoped ENNReal

namespace GapEntropy.PolicyRepresentations

abbrev UniformSeed := ℕ → unitInterval

structure KernelPolicy (n : ℕ) where
  choose : 2 ≤ n → (t : ℕ) → Kernel (History n t) (Decision n)
  markov_choose : ∀ hn t, IsMarkovKernel (choose hn t)

namespace KernelPolicy

variable {n : ℕ} (K : KernelPolicy n)

instance choose_isMarkov (hn : 2 ≤ n) (t : ℕ) : IsMarkovKernel (K.choose hn t) :=
  K.markov_choose hn t

private theorem decisionNonempty (hn : 2 ≤ n) : Nonempty (Decision n) :=
  ⟨Sum.inl ⟨0, by omega⟩⟩

noncomputable def toSeeded : SeededPolicy UniformSeed n where
  choose hn t p := by
    haveI := decisionNonempty hn
    exact kernelUniformSampler (K.choose hn t) p.2 (p.1 t)
  measurable_choose hn t := by
    have := decisionNonempty hn
    exact (measurable_kernelUniformSampler (K.choose hn t)).comp
      (measurable_snd.prodMk ((measurable_pi_apply t).comp measurable_fst))

abbrev Row (n : ℕ) := Fin n → ℝ

noncomputable def rowLaw (mean : Fin n → ℝ) : Measure (Row n) :=
  Measure.pi (fun i => gaussianReal (mean i) 1)

instance rowLaw_probability (mean : Fin n → ℝ) : IsProbabilityMeasure (rowLaw mean) := by
  unfold rowLaw
  infer_instance

/-- Apply a decision to a history and one independent reward row. -/
def actionUpdate (t : ℕ) (p : (History n t × Row n) × Decision n) : RunState n (t + 1) :=
  p.2.elim (fun i => .inr (Fin.snoc p.1.1 (i, p.1.2 i))) (fun i => .inl i)

private theorem measurable_snoc (t : ℕ) :
    Measurable (fun p : History n t × Observation n =>
      (Fin.snoc p.1 p.2 : History n (t + 1))) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using
      (measurable_snd : Measurable (fun p : History n t × Observation n => p.2))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply j).comp
        (measurable_fst : Measurable (fun p : History n t × Observation n => p.1))

theorem measurable_actionUpdate (t : ℕ) : Measurable (actionUpdate (n := n) t) := by
  apply measurable_from_prod_countable_left
  intro d
  rcases d with i | i
  · exact measurable_inr.comp ((measurable_snoc t).comp
      (measurable_fst.prodMk (measurable_const.prodMk
        ((measurable_pi_apply i).comp measurable_snd))))
  · exact measurable_const

/-- Direct transition from an active history. This definition contains no sampler. -/
noncomputable def responseKernel (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    Kernel (History n t) (RunState n (t + 1)) :=
  (Kernel.id ×ₖ (K.choose hn t ×ₖ Kernel.const _ (rowLaw mean))).map
    (fun p => actionUpdate t ((p.1, p.2.2), p.2.1))

private theorem measurable_responseUpdate (t : ℕ) :
    Measurable (fun p : History n t × (Decision n × Row n) =>
      actionUpdate t ((p.1, p.2.2), p.2.1)) :=
  (measurable_actionUpdate t).comp
    ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd))

instance responseKernel_markov (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IsMarkovKernel (K.responseKernel hn mean t) := by
  unfold responseKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_responseUpdate t)

theorem responseKernel_apply (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ)
    (h : History n t) :
    K.responseKernel hn mean t h = ((K.choose hn t h).prod (rowLaw mean)).map
      (fun p => actionUpdate t ((h, p.2), p.1)) := by
  ext B hB
  rw [responseKernel, Kernel.map_apply' _ (measurable_responseUpdate t) _ hB,
    Kernel.id_prod_apply' _ _ ((measurable_responseUpdate t) hB),
    Kernel.prod_apply, Kernel.const_apply]
  rw [Measure.map_apply (show Measurable (fun p : Decision n × Row n =>
      actionUpdate t ((h, p.2), p.1)) from
    (measurable_responseUpdate t).comp (measurable_const.prodMk measurable_id)) hB]
  rfl

/-- A returned label is absorbing; an active history uses the direct response kernel. -/
noncomputable def transition (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    Kernel (RunState n t) (RunState n (t + 1)) where
  toFun := Sum.elim (fun i => Measure.dirac (Sum.inl i)) (K.responseKernel hn mean t)
  measurable' := (Measure.measurable_dirac.comp measurable_inl).sumElim
    (K.responseKernel hn mean t).measurable

instance transition_markov (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IsMarkovKernel (K.transition hn mean t) where
  isProbabilityMeasure s := by
    rcases s with i | h
    · exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (Sum.inl i)))
    · exact inferInstanceAs (IsProbabilityMeasure (K.responseKernel hn mean t h))

/-- State law by direct kernel recursion, independent of the selected samplers. -/
noncomputable def stateLaw (hn : 2 ≤ n) (mean : Fin n → ℝ) :
    (t : ℕ) → Measure (RunState n t)
  | 0 => Measure.dirac (.inr Fin.elim0)
  | t + 1 => K.transition hn mean t ∘ₘ stateLaw hn mean t

instance stateLaw_probability (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IsProbabilityMeasure (K.stateLaw hn mean t) := by
  induction t with
  | zero => exact inferInstanceAs
      (IsProbabilityMeasure (Measure.dirac (Sum.inr Fin.elim0 : RunState n 0)))
  | succ t ih =>
    have := ih
    exact inferInstanceAs
      (IsProbabilityMeasure (K.transition hn mean t ∘ₘ K.stateLaw hn mean t))

/-- The implementation at time `t` reads exactly one fresh uniform coordinate. -/
theorem run_congr_prefix (hn : 2 ≤ n) (t : ℕ)
    {ω ω' : SeededSampleSpace UniformSeed n}
    (hu : ∀ s, s < t → ω.1 s = ω'.1 s)
    (hr : ∀ s, s < t → ω.2 s = ω'.2 s) :
    K.toSeeded.run hn ω t = K.toSeeded.run hn ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun s hs => hu s (Nat.lt_succ_of_lt hs))
      (fun s hs => hr s (Nat.lt_succ_of_lt hs))
    change K.toSeeded.step hn t ω (K.toSeeded.run hn ω t) =
      K.toSeeded.step hn t ω' (K.toSeeded.run hn ω' t)
    rw [hi]
    simp only [SeededPolicy.step, toSeeded,
      hu t (Nat.lt_succ_self t), hr t (Nat.lt_succ_self t)]

def extendPairedPrefix (t : ℕ)
    (p : (Fin t → unitInterval) × (Fin t → Row n)) : SeededSampleSpace UniformSeed n :=
  ((fun s => if h : s < t then p.1 ⟨s, h⟩ else 0),
    fun s => if h : s < t then p.2 ⟨s, h⟩ else fun _ => 0)

theorem measurable_extendPairedPrefix (t : ℕ) :
    Measurable (extendPairedPrefix (n := n) t) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro s
    by_cases h : s < t
    · simpa only [extendPairedPrefix, dif_pos h, Function.comp_def] using
        (measurable_pi_apply (⟨s, h⟩ : Fin t)).comp
          (measurable_fst : Measurable (fun p : (Fin t → unitInterval) ×
            (Fin t → Row n) => p.1))
    · simpa only [extendPairedPrefix, dif_neg h] using
        (measurable_const : Measurable (fun _ : (Fin t → unitInterval) ×
          (Fin t → Row n) => (0 : unitInterval)))
  · apply measurable_pi_lambda
    intro s
    by_cases h : s < t
    · simpa only [extendPairedPrefix, dif_pos h, Function.comp_def] using
        (measurable_pi_apply (⟨s, h⟩ : Fin t)).comp
          (measurable_snd : Measurable (fun p : (Fin t → unitInterval) ×
            (Fin t → Row n) => p.2))
    · simpa only [extendPairedPrefix, dif_neg h] using
        (measurable_const : Measurable (fun _ : (Fin t → unitInterval) ×
          (Fin t → Row n) => (fun _ : Fin n => (0 : ℝ))))

noncomputable def runFromPrefix (hn : 2 ≤ n) (t : ℕ)
    (p : (Fin t → unitInterval) × (Fin t → Row n)) : RunState n t :=
  K.toSeeded.run hn (extendPairedPrefix t p) t

theorem measurable_runFromPrefix (hn : 2 ≤ n) (t : ℕ) :
    Measurable (K.runFromPrefix hn t) :=
  (K.toSeeded.measurable_run hn t).comp (measurable_extendPairedPrefix t)

theorem run_eq_runFromPrefix (hn : 2 ≤ n) (t : ℕ)
    (ω : SeededSampleSpace UniformSeed n) :
    K.toSeeded.run hn ω t = K.runFromPrefix hn t (pairedPrefix t ω) := by
  apply K.run_congr_prefix hn t
  · intro s hs
    simp [pairedPrefix, extendPairedPrefix, hs]
  · intro s hs
    simp [pairedPrefix, extendPairedPrefix, hs]

theorem indepFun_run_freshPair (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IndepFun (fun ω => K.toSeeded.run hn ω t) (freshPair t) (freshnessLaw mean) := by
  have hi := (indepFun_pairedPrefix_freshPair mean t).comp
    (K.measurable_runFromPrefix hn t) measurable_id
  convert hi using 1
  · funext ω
    exact K.run_eq_runFromPrefix hn t ω
  · rfl

noncomputable def noiseLaw (mean : Fin n → ℝ) : Measure (unitInterval × Row n) :=
  (volume : Measure unitInterval).prod (rowLaw mean)

instance noiseLaw_probability (mean : Fin n → ℝ) : IsProbabilityMeasure (noiseLaw mean) := by
  unfold noiseLaw
  infer_instance

/-- The deterministic update driven by a single uniform and one reward row. -/
noncomputable def noiseUpdate (hn : 2 ≤ n) (t : ℕ)
    (p : RunState n t × (unitInterval × Row n)) : RunState n (t + 1) :=
  K.toSeeded.step hn t ((fun _ => p.2.1), (fun _ => p.2.2)) p.1

theorem measurable_noiseUpdate (hn : 2 ≤ n) (t : ℕ) :
    Measurable (K.noiseUpdate hn t) := by
  unfold noiseUpdate
  exact (K.toSeeded.measurable_step hn t).comp
    (((measurable_pi_lambda _ (fun _ => measurable_fst.comp measurable_snd)).prodMk
    (measurable_pi_lambda _ (fun _ => measurable_snd.comp measurable_snd))).prodMk
      measurable_fst)

theorem run_succ_eq_noiseUpdate (hn : 2 ≤ n) (t : ℕ)
    (ω : SeededSampleSpace UniformSeed n) :
    K.toSeeded.run hn ω (t + 1) =
      K.noiseUpdate hn t (K.toSeeded.run hn ω t, freshPair t ω) := by
  rfl

/-- The implemented single step has the direct kernel's law at every state. -/
theorem noiseUpdate_map (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) (s : RunState n t) :
    (noiseLaw mean).map (fun p => K.noiseUpdate hn t (s, p)) =
      K.transition hn mean t s := by
  have := decisionNonempty hn
  rcases s with i | h
  · change (noiseLaw mean).map (fun _ => (Sum.inl i : RunState n (t + 1))) =
      Measure.dirac (Sum.inl i)
    simp
  · change (noiseLaw mean).map (fun p => actionUpdate t
        ((h, p.2), kernelUniformSampler (K.choose hn t) h p.1)) =
      K.responseKernel hn mean t h
    rw [K.responseKernel_apply hn mean t h]
    have hm : MeasurePreserving (kernelUniformSampler (K.choose hn t) h)
        (volume : Measure unitInterval) (K.choose hn t h) :=
      ⟨(measurable_kernelUniformSampler (K.choose hn t)).comp
        (measurable_const.prodMk measurable_id), kernelUniformSampler_map _ h⟩
    have hp := hm.prod (MeasurePreserving.id (rowLaw mean))
    have hg : Measurable (fun p : Decision n × Row n =>
        actionUpdate t ((h, p.2), p.1)) :=
      (measurable_responseUpdate t).comp (measurable_const.prodMk measurable_id)
    rw [← hp.map_eq, Measure.map_map hg hp.measurable]
    rfl

theorem map_noiseUpdate_prod (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ)
    (μ : Measure (RunState n t)) :
    (μ.prod (noiseLaw mean)).map (K.noiseUpdate hn t) =
      K.transition hn mean t ∘ₘ μ := by
  ext B hB
  rw [Measure.map_apply (K.measurable_noiseUpdate hn t) hB,
    Measure.prod_apply ((K.measurable_noiseUpdate hn t) hB),
    Measure.bind_apply hB (K.transition hn mean t).aemeasurable]
  apply lintegral_congr
  intro s
  have hm : Measurable (fun p : unitInterval × Row n => K.noiseUpdate hn t (s, p)) :=
    (K.measurable_noiseUpdate hn t).comp (measurable_const.prodMk measurable_id)
  rw [← K.noiseUpdate_map hn mean t s, Measure.map_apply hm hB]
  rfl

/-- Exact finite-time law equality with the independently defined kernel recursion. -/
theorem run_map_eq_stateLaw (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    (freshnessLaw mean).map (fun ω => K.toSeeded.run hn ω t) =
      K.stateLaw hn mean t := by
  induction t with
  | zero =>
    change (freshnessLaw mean).map (fun _ => (Sum.inr Fin.elim0 : RunState n 0)) = _
    simp [stateLaw]
  | succ t ih =>
    have hpair : (freshnessLaw mean).map
        (fun ω => (K.toSeeded.run hn ω t, freshPair t ω)) =
        (K.stateLaw hn mean t).prod (noiseLaw mean) := by
      rw [(K.indepFun_run_freshPair hn mean t).map_prod_eq_prod_map_map
        (K.toSeeded.measurable_run hn t).aemeasurable
        (measurable_freshPair t).aemeasurable, ih,
        (measurePreserving_freshPair mean t).map_eq]
      rfl
    rw [show (fun ω => K.toSeeded.run hn ω (t + 1)) = K.noiseUpdate hn t ∘
      (fun ω => (K.toSeeded.run hn ω t, freshPair t ω)) from rfl,
      ← Measure.map_map (K.measurable_noiseUpdate hn t)
        ((K.toSeeded.measurable_run hn t).prodMk (measurable_freshPair t)),
      hpair, K.map_noiseUpdate_prod hn mean t]
    rfl

@[simp] theorem transition_return (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ)
    (i : Fin n) : K.transition hn mean t (.inl i) = Measure.dirac (.inl i) := rfl

/-- A sample decision reveals exactly the selected arm's unit-variance Gaussian. -/
theorem actionUpdate_sample_map (mean : Fin n → ℝ) (t : ℕ) (h : History n t)
    (i : Fin n) :
    (rowLaw mean).map (fun r => actionUpdate t ((h, r), .inl i)) =
      (gaussianReal (mean i) 1).map
        (fun x => (Sum.inr (Fin.snoc h (i, x)) : RunState n (t + 1))) := by
  have hm := measurePreserving_eval (fun i => gaussianReal (mean i) 1) i
  have hf : Measurable (fun x : ℝ => (Sum.inr (Fin.snoc h (i, x)) :
      RunState n (t + 1))) :=
    measurable_inr.comp ((measurable_snoc t).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  rw [← hm.map_eq, Measure.map_map hf hm.measurable]
  rfl

def activeStates (t : ℕ) : Set (RunState n t) := Set.range Sum.inr

theorem measurableSet_activeStates (t : ℕ) : MeasurableSet (activeStates (n := n) t) :=
  measurableSet_range_inr

/-- Direct unconditional cost, counting one sample exactly when the next state is active. -/
noncomputable def expectedSamples (I : Instance n) : ℝ≥0∞ :=
  ∑' t, K.stateLaw I.two_le I.mean (t + 1) (activeStates (t + 1))

/-- Direct eventual success probability, obtained from the absorbing return states. -/
noncomputable def successProb (I : Instance n) : ℝ≥0∞ :=
  ⨆ t, K.stateLaw I.two_le I.mean t {Sum.inl I.best}

theorem sampleIndicator_eq_active (hn : 2 ≤ n) (t : ℕ)
    (ω : SeededSampleSpace UniformSeed n) :
    K.toSeeded.sampleIndicator hn t ω =
      (activeStates (t + 1)).indicator 1 (K.toSeeded.run hn ω (t + 1)) := by
  classical
  cases hr : K.toSeeded.run hn ω t with
  | inl i =>
    simp [SeededPolicy.sampleIndicator, SeededPolicy.requestedArm,
      SeededPolicy.run, SeededPolicy.step, hr, activeStates]
  | inr h =>
    cases hd : K.toSeeded.choose hn t (ω.1, h) with
    | inl i =>
      simp [SeededPolicy.sampleIndicator, SeededPolicy.requestedArm,
        SeededPolicy.run, SeededPolicy.step, hr, hd, activeStates]
    | inr i =>
      simp [SeededPolicy.sampleIndicator, SeededPolicy.requestedArm,
        SeededPolicy.run, SeededPolicy.step, hr, hd, activeStates]

theorem toSeeded_expectedSamples_eq (I : Instance n) :
    K.toSeeded.expectedSamples freshnessUniformLaw I = K.expectedSamples I := by
  unfold SeededPolicy.expectedSamples SeededPolicy.sampleCount expectedSamples
  rw [lintegral_tsum (fun t => (K.toSeeded.measurable_sampleIndicator I.two_le t).aemeasurable)]
  apply tsum_congr
  intro t
  simp_rw [K.sampleIndicator_eq_active]
  rw [← lintegral_map (show Measurable ((activeStates (n := n) (t + 1)).indicator
      (1 : RunState n (t + 1) → ℝ≥0∞)) from
    measurable_const.indicator (measurableSet_activeStates (t + 1)))
      (K.toSeeded.measurable_run I.two_le (t + 1))]
  change ∫⁻ s, (activeStates (t + 1)).indicator 1 s
    ∂((freshnessLaw I.mean).map (fun ω => K.toSeeded.run I.two_le ω (t + 1))) = _
  rw [K.run_map_eq_stateLaw]
  exact lintegral_indicator_one (measurableSet_activeStates (t + 1))

theorem run_return_persists (hn : 2 ≤ n) {s t : ℕ} (hst : s ≤ t)
    (ω : SeededSampleSpace UniformSeed n) (i : Fin n)
    (hs : K.toSeeded.run hn ω s = Sum.inl i) :
    K.toSeeded.run hn ω t = Sum.inl i := by
  induction t, hst using Nat.le_induction with
  | base => exact hs
  | succ t _ ih => simp [SeededPolicy.run, SeededPolicy.step, ih]

theorem toSeeded_successProb_eq (I : Instance n) :
    K.toSeeded.successProb freshnessUniformLaw I = K.successProb I := by
  have hmono : Monotone (fun t =>
      {ω : SeededSampleSpace UniformSeed n | K.toSeeded.run I.two_le ω t = Sum.inl I.best}) := by
    intro s t hst ω hω
    exact K.run_return_persists I.two_le hst ω I.best hω
  have hevent : K.toSeeded.successEvent I = ⋃ t,
      {ω | K.toSeeded.run I.two_le ω t = Sum.inl I.best} := by
    ext ω
    simp only [SeededPolicy.successEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
    apply exists_congr
    intro t
    unfold SeededPolicy.returnedAt
    cases K.toSeeded.run I.two_le ω t <;> simp
  unfold SeededPolicy.successProb successProb
  rw [hevent, hmono.measure_iUnion]
  apply iSup_congr
  intro t
  have hret : MeasurableSet ({Sum.inl I.best} : Set (RunState n t)) := by
    have hh : MeasurableSet
        ((@Sum.inl (Fin n) (History n t)) '' {I.best}) :=
      (measurableSet_singleton I.best).inl_image
    simpa only [Set.image_singleton] using hh
  rw [← K.run_map_eq_stateLaw I.two_le I.mean t,
    Measure.map_apply (K.toSeeded.measurable_run I.two_le t) hret]
  rfl

/-- Direct total return probability. No almost-sure termination is presumed. -/
noncomputable def terminationProb (I : Instance n) : ℝ≥0∞ :=
  ⨆ t, K.stateLaw I.two_le I.mean t (Set.range Sum.inl)

def AlmostSurelyTerminates (I : Instance n) : Prop := K.terminationProb I = 1

theorem toSeeded_terminates_iff (I : Instance n) :
    K.toSeeded.AlmostSurelyTerminates freshnessUniformLaw I ↔ K.AlmostSurelyTerminates I := by
  have hmono : Monotone (fun t =>
      {ω : SeededSampleSpace UniformSeed n |
        K.toSeeded.run I.two_le ω t ∈ Set.range Sum.inl}) := by
    intro s t hst ω hω
    obtain ⟨i, hi⟩ := hω
    exact ⟨i, (K.run_return_persists I.two_le hst ω i hi.symm).symm⟩
  have hevent : {ω : SeededSampleSpace UniformSeed n |
      ∃ t i, K.toSeeded.returnedAt I.two_le t ω = some i} =
      ⋃ t, {ω | K.toSeeded.run I.two_le ω t ∈ Set.range Sum.inl} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    apply exists_congr
    intro t
    unfold SeededPolicy.returnedAt
    cases K.toSeeded.run I.two_le ω t <;> simp
  unfold SeededPolicy.AlmostSurelyTerminates AlmostSurelyTerminates terminationProb
  rw [ae_iff_prob_eq_one (Measurable.exists (fun t => Measurable.exists (fun i =>
    (K.toSeeded.measurable_returnedAt I.two_le t).eq_const (some i)))),
    hevent, hmono.measure_iUnion]
  apply Iff.of_eq
  apply congrArg (fun x : ℝ≥0∞ => x = 1)
  apply iSup_congr
  intro t
  rw [← K.run_map_eq_stateLaw I.two_le I.mean t,
    Measure.map_apply (K.toSeeded.measurable_run I.two_le t) measurableSet_range_inl]
  rfl

end KernelPolicy
end GapEntropy.PolicyRepresentations
