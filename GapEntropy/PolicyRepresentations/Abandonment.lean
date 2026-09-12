import GapEntropy.PolicyRepresentations.SeededModel

/-!
# Removing explicit abandonment without increasing sample cost

An abandonment policy can explicitly stop without returning a label. Its
operational run is defined independently below, with absorbing abandoned states.
Replacing this action by an immediate fixed-label return preserves every sample
request and can only enlarge the correct-output event. This does not model
unobservable infinite internal computation between external decisions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory GapEntropy
open scoped ENNReal BigOperators

namespace GapEntropy.PolicyRepresentations

instance (n : ℕ) : MeasurableSpace (Option (Decision n)) := ⊤

structure AbandonPolicy (S : Type*) [MeasurableSpace S] (n : ℕ) where
  choose : 2 ≤ n → (t : ℕ) → S × History n t → Option (Decision n)
  measurable_choose : ∀ hn t, Measurable (choose hn t)

namespace AbandonPolicy

abbrev State (n t : ℕ) := Option (Fin n) ⊕ History n t

variable {S : Type*} [MeasurableSpace S] {n : ℕ} (A : AbandonPolicy S n)

def step (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) (s : State n t) :
    State n (t + 1) :=
  s.elim (fun o => .inl o) (fun h =>
    (A.choose hn t (ω.1, h)).elim (.inl none) (fun d =>
      d.elim (fun i => .inr (Fin.snoc h (i, ω.2 t i))) (fun i => .inl (some i))))

def run (hn : 2 ≤ n) (ω : SeededSampleSpace S n) : (t : ℕ) → State n t
  | 0 => .inr Fin.elim0
  | t + 1 => A.step hn t ω (run hn ω t)

private theorem measurable_prod_sum_elim {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {f : α × β → δ} {g : α × γ → δ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : α × (β ⊕ γ) =>
      p.2.elim (fun b => f (p.1, b)) (fun c => g (p.1, c))) := by
  convert (hf.sumElim hg).comp (MeasurableEquiv.prodSumDistrib α β γ).measurable using 1
  funext p
  rcases p with ⟨a, b | c⟩ <;> rfl

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

theorem measurable_step (hn : 2 ≤ n) (t : ℕ) :
    Measurable (fun p : SeededSampleSpace S n × State n t => A.step hn t p.1 p.2) := by
  unfold step
  refine measurable_prod_sum_elim
    (f := fun p : SeededSampleSpace S n × Option (Fin n) =>
      (Sum.inl p.2 : State n (t + 1)))
    (g := fun p : SeededSampleSpace S n × History n t =>
      (A.choose hn t (p.1.1, p.2)).elim (.inl none) (fun d =>
        d.elim (fun i => .inr (Fin.snoc p.2 (i, p.1.2 t i)))
          (fun i => .inl (some i)))) ?_ ?_
  · exact measurable_inl.comp measurable_snd
  · let f : (SeededSampleSpace S n × History n t) × Option (Decision n) → State n (t + 1) :=
      fun q => q.2.elim (.inl none) (fun d =>
        d.elim (fun i => .inr (Fin.snoc q.1.2 (i, q.1.1.2 t i)))
          (fun i => .inl (some i)))
    have hf : Measurable f := by
      apply measurable_from_prod_countable_left
      intro d
      cases d with
      | none => exact measurable_const
      | some d =>
        rcases d with i | i
        · exact measurable_inr.comp ((measurable_snoc t).comp
            (measurable_snd.prodMk (measurable_const.prodMk
              ((measurable_pi_apply i).comp ((measurable_pi_apply t).comp
                (measurable_snd.comp measurable_fst))))))
        · exact measurable_const
    exact hf.comp (measurable_id.prodMk ((A.measurable_choose hn t).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))

theorem measurable_run (hn : 2 ≤ n) (t : ℕ) :
    Measurable (fun ω => A.run hn ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact (A.measurable_step hn t).comp (measurable_id.prodMk ih)

def returnedAt (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) : Option (Fin n) :=
  (A.run hn ω t).elim id (fun _ => none)

def requestedArm (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) : Option (Fin n) :=
  (A.run hn ω t).elim (fun _ => none)
    (fun h => (A.choose hn t (ω.1, h)).elim none (fun d => d.elim some (fun _ => none)))

theorem measurable_returnedAt (hn : 2 ≤ n) (t : ℕ) : Measurable (A.returnedAt hn t) :=
  (measurable_id.sumElim measurable_const).comp (A.measurable_run hn t)

theorem measurable_requestedArm (hn : 2 ≤ n) (t : ℕ) : Measurable (A.requestedArm hn t) := by
  have hf : Measurable (fun p : SeededSampleSpace S n × State n t =>
      p.2.elim (fun _ => (none : Option (Fin n)))
        (fun h => (A.choose hn t (p.1.1, h)).elim none
          (fun d => d.elim some (fun _ => none)))) := by
    refine measurable_prod_sum_elim
      (f := fun _ : SeededSampleSpace S n × Option (Fin n) => (none : Option (Fin n)))
      (g := fun p : SeededSampleSpace S n × History n t =>
        (A.choose hn t (p.1.1, p.2)).elim none (fun d => d.elim some (fun _ => none)))
      measurable_const ?_
    exact (measurable_of_finite (fun d : Option (Decision n) =>
      d.elim none (fun x => x.elim some (fun _ => none)))).comp
      ((A.measurable_choose hn t).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact hf.comp (measurable_id.prodMk (A.measurable_run hn t))

def sampleIndicator (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) : ℝ≥0∞ := by
  classical
  exact if (A.requestedArm hn t ω).isSome then 1 else 0

def sampleCount (hn : 2 ≤ n) (ω : SeededSampleSpace S n) : ℝ≥0∞ :=
  ∑' t, A.sampleIndicator hn t ω

theorem measurable_sampleIndicator (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.sampleIndicator hn t) := by
  classical
  apply Measurable.ite _ measurable_const measurable_const
  exact ((measurable_of_finite (fun x : Option (Fin n) => (x.isSome : Prop))).comp
    (A.measurable_requestedArm hn t)).setOf

theorem measurable_sampleCount (hn : 2 ≤ n) : Measurable (A.sampleCount hn) :=
  Measurable.tsum (A.measurable_sampleIndicator hn)

def successEvent (I : Instance n) : Set (SeededSampleSpace S n) :=
  {ω | ∃ t, A.returnedAt I.two_le t ω = some I.best}

theorem measurableSet_successEvent (I : Instance n) : MeasurableSet (A.successEvent I) :=
  (Measurable.exists fun t =>
    (A.measurable_returnedAt I.two_le t).eq_const (some I.best)).setOf

def successProb (μ : Measure S) (I : Instance n) : ℝ≥0∞ :=
  (μ.prod (rewardLaw I.mean)) (A.successEvent I)

def expectedSamples (μ : Measure S) (I : Instance n) : ℝ≥0∞ :=
  ∫⁻ ω, A.sampleCount I.two_le ω ∂(μ.prod (rewardLaw I.mean))

def defaultLabel (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

/-- Explicit abandonment is replaced by immediate return of a fixed label. -/
def complete : SeededPolicy S n where
  choose hn t p := (A.choose hn t p).getD (.inr (defaultLabel hn))
  measurable_choose hn t :=
    (measurable_of_finite (fun d : Option (Decision n) =>
      d.getD (.inr (defaultLabel hn)))).comp (A.measurable_choose hn t)

def completeState (hn : 2 ≤ n) {t : ℕ} (s : State n t) : RunState n t :=
  s.elim (fun o => .inl (o.getD (defaultLabel hn))) .inr

theorem complete_step (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) (s : State n t) :
    A.complete.step hn t ω (completeState hn s) = completeState hn (A.step hn t ω s) := by
  rcases s with o | h
  · cases o <;> rfl
  · cases hd : A.choose hn t (ω.1, h) with
    | none => simp [SeededPolicy.step, step, completeState, complete, hd]
    | some d =>
      cases d <;> simp [SeededPolicy.step, step, completeState, complete, hd]

theorem complete_run (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) :
    A.complete.run hn ω t = completeState hn (A.run hn ω t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [SeededPolicy.run, run, ih]
    exact A.complete_step hn t ω (A.run hn ω t)

theorem complete_requestedArm (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) :
    A.complete.requestedArm hn t ω = A.requestedArm hn t ω := by
  unfold SeededPolicy.requestedArm requestedArm
  rw [A.complete_run]
  rcases A.run hn ω t with o | h
  · cases o <;> rfl
  · cases hd : A.choose hn t (ω.1, h) with
    | none => simp [completeState, complete, hd]
    | some d => cases d <;> simp [completeState, complete, hd]

theorem complete_sampleCount (hn : 2 ≤ n) (ω : SeededSampleSpace S n) :
    A.complete.sampleCount hn ω = A.sampleCount hn ω := by
  unfold SeededPolicy.sampleCount sampleCount
  apply tsum_congr
  intro t
  simp only [SeededPolicy.sampleIndicator, sampleIndicator, A.complete_requestedArm]

theorem returnedAt_complete_of_returnedAt (hn : 2 ≤ n) (t : ℕ)
    (ω : SeededSampleSpace S n) (i : Fin n) (hi : A.returnedAt hn t ω = some i) :
    A.complete.returnedAt hn t ω = some i := by
  unfold SeededPolicy.returnedAt
  rw [A.complete_run]
  unfold returnedAt at hi
  rcases hr : A.run hn ω t with o | h
  · rw [hr] at hi
    cases o with
    | none => simp at hi
    | some j => simpa [completeState] using hi
  · rw [hr] at hi
    simp at hi

theorem successEvent_subset_complete (I : Instance n) :
    A.successEvent I ⊆ A.complete.successEvent I := by
  rintro ω ⟨t, ht⟩
  exact ⟨t, A.returnedAt_complete_of_returnedAt I.two_le t ω I.best ht⟩

theorem expectedSamples_complete (μ : Measure S) (I : Instance n) :
    A.complete.expectedSamples μ I = A.expectedSamples μ I := by
  unfold SeededPolicy.expectedSamples expectedSamples
  exact lintegral_congr (A.complete_sampleCount I.two_le)

theorem successProb_le_complete (μ : Measure S) (I : Instance n) :
    A.successProb μ I ≤ A.complete.successProb μ I :=
  measure_mono (A.successEvent_subset_complete I)

end AbandonPolicy
end GapEntropy.PolicyRepresentations
