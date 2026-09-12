import GapEntropy.Model

/-!
# The observation model with an arbitrary private probability space

This is an operational definition independent of the Gaussian-seed implementation.
The rewards, histories, sample/return convention, and cost accounting are the same
statistical experiment. Only the private seed space and its probability law vary.
No representability, correctness, or complexity bound is a field of a policy.
-/

open MeasureTheory ProbabilityTheory GapEntropy
open scoped ENNReal BigOperators

namespace GapEntropy.PolicyRepresentations

abbrev SeededSampleSpace (S : Type*) (n : ℕ) := S × (ℕ → Fin n → ℝ)

structure SeededPolicy (S : Type*) [MeasurableSpace S] (n : ℕ) where
  choose : 2 ≤ n → (t : ℕ) → S × History n t → Decision n
  measurable_choose : ∀ hn t, Measurable (choose hn t)

namespace SeededPolicy

variable {S : Type*} [MeasurableSpace S] {n : ℕ} (A : SeededPolicy S n)

def step (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) (s : RunState n t) :
    RunState n (t + 1) :=
  s.elim (fun i => .inl i) (fun h =>
    (A.choose hn t (ω.1, h)).elim
      (fun i => .inr (Fin.snoc h (i, ω.2 t i))) (fun i => .inl i))

def run (hn : 2 ≤ n) (ω : SeededSampleSpace S n) : (t : ℕ) → RunState n t
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
    Measurable (fun p : SeededSampleSpace S n × RunState n t => A.step hn t p.1 p.2) := by
  unfold step
  refine measurable_prod_sum_elim
    (f := fun p : SeededSampleSpace S n × Fin n => (Sum.inl p.2 : RunState n (t + 1)))
    (g := fun p : SeededSampleSpace S n × History n t =>
      (A.choose hn t (p.1.1, p.2)).elim
        (fun i => .inr (Fin.snoc p.2 (i, p.1.2 t i))) (fun i => .inl i)) ?_ ?_
  · exact measurable_inl.comp measurable_snd
  · let f : (SeededSampleSpace S n × History n t) × Decision n → RunState n (t + 1) :=
      fun q => q.2.elim
        (fun i => .inr (Fin.snoc q.1.2 (i, q.1.1.2 t i))) (fun i => .inl i)
    have hf : Measurable f := by
      apply measurable_from_prod_countable_left
      intro d
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
  (A.run hn ω t).elim some (fun _ => none)

def requestedArm (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) : Option (Fin n) :=
  (A.run hn ω t).elim (fun _ => none)
    (fun h => (A.choose hn t (ω.1, h)).elim some (fun _ => none))

theorem measurable_returnedAt (hn : 2 ≤ n) (t : ℕ) : Measurable (A.returnedAt hn t) := by
  exact ((measurable_of_finite some).sumElim measurable_const).comp (A.measurable_run hn t)

theorem measurable_requestedArm (hn : 2 ≤ n) (t : ℕ) : Measurable (A.requestedArm hn t) := by
  have hf : Measurable (fun p : SeededSampleSpace S n × RunState n t =>
      p.2.elim (fun _ => (none : Option (Fin n)))
        (fun h => (A.choose hn t (p.1.1, h)).elim some (fun _ => none))) := by
    refine measurable_prod_sum_elim
      (f := fun _ : SeededSampleSpace S n × Fin n => (none : Option (Fin n)))
      (g := fun p : SeededSampleSpace S n × History n t =>
        (A.choose hn t (p.1.1, p.2)).elim some (fun _ => none)) measurable_const ?_
    exact (measurable_of_finite (fun d : Decision n => d.elim some (fun _ => none))).comp
      ((A.measurable_choose hn t).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact hf.comp (measurable_id.prodMk (A.measurable_run hn t))

noncomputable def sampleIndicator (hn : 2 ≤ n) (t : ℕ) (ω : SeededSampleSpace S n) : ℝ≥0∞ := by
  classical
  exact if (A.requestedArm hn t ω).isSome then 1 else 0

noncomputable def sampleCount (hn : 2 ≤ n) (ω : SeededSampleSpace S n) : ℝ≥0∞ :=
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

theorem measurableSet_successEvent (I : Instance n) : MeasurableSet (A.successEvent I) := by
  exact (Measurable.exists fun t =>
    (A.measurable_returnedAt I.two_le t).eq_const (some I.best)).setOf

noncomputable def successProb (μ : Measure S) (I : Instance n) : ℝ≥0∞ :=
  (μ.prod (rewardLaw I.mean)) (A.successEvent I)

noncomputable def expectedSamples (μ : Measure S) (I : Instance n) : ℝ≥0∞ :=
  ∫⁻ ω, A.sampleCount I.two_le ω ∂(μ.prod (rewardLaw I.mean))

def AlmostSurelyTerminates (μ : Measure S) (I : Instance n) : Prop :=
  ∀ᵐ ω ∂(μ.prod (rewardLaw I.mean)), ∃ t i, A.returnedAt I.two_le t ω = some i

end SeededPolicy
end GapEntropy.PolicyRepresentations
