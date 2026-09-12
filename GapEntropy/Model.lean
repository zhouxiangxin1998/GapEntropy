import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FunProp
import GapEntropy.Instance

/-!
# Operational Gaussian best-arm model

A policy sees its independent random seed and its finite observation history.
It never receives the vector of means or the best label. Histories of length `t`
are tuples, equivalent to lists of that length. Decisions either request one
sample or return a label. Returned states are absorbing.

No concentration, testing, or change-of-measure claim is assumed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GapEntropy

abbrev Seed := ℕ → ℝ
abbrev Observation (n : ℕ) := Fin n × ℝ
abbrev History (n t : ℕ) := Fin t → Observation n
abbrev Decision (n : ℕ) := Fin n ⊕ Fin n
abbrev SampleSpace (n : ℕ) := Seed × (ℕ → Fin n → ℝ)
abbrev RunState (n t : ℕ) := Fin n ⊕ History n t

instance (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤

instance (n : ℕ) : MeasurableSingletonClass (Decision n) where
  measurableSet_singleton d := by
    rcases d with i | i
    · simpa using (measurableSet_singleton i).inl_image (β := Fin n)
    · simpa using (measurableSet_singleton i).inr_image (α := Fin n)

/-- Left decisions sample an arm; right decisions return an arm.
The proof argument only restricts the number of arms to the problem's domain. -/
structure Policy (n : ℕ) where
  choose : 2 ≤ n → (t : ℕ) → Seed × History n t → Decision n
  measurable_choose : ∀ hn t, Measurable (choose hn t)

noncomputable def seedLaw : Measure Seed :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure seedLaw := by
  unfold seedLaw
  infer_instance

noncomputable def rewardLaw {n : ℕ} (mean : Fin n → ℝ) : Measure (ℕ → Fin n → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => Measure.pi (fun i => gaussianReal (mean i) 1))

instance {n : ℕ} (mean : Fin n → ℝ) : IsProbabilityMeasure (rewardLaw mean) := by
  unfold rewardLaw
  infer_instance

noncomputable def sampleLawOfMeans {n : ℕ} (mean : Fin n → ℝ) : Measure (SampleSpace n) :=
  seedLaw.prod (rewardLaw mean)

instance {n : ℕ} (mean : Fin n → ℝ) : IsProbabilityMeasure (sampleLawOfMeans mean) := by
  unfold sampleLawOfMeans
  infer_instance

noncomputable def sampleLaw {n : ℕ} (I : Instance n) : Measure (SampleSpace n) :=
  sampleLawOfMeans I.mean

instance {n : ℕ} (I : Instance n) : IsProbabilityMeasure (sampleLaw I) := by
  unfold sampleLaw
  infer_instance

theorem sampleLawOfMeans_map_seed {n : ℕ} (mean : Fin n → ℝ) :
    (sampleLawOfMeans mean).map Prod.fst = seedLaw := by
  simp [sampleLawOfMeans]

theorem sampleLawOfMeans_map_reward {n : ℕ} (mean : Fin n → ℝ) (t : ℕ) (i : Fin n) :
    (sampleLawOfMeans mean).map (fun ω => ω.2 t i) = gaussianReal (mean i) 1 := by
  have hp : MeasurePreserving Prod.snd (sampleLawOfMeans mean) (rewardLaw mean) :=
    measurePreserving_snd
  have ht : MeasurePreserving (Function.eval t) (rewardLaw mean)
      (Measure.pi (fun j => gaussianReal (mean j) 1)) :=
    measurePreserving_eval_infinitePi _ t
  have hi := measurePreserving_eval (fun j => gaussianReal (mean j) 1) i
  exact (hi.comp (ht.comp hp)).map_eq

namespace Policy

variable {n : ℕ} (A : Policy n)

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
  · simpa only [Fin.snoc_last] using
      (measurable_snd : Measurable (fun p : History n t × Observation n => p.2))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply j).comp
        (measurable_fst : Measurable (fun p : History n t × Observation n => p.1))

def step (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) (s : RunState n t) :
    RunState n (t + 1) :=
  s.elim (fun i => .inl i) (fun h =>
    (A.choose hn t (ω.1, h)).elim
      (fun i => .inr (Fin.snoc h (i, ω.2 t i))) (fun i => .inl i))

def run (hn : 2 ≤ n) (ω : SampleSpace n) : (t : ℕ) → RunState n t
  | 0 => .inr Fin.elim0
  | t + 1 => A.step hn t ω (run hn ω t)

theorem measurable_step (hn : 2 ≤ n) (t : ℕ) :
    Measurable (fun p : SampleSpace n × RunState n t => A.step hn t p.1 p.2) := by
  unfold step
  refine measurable_prod_sum_elim
    (f := fun p : SampleSpace n × Fin n => (Sum.inl p.2 : RunState n (t + 1)))
    (g := fun p : SampleSpace n × History n t =>
      (A.choose hn t (p.1.1, p.2)).elim
        (fun i => .inr (Fin.snoc p.2 (i, p.1.2 t i))) (fun i => .inl i)) ?_ ?_
  · exact measurable_inl.comp measurable_snd
  · let f : (SampleSpace n × History n t) × Decision n → RunState n (t + 1) :=
      fun q => q.2.elim
        (fun i => .inr (Fin.snoc q.1.2 (i, q.1.1.2 t i)))
        (fun i => .inl i)
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

def returnedAt (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) : Option (Fin n) :=
  (A.run hn ω t).elim some (fun _ => none)

def requestedArm (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) : Option (Fin n) :=
  (A.run hn ω t).elim (fun _ => none)
    (fun h => (A.choose hn t (ω.1, h)).elim some (fun _ => none))

def sampleRequested (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) : Prop :=
  (A.requestedArm hn t ω).isSome

theorem measurable_returnedAt (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.returnedAt hn t) := by
  exact ((measurable_of_finite some).sumElim measurable_const).comp
    (A.measurable_run hn t)

theorem measurable_requestedArm (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.requestedArm hn t) := by
  have hf : Measurable (fun p : SampleSpace n × RunState n t =>
      p.2.elim (fun _ => (none : Option (Fin n)))
        (fun h => (A.choose hn t (p.1.1, h)).elim some (fun _ => none))) := by
    refine measurable_prod_sum_elim
      (f := fun _ : SampleSpace n × Fin n => (none : Option (Fin n)))
      (g := fun p : SampleSpace n × History n t =>
        (A.choose hn t (p.1.1, p.2)).elim some (fun _ => none)) measurable_const ?_
    exact (measurable_of_finite (fun d : Decision n => d.elim some (fun _ => none))).comp
      ((A.measurable_choose hn t).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact hf.comp (measurable_id.prodMk (A.measurable_run hn t))

theorem measurableSet_sampleRequested (hn : 2 ≤ n) (t : ℕ) :
    MeasurableSet {ω | A.sampleRequested hn t ω} := by
  exact (measurable_of_finite (fun x : Option (Fin n) => (x.isSome : Prop))).comp
    (A.measurable_requestedArm hn t) |>.setOf

noncomputable def sampleIndicator (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) : ℝ≥0∞ := by
  classical
  exact if A.sampleRequested hn t ω then 1 else 0

noncomputable def truncatedSamples (hn : 2 ≤ n) (T : ℕ) (ω : SampleSpace n) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, A.sampleIndicator hn t ω

noncomputable def sampleCount (hn : 2 ≤ n) (ω : SampleSpace n) : ℝ≥0∞ :=
  ∑' t, A.sampleIndicator hn t ω

theorem measurable_sampleIndicator (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.sampleIndicator hn t) := by
  classical
  exact Measurable.ite (A.measurableSet_sampleRequested hn t) measurable_const measurable_const

theorem measurable_truncatedSamples (hn : 2 ≤ n) (T : ℕ) :
    Measurable (A.truncatedSamples hn T) := by
  exact Finset.measurable_fun_sum _ (fun t _ => A.measurable_sampleIndicator hn t)

theorem measurable_sampleCount (hn : 2 ≤ n) : Measurable (A.sampleCount hn) := by
  exact Measurable.tsum (A.measurable_sampleIndicator hn)

noncomputable def truncatedArmSamples (hn : 2 ≤ n) (T : ℕ) (i : Fin n)
    (ω : SampleSpace n) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, if A.requestedArm hn t ω = some i then 1 else 0

theorem sampleIndicator_eq_sum_arms (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) :
    A.sampleIndicator hn t ω =
      ∑ i : Fin n, if A.requestedArm hn t ω = some i then (1 : ℝ≥0∞) else 0 := by
  classical
  cases h : A.requestedArm hn t ω with
  | none => simp [sampleIndicator, sampleRequested, h]
  | some i => simp [sampleIndicator, sampleRequested, h]

theorem sum_truncatedArmSamples (hn : 2 ≤ n) (T : ℕ) (ω : SampleSpace n) :
    ∑ i : Fin n, A.truncatedArmSamples hn T i ω = A.truncatedSamples hn T ω := by
  unfold truncatedArmSamples truncatedSamples
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun t _ => (A.sampleIndicator_eq_sum_arms hn t ω).symm)

theorem measurable_truncatedArmSamples (hn : 2 ≤ n) (T : ℕ) (i : Fin n) :
    Measurable (A.truncatedArmSamples hn T i) := by
  classical
  apply Finset.measurable_fun_sum
  intro t _
  exact Measurable.ite ((A.measurable_requestedArm hn t).eq_const (some i)).setOf
    measurable_const measurable_const

def successEvent (I : Instance n) : Set (SampleSpace n) :=
  {ω | ∃ t, A.returnedAt I.two_le t ω = some I.best}

theorem measurableSet_successEvent (I : Instance n) : MeasurableSet (A.successEvent I) := by
  exact (Measurable.exists fun t =>
    (A.measurable_returnedAt I.two_le t).eq_const (some I.best)).setOf

noncomputable def successProb (I : Instance n) : ℝ≥0∞ :=
  sampleLaw I (A.successEvent I)

/-- All paths are charged, including incorrect returns and infinite executions. -/
noncomputable def expectedSamples (I : Instance n) : ℝ≥0∞ :=
  ∫⁻ ω, A.sampleCount I.two_le ω ∂sampleLaw I

def AlmostSurelyTerminates (I : Instance n) : Prop :=
  ∀ᵐ ω ∂sampleLaw I, ∃ t i, A.returnedAt I.two_le t ω = some i

@[simp] theorem run_zero (hn : 2 ≤ n) (ω : SampleSpace n) :
    A.run hn ω 0 = .inr Fin.elim0 := rfl

@[simp] theorem run_succ (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) :
    A.run hn ω (t + 1) = A.step hn t ω (A.run hn ω t) := rfl

@[simp] theorem truncatedSamples_zero (hn : 2 ≤ n) (ω : SampleSpace n) :
    A.truncatedSamples hn 0 ω = 0 := by simp [truncatedSamples]

theorem truncatedSamples_succ (hn : 2 ≤ n) (T : ℕ) (ω : SampleSpace n) :
    A.truncatedSamples hn (T + 1) ω =
      A.truncatedSamples hn T ω + A.sampleIndicator hn T ω := by
  simp [truncatedSamples, Finset.sum_range_succ]

theorem truncatedSamples_le_sampleCount (hn : 2 ≤ n) (T : ℕ) (ω : SampleSpace n) :
    A.truncatedSamples hn T ω ≤ A.sampleCount hn ω := by
  exact ENNReal.sum_le_tsum (Finset.range T)

theorem sampleIndicator_le_one (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) :
    A.sampleIndicator hn t ω ≤ 1 := by
  classical
  unfold sampleIndicator
  split_ifs <;> simp

theorem truncatedSamples_le_time (hn : 2 ≤ n) (T : ℕ) (ω : SampleSpace n) :
    A.truncatedSamples hn T ω ≤ T := by
  calc
    A.truncatedSamples hn T ω ≤ ∑ _t ∈ Finset.range T, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum (fun t _ => A.sampleIndicator_le_one hn t ω)
    _ = T := by simp

theorem sampleCount_eq_iSup_truncatedSamples (hn : 2 ≤ n) (ω : SampleSpace n) :
    A.sampleCount hn ω = ⨆ T, A.truncatedSamples hn T ω := ENNReal.tsum_eq_iSup_nat

theorem lintegral_sampleIndicator (hn : 2 ≤ n) (t : ℕ) (μ : Measure (SampleSpace n)) :
    ∫⁻ ω, A.sampleIndicator hn t ω ∂μ = μ {ω | A.sampleRequested hn t ω} := by
  change ∫⁻ ω, {ω | A.sampleRequested hn t ω}.indicator 1 ω ∂μ = _
  exact lintegral_indicator_one (A.measurableSet_sampleRequested hn t)

theorem expectedSamples_eq_tsum (I : Instance n) :
    A.expectedSamples I = ∑' t, sampleLaw I {ω | A.sampleRequested I.two_le t ω} := by
  unfold expectedSamples sampleCount
  rw [lintegral_tsum (fun t => (A.measurable_sampleIndicator I.two_le t).aemeasurable)]
  simp only [A.lintegral_sampleIndicator]

theorem lintegral_truncatedSamples (hn : 2 ≤ n) (T : ℕ) (μ : Measure (SampleSpace n)) :
    ∫⁻ ω, A.truncatedSamples hn T ω ∂μ =
      ∑ t ∈ Finset.range T, μ {ω | A.sampleRequested hn t ω} := by
  unfold truncatedSamples
  rw [lintegral_finsetSum _ (fun t _ => A.measurable_sampleIndicator hn t)]
  simp only [A.lintegral_sampleIndicator]

theorem lintegral_truncatedSamples_eq_sum_arms (hn : 2 ≤ n) (T : ℕ)
    (μ : Measure (SampleSpace n)) :
    ∫⁻ ω, A.truncatedSamples hn T ω ∂μ =
      ∑ i : Fin n, ∫⁻ ω, A.truncatedArmSamples hn T i ω ∂μ := by
  simp_rw [← A.sum_truncatedArmSamples hn T]
  exact lintegral_finsetSum _ (fun i _ => A.measurable_truncatedArmSamples hn T i)

end Policy
end GapEntropy
