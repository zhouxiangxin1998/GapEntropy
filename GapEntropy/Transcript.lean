import GapEntropy.Freshness
import GapEntropy.GaussianKL
import GapEntropy.ConditionalKL
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Full finite adaptive transcripts

The transcript retains the seed and **every** execution state, including states
before a return. It therefore does not discard the sampled history when the
current `RunState` becomes an absorbing returned label.

`GapEntropy.ConditionalKL` proves the integral form of the conditional term. Freshness gives
the actual law recursion, Gaussian KL evaluates each transition, and induction proves the
finite source-count identity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GapEntropy

/-- Nested products retain all states, rather than just the current state. -/
def Transcript (n : ℕ) : ℕ → Type
  | 0 => Seed × RunState n 0
  | t + 1 => Transcript n t × RunState n (t + 1)

instance transcriptMeasurableSpace (n : ℕ) : (t : ℕ) → MeasurableSpace (Transcript n t)
  | 0 => inferInstanceAs (MeasurableSpace (Seed × RunState n 0))
  | t + 1 => @Prod.instMeasurableSpace (Transcript n t) (RunState n (t + 1))
      (transcriptMeasurableSpace n t) inferInstance

def transcriptSeed {n : ℕ} : (t : ℕ) → Transcript n t → Seed
  | 0, p => p.1
  | t + 1, p => transcriptSeed t p.1

def transcriptLast {n : ℕ} : (t : ℕ) → Transcript n t → RunState n t
  | 0, p => p.2
  | _ + 1, p => p.2

theorem measurable_transcriptSeed {n : ℕ} (t : ℕ) : Measurable (transcriptSeed (n := n) t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih => exact ih.comp measurable_fst

theorem measurable_transcriptLast {n : ℕ} (t : ℕ) : Measurable (transcriptLast (n := n) t) := by
  cases t <;> exact measurable_snd

/-- The library does not supply a countable-generation instance for measurable
sums. A tagged product with fixed padding values gives a measurable retraction. -/
private theorem countablyGenerated_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Inhabited α] [Inhabited β]
    [MeasurableSpace.CountablyGenerated α] [MeasurableSpace.CountablyGenerated β] :
    MeasurableSpace.CountablyGenerated (α ⊕ β) := by
  let f : α ⊕ β → Bool × (α × β) :=
    Sum.elim (fun a => (false, a, default)) (fun b => (true, default, b))
  let g : Bool × (α × β) → α ⊕ β :=
    fun p => if p.1 = true then .inr p.2.2 else .inl p.2.1
  have hf : Measurable f :=
    (measurable_const.prodMk (measurable_id.prodMk measurable_const)).sumElim
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hg : Measurable g := Measurable.ite (measurable_fst.eq_const true).setOf
    (measurable_inr.comp (measurable_snd.comp measurable_snd))
    (measurable_inl.comp (measurable_fst.comp measurable_snd))
  have hgf : g ∘ f = id := by
    funext x
    rcases x with a | b <;> simp [f, g]
  have hid : @Measurable (α ⊕ β) (α ⊕ β)
      (MeasurableSpace.comap f inferInstance) inferInstance id := by
    rw [← hgf]
    exact hg.comp (comap_measurable f)
  have heq : MeasurableSpace.comap f inferInstance = (inferInstance : MeasurableSpace (α ⊕ β)) :=
    le_antisymm hf.comap_le (by simpa only [MeasurableSpace.comap_id] using hid.comap_le)
  have hc := MeasurableSpace.CountablyGenerated.comap f
  rw [heq] at hc
  exact hc

theorem countablyGenerated_runState {n t : ℕ} (hn : 2 ≤ n) :
    MeasurableSpace.CountablyGenerated (RunState n t) := by
  let : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  exact countablyGenerated_sum

private theorem klDiv_map_eq_of_leftInverse {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : α → β} {g : β → α}
    (hf : Measurable f) (hg : Measurable g) (hgf : Function.LeftInverse g f) :
    InformationTheory.klDiv (μ.map f) (ν.map f) = InformationTheory.klDiv μ ν := by
  apply le_antisymm (InformationTheory.klDiv_map_le _ _ hf)
  have h : g ∘ f = id := funext hgf
  have hd := InformationTheory.klDiv_map_le (μ.map f) (ν.map f) hg
  simpa only [Measure.map_map hg hf, h, Measure.map_id] using hd

namespace Policy

variable {n : ℕ} (A : Policy n)

def transcript (hn : 2 ≤ n) (ω : SampleSpace n) : (t : ℕ) → Transcript n t
  | 0 => (ω.1, A.run hn ω 0)
  | t + 1 => (transcript hn ω t, A.run hn ω (t + 1))

theorem measurable_transcript (hn : 2 ≤ n) (t : ℕ) :
    Measurable (fun ω => A.transcript hn ω t) := by
  induction t with
  | zero => exact measurable_fst.prodMk (A.measurable_run hn 0)
  | succ t ih => exact ih.prodMk (A.measurable_run hn (t + 1))

@[simp] theorem transcriptSeed_transcript (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) :
    transcriptSeed t (A.transcript hn ω t) = ω.1 := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

@[simp] theorem transcriptLast_transcript (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) :
    transcriptLast t (A.transcript hn ω t) = A.run hn ω t := by
  cases t <;> rfl

/-- The previous full transcript is literally retained after every transition,
including return and absorption transitions. -/
@[simp] theorem transcript_succ_fst (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) :
    (A.transcript hn ω (t + 1)).1 = A.transcript hn ω t := rfl

theorem transcript_congr_prefix (hn : 2 ≤ n) (t : ℕ) {ω ω' : SampleSpace n}
    (hseed : ω.1 = ω'.1) :
    (∀ s, s < t → ω.2 s = ω'.2 s) → A.transcript hn ω t = A.transcript hn ω' t := by
  induction t with
  | zero => intro _; exact Prod.ext hseed rfl
  | succ t ih =>
      intro hrows
      have hp := ih (fun s hs => hrows s (Nat.lt_succ_of_lt hs))
      have hr := A.run_congr_prefix hn (t + 1) hseed hrows
      exact Prod.ext hp hr

def transcriptFromPrefix (hn : 2 ≤ n) (t : ℕ) (p : SeedPrefix n t) : Transcript n t :=
  A.transcript hn (extendPrefix t p) t

theorem measurable_transcriptFromPrefix (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.transcriptFromPrefix hn t) :=
  (A.measurable_transcript hn t).comp (measurable_extendPrefix t)

theorem transcript_eq_fromPrefix (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) :
    A.transcript hn ω t = A.transcriptFromPrefix hn t (seedPrefix t ω) := by
  unfold transcriptFromPrefix
  apply A.transcript_congr_prefix hn t
    (ω := ω) (ω' := extendPrefix t (seedPrefix t ω)) rfl
  intro s hs
  simp [seedPrefix, extendPrefix, hs]

theorem indepFun_transcript_row (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IndepFun (fun ω => A.transcript hn ω t) (fun ω : SampleSpace n => ω.2 t)
      (sampleLawOfMeans mean) := by
  have h := (indepFun_seedPrefix_row mean t).comp
    (A.measurable_transcriptFromPrefix hn t) measurable_id
  convert h using 1
  · funext ω
    exact A.transcript_eq_fromPrefix hn t ω
  · rfl

noncomputable def transcriptLaw (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    Measure (Transcript n t) :=
  (sampleLawOfMeans mean).map (fun ω => A.transcript hn ω t)

instance isProbabilityMeasure_transcriptLaw (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IsProbabilityMeasure (A.transcriptLaw hn mean t) :=
  Measure.isProbabilityMeasure_map (A.measurable_transcript hn t).aemeasurable

/-- A deterministic state update supplied with just the current reward row. -/
def transcriptRowStep (hn : 2 ≤ n) (t : ℕ) (p : Transcript n t × (Fin n → ℝ)) :
    RunState n (t + 1) :=
  A.step hn t (transcriptSeed t p.1, fun _ => p.2) (transcriptLast t p.1)

theorem measurable_transcriptRowStep (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.transcriptRowStep hn t) := by
  exact (A.measurable_step hn t).comp
    ((((measurable_transcriptSeed t).comp measurable_fst).prodMk
      (measurable_pi_lambda _ (fun _ => measurable_snd))).prodMk
      ((measurable_transcriptLast t).comp measurable_fst))

@[simp] theorem transcriptRowStep_actual (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) :
    A.transcriptRowStep hn t (A.transcript hn ω t, ω.2 t) = A.run hn ω (t + 1) := by
  simp only [transcriptRowStep, transcriptSeed_transcript, transcriptLast_transcript, run_succ]
  rfl

noncomputable def nextStateKernel (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    Kernel (Transcript n t) (RunState n (t + 1)) :=
  ((Kernel.id : Kernel (Transcript n t) (Transcript n t)) ×ₖ
    Kernel.const (Transcript n t) (Measure.pi (fun i => gaussianReal (mean i) 1))).map
      (A.transcriptRowStep hn t)

instance isMarkovKernel_nextStateKernel (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IsMarkovKernel (A.nextStateKernel hn mean t) :=
  Kernel.IsMarkovKernel.map _ (A.measurable_transcriptRowStep hn t)

theorem nextStateKernel_apply (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ)
    (p : Transcript n t) :
    A.nextStateKernel hn mean t p =
      (Measure.pi (fun i => gaussianReal (mean i) 1)).map
        (fun r => A.transcriptRowStep hn t (p, r)) := by
  rw [nextStateKernel, Kernel.map_apply _ (A.measurable_transcriptRowStep hn t),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (A.measurable_transcriptRowStep hn t) measurable_prodMk_left]
  rfl

def appendSample (t : ℕ) (h : History n t) (i : Fin n) (x : ℝ) : RunState n (t + 1) :=
  .inr (Fin.snoc h (i, x))

theorem measurable_appendSample (t : ℕ) (h : History n t) (i : Fin n) :
    Measurable (appendSample t h i) := by
  apply measurable_inr.comp
  apply measurable_pi_lambda
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa only [Fin.snoc_last] using
      (measurable_const.prodMk measurable_id : Measurable (fun x : ℝ => (i, x)))
  · simpa only [Fin.snoc_castSucc] using
      (measurable_const : Measurable (fun _ : ℝ => h k))

def lastSample (t : ℕ) (s : RunState n (t + 1)) : ℝ :=
  s.elim (fun _ => 0) (fun h => (h (Fin.last t)).2)

theorem measurable_lastSample (t : ℕ) : Measurable (lastSample (n := n) t) :=
  measurable_const.sumElim (measurable_snd.comp (measurable_pi_apply (Fin.last t)))

theorem lastSample_appendSample (t : ℕ) (h : History n t) (i : Fin n) :
    Function.LeftInverse (lastSample t) (appendSample t h i) := by
  intro x
  simp [lastSample, appendSample]

theorem nextStateKernel_of_returned (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ)
    (p : Transcript n t) (i : Fin n) (hp : transcriptLast t p = .inl i) :
    A.nextStateKernel hn mean t p = Measure.dirac (.inl i) := by
  rw [A.nextStateKernel_apply]
  simp [transcriptRowStep, step, hp]

theorem nextStateKernel_of_stop (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ)
    (p : Transcript n t) (h : History n t) (i : Fin n)
    (hp : transcriptLast t p = .inr h)
    (hd : A.choose hn t (transcriptSeed t p, h) = .inr i) :
    A.nextStateKernel hn mean t p = Measure.dirac (.inl i) := by
  rw [A.nextStateKernel_apply]
  simp [transcriptRowStep, step, hp, hd]

theorem nextStateKernel_of_sample (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ)
    (p : Transcript n t) (h : History n t) (i : Fin n)
    (hp : transcriptLast t p = .inr h)
    (hd : A.choose hn t (transcriptSeed t p, h) = .inl i) :
    A.nextStateKernel hn mean t p =
      (gaussianReal (mean i) 1).map (appendSample t h i) := by
  rw [A.nextStateKernel_apply]
  have he : (fun r => A.transcriptRowStep hn t (p, r)) =
      appendSample t h i ∘ (fun r : Fin n → ℝ => r i) := by
    funext r
    simp [transcriptRowStep, step, hp, hd, appendSample]
  rw [he, ← Measure.map_map (measurable_appendSample t h i) (measurable_pi_apply i),
    (measurePreserving_eval (fun j => gaussianReal (mean j) 1) i).map_eq]

theorem klDiv_nextStateKernel_of_sample (hn : 2 ≤ n) (mean mean' : Fin n → ℝ) (t : ℕ)
    (p : Transcript n t) (h : History n t) (i : Fin n)
    (hp : transcriptLast t p = .inr h)
    (hd : A.choose hn t (transcriptSeed t p, h) = .inl i) :
    InformationTheory.klDiv (A.nextStateKernel hn mean t p) (A.nextStateKernel hn mean' t p) =
      ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) := by
  rw [A.nextStateKernel_of_sample hn mean t p h i hp hd,
    A.nextStateKernel_of_sample hn mean' t p h i hp hd,
    klDiv_map_eq_of_leftInverse (measurable_appendSample t h i)
      (measurable_lastSample t) (lastSample_appendSample t h i)]
  exact klDiv_gaussian_unit _ _

def requestedArmFromTranscript (hn : 2 ≤ n) (t : ℕ) (p : Transcript n t) : Option (Fin n) :=
  (transcriptLast t p).elim (fun _ => none) (fun h =>
    (A.choose hn t (transcriptSeed t p, h)).elim some (fun _ => none))

theorem measurable_requestedArmFromTranscript (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.requestedArmFromTranscript hn t) := by
  have hr : Measurable (fun p : Seed × History n t =>
      (A.choose hn t p).elim some (fun _ => none)) :=
    (measurable_of_finite (fun d : Decision n => d.elim some (fun _ => none))).comp
      (A.measurable_choose hn t)
  have hl : Measurable (fun _ : Seed × Fin n => (none : Option (Fin n))) := measurable_const
  have h := (hl.sumElim hr).comp
    (MeasurableEquiv.prodSumDistrib Seed (Fin n) (History n t)).measurable
  have hf : Measurable (fun p : Seed × RunState n t =>
      p.2.elim (fun _ => (none : Option (Fin n)))
        (fun h => (A.choose hn t (p.1, h)).elim some (fun _ => none))) := by
    convert h using 1
    funext p
    rcases p with ⟨z, i | hist⟩ <;> rfl
  exact hf.comp ((measurable_transcriptSeed t).prodMk (measurable_transcriptLast t))

@[simp] theorem requestedArmFromTranscript_actual (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) :
    A.requestedArmFromTranscript hn t (A.transcript hn ω t) = A.requestedArm hn t ω := by
  simp only [requestedArmFromTranscript, transcriptLast_transcript, transcriptSeed_transcript,
    requestedArm]

noncomputable def kernelInformation (hn : 2 ≤ n) (mean mean' : Fin n → ℝ) (t : ℕ)
    (p : Transcript n t) : ℝ≥0∞ :=
  ∑ i : Fin n, if A.requestedArmFromTranscript hn t p = some i
    then ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) else 0

theorem measurable_kernelInformation (hn : 2 ≤ n) (mean mean' : Fin n → ℝ) (t : ℕ) :
    Measurable (A.kernelInformation hn mean mean' t) := by
  apply Finset.measurable_fun_sum
  intro i _
  exact Measurable.ite ((A.measurable_requestedArmFromTranscript hn t).eq_const (some i)).setOf
    measurable_const measurable_const

theorem klDiv_nextStateKernel_eq_information (hn : 2 ≤ n) (mean mean' : Fin n → ℝ)
    (t : ℕ) (p : Transcript n t) :
    InformationTheory.klDiv (A.nextStateKernel hn mean t p) (A.nextStateKernel hn mean' t p) =
      A.kernelInformation hn mean mean' t p := by
  cases hp : transcriptLast t p with
  | inl i =>
      rw [A.nextStateKernel_of_returned hn mean t p i hp,
        A.nextStateKernel_of_returned hn mean' t p i hp]
      simp [kernelInformation, requestedArmFromTranscript, hp]
  | inr h =>
      cases hd : A.choose hn t (transcriptSeed t p, h) with
      | inl i =>
          rw [A.klDiv_nextStateKernel_of_sample hn mean mean' t p h i hp hd]
          simp [kernelInformation, requestedArmFromTranscript, hp, hd]
      | inr i =>
          rw [A.nextStateKernel_of_stop hn mean t p h i hp hd,
            A.nextStateKernel_of_stop hn mean' t p h i hp hd]
          simp [kernelInformation, requestedArmFromTranscript, hp, hd]

theorem kernelInformation_ne_top (hn : 2 ≤ n) (mean mean' : Fin n → ℝ)
    (t : ℕ) (p : Transcript n t) : A.kernelInformation hn mean mean' t p ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro i _
  split <;> simp

theorem klDiv_nextStateKernel_ne_top (hn : 2 ≤ n) (mean mean' : Fin n → ℝ)
    (t : ℕ) (p : Transcript n t) :
    InformationTheory.klDiv (A.nextStateKernel hn mean t p) (A.nextStateKernel hn mean' t p) ≠ ∞ := by
  rw [A.klDiv_nextStateKernel_eq_information]
  exact A.kernelInformation_ne_top hn mean mean' t p

/-- The integral of the pointwise kernel KL has exactly the source-measure
one-step sampling weights. -/
theorem lintegral_kernelInformation_transcriptLaw (hn : 2 ≤ n) (mean mean' : Fin n → ℝ)
    (t : ℕ) :
    ∫⁻ p, A.kernelInformation hn mean mean' t p ∂A.transcriptLaw hn mean t =
      ∑ i : Fin n, ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) *
        sampleLawOfMeans mean {ω | A.requestedArm hn t ω = some i} := by
  rw [transcriptLaw, lintegral_map (A.measurable_kernelInformation hn mean mean' t)
    (A.measurable_transcript hn t)]
  simp only [kernelInformation, requestedArmFromTranscript_actual]
  rw [lintegral_finsetSum _ (fun i _ =>
    Measurable.ite ((A.measurable_requestedArm hn t).eq_const (some i)).setOf
      measurable_const measurable_const)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Set.indicator, Set.mem_ofPred_eq] using
    lintegral_indicator_const (μ := sampleLawOfMeans mean)
      ((A.measurable_requestedArm hn t).eq_const (some i)).setOf
      (ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2))

theorem compProd_nextStateKernel (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ)
    (μ : Measure (Transcript n t)) [SFinite μ] :
    μ ⊗ₘ A.nextStateKernel hn mean t =
      (μ.prod (Measure.pi (fun i => gaussianReal (mean i) 1))).map
        (fun p => (p.1, A.transcriptRowStep hn t p)) := by
  have hg : Measurable (fun p : Transcript n t × (Fin n → ℝ) =>
      (p.1, A.transcriptRowStep hn t p)) :=
    measurable_fst.prodMk (A.measurable_transcriptRowStep hn t)
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hg hs, Measure.prod_apply (hg hs)]
  apply lintegral_congr
  intro p
  have hp : Measurable (fun r => A.transcriptRowStep hn t (p, r)) :=
    (A.measurable_transcriptRowStep hn t).comp measurable_prodMk_left
  rw [A.nextStateKernel_apply, Measure.map_apply hp (measurable_prodMk_left hs)]
  rfl

theorem transcript_row_jointLaw (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    (sampleLawOfMeans mean).map (fun ω => (A.transcript hn ω t, ω.2 t)) =
      (A.transcriptLaw hn mean t).prod (Measure.pi (fun i => gaussianReal (mean i) 1)) := by
  rw [(A.indepFun_transcript_row hn mean t).map_prod_eq_prod_map_map
    (A.measurable_transcript hn t).aemeasurable (by fun_prop)]
  congr 1
  have ht : MeasurePreserving (Function.eval t) (rewardLaw mean)
      (Measure.pi (fun i => gaussianReal (mean i) 1)) :=
    measurePreserving_eval_infinitePi _ t
  exact (ht.comp measurePreserving_snd).map_eq

/-- The actual rich-transcript laws follow the stated adaptive kernel recursion. -/
theorem transcriptLaw_succ (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    A.transcriptLaw hn mean (t + 1) =
      A.transcriptLaw hn mean t ⊗ₘ A.nextStateKernel hn mean t := by
  rw [A.compProd_nextStateKernel, ← A.transcript_row_jointLaw hn mean t]
  rw [Measure.map_map
    (measurable_fst.prodMk (A.measurable_transcriptRowStep hn t))
    ((A.measurable_transcript hn t).prodMk (by fun_prop))]
  unfold transcriptLaw
  congr 1
  funext ω
  exact Prod.ext rfl (A.transcriptRowStep_actual hn t ω).symm

set_option backward.isDefEq.respectTransparency false in
theorem transcriptLaw_zero (hn : 2 ≤ n) (mean : Fin n → ℝ) :
    A.transcriptLaw hn mean 0 =
      seedLaw.map (fun z => (z, (Sum.inr Fin.elim0 : RunState n 0))) := by
  have hf : Measurable (fun z : Seed => (z, (Sum.inr Fin.elim0 : RunState n 0))) :=
    measurable_id.prodMk measurable_const
  rw [← sampleLawOfMeans_map_seed mean, Measure.map_map hf measurable_fst]
  rfl

@[simp] theorem klDiv_transcriptLaw_zero (hn : 2 ≤ n) (mean mean' : Fin n → ℝ) :
    InformationTheory.klDiv (A.transcriptLaw hn mean 0) (A.transcriptLaw hn mean' 0) = 0 := by
  have h : A.transcriptLaw hn mean 0 = A.transcriptLaw hn mean' 0 :=
    (A.transcriptLaw_zero hn mean).trans (A.transcriptLaw_zero hn mean').symm
  rw [h]
  exact InformationTheory.klDiv_self _

theorem transcriptLaw_map_last (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    (A.transcriptLaw hn mean t).map (transcriptLast t) =
      (sampleLawOfMeans mean).map (fun ω => A.run hn ω t) := by
  rw [transcriptLaw, Measure.map_map (measurable_transcriptLast t)
    (A.measurable_transcript hn t)]
  simp only [Function.comp_def, A.transcriptLast_transcript]

/-- Exact chain rule for the actual full transcript. The second summand is
still conditional KL as a divergence of composition-products. -/
theorem klDiv_transcriptLaw_succ (hn : 2 ≤ n) (mean mean' : Fin n → ℝ) (t : ℕ) :
    InformationTheory.klDiv (A.transcriptLaw hn mean (t + 1))
      (A.transcriptLaw hn mean' (t + 1)) =
      InformationTheory.klDiv (A.transcriptLaw hn mean t) (A.transcriptLaw hn mean' t) +
        InformationTheory.klDiv
          (A.transcriptLaw hn mean t ⊗ₘ A.nextStateKernel hn mean t)
          (A.transcriptLaw hn mean t ⊗ₘ A.nextStateKernel hn mean' t) := by
  rw [A.transcriptLaw_succ, A.transcriptLaw_succ]
  exact InformationTheory.klDiv_compProd_eq_add _ _ _ _

/-- The common-marginal conditional KL is evaluated using genuine pointwise
Gaussian KL and the actual source transcript distribution. -/
theorem klDiv_transcriptLaw_succ_eq_add_information (hn : 2 ≤ n)
    (mean mean' : Fin n → ℝ) (t : ℕ) :
    InformationTheory.klDiv (A.transcriptLaw hn mean (t + 1))
      (A.transcriptLaw hn mean' (t + 1)) =
      InformationTheory.klDiv (A.transcriptLaw hn mean t) (A.transcriptLaw hn mean' t) +
        ∑ i : Fin n, ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) *
          sampleLawOfMeans mean {ω | A.requestedArm hn t ω = some i} := by
  let : MeasurableSpace.CountablyGenerated (RunState n (t + 1)) := countablyGenerated_runState hn
  rw [A.klDiv_transcriptLaw_succ,
    klDiv_compProd_right_eq_lintegral_of_ne_top (Filter.Eventually.of_forall
      (A.klDiv_nextStateKernel_ne_top hn mean mean' t))]
  simp_rw [A.klDiv_nextStateKernel_eq_information]
  rw [A.lintegral_kernelInformation_transcriptLaw]

theorem klDiv_transcriptLaw_eq_sum_time (hn : 2 ≤ n) (mean mean' : Fin n → ℝ) (T : ℕ) :
    InformationTheory.klDiv (A.transcriptLaw hn mean T) (A.transcriptLaw hn mean' T) =
      ∑ t ∈ Finset.range T, ∑ i : Fin n, ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) *
        sampleLawOfMeans mean {ω | A.requestedArm hn t ω = some i} := by
  induction T with
  | zero => simp
  | succ T ih => rw [A.klDiv_transcriptLaw_succ_eq_add_information, ih, Finset.sum_range_succ]

theorem lintegral_truncatedArmSamples (hn : 2 ≤ n) (T : ℕ) (i : Fin n)
    (μ : Measure (SampleSpace n)) :
    ∫⁻ ω, A.truncatedArmSamples hn T i ω ∂μ =
      ∑ t ∈ Finset.range T, μ {ω | A.requestedArm hn t ω = some i} := by
  unfold truncatedArmSamples
  rw [lintegral_finsetSum _ (fun t _ =>
    Measurable.ite ((A.measurable_requestedArm hn t).eq_const (some i)).setOf
      measurable_const measurable_const)]
  apply Finset.sum_congr rfl
  intro t _
  simpa only [Set.indicator, Set.mem_ofPred_eq, one_mul] using
    lintegral_indicator_const (μ := μ)
      ((A.measurable_requestedArm hn t).eq_const (some i)).setOf (1 : ℝ≥0∞)

/-- Finite adaptive transcript KL equals the Gaussian information cost times
the expected arm counts, all evaluated under the source mean vector. This also
holds for mean vectors with ties and for policies that may never return. -/
theorem klDiv_transcriptLaw_eq_source_counts (hn : 2 ≤ n)
    (mean mean' : Fin n → ℝ) (T : ℕ) :
    InformationTheory.klDiv (A.transcriptLaw hn mean T) (A.transcriptLaw hn mean' T) =
      ∑ i : Fin n, ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) *
        ∫⁻ ω, A.truncatedArmSamples hn T i ω ∂sampleLawOfMeans mean := by
  rw [A.klDiv_transcriptLaw_eq_sum_time, Finset.sum_comm]
  simp_rw [A.lintegral_truncatedArmSamples, Finset.mul_sum]

/-- Current-state laws are only marginals of the full transcript, so their KL
is bounded by full-transcript KL; equality is not asserted. -/
theorem klDiv_run_le_transcript (hn : 2 ≤ n) (mean mean' : Fin n → ℝ) (t : ℕ) :
    InformationTheory.klDiv
      ((sampleLawOfMeans mean).map (fun ω => A.run hn ω t))
      ((sampleLawOfMeans mean').map (fun ω => A.run hn ω t)) ≤
      InformationTheory.klDiv (A.transcriptLaw hn mean t) (A.transcriptLaw hn mean' t) := by
  rw [← A.transcriptLaw_map_last, ← A.transcriptLaw_map_last]
  exact InformationTheory.klDiv_map_le _ _ (measurable_transcriptLast t)

theorem klDiv_run_le_source_counts (hn : 2 ≤ n) (mean mean' : Fin n → ℝ) (T : ℕ) :
    InformationTheory.klDiv
      ((sampleLawOfMeans mean).map (fun ω => A.run hn ω T))
      ((sampleLawOfMeans mean').map (fun ω => A.run hn ω T)) ≤
      ∑ i : Fin n, ENNReal.ofReal ((mean i - mean' i) ^ 2 / 2) *
        ∫⁻ ω, A.truncatedArmSamples hn T i ω ∂sampleLawOfMeans mean := by
  rw [← A.klDiv_transcriptLaw_eq_source_counts]
  exact A.klDiv_run_le_transcript hn mean mean' T

end Policy
end GapEntropy
