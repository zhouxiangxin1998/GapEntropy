import GapEntropy.UniversalCallFreshness
import GapEntropy.PredictableBernoulli
import GapEntropy.StoppedBlocks
import GapEntropy.CountableConditional

/-! Actual scheduled Gaussian arrays and countable past-parameter conditional laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace GapEntropy.AdaptiveGaussianCalls

variable {n : ℕ}

def severeProbability (m : ℕ) (d : ℝ) : unitInterval :=
  ⟨(GaussianNoise.law m).real {v | GaussianNoise.mean v < -(5 * d / 16)},
    measureReal_nonneg, measureReal_le_one⟩

def blockSevere (m : ℕ) (d : ℝ) (v : Fin m → ℝ) : Bool :=
  decide (GaussianNoise.mean v < -(5 * d / 16))

theorem measurable_blockSevere (m : ℕ) (d : ℝ) : Measurable (blockSevere m d) := by
  apply measurable_to_bool
  change MeasurableSet {v | decide (GaussianNoise.mean v < -(5 * d / 16)) = true}
  simpa only [decide_eq_true_eq] using
    measurableSet_lt (GaussianNoise.mean_measurable m) measurable_const

/-- An actual Gaussian block's severe indicator has its Bernoulli law, including both outcomes. -/
theorem blockSevere_hasLaw (m : ℕ) (d : ℝ) :
    HasLaw (blockSevere m d) (bernoulliMeasure true false (severeProbability m d)) (GaussianNoise.law m) := by
  refine ⟨(measurable_blockSevere m d).aemeasurable, ?_⟩
  let : IsProbabilityMeasure ((GaussianNoise.law m).map (blockSevere m d)) :=
    Measure.isProbabilityMeasure_map (measurable_blockSevere m d).aemeasurable
  apply ext_iff_measureReal_singleton.mpr
  intro b
  rw [Measure.real_def, Measure.map_apply (measurable_blockSevere m d) (measurableSet_singleton b)]
  change (GaussianNoise.law m).real ((blockSevere m d) ⁻¹' {b}) = _
  cases b with
  | true =>
    have heq : (blockSevere m d) ⁻¹' {true} =
        {v | GaussianNoise.mean v < -(5 * d / 16)} := by
      ext v
      simp [blockSevere]
    rw [heq]
    simp [severeProbability]
  | false =>
    have heq : (blockSevere m d) ⁻¹' {false} =
        {v | GaussianNoise.mean v < -(5 * d / 16)}ᶜ := by
      ext v
      simp [blockSevere]
    rw [heq, measureReal_compl (measurableSet_lt (GaussianNoise.mean_measurable m) measurable_const)]
    simp [severeProbability]

/-- Curried actual scheduled noises have the full independent arm-block law. -/
theorem schedule_centeredBlocks_hasLaw (S : Finset (Fin n)) (start m : ℕ) (mean : Fin n → ℝ) :
    HasLaw (fun ω : SampleSpace n => fun i : Fin n => fun j : Fin m =>
      MedianPolicy.fixedObservation S start i j ω - mean i)
      (BatchCollapse.callLaw n m) (sampleLawOfMeans mean) := by
  have hreshape : HasLaw (MeasurableEquiv.curry (Fin n) (Fin m) ℝ)
      (BatchCollapse.callLaw n m)
      (Measure.pi (fun _ : Fin n × Fin m => gaussianReal 0 1)) := by
    refine ⟨(MeasurableEquiv.curry (Fin n) (Fin m) ℝ).measurable.aemeasurable, ?_⟩
    simpa only [BatchCollapse.callLaw, GaussianNoise.law, Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin m) => gaussianReal 0 1)
  exact hreshape.comp (UniversalCall.schedule_noises_hasLaw S start m mean)

def scheduledSevere (S : Finset (Fin n)) (start m : ℕ) (mean : Fin n → ℝ) (d : ℝ)
    (ω : SampleSpace n) (i : Fin n) : Bool :=
  blockSevere m d (fun j => MedianPolicy.fixedObservation S start i j ω - mean i)

theorem measurable_scheduledSevere (S : Finset (Fin n)) (start m : ℕ)
    (mean : Fin n → ℝ) (d : ℝ) : Measurable (scheduledSevere S start m mean d) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_blockSevere m d).comp (by dsimp [MedianPolicy.fixedObservation]; fun_prop)

/-- The entire actual severe vector is a product Bernoulli law, not just coordinate marginals. -/
theorem scheduledSevere_hasLaw (S : Finset (Fin n)) (start m : ℕ) (mean : Fin n → ℝ) (d : ℝ) :
    HasLaw (scheduledSevere S start m mean d)
      (bernoulliFlagLaw (fun _ : Fin n => severeProbability m d)) (sampleLawOfMeans mean) := by
  have hflags : HasLaw (fun v : Fin n → Fin m → ℝ => fun i => blockSevere m d (v i))
      (bernoulliFlagLaw (fun _ : Fin n => severeProbability m d)) (BatchCollapse.callLaw n m) := by
    refine ⟨(measurable_pi_lambda _ fun i => (measurable_blockSevere m d).comp
      (measurable_pi_apply i)).aemeasurable, ?_⟩
    change (Measure.pi fun _ : Fin n => GaussianNoise.law m).map _ = _
    rw [Measure.pi_map_pi (f := fun (_ : Fin n) => blockSevere m d)
      (fun _ => (measurable_blockSevere m d).aemeasurable)]
    simp only [(blockSevere_hasLaw m d).map_eq, bernoulliFlagLaw]
  exact hflags.comp (schedule_centeredBlocks_hasLaw S start m mean)

/-- The severe flag is the literal centered empirical-mean error, on every active arm. -/
theorem scheduledSevere_eq_decide (S : Finset (Fin n)) (start : ℕ) {m : ℕ} (hm : 0 < m)
    (mean : Fin n → ℝ) (d : ℝ) (ω : SampleSpace n) (i : Fin n) :
    scheduledSevere S start m mean d ω i =
      decide (UniversalCall.scheduleEstimate S start m ω i - mean i < -(5 * d / 16)) := by
  unfold scheduledSevere blockSevere GaussianNoise.mean UniversalCall.scheduleEstimate Gaussian.sampleMean
  congr 2
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sub_div, mul_div_cancel_left₀ _ (by exact_mod_cast hm.ne')]

/-- The exact Bernoulli parameter obeys the derived Gaussian severe-tail estimate. -/
theorem severeProbability_le {m : ℕ} {d ρ : ℝ} (hd : 0 < d) (hρ : 0 < ρ)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ)) (hm : 0 < m) :
    (severeProbability m d : ℝ) ≤ ρ ^ (25 : ℕ) := by
  exact (BatchCollapse.noise_lower_tail hm (by positivity : 0 ≤ 5 * d / 16)).trans
    (BatchCollapse.severe_tail_of_budget hd hρ hbudget)

/-- The complete severe vector is independent of all observations and seed bits before its block. -/
theorem indepFun_prefix_scheduledSevere (S : Finset (Fin n)) (hS : S.Nonempty)
    (start : ℕ) {m : ℕ} (hm : 0 < m) (mean : Fin n → ℝ) (d : ℝ) :
    IndepFun (seedPrefix (n := n) start) (scheduledSevere S start m mean d)
      (sampleLawOfMeans mean) := by
  let f : (Fin n → ℝ) → Fin n → Bool := fun x i => decide (x i - mean i < -(5 * d / 16))
  have hf : Measurable f := by
    apply measurable_pi_lambda
    intro i
    apply measurable_to_bool
    change MeasurableSet {x : Fin n → ℝ | decide (x i - mean i < -(5 * d / 16)) = true}
    simpa only [decide_eq_true_eq] using
      measurableSet_lt ((show Measurable (fun x : Fin n → ℝ => x i) from measurable_pi_apply i).sub_const (mean i))
        (measurable_const (a := -(5 * d / 16)))
  have hi := (UniversalCall.indepFun_prefix_scheduleEstimate S hS start m mean).comp measurable_id hf
  have heq : scheduledSevere S start m mean d = f ∘ UniversalCall.scheduleEstimate S start m := by
    funext ω i
    exact scheduledSevere_eq_decide S start hm mean d ω i
  rw [heq]
  simpa only [Function.id_comp] using hi

/-- Actual past-event factorization for every joint flag outcome. -/
theorem scheduledSevere_event_factor (S : Finset (Fin n)) (hS : S.Nonempty)
    (start : ℕ) {m : ℕ} (hm : 0 < m) (mean : Fin n → ℝ) (d : ℝ)
    (E : Set (SeedPrefix n start)) (hE : MeasurableSet E) (x : Fin n → Bool) :
    (sampleLawOfMeans mean).real {ω | seedPrefix start ω ∈ E ∧
      scheduledSevere S start m mean d ω = x} =
      (sampleLawOfMeans mean).real ((seedPrefix start) ⁻¹' E) *
        (bernoulliFlagLaw (fun _ : Fin n => severeProbability m d)).real {x} := by
  have hf := (indepFun_prefix_scheduledSevere S hS start hm mean d).measure_inter_preimage_eq_mul
    E {x} hE (measurableSet_singleton x)
  have hmap := (scheduledSevere_hasLaw S start m mean d).map_eq
  have heq : sampleLawOfMeans mean ((scheduledSevere S start m mean d) ⁻¹' {x}) =
      bernoulliFlagLaw (fun _ : Fin n => severeProbability m d) {x} := by
    rw [← hmap, Measure.map_apply (measurable_scheduledSevere S start m mean d)
      (measurableSet_singleton x)]
  rw [heq] at hf
  exact (congrArg ENNReal.toReal hf).trans ENNReal.toReal_mul

/-- Countable call metadata. Real-valued tolerances may be arbitrary functions of this
metadata, as they are in the actual universal controller. -/
structure Schedule (κ : Type*) (n : ℕ) where
  active : κ → Finset (Fin n)
  start : κ → ℕ
  samples : κ → ℕ
  tolerance : κ → ℝ
  active_nonempty : ∀ k, (active k).Nonempty
  samples_pos : ∀ k, 0 < samples k

namespace Schedule
variable {κ : Type*} [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (C : Schedule κ n)

def flags (mean : Fin n → ℝ) (choice : SampleSpace n → κ) (ω : SampleSpace n) : Fin n → Bool :=
  scheduledSevere (C.active (choice ω)) (C.start (choice ω)) (C.samples (choice ω))
    mean (C.tolerance (choice ω)) ω

def parameters (choice : SampleSpace n → κ) (ω : SampleSpace n) (_i : Fin n) : unitInterval :=
  severeProbability (C.samples (choice ω)) (C.tolerance (choice ω))

theorem measurable_flags (mean : Fin n → ℝ) {choice : SampleSpace n → κ}
    (hchoice : Measurable choice) : Measurable (C.flags mean choice) := by
  have hF : Measurable (fun p : κ × SampleSpace n =>
      scheduledSevere (C.active p.1) (C.start p.1) (C.samples p.1) mean (C.tolerance p.1) p.2) := by
    apply measurable_from_prod_countable_right
    intro k
    exact measurable_scheduledSevere (C.active k) (C.start k) (C.samples k) mean (C.tolerance k)
  exact hF.comp (hchoice.prodMk measurable_id)

/-- Causal history representation on every selected metadata branch. This is a measurability
condition in the original reward table, and contains no probability or distribution conclusion. -/
def PastAtChoice (m : MeasurableSpace (SampleSpace n)) (choice : SampleSpace n → κ) : Prop :=
  ∀ R, MeasurableSet[m] R → ∀ k, ∃ E : Set (SeedPrefix n (C.start k)), MeasurableSet E ∧
    {ω | ω ∈ R ∧ choice ω = k} = (seedPrefix (C.start k)) ⁻¹' E

/-- Complete conditional product law for the actual scheduled severe indicators at a random
finite past boundary and a past-selected random sample size. No Gaussian law is assumed. -/
theorem hasConditionalBernoulliLaw (mean : Fin n → ℝ)
    {m : MeasurableSpace (SampleSpace n)} (hm : m ≤ (Prod.instMeasurableSpace : MeasurableSpace (SampleSpace n)))
    {choice : SampleSpace n → κ} (hchoice : Measurable[m] choice)
    (hpast : C.PastAtChoice m choice) :
    HasConditionalBernoulliLaw (sampleLawOfMeans mean) m (C.flags mean choice) (C.parameters choice) := by
  let μ := sampleLawOfMeans mean
  have hchoice' : Measurable[Prod.instMeasurableSpace] choice := hchoice.mono hm le_rfl
  have hX := C.measurable_flags mean hchoice'
  intro x
  let f : SampleSpace n → ℝ := {ω | C.flags mean choice ω = x}.indicator (fun _ => 1)
  let q : κ → ℝ := fun k =>
    (bernoulliFlagLaw (fun _ : Fin n => severeProbability (C.samples k) (C.tolerance k))).real {x}
  let g : SampleSpace n → ℝ := fun ω => q (choice ω)
  have hq0 (k : κ) : 0 ≤ q k := measureReal_nonneg
  have hq1 (k : κ) : q k ≤ 1 := measureReal_le_one
  have hgm : Measurable[m] g := (measurable_of_countable q).comp hchoice
  have hgint : Integrable g μ := (integrable_const (1 : ℝ)).mono'
    (hgm.mono hm le_rfl).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 (choice ω))]
      exact hq1 (choice ω))
  have hfmeas : MeasurableSet[Prod.instMeasurableSpace] {ω | C.flags mean choice ω = x} :=
    hX (measurableSet_singleton x)
  have hfint : Integrable f μ := (integrable_const (1 : ℝ)).indicator hfmeas
  have hce : g =ᵐ[μ] μ[f | m] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hfint
      (fun _ _ _ => hgint.integrableOn) _ hgm.aestronglyMeasurable
    intro R hR _
    let part : κ → Set (SampleSpace n) := fun k => {ω | ω ∈ R ∧ choice ω = k}
    have hpart (k : κ) : MeasurableSet[Prod.instMeasurableSpace] (part k) :=
      (hm _ hR).inter (hchoice' (measurableSet_singleton k))
    have hdis : Pairwise (Function.onFun Disjoint part) := by
      intro k l hkl
      apply Set.disjoint_left.mpr
      intro ω hk hl
      exact hkl (hk.2.symm.trans hl.2)
    have hunion : (⋃ k, part k) = R := by ext ω; simp [part]
    have hpartEq (k : κ) : (∫ ω in part k, g ω ∂μ) = ∫ ω in part k, f ω ∂μ := by
      obtain ⟨E, hE, hER⟩ := hpast R hR k
      have hfactor := scheduledSevere_event_factor (C.active k) (C.active_nonempty k)
        (C.start k) (C.samples_pos k) mean (C.tolerance k) E hE x
      have heq : part k ∩ {ω | C.flags mean choice ω = x} =
          {ω | seedPrefix (C.start k) ω ∈ E ∧
            scheduledSevere (C.active k) (C.start k) (C.samples k) mean (C.tolerance k) ω = x} := by
        ext ω
        constructor
        · rintro ⟨hpartω, hXω⟩
          have hchoiceω : choice ω = k := hpartω.2
          refine ⟨?_, ?_⟩
          · change ω ∈ (seedPrefix (C.start k)) ⁻¹' E
            rw [← hER]
            exact hpartω
          · simpa only [Set.mem_ofPred_eq, flags, hchoiceω] using hXω
        · rintro ⟨hEω, hXω⟩
          have hpω : ω ∈ part k := by
            change ω ∈ {ω | ω ∈ R ∧ choice ω = k}
            rw [hER]
            exact hEω
          exact ⟨hpω, by simpa only [Set.mem_ofPred_eq, flags, hpω.2] using hXω⟩
      calc
        (∫ ω in part k, g ω ∂μ) = ∫ _ω in part k, q k ∂μ :=
          setIntegral_congr_fun (hpart k) fun ω hω => by simp only [g, hω.2]
        _ = μ.real (part k) * q k := by rw [setIntegral_const, smul_eq_mul]
        _ = μ.real (part k ∩ {ω | C.flags mean choice ω = x}) := by
          rw [heq]
          change _ = (sampleLawOfMeans mean).real _
          rw [hfactor]
          congr 1
          exact congrArg (fun s => (sampleLawOfMeans mean).real s) hER
        _ = ∫ ω in part k, f ω ∂μ := by
          dsimp only [f]
          rw [setIntegral_indicator hfmeas, setIntegral_const, smul_eq_mul, mul_one]
    rw [← hunion, integral_iUnion hpart hdis hgint.integrableOn,
      integral_iUnion hpart hdis hfint.integrableOn]
    exact tsum_congr hpartEq
  have hef : f = (fun ω => if C.flags mean choice ω = x then (1 : ℝ) else 0) := by
    funext ω
    by_cases hx : C.flags mean choice ω = x <;> simp [f, hx]
  rw [hef] at hce
  exact hce.symm

variable [MeasurableSpace (Option κ)] [MeasurableSingletonClass (Option κ)]

/-- An inactive/terminal stage produces no fresh flags and consumes no hazard. -/
def optionalFlags (mean : Fin n → ℝ) (choice : SampleSpace n → Option κ)
    (ω : SampleSpace n) : Fin n → Bool :=
  match choice ω with
  | none => fun _ => false
  | some k => scheduledSevere (C.active k) (C.start k) (C.samples k) mean (C.tolerance k) ω

def optionalParameters (k : Option κ) (_i : Fin n) : unitInterval :=
  match k with
  | none => 0
  | some k => severeProbability (C.samples k) (C.tolerance k)

omit [MeasurableSpace κ] [MeasurableSingletonClass κ] in
theorem measurable_optionalFlags (mean : Fin n → ℝ) {choice : SampleSpace n → Option κ}
    (hchoice : Measurable choice) : Measurable (C.optionalFlags mean choice) := by
  have hF : Measurable (fun p : Option κ × SampleSpace n =>
      match p.1 with
      | none => (fun _ : Fin n => false)
      | some k => scheduledSevere (C.active k) (C.start k) (C.samples k) mean (C.tolerance k) p.2) := by
    apply measurable_from_prod_countable_right
    intro k
    cases k with
    | none => exact measurable_const
    | some k => exact measurable_scheduledSevere (C.active k) (C.start k) (C.samples k) mean (C.tolerance k)
  exact hF.comp (hchoice.prodMk measurable_id)

def OptionalPastAtChoice (m : MeasurableSpace (SampleSpace n))
    (choice : SampleSpace n → Option κ) : Prop :=
  ∀ R, MeasurableSet[m] R → ∀ k, ∃ E : Set (SeedPrefix n (C.start k)), MeasurableSet E ∧
    {ω | ω ∈ R ∧ choice ω = some k} = (seedPrefix (C.start k)) ⁻¹' E

omit [MeasurableSpace κ] [MeasurableSingletonClass κ] in
/-- The actual conditional product law includes absorbing terminal stages exactly, without
sampling auxiliary Gaussian data at terminal stages. -/
theorem optional_hasConditionalBernoulliLaw (mean : Fin n → ℝ)
    {m : MeasurableSpace (SampleSpace n)}
    (hm : m ≤ (Prod.instMeasurableSpace : MeasurableSpace (SampleSpace n)))
    {choice : SampleSpace n → Option κ} (hchoice : Measurable[m] choice)
    (hpast : C.OptionalPastAtChoice m choice) :
    HasConditionalBernoulliLaw (sampleLawOfMeans mean) m (C.optionalFlags mean choice)
      (fun ω => C.optionalParameters (choice ω)) := by
  unfold HasConditionalBernoulliLaw
  apply conditionalLaw_of_countable_partition (mΩ := Prod.instMeasurableSpace)
    (sampleLawOfMeans mean) hm choice hchoice
    (C.optionalFlags mean choice) (C.measurable_optionalFlags mean (hchoice.mono hm le_rfl))
    (fun k => bernoulliFlagLaw (C.optionalParameters k))
  intro R hR k x
  cases k with
  | none =>
    have hzero : bernoulliFlagLaw (C.optionalParameters none) =
        Measure.dirac (fun _ : Fin n => false) := by
      simp only [optionalParameters, bernoulliFlagLaw, bernoulliMeasure_zero]
      rw [← Measure.infinitePi_eq_pi]
      exact Measure.infinitePi_dirac _
    rw [hzero]
    by_cases hx : (fun _ : Fin n => false) = x
    · have heq : {ω | ω ∈ R ∧ choice ω = none} ∩
          {ω | C.optionalFlags mean choice ω = x} = {ω | ω ∈ R ∧ choice ω = none} := by
        ext ω
        constructor
        · exact And.left
        · intro hω
          exact ⟨hω, by simpa only [Set.mem_ofPred_eq, optionalFlags, hω.2] using hx⟩
      rw [heq]
      simp [← hx, Measure.real_def, Measure.dirac_apply']
    · have heq : {ω | ω ∈ R ∧ choice ω = none} ∩
          {ω | C.optionalFlags mean choice ω = x} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨hω, hflag⟩
        exact hx (by simpa only [Set.mem_ofPred_eq, optionalFlags, hω.2] using hflag)
      rw [heq]
      simp [hx, Measure.real_def, Measure.dirac_apply']
  | some k =>
    obtain ⟨E, hE, hER⟩ := hpast R hR k
    have hfactor := scheduledSevere_event_factor (C.active k) (C.active_nonempty k)
      (C.start k) (C.samples_pos k) mean (C.tolerance k) E hE x
    have heq : {ω | ω ∈ R ∧ choice ω = some k} ∩ {ω | C.optionalFlags mean choice ω = x} =
        {ω | seedPrefix (C.start k) ω ∈ E ∧
          scheduledSevere (C.active k) (C.start k) (C.samples k) mean (C.tolerance k) ω = x} := by
      ext ω
      constructor
      · rintro ⟨hω, hflag⟩
        refine ⟨?_, ?_⟩
        · change ω ∈ (seedPrefix (C.start k)) ⁻¹' E
          rw [← hER]
          exact hω
        · simpa only [Set.mem_ofPred_eq, optionalFlags, hω.2] using hflag
      · rintro ⟨hω, hflag⟩
        have hpω : ω ∈ {ω | ω ∈ R ∧ choice ω = some k} := by
          rw [hER]
          exact hω
        exact ⟨hpω, by simpa only [Set.mem_ofPred_eq, optionalFlags, hpω.2] using hflag⟩
    rw [heq, hfactor, hER]
    rfl

end Schedule
end GapEntropy.AdaptiveGaussianCalls
