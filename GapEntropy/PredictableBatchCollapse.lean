import GapEntropy.BatchCollapse
import GapEntropy.BatchAllocation
import GapEntropy.SortingMeasurability
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.ProductMeasure

/-!
# Predictable Gaussian batch collapse

The conditional premise specifies the complete Gaussian reservoir distribution given the
exposed history. Actual single-call Gaussian estimates then imply a conditional work charge.
Unused reservoir coordinates can be auxiliary independent blocks; their realization for a
particular sampling policy remains a separate fresh-sample obligation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GapEntropy.PredictableBatchCollapse

abbrev Reservoir (n : ℕ) := ∀ m : ℕ, Fin n → Fin m → ℝ

def reservoirLaw (n : ℕ) : Measure (Reservoir n) :=
  Measure.infinitePi (fun m => BatchCollapse.callLaw n m)

instance reservoirLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (reservoirLaw n) := by
  unfold reservoirLaw
  infer_instance

variable {n : ℕ} {Γ : Type*} [MeasurableSpace Γ]

/-- Parameters exposed before the fresh sampling block. -/
structure Parameters (Γ : Type*) [MeasurableSpace Γ] (n : ℕ) where
  active : Γ → Finset (Fin n)
  sampleSize : Γ → ℕ
  tolerance : Γ → ℝ
  reference : Γ → ℝ
  /-- Tail parameter ρ; in the manuscript this is the call confidence α divided by 128. -/
  confidence : Γ → ℝ
  eligible : Set Γ
  measurable_active : Measurable active
  measurable_sampleSize : Measurable sampleSize
  measurable_tolerance : Measurable tolerance
  measurable_reference : Measurable reference
  measurable_confidence : Measurable confidence
  measurable_eligible : MeasurableSet eligible

namespace Parameters

variable (C : Parameters Γ n)

def work (γ : Γ) : ℝ := (C.active γ).card * (C.tolerance γ ^ 2)⁻¹

theorem work_nonneg (γ : Γ) : 0 ≤ C.work γ := by unfold work; positivity

theorem measurable_work : Measurable C.work := by
  have hc : Measurable (fun γ => ((C.active γ).card : ℝ)) :=
    (measurable_of_finite (fun S : Finset (Fin n) => (S.card : ℝ))).comp C.measurable_active
  exact hc.mul (C.measurable_tolerance.pow_const 2).inv

/-- Only eligible histories contribute to this event. -/
def event (I : Instance n) (B : Finset (Fin n)) : Set (Γ × Reservoir n) :=
  {p | p.1 ∈ C.eligible ∧ BatchCollapse.collapse (C.active p.1) B
    (BatchCollapse.empirical I.mean (p.2 (C.sampleSize p.1)))
    (C.reference p.1) (C.tolerance p.1)}

theorem measurableSet_collapse {Ω : Type*} [MeasurableSpace Ω]
    {S : Ω → Finset (Fin n)} {X : Fin n → Ω → ℝ} {z d : Ω → ℝ}
    (B : Finset (Fin n)) (hS : Measurable S) (hX : ∀ i, Measurable (X i))
    (hz : Measurable z) (hd : Measurable d) :
    MeasurableSet {ω | BatchCollapse.collapse (S ω) B (fun i => X i ω) (z ω) (d ω)} := by
  let P : Finset (Fin n) × Finset (Fin n) → Prop := fun p =>
    ((p.1 ∩ B).card = 1 ∧ (p.2 ∩ B).card = 0) ∨
    (2 ≤ (p.1 ∩ B).card ∧ (p.2 ∩ B).card ≤ 1)
  exact measurableSet_setOfPred.mpr ((measurable_of_finite P).comp
    (hS.prodMk (SortingMeasurability.padded_measurable hS hX hz hd)))

theorem measurable_event (I : Instance n) (B : Finset (Fin n)) :
    MeasurableSet (C.event I B) := by
  have hf (m : ℕ) : MeasurableSet {p : Γ × Reservoir n |
      BatchCollapse.collapse (C.active p.1) B
        (BatchCollapse.empirical I.mean (p.2 m)) (C.reference p.1) (C.tolerance p.1)} := by
    apply measurableSet_collapse B (C.measurable_active.comp measurable_fst)
      _ (C.measurable_reference.comp measurable_fst) (C.measurable_tolerance.comp measurable_fst)
    intro i
    exact measurable_const.add ((GaussianNoise.mean_measurable m).comp
      ((measurable_pi_apply i).comp ((measurable_pi_apply m).comp measurable_snd)))
  have heq : C.event I B = (Prod.fst ⁻¹' C.eligible) ∩
      ⋃ m : ℕ, {p : Γ × Reservoir n | C.sampleSize p.1 = m} ∩
        {p | BatchCollapse.collapse (C.active p.1) B
          (BatchCollapse.empirical I.mean (p.2 m)) (C.reference p.1) (C.tolerance p.1)} := by
    ext p
    simp only [event, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_iUnion]
    constructor
    · rintro ⟨he, hc⟩
      exact ⟨he, C.sampleSize p.1, rfl, hc⟩
    · rintro ⟨he, m, hm, hc⟩
      exact ⟨he, hm.symm ▸ hc⟩
  rw [heq]
  exact (C.measurable_eligible.preimage measurable_fst).inter
    (MeasurableSet.iUnion fun m =>
      (measurableSet_eq_fun (C.measurable_sampleSize.comp measurable_fst) measurable_const).inter (hf m))

theorem reservoir_event_real (I : Instance n) (B : Finset (Fin n))
    {γ : Γ} (hγ : γ ∈ C.eligible) :
    (reservoirLaw n).real {y | (γ, y) ∈ C.event I B} =
      (BatchCollapse.callLaw n (C.sampleSize γ)).real
        {x | BatchCollapse.collapse (C.active γ) B (BatchCollapse.empirical I.mean x)
          (C.reference γ) (C.tolerance γ)} := by
  have hE : MeasurableSet {x : Fin n → Fin (C.sampleSize γ) → ℝ |
      BatchCollapse.collapse (C.active γ) B (BatchCollapse.empirical I.mean x)
        (C.reference γ) (C.tolerance γ)} := measurableSet_collapse B measurable_const
    (fun i => measurable_const.add ((GaussianNoise.mean_measurable _).comp (measurable_pi_apply i)))
    measurable_const measurable_const
  have hp := (measurePreserving_eval_infinitePi
    (fun m => BatchCollapse.callLaw n m) (C.sampleSize γ)).measure_preimage hE.nullMeasurableSet
  simpa only [Measure.real_def, event, hγ, true_and, reservoirLaw, Function.eval,
    Set.preimage_ofPred_eq, Set.mem_ofPred_eq] using congrArg ENNReal.toReal hp

/-- Numerical and geometric eligibility conditions from the original instance.
There is no probability bound among these fields. -/
structure Admissible (I : Instance n) (B : Finset (Fin n)) (η M : ℝ) : Prop where
  work_le : ∀ γ, C.work γ ≤ M
  core_nonempty : ∀ γ ∈ C.eligible, (C.active γ ∩ B).Nonempty
  active_card : ∀ γ ∈ C.eligible, 8 ≤ (C.active γ).card
  sampleSize_pos : ∀ γ ∈ C.eligible, 0 < C.sampleSize γ
  tolerance_pos : ∀ γ ∈ C.eligible, 0 < C.tolerance γ
  confidence_pos : ∀ γ ∈ C.eligible, 0 < C.confidence γ
  confidence_allocation : ∀ γ ∈ C.eligible, C.confidence γ ≤ η * C.work γ / M
  upper_valid : ∀ γ ∈ C.eligible, C.reference γ ≤ I.mean I.best + C.tolerance γ / 16
  core_gap : ∀ γ ∈ C.eligible, ∀ i ∈ B, I.gap i ≤ C.tolerance γ / 8
  sampling_budget : ∀ γ ∈ C.eligible,
    512 * (C.tolerance γ ^ 2)⁻¹ * Real.log (1 / C.confidence γ) ≤ C.sampleSize γ

/-- E.16 and E.17 charged to the actual Gaussian reservoir probability. -/
theorem reservoir_event_le_charge (I : Instance n) (B : Finset (Fin n))
    (hbest : I.best ∈ B) {η M : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1280)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ M)
    (hC : C.Admissible I B η M) (γ : Γ) :
    (reservoirLaw n).real {y | (γ, y) ∈ C.event I B} ≤
      (3 * η ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / M) ^ (3 : ℕ)) * (C.work γ / M) := by
  have hM : 0 < M := hh.trans_le hhM
  by_cases he : γ ∈ C.eligible
  · rw [C.reservoir_event_real I B he]
    have hw : 0 < C.work γ := by
      unfold work
      exact mul_pos (by exact_mod_cast (show 0 < (C.active γ).card by
        have := hC.active_card γ he; omega)) (inv_pos.mpr (sq_pos_of_pos (hC.tolerance_pos γ he)))
    have hρ : C.confidence γ ≤ 1 / 2 := by
      have := hC.confidence_allocation γ he
      have hwm : C.work γ / M ≤ 1 := (div_le_one hM).mpr (hC.work_le γ)
      have hmul := mul_le_mul_of_nonneg_left hwm hη.le
      rw [mul_one] at hmul
      rw [mul_div_assoc] at this
      linarith
    exact (BatchCollapse.collapse_probability_le_source_exponent I (C.active γ) B hbest
      (hC.core_nonempty γ he) (hC.active_card γ he) hh (hC.sampleSize_pos γ he)
      (hC.tolerance_pos γ he) (hC.confidence_pos γ he) hρ (hC.upper_valid γ he)
      (hC.core_gap γ he) (hC.sampling_budget γ he)).trans
      (batch_reserved_charge_bound hη hηsmall hh hhM hw (hC.work_le γ)
        (hC.confidence_pos γ he) (hC.confidence_allocation γ he))
  · have hempty : {y | (γ, y) ∈ C.event I B} = ∅ := by ext y; simp [event, he]
    rw [hempty, measureReal_empty]
    have := C.work_nonneg γ
    positivity

def eventIndicator (I : Instance n) (B : Finset (Fin n)) : Γ × Reservoir n → ℝ :=
  (C.event I B).indicator (fun _ => 1)

theorem measurable_eventIndicator (I : Instance n) (B : Finset (Fin n)) :
    Measurable (C.eventIndicator I B) :=
  measurable_const.indicator (C.measurable_event I B)

theorem norm_eventIndicator_le (I : Instance n) (B : Finset (Fin n)) (p : Γ × Reservoir n) :
    ‖C.eventIndicator I B p‖ ≤ 1 := by
  classical
  by_cases hp : p ∈ C.event I B <;> simp [eventIndicator, hp]

theorem integral_eventIndicator (I : Instance n) (B : Finset (Fin n)) (γ : Γ) :
    (∫ y, C.eventIndicator I B (γ, y) ∂reservoirLaw n) =
      (reservoirLaw n).real {y | (γ, y) ∈ C.event I B} := by
  have he : MeasurableSet {y : Reservoir n | (γ, y) ∈ C.event I B} :=
    (C.measurable_event I B).preimage ((measurable_const (a := γ)).prodMk measurable_id)
  simpa only [eventIndicator, Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq, smul_eq_mul, mul_one] using
    (integral_indicator_const (μ := reservoirLaw n) (1 : ℝ) he)

end Parameters

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Full conditional Gaussian law at the exposed history, including same-call arm independence. -/
def HasFreshReservoir (H : Ω → Γ) (Y : Ω → Reservoir n) : Prop :=
  ∀ᵐ ω ∂μ, condDistrib Y H μ (H ω) = reservoirLaw n

namespace Parameters

variable (C : Parameters Γ n) {μ}

theorem condExp_eventIndicator_le_charge (I : Instance n) (B : Finset (Fin n))
    (hbest : I.best ∈ B) {η M : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1280)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ M)
    (hC : C.Admissible I B η M) {H : Ω → Γ} {Y : Ω → Reservoir n}
    (hH : Measurable H) (hY : Measurable Y) (hfresh : HasFreshReservoir μ H Y) :
    μ[fun ω => C.eventIndicator I B (H ω, Y ω) | MeasurableSpace.comap H inferInstance] ≤ᵐ[μ]
      fun ω => (3 * η ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / M) ^ (3 : ℕ)) *
        (C.work (H ω) / M) := by
  have hfint : Integrable (fun ω => C.eventIndicator I B (H ω, Y ω)) μ :=
    (integrable_const (1 : ℝ)).mono'
      ((C.measurable_eventIndicator I B).comp (hH.prodMk hY)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => C.norm_eventIndicator_le I B (H ω, Y ω))
  have hce := condExp_prod_ae_eq_integral_condDistrib hH hY.aemeasurable
    (C.measurable_eventIndicator I B).stronglyMeasurable hfint
  filter_upwards [hce, hfresh] with ω hce hfresh
  rw [hce, hfresh, C.integral_eventIndicator]
  exact C.reservoir_event_le_charge I B hbest hη hηsmall hh hhM hC (H ω)

/-- Integrating the derived conditional estimate gives the expected work charge. -/
theorem probability_event_le_expected_charge (I : Instance n) (B : Finset (Fin n))
    (hbest : I.best ∈ B) {η M : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1280)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ M)
    (hC : C.Admissible I B η M) {H : Ω → Γ} {Y : Ω → Reservoir n}
    (hH : Measurable H) (hY : Measurable Y) (hfresh : HasFreshReservoir μ H Y) :
    μ.real {ω | (H ω, Y ω) ∈ C.event I B} ≤
      (3 * η ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / M) ^ (3 : ℕ)) *
        ((∫ ω, C.work (H ω) ∂μ) / M) := by
  have hwork : Integrable (fun ω => C.work (H ω)) μ :=
    (integrable_const M).mono' (C.measurable_work.comp hH).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (C.work_nonneg _)]
        exact hC.work_le _)
  have hint := integral_mono_ae (integrable_condExp (μ := μ))
    ((hwork.div_const M).const_mul
      (3 * η ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / M) ^ (3 : ℕ)))
    (C.condExp_eventIndicator_le_charge I B hbest hη hηsmall hh hhM hC hH hY hfresh)
  rw [integral_condExp hH.comap_le, integral_const_mul, integral_div] at hint
  have he : MeasurableSet {ω | (H ω, Y ω) ∈ C.event I B} :=
    (C.measurable_event I B).preimage (hH.prodMk hY)
  have heq : (∫ ω, C.eventIndicator I B (H ω, Y ω) ∂μ) =
      μ.real {ω | (H ω, Y ω) ∈ C.event I B} := by
    simpa only [eventIndicator, Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq, smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) he)
  rwa [heq] at hint

end Parameters
/-- Finite predictable-call union bound. Adaptivity is allowed through each exposed history;
independence between distinct calls is not assumed. -/
theorem probability_any_call_finset_le
    (C : ℕ → Parameters Γ n) (I : Instance n) (B : Finset (Fin n))
    (hbest : I.best ∈ B) {η M : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1280)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ M)
    (hC : ∀ t, (C t).Admissible I B η M) (H : ℕ → Ω → Γ) (Y : ℕ → Ω → Reservoir n)
    (hH : ∀ t, Measurable (H t)) (hY : ∀ t, Measurable (Y t))
    (hfresh : ∀ t, HasFreshReservoir μ (H t) (Y t)) (F : Finset ℕ)
    (hcap : ∀ᵐ ω ∂μ, ∑ t ∈ F, (C t).work (H t ω) ≤ M) :
    μ.real (⋃ t ∈ F, {ω | (H t ω, Y t ω) ∈ (C t).event I B}) ≤
      3 * η ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / M) ^ (3 : ℕ) := by
  let K := 3 * η ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / M) ^ (3 : ℕ)
  have hM : 0 < M := hh.trans_le hhM
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hwint (t : ℕ) : Integrable (fun ω => (C t).work (H t ω)) μ :=
    (integrable_const M).mono' ((C t).measurable_work.comp (hH t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((C t).work_nonneg _)]
        exact (hC t).work_le _)
  have hsum : (∫ ω, ∑ t ∈ F, (C t).work (H t ω) ∂μ) ≤ M := by
    have h := integral_mono_ae (integrable_finsetSum F (fun t _ => hwint t))
      (integrable_const M) hcap
    simpa using h
  calc
    μ.real (⋃ t ∈ F, {ω | (H t ω, Y t ω) ∈ (C t).event I B}) ≤
        ∑ t ∈ F, μ.real {ω | (H t ω, Y t ω) ∈ (C t).event I B} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ t ∈ F, K * ((∫ ω, (C t).work (H t ω) ∂μ) / M) :=
      Finset.sum_le_sum fun t _ => (C t).probability_event_le_expected_charge I B hbest
        hη hηsmall hh hhM (hC t) (hH t) (hY t) (hfresh t)
    _ = K * ((∫ ω, ∑ t ∈ F, (C t).work (H t ω) ∂μ) / M) := by
      rw [← Finset.mul_sum, ← Finset.sum_div, integral_finsetSum F (fun t _ => hwint t)]
    _ ≤ K := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ((div_le_one hM).mpr hsum) hK

/-- E.12 for countably many calls with a pathwise work reservation cap on every prefix.
The probabilistic premise is the complete conditional Gaussian law of each fresh call. -/
theorem probability_any_call_le
    (C : ℕ → Parameters Γ n) (I : Instance n) (B : Finset (Fin n))
    (hbest : I.best ∈ B) {η M : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1280)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ M)
    (hC : ∀ t, (C t).Admissible I B η M) (H : ℕ → Ω → Γ) (Y : ℕ → Ω → Reservoir n)
    (hH : ∀ t, Measurable (H t)) (hY : ∀ t, Measurable (Y t))
    (hfresh : ∀ t, HasFreshReservoir μ (H t) (Y t))
    (hcap : ∀ T, ∀ᵐ ω ∂μ, ∑ t ∈ Finset.range T, (C t).work (H t ω) ≤ M) :
    μ (⋃ t, {ω | (H t ω, Y t ω) ∈ (C t).event I B}) ≤
      ENNReal.ofReal (3 * η ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / M) ^ (3 : ℕ)) := by
  have hM : 0 < M := hh.trans_le hhM
  have hK : 0 ≤ 3 * η ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / M) ^ (3 : ℕ) := by
    positivity
  rw [measure_iUnion_eq_iSup_accumulate]
  apply iSup_le
  intro T
  have heq : Set.accumulate (fun t => {ω | (H t ω, Y t ω) ∈ (C t).event I B}) T =
      ⋃ t ∈ Finset.range (T + 1), {ω | (H t ω, Y t ω) ∈ (C t).event I B} := by
    ext ω
    simp only [Set.accumulate_def, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
  rw [heq]
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hK).mpr
  exact probability_any_call_finset_le μ C I B hbest hη hηsmall hh hhM hC H Y hH hY hfresh
    (Finset.range (T + 1)) (hcap (T + 1))

end GapEntropy.PredictableBatchCollapse
