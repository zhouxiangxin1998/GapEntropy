import GapEntropy.UniversalSevereProcess
import GapEntropy.PredictableBatchCollapse

/-! Actual universal-call E.12 via the fixed maximal upper-valid reference. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace GapEntropy.UniversalBatchCollapse
open UniversalAttempt UniversalSevereProcess UniversalCall EliminationTape AdaptiveGaussianCalls
variable {n : ℕ}

/-- Increasing the numerical reference can only delete more arms in the padded rule. -/
theorem padded_reference_antitone (S : Finset (Fin n)) (x : Fin n → ℝ) {z z' d : ℝ}
    (hz : z ≤ z') : Elimination.padded S x z' d ⊆ Elimination.padded S x z d := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · apply Finset.mem_union_left
    obtain ⟨hiS, hxi⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiS, by linarith⟩
  · exact Finset.mem_union_right _ hi

/-- A collapse with any upper-valid reference is contained in the fixed maximal-reference
collapse, eliminating any need to condition on the random reference value. -/
theorem collapse_reference_mono (S B : Finset (Fin n)) (x : Fin n → ℝ) {z z' d : ℝ}
    (hz : z ≤ z') (hc : BatchCollapse.collapse S B x z d) :
    BatchCollapse.collapse S B x z' d := by
  have hcard := Finset.card_le_card (Finset.inter_subset_inter
    (padded_reference_antitone S x (d := d) hz) (Finset.Subset.rfl : B ⊆ B))
  rcases hc with ⟨hbefore, hafter⟩ | ⟨hbefore, hafter⟩
  · exact Or.inl ⟨hbefore, by omega⟩
  · exact Or.inr ⟨hbefore, hcard.trans hafter⟩

theorem empirical_centeredBlocks_eq (S : Finset (Fin n)) (start : ℕ) {m : ℕ} (hm : 0 < m)
    (mean : Fin n → ℝ) (ω : SampleSpace n) :
    BatchCollapse.empirical mean (fun i (j : Fin m) => MedianPolicy.fixedObservation S start i j ω - mean i) =
      scheduleEstimate S start m ω := by
  funext i
  unfold BatchCollapse.empirical GaussianNoise.mean scheduleEstimate Gaussian.sampleMean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sub_div, mul_div_cancel_left₀ _ (by exact_mod_cast hm.ne')]
  ring

/-- Fixed actual scheduled sample means have exactly the independent block comparison law. -/
theorem schedule_collapse_probability (I : Instance n) (S B : Finset (Fin n))
    (start : ℕ) {m : ℕ} (hm : 0 < m) (z d : ℝ) :
    (sampleLawOfMeans I.mean).real {ω | BatchCollapse.collapse S B (scheduleEstimate S start m ω) z d} =
      (BatchCollapse.callLaw n m).real {v | BatchCollapse.collapse S B (BatchCollapse.empirical I.mean v) z d} := by
  have hE : MeasurableSet {v : Fin n → Fin m → ℝ |
      BatchCollapse.collapse S B (BatchCollapse.empirical I.mean v) z d} :=
    PredictableBatchCollapse.Parameters.measurableSet_collapse B measurable_const
      (fun i => measurable_const.add ((GaussianNoise.mean_measurable m).comp (measurable_pi_apply i)))
      measurable_const measurable_const
  have he := (schedule_centeredBlocks_hasLaw S start m I.mean).measure_eq hE
  simp only [empirical_centeredBlocks_eq S start hm I.mean] at he
  exact congrArg ENNReal.toReal he

theorem call_work_eq (c : Config) (a : Metadata n) :
    ((a.call c).work : ℝ) = (a.active.card : ℝ) * (a.tolerance ^ 2)⁻¹ := by
  change ((a.active.card * 4 ^ a.scale : ℕ) : ℝ) = _
  rw [Nat.cast_mul, Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  congr 1
  unfold Metadata.tolerance
  simp only [zpow_neg, zpow_natCast, inv_pow, inv_inv]
  rw [← pow_mul, Nat.mul_comm a.scale 2, pow_mul]
  norm_num

def eligible (I : Instance n) (B : Finset (Fin n)) (a : Metadata n) : Prop :=
  8 ≤ a.active.card ∧ (a.active ∩ B).Nonempty ∧ ∀ i ∈ B, I.gap i ≤ a.tolerance / 8

def comparison (c : Config) (I : Instance n) (B : Finset (Fin n)) (a : Accepted c n)
    (ω : SampleSpace n) : Bool :=
  decide (eligible I B a.val ∧ BatchCollapse.collapse a.val.active B
    (scheduleEstimate a.val.active (activeBoundary c a.val) (activeSamples a.val.tolerance (a.val.alpha c)) ω)
    (I.mean I.best + a.val.tolerance / 16) a.val.tolerance)

theorem measurable_comparison (c : Config) (I : Instance n) (B : Finset (Fin n)) (a : Accepted c n) :
    Measurable (comparison c I B a) := by
  apply measurable_to_bool
  change MeasurableSet {ω | decide (_ ∧ _) = true}
  simp only [decide_eq_true_eq]
  apply MeasurableSet.inter (MeasurableSet.const _)
  exact PredictableBatchCollapse.Parameters.measurableSet_collapse B measurable_const
    (fun i => by unfold scheduleEstimate Gaussian.sampleMean MedianPolicy.fixedObservation; fun_prop)
    measurable_const measurable_const

/-- Actual fixed comparison probability, from the actual Gaussian estimates and source hardness. -/
theorem comparison_probability_le (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (hbest : I.best ∈ B)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ c.workCap)
    (a : Accepted c n) :
    (sampleLawOfMeans I.mean).real {ω | comparison c I B a ω = true} ≤
      (3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ)) *
        (((a.val.call c).work : ℝ) / c.workCap) := by
  have hM : (0 : ℝ) < c.workCap := by unfold Config.workCap; positivity
  have hwNat : 0 < (a.val.call c).work := by
    have := Reservation.two_le_call_work (a.val.call c) a.property.1
    omega
  have hw : (0 : ℝ) < (a.val.call c).work := by exact_mod_cast hwNat
  have hwM : ((a.val.call c).work : ℝ) ≤ c.workCap := by
    exact_mod_cast (show (a.val.call c).work ≤ c.workCap by have := a.property.2.1; omega)
  have hη : 0 < eta c := by unfold eta Config.errorBudget; exact div_pos (div_pos hδ.1 (by norm_num)) (by norm_num)
  have hηsmall : eta c ≤ 1 / 1280 := by unfold eta Config.errorBudget; linarith [hδ.2]
  have hα := alpha_pos c hδ.1 a
  have hα1 : a.val.alpha c ≤ 1 :=
    (alpha_le_errorBudget c hδ.1.le a).trans (by unfold Config.errorBudget; linarith [hδ.2])
  have hρalloc : a.val.alpha c / 128 ≤ eta c * ((a.val.call c).work : ℝ) / c.workCap := by
    have ha := Reservation.callConfidence_le_work_fraction
      (show 0 ≤ c.errorBudget by unfold Config.errorBudget; linarith [hδ.1])
      c.workCap c.attempt a.val.baseCall
    change a.val.alpha c ≤ c.errorBudget * ((a.val.call c).work : ℝ) / c.workCap at ha
    have hb := div_le_div_of_nonneg_right ha (by norm_num : (0 : ℝ) ≤ 128)
    calc
      a.val.alpha c / 128 ≤ (c.errorBudget * ((a.val.call c).work : ℝ) / c.workCap) / 128 := hb
      _ = eta c * ((a.val.call c).work : ℝ) / c.workCap := by unfold eta; ring
  by_cases he : eligible I B a.val
  · have heq : {ω | comparison c I B a ω = true} =
        {ω | BatchCollapse.collapse a.val.active B
          (scheduleEstimate a.val.active (activeBoundary c a.val) (activeSamples a.val.tolerance (a.val.alpha c)) ω)
          (I.mean I.best + a.val.tolerance / 16) a.val.tolerance} := by ext ω; simp [comparison, he]
    rw [heq, schedule_collapse_probability I a.val.active B _ (activeSamples_pos (tolerance_pos a.val) hα hα1)]
    have hb := BatchCollapse.collapse_probability_le_source_exponent I a.val.active B hbest he.2.1 he.1 hh
      (activeSamples_pos (tolerance_pos a.val) hα hα1) (tolerance_pos a.val)
      (show 0 < a.val.alpha c / 128 by positivity) (show a.val.alpha c / 128 ≤ 1 / 2 by linarith)
      le_rfl he.2.2 (by simpa only [one_div, inv_div, one_mul, activeSamples] using
        (Nat.le_ceil (512 * (a.val.tolerance ^ 2)⁻¹ * Real.log (128 / a.val.alpha c))))
    apply hb.trans
    unfold BatchCollapse.workRatio
    rw [← call_work_eq c a.val]
    exact batch_reserved_charge_bound hη hηsmall hh hhM hw hwM (by positivity) hρalloc
  · have heq : {ω | comparison c I B a ω = true} = ∅ := by ext ω; simp [comparison, he]
    rw [heq, measureReal_empty]
    positivity


theorem comparison_event_factor (c : Config) (I : Instance n) (B : Finset (Fin n))
    (a : Accepted c n) (E : Set (SeedPrefix n (activeBoundary c a.val)))
    (hE : MeasurableSet E) (x : Bool) :
    (sampleLawOfMeans I.mean).real {ω | seedPrefix (activeBoundary c a.val) ω ∈ E ∧
      comparison c I B a ω = x} =
      (sampleLawOfMeans I.mean).real ((seedPrefix (activeBoundary c a.val)) ⁻¹' E) *
        (sampleLawOfMeans I.mean).real {ω | comparison c I B a ω = x} := by
  let f : (Fin n → ℝ) → Bool := fun v => decide (eligible I B a.val ∧
    BatchCollapse.collapse a.val.active B v (I.mean I.best + a.val.tolerance / 16) a.val.tolerance)
  have hf : Measurable f := by
    apply measurable_to_bool
    change MeasurableSet {v | decide (_ ∧ _) = true}
    simp only [decide_eq_true_eq]
    exact (MeasurableSet.const _).inter
      (PredictableBatchCollapse.Parameters.measurableSet_collapse B measurable_const
        (fun i => measurable_pi_apply i) measurable_const measurable_const)
  have hi := (indepFun_prefix_scheduleEstimate a.val.active
    (Finset.card_pos.mp (by have := a.property.1; omega)) (activeBoundary c a.val)
    (activeSamples a.val.tolerance (a.val.alpha c)) I.mean).comp measurable_id hf
  have hfactor := hi.measure_inter_preimage_eq_mul E {x} hE (measurableSet_singleton x)
  exact (congrArg ENNReal.toReal hfactor).trans ENNReal.toReal_mul

def selectedComparison (c : Config) (I : Instance n) (B : Finset (Fin n)) (r : ℕ)
    (ω : SampleSpace n) : Bool :=
  match choice c r ω with
  | none => false
  | some a => comparison c I B a ω

/-- Any eligible actual collapse with an upper-valid reference triggers the fixed comparison. -/
theorem selectedComparison_true_of_collapse (c : Config) (I : Instance n) (B : Finset (Fin n))
    (r : ℕ) (ω : SampleSpace n) (a : Accepted c n) (ha : choice c r ω = some a)
    (he : eligible I B a.val) {z : ℝ} (hz : z ≤ I.mean I.best + a.val.tolerance / 16)
    (hc : BatchCollapse.collapse a.val.active B
      (scheduleEstimate a.val.active (activeBoundary c a.val)
        (activeSamples a.val.tolerance (a.val.alpha c)) ω) z a.val.tolerance) :
    selectedComparison c I B r ω = true := by
  simp only [selectedComparison, ha, comparison, decide_eq_true_eq]
  exact ⟨he, collapse_reference_mono _ _ _ hz hc⟩

theorem measurable_selectedComparison (c : Config) (I : Instance n) (B : Finset (Fin n)) (r : ℕ) :
    Measurable (selectedComparison c I B r) := by
  have hf : Measurable (fun p : Option (Accepted c n) × SampleSpace n =>
      (match p.1 with | none => false | some a => comparison c I B a p.2 : Bool)) := by
    apply measurable_from_prod_countable_right
    intro k
    cases k with
    | none => exact measurable_const
    | some a => exact measurable_comparison c I B a
  exact hf.comp (((choice_adapted c r).mono ((callFiltration c).le r) le_rfl).prodMk measurable_id)

def comparisonLaw (c : Config) (I : Instance n) (B : Finset (Fin n)) :
    Option (Accepted c n) → Measure Bool
  | none => Measure.dirac false
  | some a => (sampleLawOfMeans I.mean).map (comparison c I B a)

instance comparisonLaw_isProbabilityMeasure (c : Config) (I : Instance n) (B : Finset (Fin n))
    (k : Option (Accepted c n)) : IsProbabilityMeasure (comparisonLaw c I B k) := by
  cases k with
  | none => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac false))
  | some a => exact Measure.isProbabilityMeasure_map (measurable_comparison c I B a).aemeasurable

/-- Actual conditional law at the selected random call size and boundary, without a reservoir
extension. The comparison uses a deterministic upper-valid reference. -/
theorem conditional_comparison_law (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (r : ℕ) (x : Bool) :
    (sampleLawOfMeans I.mean)[fun ω => if selectedComparison c I B r ω = x then (1 : ℝ) else 0 |
      callPast c r] =ᵐ[sampleLawOfMeans I.mean]
      fun ω => (comparisonLaw c I B (choice c r ω)).real {x} := by
  apply conditionalLaw_of_countable_partition (sampleLawOfMeans I.mean) ((callFiltration c).le r)
    (choice c r) (choice_adapted c r) (selectedComparison c I B r)
    (measurable_selectedComparison c I B r) (comparisonLaw c I B)
  intro R hR k y
  cases k with
  | none =>
    by_cases hy : false = y
    · have heq : {ω | ω ∈ R ∧ choice c r ω = none} ∩
          {ω | selectedComparison c I B r ω = y} = {ω | ω ∈ R ∧ choice c r ω = none} := by
        ext ω
        constructor
        · exact And.left
        · intro hω
          exact ⟨hω, by simpa only [Set.mem_ofPred_eq, selectedComparison, hω.2] using hy⟩
      rw [heq]
      simp [comparisonLaw, ← hy, Measure.real_def, Measure.dirac_apply']
    · have heq : {ω | ω ∈ R ∧ choice c r ω = none} ∩
          {ω | selectedComparison c I B r ω = y} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨hω, hflag⟩
        exact hy (by simpa only [Set.mem_ofPred_eq, selectedComparison, hω.2] using hflag)
      rw [heq]
      simp [comparisonLaw, hy, Measure.real_def, Measure.dirac_apply']
  | some a =>
    obtain ⟨E, hE, hER⟩ := schedule_past c hδ r R hR a
    dsimp only [gaussianSchedule] at E hE hER
    have heq : {ω | ω ∈ R ∧ choice c r ω = some a} ∩
        {ω | selectedComparison c I B r ω = y} =
        {ω | seedPrefix (activeBoundary c a.val) ω ∈ E ∧ comparison c I B a ω = y} := by
      ext ω
      constructor
      · rintro ⟨hω, hf⟩
        refine ⟨?_, ?_⟩
        · change ω ∈ (seedPrefix (activeBoundary c a.val)) ⁻¹' E
          rw [← hER]
          exact hω
        · simpa only [Set.mem_ofPred_eq, selectedComparison, hω.2] using hf
      · rintro ⟨hω, hf⟩
        have hpω : ω ∈ {ω | ω ∈ R ∧ choice c r ω = some a} := by rw [hER]; exact hω
        exact ⟨hpω, by simpa only [Set.mem_ofPred_eq, selectedComparison, hpω.2] using hf⟩
    rw [heq, comparison_event_factor c I B a E hE y, hER]
    congr 1
    simp only [comparisonLaw, Measure.real_def,
      Measure.map_apply (measurable_comparison c I B a) (measurableSet_singleton y)]
    rfl


theorem workCharge_eq_choice (c : Config) (r : ℕ) (ω : SampleSpace n) :
    workCharge c (stage c ω.2 r) =
      match choice c r ω with | none => 0 | some a => (a.val.call c).work := by
  unfold choice choiceFromStage
  cases hs : stage c ω.2 r with
  | inl result => rfl
  | inr st =>
    rcases st with ⟨a, z⟩
    simp only [workCharge]
    split_ifs <;> rfl

theorem workCharge_le_workCap (c : Config) (st : Stage n) : workCharge c st ≤ c.workCap := by
  cases st with
  | inl result => exact Nat.zero_le _
  | inr st =>
    rcases st with ⟨a, z⟩
    by_cases ha : a.Allowed c
    · simp only [workCharge, if_pos ha]
      have := ha.2.1
      omega
    · simp only [workCharge, if_neg ha]
      exact Nat.zero_le _

theorem comparisonLaw_real_true_le_charge (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (hbest : I.best ∈ B)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ c.workCap)
    (r : ℕ) (ω : SampleSpace n) :
    (comparisonLaw c I B (choice c r ω)).real {true} ≤
      (3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ)) *
        ((workCharge c (stage c ω.2 r) : ℝ) / c.workCap) := by
  rw [workCharge_eq_choice]
  cases hk : choice c r ω with
  | none => simp [comparisonLaw, Measure.real_def, Measure.dirac_apply']
  | some a =>
    rw [comparisonLaw, map_measureReal_apply (measurable_comparison c I B a)
      (measurableSet_singleton true)]
    exact comparison_probability_le c hδ I B hbest hh hhM a

theorem condExp_comparison_le_charge (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (hbest : I.best ∈ B)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ c.workCap)
    (r : ℕ) :
    (sampleLawOfMeans I.mean)[fun ω => if selectedComparison c I B r ω = true then (1 : ℝ) else 0 |
      callPast c r] ≤ᵐ[sampleLawOfMeans I.mean]
      fun ω => (3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ)) *
        ((workCharge c (stage c ω.2 r) : ℝ) / c.workCap) := by
  filter_upwards [conditional_comparison_law c hδ I B r true] with ω hω
  rw [hω]
  exact comparisonLaw_real_true_le_charge c hδ I B hbest hh hhM r ω

theorem integrable_workCharge (c : Config) (I : Instance n) (r : ℕ) :
    Integrable (fun ω : SampleSpace n => (workCharge c (stage c ω.2 r) : ℝ)) (sampleLawOfMeans I.mean) := by
  have hmeas : Measurable (fun ω : SampleSpace n => (workCharge c (stage c ω.2 r) : ℝ)) := by
    exact (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      ((measurable_workCharge c).comp ((measurable_stage c r).comp measurable_snd))
  apply (integrable_const (c.workCap : ℝ)).mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast workCharge_le_workCap c (stage c ω.2 r)

theorem probability_comparison_le_expected_charge (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (hbest : I.best ∈ B)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ c.workCap)
    (r : ℕ) :
    (sampleLawOfMeans I.mean).real {ω | selectedComparison c I B r ω = true} ≤
      (3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ)) *
        ((∫ ω, (workCharge c (stage c ω.2 r) : ℝ) ∂sampleLawOfMeans I.mean) / c.workCap) := by
  have hint := integral_mono_ae (integrable_condExp (μ := sampleLawOfMeans I.mean))
    (((integrable_workCharge c I r).div_const (c.workCap : ℝ)).const_mul
      (3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ)))
    (condExp_comparison_le_charge c hδ I B hbest hh hhM r)
  have hm : callPast c (n := n) r ≤ Prod.instMeasurableSpace := (callFiltration c).le r
  rw [integral_condExp hm, integral_const_mul, integral_div] at hint
  have hE : MeasurableSet {ω | selectedComparison c I B r ω = true} :=
    (measurable_selectedComparison c I B r) (measurableSet_singleton true)
  have heq : (∫ ω, (if selectedComparison c I B r ω = true then (1 : ℝ) else 0)
      ∂sampleLawOfMeans I.mean) =
      (sampleLawOfMeans I.mean).real {ω | selectedComparison c I B r ω = true} := by
    simpa only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := sampleLawOfMeans I.mean) (1 : ℝ) hE)
  rwa [heq] at hint

/-- Actual finite-horizon E.12, charged to the implemented reservation counter. -/
theorem probability_any_comparison_prefix_le (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (hbest : I.best ∈ B)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ c.workCap)
    (T : ℕ) :
    (sampleLawOfMeans I.mean).real (⋃ r ∈ Finset.range T, {ω | selectedComparison c I B r ω = true}) ≤
      3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ) := by
  let K := 3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ)
  have hM : (0 : ℝ) < c.workCap := by unfold Config.workCap; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsum : (∫ ω, ∑ r ∈ Finset.range T, (workCharge c (stage c ω.2 r) : ℝ)
      ∂sampleLawOfMeans I.mean) ≤ c.workCap := by
    have h := integral_mono (integrable_finsetSum (Finset.range T)
      (fun r _ => integrable_workCharge c I r)) (integrable_const (c.workCap : ℝ))
      (fun ω : SampleSpace n => (show (∑ r ∈ Finset.range T,
        (workCharge c (stage c ω.2 r) : ℝ)) ≤ c.workCap by
          exact_mod_cast stage_work_sum_le c ω.2 T))
    simpa using h
  calc
    _ ≤ ∑ r ∈ Finset.range T, (sampleLawOfMeans I.mean).real
        {ω | selectedComparison c I B r ω = true} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.range T, K *
        ((∫ ω, (workCharge c (stage c ω.2 r) : ℝ) ∂sampleLawOfMeans I.mean) / c.workCap) :=
      Finset.sum_le_sum fun r _ => probability_comparison_le_expected_charge c hδ I B hbest hh hhM r
    _ = K * ((∫ ω, ∑ r ∈ Finset.range T, (workCharge c (stage c ω.2 r) : ℝ)
        ∂sampleLawOfMeans I.mean) / c.workCap) := by
      rw [← Finset.mul_sum, ← Finset.sum_div,
        integral_finsetSum (Finset.range T) (fun r _ => integrable_workCharge c I r)]
    _ ≤ K := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ((div_le_one hM).mpr hsum) hK

/-- E.12 for the actual universal attempt, including its selected random sample sizes and
all chronological calls. There is no conditional-law or independence premise. -/
theorem probability_any_comparison_le (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (hbest : I.best ∈ B)
    (hh : 0 < BatchCollapse.outsideHardness I B) (hhM : BatchCollapse.outsideHardness I B ≤ c.workCap) :
    sampleLawOfMeans I.mean (⋃ r, {ω | selectedComparison c I B r ω = true}) ≤
      ENNReal.ofReal (3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ)) := by
  have hK : 0 ≤ 3 * eta c ^ (4 : ℕ) * (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ) := by positivity
  rw [measure_iUnion_eq_iSup_accumulate]
  apply iSup_le
  intro T
  have heq : Set.accumulate (fun r => {ω | selectedComparison c I B r ω = true}) T =
      ⋃ r ∈ Finset.range (T + 1), {ω | selectedComparison c I B r ω = true} := by
    ext ω
    simp only [Set.accumulate_def, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
  rw [heq]
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hK).mpr
  exact probability_any_comparison_prefix_le c hδ I B hbest hh hhM (T + 1)

end GapEntropy.UniversalBatchCollapse
