import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# Binary testing inequalities

`binaryKL` is the finite real formula for Bernoulli relative entropy. Results
interpreting it as KL require the target probability to lie strictly between
zero and one; real logarithms alone cannot represent infinite boundary KL.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GapEntropy

/-- The finite Bernoulli KL formula, written using mathlib's binary entropy.
It agrees with measure KL for `0 ≤ p ≤ 1` and `0 < q < 1`. -/
def binaryKL (p q : ℝ) : ℝ :=
  -Real.binEntropy p - p * Real.log q - (1 - p) * Real.log (1 - q)

@[simp] theorem binaryKL_self (p : ℝ) : binaryKL p p = 0 := by
  simp [binaryKL, Real.binEntropy, Real.log_inv]

theorem binaryKL_eq_log_ratio (p q : ℝ) (hq : q ≠ 0) (hq1 : 1 - q ≠ 0) :
    binaryKL p q = p * Real.log (p / q) +
      (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  have hm (x y : ℝ) (hy : y ≠ 0) :
      x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
    by_cases hx : x = 0
    · simp [hx]
    rw [Real.log_div hx hy]
    ring
  rw [hm p q hq, hm (1 - p) (1 - q) hq1]
  simp only [binaryKL, Real.binEntropy, Real.log_inv]
  ring

@[fun_prop] theorem continuous_binaryKL_left (q : ℝ) : Continuous (fun p ↦ binaryKL p q) := by
  unfold binaryKL
  fun_prop

/-- First derivative in the target probability. The source parameter may be a boundary point. -/
theorem hasDerivAt_binaryKL_right (p q : ℝ) (hq : q ≠ 0) (hq1 : 1 - q ≠ 0) :
    HasDerivAt (binaryKL p) ((q - p) / (q * (1 - q))) q := by
  have hi := hasDerivAt_id q
  have h := ((hasDerivAt_const q (-Real.binEntropy p)).sub ((hi.log hq).const_mul p)).sub
    ((((hasDerivAt_const q 1).sub hi).log hq1).const_mul (1 - p))
  convert! h using 1
  norm_num [binaryKL]
  field_simp [hq, hq1]
  ring

private theorem reciprocal_bernoulli_variance_ge_four (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    0 ≤ 1 / (q * (1 - q)) - 4 := by
  have hd : 0 < q * (1 - q) := mul_pos hq (sub_pos.mpr hq1)
  have hv : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have h : 4 ≤ 1 / (q * (1 - q)) := (le_div_iff₀ hd).mpr (by nlinarith)
  linarith

private theorem hasDerivAt_pinsker_remainder (p q : ℝ) (hq : q ≠ 0) (hq1 : 1 - q ≠ 0) :
    HasDerivAt (fun x ↦ binaryKL p x - 2 * (p - x) ^ 2)
      ((q - p) * (1 / (q * (1 - q)) - 4)) q := by
  have h := (hasDerivAt_binaryKL_right p q hq hq1).sub
    ((((hasDerivAt_const q p).sub (hasDerivAt_id q)).pow 2).const_mul 2)
  convert! h using 1
  norm_num [binaryKL]
  field_simp [hq, hq1]
  ring

/-- Pinsker's sharp binary quadratic bound in the open square. -/
theorem binaryKL_pinsker_open (p q : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) : 2 * (p - q) ^ 2 ≤ binaryKL p q := by
  let f := fun x ↦ binaryKL p x - 2 * (p - x) ^ 2
  let f' := fun x ↦ (x - p) * (1 / (x * (1 - x)) - 4)
  have hd (x : ℝ) (hx : 0 < x) (hx1 : x < 1) : HasDerivAt f (f' x) x :=
    hasDerivAt_pinsker_remainder p x hx.ne' (sub_pos.mpr hx1).ne'
  rcases le_total p q with hpq | hqp
  · have hinside (x : ℝ) (hx : x ∈ Icc p q) : 0 < x ∧ x < 1 :=
      ⟨hp.trans_le hx.1, hx.2.trans_lt hq1⟩
    have hm : MonotoneOn f (Icc p q) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p q)
        (fun x hx ↦ (hd x (hinside x hx).1 (hinside x hx).2).continuousAt.continuousWithinAt)
        (fun x hx ↦ (hd x (hinside x (interior_subset hx)).1
          (hinside x (interior_subset hx)).2).hasDerivWithinAt)
        (fun x hx ↦ mul_nonneg (sub_nonneg.mpr (interior_subset hx).1)
          (reciprocal_bernoulli_variance_ge_four x (hinside x (interior_subset hx)).1
            (hinside x (interior_subset hx)).2))
    have h := hm (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq) hpq
    simp only [f, sub_self, binaryKL_self] at h
    linarith
  · have hinside (x : ℝ) (hx : x ∈ Icc q p) : 0 < x ∧ x < 1 :=
      ⟨hq.trans_le hx.1, hx.2.trans_lt hp1⟩
    have hm : AntitoneOn f (Icc q p) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc q p)
        (fun x hx ↦ (hd x (hinside x hx).1 (hinside x hx).2).continuousAt.continuousWithinAt)
        (fun x hx ↦ (hd x (hinside x (interior_subset hx)).1
          (hinside x (interior_subset hx)).2).hasDerivWithinAt)
        (fun x hx ↦ mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (interior_subset hx).2)
          (reciprocal_bernoulli_variance_ge_four x (hinside x (interior_subset hx)).1
            (hinside x (interior_subset hx)).2))
    have h := hm (left_mem_Icc.mpr hqp) (right_mem_Icc.mpr hqp) hqp
    simp only [f, sub_self, binaryKL_self] at h
    linarith

/-- The source endpoints are included by continuity of `x log x`; the target is nondegenerate. -/
theorem binaryKL_pinsker (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) : 2 * (p - q) ^ 2 ≤ binaryKL p q := by
  have hc : IsClosed {x : ℝ | 2 * (x - q) ^ 2 ≤ binaryKL x q} :=
    isClosed_le (by fun_prop) (continuous_binaryKL_left q)
  have hi : Ioo (0 : ℝ) 1 ⊆ {x : ℝ | 2 * (x - q) ^ 2 ≤ binaryKL x q} :=
    fun x hx ↦ binaryKL_pinsker_open x q hx.1 hx.2 hq hq1
  have h := closure_minimal hi hc
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at h
  exact h ⟨hp, hp1⟩

/-- Binary entropy contributes at most `log 2` to event probability transfer. -/
theorem binaryKL_ge_event_log (p q : ℝ) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    p * Real.log q⁻¹ - Real.log 2 ≤ binaryKL p q := by
  have hlog : Real.log (1 - q) ≤ 0 :=
    Real.log_nonpos (sub_pos.mpr hq1).le (by linarith)
  have hterm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp1) hlog
  have hent := Real.binEntropy_le_log_two (p := p)
  simp only [binaryKL, Real.log_inv]
  linarith

/-- Manuscript B.11's exponential transfer, once the KL comparison has been established. -/
theorem binary_event_transfer (p q a b : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) (hKL : binaryKL p q ≤ (a + b) / 2) :
    Real.exp (-(a + b)) / 4 ≤ q := by
  have hlog : 0 ≤ Real.log q⁻¹ := Real.log_nonneg ((one_le_inv₀ hq).mpr hq1.le)
  have hmul := mul_le_mul_of_nonneg_right hp hlog
  have h := binaryKL_ge_event_log p q hp1 hq hq1
  have he : -(a + b) - 2 * Real.log 2 ≤ Real.log q := by
    rw [Real.log_inv] at h hmul
    linarith
  have hh := Real.exp_le_exp.mpr he
  have hfour : 2 * Real.log 2 = Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hfour, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log hq] at hh
  exact hh

/-- The confidence comparison used in manuscript (B.9), throughout the stated range. -/
theorem binaryKL_confidence_bound (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 10) :
    Real.log δ⁻¹ ≤ 2 * binaryKL (1 - δ) δ := by
  have hδ1 : δ < 1 := by linarith
  have hpos : 0 < 1 - δ := sub_pos.mpr hδ1
  have hinv : 10 < δ⁻¹ := by
    simpa only [one_div] using (lt_div_iff₀ hδ).mpr (show 10 * δ < 1 by linarith)
  have hL : 1 ≤ Real.log δ⁻¹ := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log δ⁻¹ := Real.log_le_log (Real.exp_pos _)
        (Real.exp_one_lt_three.le.trans (by linarith))
  have hic : (1 - δ)⁻¹ ≤ 10 / 9 := by
    simpa only [one_div] using
      (div_le_iff₀ hpos).mpr (show (1 : ℝ) ≤ (10 / 9) * (1 - δ) by linarith)
  have hlog : -(1 / 9) ≤ Real.log (1 - δ) := by
    linarith [Real.one_sub_inv_le_log_of_pos hpos]
  have hform : binaryKL (1 - δ) δ =
      (1 - 2 * δ) * (Real.log δ⁻¹ + Real.log (1 - δ)) := by
    simp only [binaryKL, Real.binEntropy, Real.log_inv, sub_sub_cancel]
    ring
  rw [hform]
  calc
    Real.log δ⁻¹ ≤ (8 / 5) * (Real.log δ⁻¹ - 1 / 9) := by linarith
    _ ≤ (8 / 5) * (Real.log δ⁻¹ + Real.log (1 - δ)) := by linarith
    _ ≤ 2 * ((1 - 2 * δ) * (Real.log δ⁻¹ + Real.log (1 - δ))) := by
      have h := mul_le_mul_of_nonneg_right (show (8 / 5 : ℝ) ≤ 2 * (1 - 2 * δ) by linarith)
        (show 0 ≤ Real.log δ⁻¹ + Real.log (1 - δ) by linarith)
      nlinarith

/-- On a finite discrete space, nonzero target mass at each singleton implies absolute continuity. -/
theorem absolutelyContinuous_of_singleton_ne_zero {B : Type*} [MeasurableSpace B]
    (μ ν : Measure B) (hν : ∀ b, ν {b} ≠ 0) : μ ≪ ν := by
  intro s hs
  have he : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    apply hν b
    exact le_zero_iff.mp (hs ▸ measure_mono (Set.singleton_subset_iff.mpr hb))
  simp [he]

private theorem rnDeriv_count_discrete {B : Type*} [MeasurableSpace B] [Fintype B]
    [MeasurableSingletonClass B] (μ : Measure B) :
    μ.rnDeriv .count =ᵐ[Measure.count] fun b ↦ μ {b} := by
  have he : (Measure.count : Measure B).withDensity (fun b ↦ μ {b}) = μ := by
    rw [count_withDensity, Measure.sum_smul_dirac]
  simpa only [he] using
    (Measure.rnDeriv_withDensity (Measure.count : Measure B) (measurable_of_finite (fun b ↦ μ {b})))

/-- The actual measure KL on a finite probability space is its finite mass formula
when the target has full support. -/
theorem klDiv_discrete_probability {B : Type*} [MeasurableSpace B] [Fintype B]
    [MeasurableSingletonClass B] (μ ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ b, ν {b} ≠ 0) :
    InformationTheory.klDiv μ ν =
      ENNReal.ofReal (∑ b, μ.real {b} * Real.log (μ.real {b} / ν.real {b})) := by
  have hμν := absolutelyContinuous_of_singleton_ne_zero μ ν hν
  have hμc : μ ≪ Measure.count :=
    absolutelyContinuous_of_singleton_ne_zero μ _ (fun b ↦ by simp)
  have hνc : ν ≪ Measure.count :=
    absolutelyContinuous_of_singleton_ne_zero ν _ (fun b ↦ by simp)
  have hllr : llr μ ν =ᵐ[μ] fun b ↦ Real.log (μ.real {b} / ν.real {b}) := by
    filter_upwards [hμν.ae_le (Measure.rnDeriv_eq_div hμc hνc),
      hμc.ae_le (rnDeriv_count_discrete μ), hμc.ae_le (rnDeriv_count_discrete ν)]
      with b hr hμb hνb
    rw [llr, hr, hμb, hνb, ENNReal.toReal_div]
    rfl
  rw [InformationTheory.klDiv_of_ac_of_integrable hμν Integrable.of_finite,
    integral_congr_ae hllr, integral_fintype Integrable.of_finite]
  simp only [probReal_univ, add_sub_cancel_right, smul_eq_mul]

theorem bool_probability_false (μ : Measure Bool) [IsProbabilityMeasure μ] :
    μ.real {false} = 1 - μ.real {true} := by
  have hc : ({true} : Set Bool)ᶜ = {false} := by ext b; cases b <;> simp
  rw [← hc, probReal_compl_eq_one_sub (measurableSet_singleton _)]

/-- Identification of the scalar Bernoulli formula with actual ENNReal KL. -/
theorem klDiv_bool_probability (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hq : 0 < ν.real {true}) (hq1 : ν.real {true} < 1) :
    InformationTheory.klDiv μ ν = ENNReal.ofReal (binaryKL (μ.real {true}) (ν.real {true})) := by
  have hν : ∀ b, ν {b} ≠ 0 := by
    intro b hb
    cases b
    · have h : 0 < ν.real {false} := by rw [bool_probability_false]; linarith
      simp [measureReal_def, hb] at h
    · simp [measureReal_def, hb] at hq
  rw [klDiv_discrete_probability μ ν hν]
  congr 1
  rw [Fintype.sum_bool, bool_probability_false μ, bool_probability_false ν,
    binaryKL_eq_log_ratio _ _ hq.ne' (sub_pos.mpr hq1).ne']

/-- Measurable events define measurable maps to Bool. -/
def eventBool {Ω : Type*} (E : Set Ω) (ω : Ω) : Bool := by
  classical
  exact decide (ω ∈ E)

@[simp] theorem eventBool_preimage_true {Ω : Type*} (E : Set Ω) :
    eventBool E ⁻¹' {true} = E := by
  classical
  ext ω
  simp [eventBool]

theorem measurable_eventBool {Ω : Type*} [MeasurableSpace Ω] {E : Set Ω}
    (hE : MeasurableSet E) : Measurable (eventBool E) := by
  apply measurable_to_bool
  simpa using hE

theorem eventBool_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {E : Set Ω} (hE : MeasurableSet E) :
    (μ.map (eventBool E)).real {true} = μ.real E := by
  simp [measureReal_def, Measure.map_apply (measurable_eventBool hE) (measurableSet_singleton true)]

/-- Binary data processing for a measurable event, using the actual source and target measures. -/
theorem binary_event_data_processing {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {E : Set Ω} (hE : MeasurableSet E)
    (hq : 0 < ν.real E) (hq1 : ν.real E < 1) :
    ENNReal.ofReal (binaryKL (μ.real E) (ν.real E)) ≤ InformationTheory.klDiv μ ν := by
  have hm := measurable_eventBool hE
  have : IsProbabilityMeasure (μ.map (eventBool E)) := Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsProbabilityMeasure (ν.map (eventBool E)) := Measure.isProbabilityMeasure_map hm.aemeasurable
  have h := InformationTheory.klDiv_map_le μ ν hm
  rw [klDiv_bool_probability _ _ (by simpa [eventBool_probability _ hE] using hq)
    (by simpa [eventBool_probability _ hE] using hq1), eventBool_probability μ hE,
    eventBool_probability ν hE] at h
  exact h

theorem measureReal_zero_of_ac {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) {E : Set Ω} (hν : ν.real E = 0) :
    μ.real E = 0 := by
  exact (measureReal_eq_zero_iff (measure_ne_top μ E)).mpr
    (hμν ((measureReal_eq_zero_iff (measure_ne_top ν E)).mp hν))

/-- Event form of Pinsker's inequality, including target probabilities zero and one
and including infinite source/target divergence. -/
theorem measure_event_pinsker {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {E : Set Ω} (hE : MeasurableSet E) :
    ENNReal.ofReal (2 * (μ.real E - ν.real E) ^ 2) ≤ InformationTheory.klDiv μ ν := by
  by_cases htop : InformationTheory.klDiv μ ν = ∞
  · simp [htop]
  have hac := (InformationTheory.klDiv_ne_top_iff.mp htop).1
  by_cases hq0 : ν.real E = 0
  · have hp0 := measureReal_zero_of_ac hac hq0
    simp [hq0, hp0]
  by_cases hq1 : ν.real E = 1
  · have hqc : ν.real Eᶜ = 0 := by rw [probReal_compl_eq_one_sub hE, hq1]; norm_num
    have hpc := measureReal_zero_of_ac hac hqc
    have hp1 : μ.real E = 1 := by rw [probReal_compl_eq_one_sub hE] at hpc; linarith
    simp [hq1, hp1]
  have hq : 0 < ν.real E := lt_of_le_of_ne measureReal_nonneg (Ne.symm hq0)
  have hq' : ν.real E < 1 := lt_of_le_of_ne measureReal_le_one hq1
  exact (ENNReal.ofReal_le_ofReal (binaryKL_pinsker _ _ measureReal_nonneg measureReal_le_one
    hq hq')).trans (binary_event_data_processing μ ν hE hq hq')

/-- The usual total-variation event estimate, stated from a real finite KL upper bound. -/
theorem measure_event_abs_sub_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {E : Set Ω} (hE : MeasurableSet E)
    (K : ℝ) (hK : 0 ≤ K) (hKL : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal K) :
    |μ.real E - ν.real E| ≤ Real.sqrt (K / 2) := by
  have h := (ENNReal.ofReal_le_ofReal_iff hK).mp ((measure_event_pinsker μ ν hE).trans hKL)
  have hs := Real.sq_sqrt (show 0 ≤ K / 2 by positivity)
  nlinarith [abs_nonneg (μ.real E - ν.real E), Real.sqrt_nonneg (K / 2),
    sq_abs (μ.real E - ν.real E)]

/-- Manuscript stopping-window probability transfer for actual measures.
The endpoints of the target event probability are handled using absolute continuity. -/
theorem measure_event_transfer {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {E : Set Ω} (hE : MeasurableSet E)
    (a b : ℝ) (hp : 1 / 2 ≤ μ.real E) (hab : 0 ≤ a + b)
    (hKL : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal ((a + b) / 2)) :
    Real.exp (-(a + b)) / 4 ≤ ν.real E := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hac := (InformationTheory.klDiv_ne_top_iff.mp hfin).1
  have hq : 0 < ν.real E := by
    by_contra hn
    have hq0 : ν.real E = 0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
    have hp0 := measureReal_zero_of_ac hac hq0
    linarith
  by_cases hq1 : ν.real E = 1
  · rw [hq1]
    have he : Real.exp (-(a + b)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hab)
    linarith
  have hq' : ν.real E < 1 := lt_of_le_of_ne measureReal_le_one hq1
  apply binary_event_transfer _ _ a b hp measureReal_le_one hq hq'
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (a + b) / 2)).mp
    ((binary_event_data_processing μ ν hE hq hq').trans hKL)

theorem hasDerivAt_binaryKL_left (p q : ℝ) (hp : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt (fun x ↦ binaryKL x q)
      (Real.log p - Real.log (1 - p) - Real.log q + Real.log (1 - q)) p := by
  have h := ((Real.hasDerivAt_binEntropy hp hp1).neg.sub
    ((hasDerivAt_id p).mul_const (Real.log q))).sub
    (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul_const (Real.log (1 - q)))
  convert! h using 1
  norm_num [binaryKL]

/-- For source probabilities above the target, binary KL increases with the source probability. -/
theorem binaryKL_mono_source (q r p : ℝ) (hq : 0 < q) (hqr : q ≤ r) (hrp : r ≤ p)
    (hp1 : p ≤ 1) : binaryKL r q ≤ binaryKL p q := by
  let f' := fun x ↦ Real.log x - Real.log (1 - x) - Real.log q + Real.log (1 - q)
  have hin (x : ℝ) (hx : x ∈ interior (Icc r p)) : 0 < x ∧ x < 1 ∧ q ≤ x := by
    rw [interior_Icc] at hx
    exact ⟨hq.trans_le (hqr.trans hx.1.le), hx.2.trans_le hp1, hqr.trans hx.1.le⟩
  have hd (x : ℝ) (hx : x ∈ interior (Icc r p)) :
      HasDerivWithinAt (fun y ↦ binaryKL y q) (f' x) (interior (Icc r p)) x :=
    (hasDerivAt_binaryKL_left x q (hin x hx).1.ne' (hin x hx).2.1.ne).hasDerivWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc r p)
    (continuous_binaryKL_left q).continuousOn hd (fun x hx ↦ show 0 ≤ f' x from by
      have hl := Real.log_le_log hq (hin x hx).2.2
      have hr := Real.log_le_log (sub_pos.mpr (hin x hx).2.1)
        (show 1 - x ≤ 1 - q by linarith [(hin x hx).2.2])
      dsimp [f']
      linarith)
  exact hm (left_mem_Icc.mpr hrp) (right_mem_Icc.mpr hrp) hrp

/-- For target probabilities below the source, binary KL decreases with the target probability. -/
theorem binaryKL_antitone_target (p q r : ℝ) (hq : 0 < q) (hqr : q ≤ r)
    (hr1 : r < 1) (hrp : r ≤ p) : binaryKL p r ≤ binaryKL p q := by
  let f' := fun x ↦ (x - p) / (x * (1 - x))
  have hin (x : ℝ) (hx : x ∈ Icc q r) : 0 < x ∧ x < 1 ∧ x ≤ p :=
    ⟨hq.trans_le hx.1, hx.2.trans_lt hr1, hx.2.trans hrp⟩
  have hd (x : ℝ) (hx : x ∈ Icc q r) : HasDerivAt (binaryKL p) (f' x) x :=
    hasDerivAt_binaryKL_right p x (hin x hx).1.ne' (sub_pos.mpr (hin x hx).2.1).ne'
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc q r)
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx ↦ show f' x ≤ 0 from div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hin x (interior_subset hx)).2.2)
      (mul_nonneg (hin x (interior_subset hx)).1.le
        (sub_pos.mpr (hin x (interior_subset hx)).2.1).le))
  exact hm (left_mem_Icc.mpr hqr) (right_mem_Icc.mpr hqr) hqr

/-- Uniform confidence lower bound for any binary test with source success at least
`1-δ` and target success at most `δ`. -/
theorem binaryKL_confidence_comparison (p q δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 10)
    (hp : 1 - δ ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hqδ : q ≤ δ) :
    Real.log δ⁻¹ ≤ 2 * binaryKL p q := by
  have hδ1 : δ < 1 := by linarith
  have hm := binaryKL_mono_source δ (1 - δ) p hδ (by linarith) hp hp1
  have ha := binaryKL_antitone_target p q δ hq hqδ hδ1 (by linarith)
  linarith [binaryKL_confidence_bound δ hδ hδsmall]

/-- The confidence lower bound applies to genuine measurable events, including target probability zero. -/
theorem measure_event_confidence_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Ω} (hE : MeasurableSet E) (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 10)
    (hp : 1 - δ ≤ μ.real E) (hqδ : ν.real E ≤ δ) :
    ENNReal.ofReal (Real.log δ⁻¹ / 2) ≤ InformationTheory.klDiv μ ν := by
  by_cases htop : InformationTheory.klDiv μ ν = ∞
  · simp [htop]
  have hac := (InformationTheory.klDiv_ne_top_iff.mp htop).1
  have hq : 0 < ν.real E := by
    by_contra hn
    have hq0 : ν.real E = 0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
    have hp0 := measureReal_zero_of_ac hac hq0
    linarith
  have hq1 : ν.real E < 1 := by linarith
  have hscalar := binaryKL_confidence_comparison (μ.real E) (ν.real E) δ
    hδ hδsmall hp measureReal_le_one hq hqδ
  exact (ENNReal.ofReal_le_ofReal (by linarith : Real.log δ⁻¹ / 2 ≤
    binaryKL (μ.real E) (ν.real E))).trans (binary_event_data_processing μ ν hE hq hq1)

end GapEntropy
