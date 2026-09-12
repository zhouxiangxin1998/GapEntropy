import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Finite filtered products and adaptive Bernoulli exponential moments

Flags are exposed in one global sequence. An upper bound on their actual
conditional expectations suffices for product/MGF bounds; independence of the
adaptive sequence is not assumed. This is a finite-sequence foundation and does
not assert the full per-arm ever-flag coupling of manuscript Lemma E.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace GapEntropy

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Product of factors exposed before time `T`. -/
def prefixProduct (Z : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∏ t ∈ Finset.range T, Z t ω

theorem stronglyMeasurable_prefixProduct (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t)) (T : ℕ) :
    StronglyMeasurable[ℱ T] (prefixProduct Z T) := by
  apply Finset.stronglyMeasurable_fun_prod
  intro t ht
  exact (hZ t).mono (ℱ.mono (by simpa using Finset.mem_range.mp ht))

theorem prefixProduct_nonneg (Z : ℕ → Ω → ℝ) (hZ : ∀ t ω, 0 ≤ Z t ω)
    (T : ℕ) (ω : Ω) : 0 ≤ prefixProduct Z T ω :=
  Finset.prod_nonneg (fun t _ ↦ hZ t ω)

theorem integrable_prefixProduct (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ)
    (C : ℕ → ℝ) (hZ : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t))
    (hZ0 : ∀ t ω, 0 ≤ Z t ω) (hZC : ∀ t ω, Z t ω ≤ C t) (T : ℕ) :
    Integrable (prefixProduct Z T) μ := by
  apply (integrable_const (∏ t ∈ Finset.range T, C t)).mono'
    ((stronglyMeasurable_prefixProduct ℱ Z hZ T).mono (ℱ.le T)).aestronglyMeasurable
  exact ae_of_all _ fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (prefixProduct_nonneg Z hZ0 T ω)]
    exact Finset.prod_le_prod (fun t _ ↦ hZ0 t ω) (fun t _ ↦ hZC t ω)

/-- Conditional expectation bounds at successive times multiply for nonnegative
adapted factors. All integrability obligations follow from deterministic bounds. -/
theorem integral_prefixProduct_le (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ)
    (c C : ℕ → ℝ) (hZ : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t))
    (hZ0 : ∀ t ω, 0 ≤ Z t ω) (hZC : ∀ t ω, Z t ω ≤ C t)
    (hc : ∀ t, 0 ≤ c t)
    (hcond : ∀ t, μ[Z t | ℱ t] ≤ᵐ[μ] fun _ ↦ c t) (T : ℕ) :
    (∫ ω, prefixProduct Z T ω ∂μ) ≤ ∏ t ∈ Finset.range T, c t := by
  have hint (t : ℕ) : Integrable (Z t) μ := by
    apply (integrable_const (C t)).mono' ((hZ t).mono (ℱ.le _)).aestronglyMeasurable
    exact ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 t ω)]
      exact hZC t ω
  have hpint := integrable_prefixProduct (μ := μ) ℱ Z C hZ hZ0 hZC
  induction T with
  | zero => simp [prefixProduct]
  | succ T ih =>
    have hprod : Integrable (prefixProduct Z T * Z T) μ := by
      have heq : prefixProduct Z T * Z T = prefixProduct Z (T + 1) := by
        funext ω
        exact (Finset.prod_range_succ _ _).symm
      rw [heq]
      exact hpint (T + 1)
    have hce := condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_prefixProduct ℱ Z hZ T) hprod (hint T)
    have hceint : Integrable (prefixProduct Z T * μ[Z T | ℱ T]) μ :=
      integrable_condExp.congr hce
    calc
      (∫ ω, prefixProduct Z (T + 1) ω ∂μ) =
          ∫ ω, μ[prefixProduct Z T * Z T | ℱ T] ω ∂μ := by
        rw [integral_condExp (ℱ.le T)]
        simp only [prefixProduct, Finset.prod_range_succ, Pi.mul_apply]
      _ = ∫ ω, prefixProduct Z T ω * μ[Z T | ℱ T] ω ∂μ := integral_congr_ae hce
      _ ≤ ∫ ω, prefixProduct Z T ω * c T ∂μ := by
        apply integral_mono_ae hceint ((hpint T).mul_const (c T))
        filter_upwards [hcond T] with ω hω
        exact mul_le_mul_of_nonneg_left hω (prefixProduct_nonneg Z hZ0 T ω)
      _ = (∫ ω, prefixProduct Z T ω ∂μ) * c T := integral_mul_const _ _
      _ ≤ (∏ t ∈ Finset.range T, c t) * c T := mul_le_mul_of_nonneg_right ih (hc T)
      _ = _ := (Finset.prod_range_succ _ _).symm

/-- A Bernoulli exponential factor is affine in its zero-one input. -/
theorem exp_mul_binary (w x : ℝ) (hx : x = 0 ∨ x = 1) :
    Real.exp (w * x) = 1 + (Real.exp w - 1) * x := by
  rcases hx with rfl | rfl <;> simp

/-- Product of the first binary flags has expectation at most the product of
their conditional probability bounds. -/
theorem adaptive_binary_prefix_product_le (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (r : ℕ → ℝ) (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hbin : ∀ t ω, X t ω = 0 ∨ X t ω = 1) (hr : ∀ t, r t ∈ Set.Icc 0 1)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ ↦ r t) (T : ℕ) :
    (∫ ω, prefixProduct X T ω ∂μ) ≤ ∏ t ∈ Finset.range T, r t := by
  apply integral_prefixProduct_le ℱ X r (fun _ ↦ 1) hX
    (fun t ω ↦ by rcases hbin t ω with h | h <;> simp [h])
    (fun t ω ↦ by rcases hbin t ω with h | h <;> simp [h])
    (fun t ↦ (hr t).1) hcond T

/-- Nonnegative weighted MGF domination for binary flags revealed adaptively
on one global filtration. The right side is the independent Bernoulli MGF. -/
theorem adaptive_binary_mgf_le (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (r w : ℕ → ℝ) (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hbin : ∀ t ω, X t ω = 0 ∨ X t ω = 1) (hr : ∀ t, r t ∈ Set.Icc 0 1)
    (hw : ∀ t, 0 ≤ w t)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ ↦ r t) (T : ℕ) :
    (∫ ω, Real.exp (∑ t ∈ Finset.range T, w t * X t ω) ∂μ) ≤
      ∏ t ∈ Finset.range T, (1 + r t * (Real.exp (w t) - 1)) := by
  let Z : ℕ → Ω → ℝ := fun t ω ↦ 1 + (Real.exp (w t) - 1) * X t ω
  have hexp (t : ℕ) : 0 ≤ Real.exp (w t) - 1 := sub_nonneg.mpr (Real.one_le_exp (hw t))
  have hint (t : ℕ) : Integrable (X t) μ := by
    apply (integrable_const (1 : ℝ)).mono' ((hX t).mono (ℱ.le _)).aestronglyMeasurable
    exact ae_of_all _ fun ω ↦ by rcases hbin t ω with h | h <;> simp [h]
  have hZ : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t) :=
    fun t ↦ stronglyMeasurable_const.add (stronglyMeasurable_const.mul (hX t))
  have hZ0 : ∀ t ω, 0 ≤ Z t ω := by
    intro t ω
    rw [show Z t ω = Real.exp (w t * X t ω) from (exp_mul_binary _ _ (hbin t ω)).symm]
    exact (Real.exp_pos _).le
  have hZC : ∀ t ω, Z t ω ≤ Real.exp (w t) := by
    intro t ω
    rcases hbin t ω with h | h
    · simpa [Z, h] using Real.one_le_exp (hw t)
    · simp [Z, h]
  have hc (t : ℕ) : 0 ≤ 1 + r t * (Real.exp (w t) - 1) := by
    positivity [((hr t).1), hexp t]
  have hZcond (t : ℕ) : μ[Z t | ℱ t] ≤ᵐ[μ] fun _ ↦ 1 + r t * (Real.exp (w t) - 1) := by
    have hadd := condExp_add (integrable_const (1 : ℝ))
      ((hint t).const_mul (Real.exp (w t) - 1)) (ℱ t)
    have hmul := condExp_smul (μ := μ) (Real.exp (w t) - 1) (X t) (ℱ t)
    filter_upwards [hadd, hmul, hcond t] with ω ha hm hc
    simp only [Pi.add_apply, condExp_const (ℱ.le t), Pi.smul_apply, smul_eq_mul] at ha hm
    change μ[Z t | ℱ t] ω = _ at ha
    change μ[fun x ↦ (Real.exp (w t) - 1) * X t x | ℱ t] ω =
      (Real.exp (w t) - 1) * μ[X t | ℱ t] ω at hm
    rw [ha, hm]
    nlinarith [mul_le_mul_of_nonneg_left hc (hexp t)]
  have h := integral_prefixProduct_le ℱ Z
    (fun t ↦ 1 + r t * (Real.exp (w t) - 1)) (fun t ↦ Real.exp (w t))
    hZ hZ0 hZC hc hZcond T
  have heq (ω : Ω) : Real.exp (∑ t ∈ Finset.range T, w t * X t ω) = prefixProduct Z T ω := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl (fun t _ ↦ exp_mul_binary _ _ (hbin t ω))
  simpa only [heq] using h

/-- Exponential moments of any bounded finite binary sum are integrable. -/
theorem integrable_exp_sum_binary (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (w : ℕ → ℝ) (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hbin : ∀ t ω, X t ω = 0 ∨ X t ω = 1) (hw : ∀ t, 0 ≤ w t) (T : ℕ) :
    Integrable (fun ω ↦ Real.exp (∑ t ∈ Finset.range T, w t * X t ω)) μ := by
  apply (integrable_const (Real.exp (∑ t ∈ Finset.range T, w t))).mono'
  · exact (Real.measurable_exp.comp (Finset.measurable_fun_sum _
      (fun t _ ↦ measurable_const.mul ((hX t).mono (ℱ.le _)).measurable))).aestronglyMeasurable
  · exact ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply Finset.sum_le_sum
      intro t _
      rcases hbin t ω with h | h <;> simp [h, hw t]

/-- Exponential relaxation of the independent-Bernoulli product bound. -/
theorem adaptive_binary_mgf_le_exp (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (r w : ℕ → ℝ) (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hbin : ∀ t ω, X t ω = 0 ∨ X t ω = 1) (hr : ∀ t, r t ∈ Set.Icc 0 1)
    (hw : ∀ t, 0 ≤ w t)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ ↦ r t) (T : ℕ) :
    (∫ ω, Real.exp (∑ t ∈ Finset.range T, w t * X t ω) ∂μ) ≤
      Real.exp (∑ t ∈ Finset.range T, r t * (Real.exp (w t) - 1)) := by
  apply (adaptive_binary_mgf_le ℱ X r w hX hbin hr hw hcond T).trans
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro t _
    exact add_nonneg (by norm_num) (mul_nonneg (hr t).1
      (sub_nonneg.mpr (Real.one_le_exp (hw t))))
  · intro t _
    simpa only [add_comm] using Real.add_one_le_exp (r t * (Real.exp (w t) - 1))

/-- Actual upper-tail probability for a weighted adaptive binary sequence. -/
theorem adaptive_binary_tail_real_le (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (r v : ℕ → ℝ) (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hbin : ∀ t ω, X t ω = 0 ∨ X t ω = 1) (hr : ∀ t, r t ∈ Set.Icc 0 1)
    (hv : ∀ t, 0 ≤ v t)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ ↦ r t)
    (T : ℕ) (a θ : ℝ) (hθ : 0 ≤ θ) :
    μ.real {ω | a ≤ ∑ t ∈ Finset.range T, v t * X t ω} ≤
      Real.exp (-θ * a) * ∏ t ∈ Finset.range T,
        (1 + r t * (Real.exp (θ * v t) - 1)) := by
  have hw (t : ℕ) : 0 ≤ θ * v t := mul_nonneg hθ (hv t)
  have hint : Integrable (fun ω ↦ Real.exp (θ * ∑ t ∈ Finset.range T, v t * X t ω)) μ := by
    simpa only [Finset.mul_sum, mul_assoc] using
      integrable_exp_sum_binary (μ := μ) ℱ X (fun t ↦ θ * v t) hX hbin hw T
  have htail := measure_ge_le_exp_mul_mgf a hθ hint
  apply htail.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [mgf, Finset.mul_sum, mul_assoc] using
    adaptive_binary_mgf_le (μ := μ) ℱ X r (fun t ↦ θ * v t) hX hbin hr hw hcond T

/-- ENNReal form of the actual weighted-tail probability bound. -/
theorem adaptive_binary_tail_le (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (r v : ℕ → ℝ) (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hbin : ∀ t ω, X t ω = 0 ∨ X t ω = 1) (hr : ∀ t, r t ∈ Set.Icc 0 1)
    (hv : ∀ t, 0 ≤ v t)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ ↦ r t)
    (T : ℕ) (a θ : ℝ) (hθ : 0 ≤ θ) :
    μ {ω | a ≤ ∑ t ∈ Finset.range T, v t * X t ω} ≤
      ENNReal.ofReal (Real.exp (-θ * a) * ∏ t ∈ Finset.range T,
        (1 + r t * (Real.exp (θ * v t) - 1))) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal (adaptive_binary_tail_real_le ℱ X r v hX hbin hr hv hcond T a θ hθ)

/-- An actual probability law with independent binary coordinates. -/
def independentBernoulliLaw {ι : Type*} [Fintype ι] (r : ι → unitInterval) :
    Measure (ι → ℝ) := Measure.pi (fun i ↦ bernoulliMeasure (1 : ℝ) 0 (r i))

instance independentBernoulliLaw_isProbability {ι : Type*} [Fintype ι]
    (r : ι → unitInterval) : IsProbabilityMeasure (independentBernoulliLaw r) := by
  unfold independentBernoulliLaw
  infer_instance

theorem independentBernoulliLaw_indep {ι : Type*} [Fintype ι] (r : ι → unitInterval) :
    iIndepFun (fun i (ω : ι → ℝ) ↦ ω i) (independentBernoulliLaw r) :=
  iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- The product appearing in the adaptive bound is literally the exponential
moment under the independent Bernoulli product measure. -/
theorem integral_exp_independentBernoulliLaw {ι : Type*} [Fintype ι]
    (r : ι → unitInterval) (w : ι → ℝ) :
    (∫ ω, Real.exp (∑ i, w i * ω i) ∂independentBernoulliLaw r) =
      ∏ i, (1 + (r i : ℝ) * (Real.exp (w i) - 1)) := by
  simp_rw [Real.exp_sum]
  rw [independentBernoulliLaw,
    integral_fintype_prod_eq_prod (fun i x ↦ Real.exp (w i * x))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_bernoulliMeasure]
  simp only [mul_one, mul_zero, Real.exp_zero, smul_eq_mul]
  ring

/-- Direct MGF comparison with an actual independent Bernoulli law. -/
theorem adaptive_binary_mgf_le_independent (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (r w : ℕ → ℝ) (hX : ∀ t, StronglyMeasurable[ℱ (t + 1)] (X t))
    (hbin : ∀ t ω, X t ω = 0 ∨ X t ω = 1) (hr : ∀ t, r t ∈ Set.Icc 0 1)
    (hw : ∀ t, 0 ≤ w t)
    (hcond : ∀ t, μ[X t | ℱ t] ≤ᵐ[μ] fun _ ↦ r t) (T : ℕ) :
    (∫ ω, Real.exp (∑ t ∈ Finset.range T, w t * X t ω) ∂μ) ≤
      ∫ y, Real.exp (∑ t : Fin T, w t * y t)
        ∂independentBernoulliLaw (fun t : Fin T ↦ ⟨r t, hr t⟩) := by
  rw [integral_exp_independentBernoulliLaw]
  rw [Fin.prod_univ_eq_prod_range (fun t ↦ 1 + r t * (Real.exp (w t) - 1)) T]
  exact adaptive_binary_mgf_le ℱ X r w hX hbin hr hw hcond T

end GapEntropy
