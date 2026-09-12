import Mathlib.Probability.Kernel.Representation
import Mathlib.Topology.Order.IntermediateValue

/-!
# A continuous strictly increasing CDF produces a uniform random variable

This is an explicit probability-integral transform, not a sampler assumption.
The Gaussian hypotheses needed by the application are discharged separately.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology ENNReal

namespace GapEntropy.PolicyRepresentations

/-- The CDF, viewed as a function into the closed unit interval. -/
def cdfToUnitInterval (μ : Measure ℝ) (x : ℝ) : unitInterval :=
  ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩

theorem measurable_cdfToUnitInterval (μ : Measure ℝ) : Measurable (cdfToUnitInterval μ) :=
  (monotone_cdf μ).measurable.subtype_mk

/-- The source measure is mapped exactly to uniform volume, including both endpoints. -/
theorem cdfToUnitInterval_map (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (cdf μ)) (hstrict : StrictMono (cdf μ)) :
    μ.map (cdfToUnitInterval μ) = (volume : Measure unitInterval) := by
  have hm := measurable_cdfToUnitInterval μ
  let : IsProbabilityMeasure (μ.map (cdfToUnitInterval μ)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  have hpos (x : ℝ) : 0 < cdf μ x :=
    lt_of_le_of_lt (cdf_nonneg μ (x - 1)) (hstrict (by linarith))
  apply Measure.ext_of_Iic
  intro y
  by_cases hy0 : (y : ℝ) = 0
  · have he : y = (0 : unitInterval) := Subtype.ext hy0
    subst y
    have hpre : cdfToUnitInterval μ ⁻¹' Iic (0 : unitInterval) = ∅ := by
      ext x
      change (cdf μ x ≤ 0) ↔ False
      exact iff_false_intro (not_le_of_gt (hpos x))
    rw [Measure.map_apply hm measurableSet_Iic, hpre, measure_empty]
    simp
  by_cases hy1 : (y : ℝ) = 1
  · have he : y = (1 : unitInterval) := Subtype.ext hy1
    subst y
    have hI : Iic (1 : unitInterval) = univ := by
      ext u
      change ((u : ℝ) ≤ 1) ↔ True
      exact iff_true_intro u.2.2
    rw [hI]
    simp
  have hy : (y : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne y.2.1 (Ne.symm hy0), lt_of_le_of_ne y.2.2 hy1⟩
  have hsurj := isPreconnected_univ.intermediate_value_Ioo
    (l₁ := (atBot : Filter ℝ)) (l₂ := (atTop : Filter ℝ))
    (by simp) (by simp) hcont.continuousOn
    (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ) hy
  obtain ⟨x, _, hx⟩ := hsurj
  have hpre : cdfToUnitInterval μ ⁻¹' Iic y = Iic x := by
    ext z
    change cdf μ z ≤ (y : ℝ) ↔ z ≤ x
    rw [← hx]
    exact hstrict.le_iff_le
  rw [Measure.map_apply hm measurableSet_Iic, hpre, ← ofReal_cdf μ x, hx,
    unitInterval.volume_Iic]

theorem measurePreserving_cdfToUnitInterval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (cdf μ)) (hstrict : StrictMono (cdf μ)) :
    MeasurePreserving (cdfToUnitInterval μ) μ (volume : Measure unitInterval) :=
  ⟨measurable_cdfToUnitInterval μ, cdfToUnitInterval_map μ hcont hstrict⟩

end GapEntropy.PolicyRepresentations
