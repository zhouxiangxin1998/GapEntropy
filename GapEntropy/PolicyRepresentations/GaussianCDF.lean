import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Regularity of the standard Gaussian CDF

The distribution has no atoms, so its CDF is continuous. Its density is positive
everywhere, so every nonempty interval has positive measure and the CDF is
strictly increasing. These facts discharge the hypotheses of the explicit
probability-integral transform in `GapEntropy.PolicyRepresentations.CDFUniform`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace GapEntropy.PolicyRepresentations

theorem continuous_gaussianCDF : Continuous (cdf (gaussianReal 0 1)) := by
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  apply continuous_iff_continuousAt.mpr
  intro a
  have hi : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Iic (a + 1))
      (gaussianReal 0 1) := (integrable_const 1).integrableOn
  have hc := hi.continuousOn_Iic_primitive_Iic.continuousAt
    (Iic_mem_nhds (show a < a + 1 by linarith))
  simpa only [setIntegral_const, smul_eq_mul, mul_one, ← cdf_eq_real] using hc

theorem strictMono_gaussianCDF : StrictMono (cdf (gaussianReal 0 1)) := by
  intro a b hab
  have hp : 0 < (gaussianReal 0 1) (Ioc a b) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hvzero : volume (Ioc a b) = 0 :=
      gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0) hzero
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hvzero
    linarith
  rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc,
    ENNReal.ofReal_pos] at hp
  linarith

end GapEntropy.PolicyRepresentations
