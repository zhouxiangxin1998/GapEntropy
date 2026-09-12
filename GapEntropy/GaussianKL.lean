import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

/-!
# Kullback--Leibler divergence of unit-variance Gaussian measures

This proves the single-observation identity used in manuscript Lemma A.1 and
equation (B.4), for the actual `gaussianReal` measures and mathlib's
`InformationTheory.klDiv`. Means are arbitrary real numbers, with no restriction
at the endpoint one.

The proof uses existing Gaussian densities, Radon--Nikodym ratio identities,
Gaussian first moments, and the definition of KL. The adaptive transcript chain
rule is a separate obligation, not an assumption or conclusion of this file.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GapEntropy

/-- Nondegenerate unit-variance Gaussian measures are mutually absolutely continuous. -/
theorem gaussian_unit_absolutelyContinuous (μ ν : ℝ) :
    gaussianReal μ 1 ≪ gaussianReal ν 1 :=
  (gaussianReal_absolutelyContinuous μ one_ne_zero).trans
    (gaussianReal_absolutelyContinuous' ν one_ne_zero)

/-- The log density ratio simplifies to an affine function of the observation. -/
theorem log_gaussian_unit_density_ratio (μ ν x : ℝ) :
    Real.log (gaussianPDFReal μ 1 x / gaussianPDFReal ν 1 x) =
      (μ - ν) * x + (ν ^ 2 - μ ^ 2) / 2 := by
  rw [Real.log_div (gaussianPDFReal_pos μ 1 x one_ne_zero).ne'
    (gaussianPDFReal_pos ν 1 x one_ne_zero).ne']
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one]
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by positivity
  rw [Real.log_mul hc (Real.exp_ne_zero _), Real.log_mul hc (Real.exp_ne_zero _)]
  simp only [Real.log_exp]
  ring

/-- Under the source Gaussian, the actual measure-theoretic log-likelihood ratio
agrees almost everywhere with its affine density formula. -/
theorem llr_gaussian_unit_ae (μ ν : ℝ) :
    llr (gaussianReal μ 1) (gaussianReal ν 1) =ᵐ[gaussianReal μ 1]
      fun x ↦ (μ - ν) * x + (ν ^ 2 - μ ^ 2) / 2 := by
  have hμ : gaussianReal μ 1 ≪ volume := gaussianReal_absolutelyContinuous μ one_ne_zero
  have hν : gaussianReal ν 1 ≪ volume := gaussianReal_absolutelyContinuous ν one_ne_zero
  have hratio := (gaussian_unit_absolutelyContinuous μ ν).ae_le
    (Measure.rnDeriv_eq_div hμ hν)
  have hμpdf := hμ.ae_le (rnDeriv_gaussianReal μ 1)
  have hνpdf := hμ.ae_le (rnDeriv_gaussianReal ν 1)
  filter_upwards [hratio, hμpdf, hνpdf] with x hr hμx hνx
  rw [llr, hr, hμx, hνx, ENNReal.toReal_div, toReal_gaussianPDF, toReal_gaussianPDF]
  exact log_gaussian_unit_density_ratio μ ν x

theorem integrable_id_gaussian_unit (μ : ℝ) :
    Integrable (fun x : ℝ ↦ x) (gaussianReal μ 1) := by
  exact memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := μ) (v := 1) 1)

/-- Integrability is proved separately, so KL is not silently replaced by its
`toReal` value when the actual divergence might be infinite. -/
theorem integrable_llr_gaussian_unit (μ ν : ℝ) :
    Integrable (llr (gaussianReal μ 1) (gaussianReal ν 1)) (gaussianReal μ 1) := by
  rw [integrable_congr (llr_gaussian_unit_ae μ ν)]
  exact ((integrable_id_gaussian_unit μ).const_mul (μ - ν)).add (integrable_const _)

theorem integral_llr_gaussian_unit (μ ν : ℝ) :
    (∫ x, llr (gaussianReal μ 1) (gaussianReal ν 1) x ∂gaussianReal μ 1) =
      (μ - ν) ^ 2 / 2 := by
  rw [integral_congr_ae (llr_gaussian_unit_ae μ ν),
    integral_add ((integrable_id_gaussian_unit μ).const_mul (μ - ν)) (integrable_const _),
    integral_const_mul, integral_id_gaussianReal]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Exact ENNReal-valued KL between two unit-variance Gaussian laws. -/
theorem klDiv_gaussian_unit (μ ν : ℝ) :
    InformationTheory.klDiv (gaussianReal μ 1) (gaussianReal ν 1) =
      ENNReal.ofReal ((μ - ν) ^ 2 / 2) := by
  rw [InformationTheory.klDiv_of_ac_of_integrable (gaussian_unit_absolutelyContinuous μ ν)
    (integrable_llr_gaussian_unit μ ν), integral_llr_gaussian_unit]
  simp

theorem klDiv_gaussian_unit_ne_top (μ ν : ℝ) :
    InformationTheory.klDiv (gaussianReal μ 1) (gaussianReal ν 1) ≠ ∞ := by
  rw [klDiv_gaussian_unit]
  exact ENNReal.ofReal_ne_top

theorem toReal_klDiv_gaussian_unit (μ ν : ℝ) :
    (InformationTheory.klDiv (gaussianReal μ 1) (gaussianReal ν 1)).toReal =
      (μ - ν) ^ 2 / 2 := by
  rw [klDiv_gaussian_unit, ENNReal.toReal_ofReal]
  positivity

end GapEntropy
