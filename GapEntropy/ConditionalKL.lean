import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Conditional KL as an integral of the pointwise kernel divergences

Mathlib's KL chain rule leaves the conditional term as a KL between two
composition-products with a common first marginal. This file identifies that
term with the integral of the pointwise kernel KL, using the jointly measurable
kernel Radon--Nikodym derivative.

The target measurable space is countably generated, or the source type is
countable, as expressed by `CountableOrCountablyGenerated`. Absolute continuity
of the pointwise kernels is an explicit, independently checkable premise. No KL
identity, integrability of a logarithm, or conditional expectation identity is
assumed. The nonnegative `klFun` representation handles infinite divergences.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GapEntropy

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]
  {μ : Measure α} {κ η : Kernel α β}
  [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]

/-- Kernel RN derivatives are also RN derivatives of the composition-products,
almost everywhere under the target composition-product. -/
theorem rnDeriv_compProd_right_ae (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      fun p ↦ κ.rnDeriv η p.1 p.2 := by
  have hκ : η.withDensity (κ.rnDeriv η) =ᵐ[μ] κ := by
    filter_upwards [hκη] with a ha
    exact Kernel.withDensity_rnDeriv_eq ha
  have hprod : (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) = μ ⊗ₘ κ := by
    rw [← Measure.compProd_withDensity (κ.measurable_rnDeriv η)]
    exact Measure.compProd_congr hκ
  simpa only [hprod] using
    (Measure.rnDeriv_withDensity (μ ⊗ₘ η) (κ.measurable_rnDeriv η))

/-- Pointwise KL can be written using the jointly measurable kernel RN derivative,
rather than a possibly non-jointly-measurable choice of measure RN derivatives. -/
theorem klDiv_kernel_eq_lintegral_klFun {a : α} (ha : κ a ≪ η a) :
    InformationTheory.klDiv (κ a) (η a) =
      ∫⁻ b, ENNReal.ofReal (InformationTheory.klFun (κ.rnDeriv η a b).toReal) ∂η a := by
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac ha]
  apply lintegral_congr_ae
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)] with b hb
  rw [hb]

/-- Measurability of the nonnegative kernel divergence integrand. -/
theorem measurable_kernel_klFun_integral (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦
      ∫⁻ b, ENNReal.ofReal (InformationTheory.klFun (κ.rnDeriv η a b).toReal) ∂η a) := by
  apply Measurable.lintegral_kernel_prod_right
  fun_prop

omit [IsFiniteMeasure μ] in
theorem aemeasurable_kernel_klDiv (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    AEMeasurable (fun a ↦ InformationTheory.klDiv (κ a) (η a)) μ := by
  apply (measurable_kernel_klFun_integral κ η).aemeasurable.congr
  filter_upwards [hκη] with a ha
  exact (klDiv_kernel_eq_lintegral_klFun ha).symm

theorem measurable_kernel_klDiv (hκη : ∀ a, κ a ≪ η a) :
    Measurable (fun a ↦ InformationTheory.klDiv (κ a) (η a)) := by
  have h : (fun a ↦ InformationTheory.klDiv (κ a) (η a)) =
      fun a ↦ ∫⁻ b, ENNReal.ofReal (InformationTheory.klFun (κ.rnDeriv η a b).toReal) ∂η a := by
    funext a
    exact klDiv_kernel_eq_lintegral_klFun (hκη a)
  rw [h]
  exact measurable_kernel_klFun_integral κ η

/-- Conditional KL identity with a common first marginal, in its full ENNReal form.
This remains valid when the divergence or its integral is infinite. -/
theorem klDiv_compProd_right_eq_lintegral (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) =
      ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac
    (Measure.AbsolutelyContinuous.compProd_right hκη)]
  calc
    (∫⁻ p, ENNReal.ofReal
        (InformationTheory.klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) ∂μ ⊗ₘ η) =
        ∫⁻ p, ENNReal.ofReal (InformationTheory.klFun (κ.rnDeriv η p.1 p.2).toReal) ∂μ ⊗ₘ η := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_compProd_right_ae hκη] with p hp
      rw [hp]
    _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (InformationTheory.klFun (κ.rnDeriv η a b).toReal) ∂η a ∂μ := by
      rw [Measure.lintegral_compProd]
      fun_prop
    _ = ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hκη] with a ha
      exact (klDiv_kernel_eq_lintegral_klFun ha).symm

/-- A convenient sufficient condition for the conditional identity is finite
pointwise KL, which itself entails absolute continuity. -/
theorem klDiv_compProd_right_eq_lintegral_of_ne_top
    (hfin : ∀ᵐ a ∂μ, InformationTheory.klDiv (κ a) (η a) ≠ ∞) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) =
      ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
  apply klDiv_compProd_right_eq_lintegral
  filter_upwards [hfin] with a ha
  exact (InformationTheory.klDiv_ne_top_iff.mp ha).1

/-- The integral form of the Markov-kernel KL chain rule, under pointwise absolute continuity. -/
theorem klDiv_compProd_eq_add_lintegral (ν : Measure α) [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsMarkovKernel η] (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) =
      InformationTheory.klDiv μ ν + ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
  rw [InformationTheory.klDiv_compProd_eq_add, klDiv_compProd_right_eq_lintegral hκη]

end GapEntropy
