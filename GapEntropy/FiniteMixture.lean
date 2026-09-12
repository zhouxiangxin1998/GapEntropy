import GapEntropy.ConditionalKL
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# KL of finite mixtures with a common latent prior

Retaining the latent index gives the average component divergence; discarding
it can only decrease KL. Finite weighted mixtures below are actual finite sums
of measures. Zero weights and infinite component KL are allowed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GapEntropy

section Kernels

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]
  {μ : Measure α} {κ η : Kernel α β}
  [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]

/-- Hiding the common latent index can only decrease conditional KL. -/
theorem klDiv_mixture_le_lintegral_of_ae_ac (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    InformationTheory.klDiv (κ ∘ₘ μ) (η ∘ₘ μ) ≤
      ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
  calc
    InformationTheory.klDiv (κ ∘ₘ μ) (η ∘ₘ μ) ≤
        InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) := by
      rw [← Measure.snd_compProd, ← Measure.snd_compProd]
      exact InformationTheory.klDiv_map_le _ _ measurable_snd
    _ = _ := klDiv_compProd_right_eq_lintegral hκη

/-- The mixture bound needs no absolute-continuity assumption when pointwise KL
is a.e. measurable. In the finite-prior application this measurability is automatic. -/
theorem klDiv_mixture_le_lintegral
    (hm : AEMeasurable (fun a ↦ InformationTheory.klDiv (κ a) (η a)) μ) :
    InformationTheory.klDiv (κ ∘ₘ μ) (η ∘ₘ μ) ≤
      ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
  by_cases htop : (∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ) = ∞
  · simp [htop]
  apply klDiv_mixture_le_lintegral_of_ae_ac
  filter_upwards [ae_lt_top' hm htop] with a ha
  exact (InformationTheory.klDiv_ne_top_iff.mp ha.ne).1

end Kernels

section FamilyKernel

variable {ι Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
  [Countable ι] [MeasurableSingletonClass ι]

/-- Any countable discrete family of measures is a kernel. -/
def familyKernel (F : ι → Measure Ω) : Kernel ι Ω := Kernel.ofFunOfCountable F

@[simp] theorem familyKernel_apply (F : ι → Measure Ω) (i : ι) :
    familyKernel F i = F i := rfl

instance familyKernel_isMarkov (F : ι → Measure Ω) [∀ i, IsProbabilityMeasure (F i)] :
    IsMarkovKernel (familyKernel F) where
  isProbabilityMeasure i := by simpa using (inferInstance : IsProbabilityMeasure (F i))

/-- Kernel composition with a finite prior is the actual weighted sum of measures. -/
theorem familyKernel_comp_eq_sum [Fintype ι] (π : Measure ι) (F : ι → Measure Ω) :
    familyKernel F ∘ₘ π = ∑ i, π {i} • F i := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp [lintegral_fintype, Measure.finsetSum_apply, mul_comm]

end FamilyKernel

section Finite

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

/-- Finite mixture as a finite sum of actual measures. -/
def finiteMixture (w : ι → ℝ≥0∞) (F : ι → Measure Ω) : Measure Ω :=
  ∑ i, w i • F i

/-- The normalized weighted mixture is a probability measure. -/
theorem isProbabilityMeasure_finiteMixture (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (F : ι → Measure Ω) [∀ i, IsProbabilityMeasure (F i)] :
    IsProbabilityMeasure (finiteMixture w F) := by
  constructor
  simp [finiteMixture, Measure.finsetSum_apply, hw]

/-- Joint convexity of KL for finite probability mixtures with a common prior.
Components need not be absolutely continuous, and zero weights are allowed. -/
theorem klDiv_finiteMixture_le (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (F G : ι → Measure Ω) [∀ i, IsProbabilityMeasure (F i)]
    [∀ i, IsProbabilityMeasure (G i)] :
    InformationTheory.klDiv (finiteMixture w F) (finiteMixture w G) ≤
      ∑ i, w i * InformationTheory.klDiv (F i) (G i) := by
  let : MeasurableSpace ι := ⊤
  let π : Measure ι := (PMF.ofFintype w hw).toMeasure
  have hπ (i : ι) : π {i} = w i :=
    (PMF.ofFintype w hw).toMeasure_apply_singleton i (measurableSet_singleton i)
  have hF : familyKernel F ∘ₘ π = finiteMixture w F := by
    simp [familyKernel_comp_eq_sum, hπ, finiteMixture]
  have hG : familyKernel G ∘ₘ π = finiteMixture w G := by
    simp [familyKernel_comp_eq_sum, hπ, finiteMixture]
  have h := klDiv_mixture_le_lintegral (μ := π) (κ := familyKernel F)
    (η := familyKernel G) (measurable_of_countable _).aemeasurable
  simpa [hF, hG, lintegral_fintype, hπ, mul_comm] using h

/-- Uniform weights on a nonempty finite type sum to one. -/
theorem uniform_weights_sum [Nonempty ι] :
    (∑ _i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹) = 1 := by
  simp [ENNReal.mul_inv_cancel, Fintype.card_ne_zero]

/-- The uniform mixture over a finite latent parameter. -/
def uniformMixture (F : ι → Measure Ω) : Measure Ω :=
  finiteMixture (fun _ ↦ (Fintype.card ι : ℝ≥0∞)⁻¹) F

instance uniformMixture_isProbability [Nonempty ι] (F : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (F i)] : IsProbabilityMeasure (uniformMixture F) :=
  isProbabilityMeasure_finiteMixture _ uniform_weights_sum F

/-- KL after hiding a uniformly sampled finite index is at most its average
component KL, as an inequality of ENNReal divergences. -/
theorem klDiv_uniformMixture_le [Nonempty ι] (F G : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (F i)] [∀ i, IsProbabilityMeasure (G i)] :
    InformationTheory.klDiv (uniformMixture F) (uniformMixture G) ≤
      (∑ i, InformationTheory.klDiv (F i) (G i)) / Fintype.card ι := by
  calc
    InformationTheory.klDiv (uniformMixture F) (uniformMixture G) ≤
        ∑ i, (Fintype.card ι : ℝ≥0∞)⁻¹ * InformationTheory.klDiv (F i) (G i) :=
      klDiv_finiteMixture_le _ uniform_weights_sum F G
    _ = _ := by rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

end Finite

end GapEntropy
