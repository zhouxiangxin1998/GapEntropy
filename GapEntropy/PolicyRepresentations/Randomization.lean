import GapEntropy.Model
import GapEntropy.PolicyRepresentations.CDFUniform
import GapEntropy.PolicyRepresentations.GaussianCDF

/-!
# Realizing measurable probability kernels from Gaussian randomness

A standard Gaussian is mapped to uniform volume by its proved continuous,
strictly increasing CDF. Mathlib's kernel representation theorem then realizes
any Markov kernel with a nonempty standard Borel target, jointly measurably in
its parameter. The parameter space need not itself be standard Borel.

In particular, any probability measure on any standard Borel seed space is the
exact image of `GapEntropy.seedLaw`. No sampler or representability hypothesis is
part of any final theorem in this file.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

namespace GapEntropy.PolicyRepresentations

/-- An actual standard-Gaussian-to-uniform transform. -/
def gaussianToUnitInterval : ℝ → unitInterval :=
  cdfToUnitInterval (gaussianReal 0 1)

theorem measurable_gaussianToUnitInterval : Measurable gaussianToUnitInterval :=
  measurable_cdfToUnitInterval (gaussianReal 0 1)

theorem measurePreserving_gaussianToUnitInterval :
    MeasurePreserving gaussianToUnitInterval (gaussianReal 0 1)
      (volume : Measure unitInterval) :=
  measurePreserving_cdfToUnitInterval (gaussianReal 0 1)
    continuous_gaussianCDF strictMono_gaussianCDF

theorem gaussianToUnitInterval_map :
    (gaussianReal 0 1).map gaussianToUnitInterval = (volume : Measure unitInterval) :=
  measurePreserving_gaussianToUnitInterval.map_eq

/-- Only the first coordinate of the existing infinite Gaussian seed is needed. -/
def seedToUnitInterval (z : GapEntropy.Seed) : unitInterval :=
  gaussianToUnitInterval (z 0)

theorem measurePreserving_seedCoordinate (t : ℕ) :
    MeasurePreserving (fun z : GapEntropy.Seed => z t) GapEntropy.seedLaw (gaussianReal 0 1) :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) t

theorem measurePreserving_seedToUnitInterval :
    MeasurePreserving seedToUnitInterval GapEntropy.seedLaw (volume : Measure unitInterval) :=
  measurePreserving_gaussianToUnitInterval.comp (measurePreserving_seedCoordinate 0)

theorem measurable_seedToUnitInterval : Measurable seedToUnitInterval :=
  measurePreserving_seedToUnitInterval.measurable

section ProbabilityMeasures
variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]

/-- Nonemptiness of the target follows from the probability-measure assumption. -/
theorem exists_measurable_uniformSampler (μ : Measure S) [IsProbabilityMeasure μ] :
    ∃ f : unitInterval → S, Measurable f ∧ (volume : Measure unitInterval).map f = μ := by
  let : Nonempty S := nonempty_of_isProbabilityMeasure μ
  exact μ.exists_measurable_map_eq

def uniformSampler (μ : Measure S) [IsProbabilityMeasure μ] : unitInterval → S :=
  Classical.choose (exists_measurable_uniformSampler μ)

theorem measurable_uniformSampler (μ : Measure S) [IsProbabilityMeasure μ] :
    Measurable (uniformSampler μ) :=
  (Classical.choose_spec (exists_measurable_uniformSampler μ)).1

theorem uniformSampler_map (μ : Measure S) [IsProbabilityMeasure μ] :
    (volume : Measure unitInterval).map (uniformSampler μ) = μ :=
  (Classical.choose_spec (exists_measurable_uniformSampler μ)).2

theorem measurePreserving_uniformSampler (μ : Measure S) [IsProbabilityMeasure μ] :
    MeasurePreserving (uniformSampler μ) (volume : Measure unitInterval) μ :=
  ⟨measurable_uniformSampler μ, uniformSampler_map μ⟩

/-- A single standard Gaussian realizes an arbitrary standard Borel probability measure. -/
def gaussianSampler (μ : Measure S) [IsProbabilityMeasure μ] : ℝ → S :=
  uniformSampler μ ∘ gaussianToUnitInterval

theorem measurePreserving_gaussianSampler (μ : Measure S) [IsProbabilityMeasure μ] :
    MeasurePreserving (gaussianSampler μ) (gaussianReal 0 1) μ :=
  (measurePreserving_uniformSampler μ).comp measurePreserving_gaussianToUnitInterval

/-- Exact realization from the `GapEntropy` model's independent Gaussian seed. -/
def seedSampler (μ : Measure S) [IsProbabilityMeasure μ] : GapEntropy.Seed → S :=
  uniformSampler μ ∘ seedToUnitInterval

theorem measurePreserving_seedSampler (μ : Measure S) [IsProbabilityMeasure μ] :
    MeasurePreserving (seedSampler μ) GapEntropy.seedLaw μ :=
  (measurePreserving_uniformSampler μ).comp measurePreserving_seedToUnitInterval

theorem measurable_seedSampler (μ : Measure S) [IsProbabilityMeasure μ] :
    Measurable (seedSampler μ) := (measurePreserving_seedSampler μ).measurable

theorem seedSampler_map (μ : Measure S) [IsProbabilityMeasure μ] :
    GapEntropy.seedLaw.map (seedSampler μ) = μ := (measurePreserving_seedSampler μ).map_eq

theorem exists_measurePreserving_seedSampler (μ : Measure S) [IsProbabilityMeasure μ] :
    ∃ f : GapEntropy.Seed → S, MeasurePreserving f GapEntropy.seedLaw μ :=
  ⟨seedSampler μ, measurePreserving_seedSampler μ⟩

end ProbabilityMeasures

section Kernels
variable {H S : Type*} [MeasurableSpace H] [MeasurableSpace S]
    [StandardBorelSpace S] [Nonempty S]

/-- Mathlib's proved jointly measurable kernel representation, selected once per kernel. -/
def kernelUniformSampler (κ : Kernel H S) [IsMarkovKernel κ] : H → unitInterval → S :=
  Classical.choose (Kernel.exists_measurable_map_eq_unitInterval κ)

theorem measurable_kernelUniformSampler (κ : Kernel H S) [IsMarkovKernel κ] :
    Measurable (Function.uncurry (kernelUniformSampler κ)) :=
  (Classical.choose_spec (Kernel.exists_measurable_map_eq_unitInterval κ)).1

theorem kernelUniformSampler_map (κ : Kernel H S) [IsMarkovKernel κ] (h : H) :
    (volume : Measure unitInterval).map (kernelUniformSampler κ h) = κ h :=
  (Classical.choose_spec (Kernel.exists_measurable_map_eq_unitInterval κ)).2 h

def kernelGaussianSampler (κ : Kernel H S) [IsMarkovKernel κ] : H → ℝ → S :=
  fun h z => kernelUniformSampler κ h (gaussianToUnitInterval z)

theorem measurable_kernelGaussianSampler (κ : Kernel H S) [IsMarkovKernel κ] :
    Measurable (Function.uncurry (kernelGaussianSampler κ)) :=
  (measurable_kernelUniformSampler κ).comp
    (measurable_fst.prodMk (measurable_gaussianToUnitInterval.comp measurable_snd))

theorem measurePreserving_kernelGaussianSampler (κ : Kernel H S) [IsMarkovKernel κ]
    (h : H) : MeasurePreserving (kernelGaussianSampler κ h) (gaussianReal 0 1) (κ h) :=
  (show MeasurePreserving (kernelUniformSampler κ h) (volume : Measure unitInterval) (κ h) from
    ⟨(measurable_kernelUniformSampler κ).of_uncurry_left, kernelUniformSampler_map κ h⟩).comp
    measurePreserving_gaussianToUnitInterval

def kernelSeedSampler (κ : Kernel H S) [IsMarkovKernel κ] : H → GapEntropy.Seed → S :=
  fun h z => kernelUniformSampler κ h (seedToUnitInterval z)

theorem measurable_kernelSeedSampler (κ : Kernel H S) [IsMarkovKernel κ] :
    Measurable (Function.uncurry (kernelSeedSampler κ)) :=
  (measurable_kernelUniformSampler κ).comp
    (measurable_fst.prodMk (measurable_seedToUnitInterval.comp measurable_snd))

theorem measurePreserving_kernelSeedSampler (κ : Kernel H S) [IsMarkovKernel κ]
    (h : H) : MeasurePreserving (kernelSeedSampler κ h) GapEntropy.seedLaw (κ h) :=
  (show MeasurePreserving (kernelUniformSampler κ h) (volume : Measure unitInterval) (κ h) from
    ⟨(measurable_kernelUniformSampler κ).of_uncurry_left, kernelUniformSampler_map κ h⟩).comp
    measurePreserving_seedToUnitInterval

theorem kernelSeedSampler_map (κ : Kernel H S) [IsMarkovKernel κ] (h : H) :
    GapEntropy.seedLaw.map (kernelSeedSampler κ h) = κ h :=
  (measurePreserving_kernelSeedSampler κ h).map_eq

/-- The requested uncurried finite-action interface, also valid for general standard Borel targets. -/
theorem exists_measurable_kernelSeedSampler (κ : Kernel H S) [IsMarkovKernel κ] :
    ∃ f : H × GapEntropy.Seed → S, Measurable f ∧
      ∀ h, GapEntropy.seedLaw.map (fun z => f (h, z)) = κ h :=
  ⟨Function.uncurry (kernelSeedSampler κ), measurable_kernelSeedSampler κ,
    kernelSeedSampler_map κ⟩

end Kernels

/-- Every nonempty finite action space is covered, for an arbitrary measurable history space. -/
theorem exists_measurable_fin_kernelSampler {H : Type*} [MeasurableSpace H]
    {m : ℕ} (hm : 0 < m) (κ : Kernel H (Fin m)) [IsMarkovKernel κ] :
    ∃ f : H × GapEntropy.Seed → Fin m, Measurable f ∧
      ∀ h, GapEntropy.seedLaw.map (fun z => f (h, z)) = κ h := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact exists_measurable_kernelSeedSampler κ

end GapEntropy.PolicyRepresentations
