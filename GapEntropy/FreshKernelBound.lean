import GapEntropy.StoppedBlocks
import Mathlib.MeasureTheory.Integral.Prod

/-! A uniform measurable fiber bound may depend on an arbitrary real-valued
past parameter. Independence is genuine independence of random variables;
no discretization of the parameter or assumed conditional tail is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace GapEntropy
variable {Ω U V : Type*} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace V]

theorem prod_event_le_of_fiber (μ : Measure U) (ν : Measure V)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set U) (hE : MeasurableSet E) (B : Set (U × V)) (hB : MeasurableSet B)
    (p : ℝ≥0∞) (hp : ∀ u ∈ E, ν {v | (u, v) ∈ B} ≤ p) :
    (μ.prod ν) {q | q.1 ∈ E ∧ q ∈ B} ≤ μ E * p := by
  rw [Measure.prod_apply (show MeasurableSet {q : U × V | q.1 ∈ E ∧ q ∈ B} from
    (hE.preimage measurable_fst).inter hB)]
  calc
    (∫⁻ u, ν ((Prod.mk u) ⁻¹' {q | q.1 ∈ E ∧ q ∈ B}) ∂μ) ≤
        ∫⁻ u, E.indicator (fun _ => p) u ∂μ := by
      apply lintegral_mono
      intro u
      by_cases hu : u ∈ E
      · simpa only [Set.preimage, Set.mem_ofPred_eq, hu, true_and, Set.indicator_of_mem hu] using hp u hu
      · simp only [Set.preimage, Set.mem_ofPred_eq, hu, false_and, Set.ofPred_false, measure_empty,
          Set.indicator_of_notMem hu, le_refl]
    _ = μ E * p := by rw [lintegral_indicator_const hE]; exact mul_comm _ _

theorem independent_kernel_event_le (μ : Measure Ω) (ν : Measure V)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → U) (Y : Ω → V) (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y μ) (hYlaw : HasLaw Y ν μ)
    (E : Set U) (hE : MeasurableSet E) (B : Set (U × V)) (hB : MeasurableSet B)
    (p : ℝ≥0∞) (hp : ∀ u ∈ E, ν {v | (u, v) ∈ B} ≤ p) :
    μ {ω | X ω ∈ E ∧ (X ω, Y ω) ∈ B} ≤ μ (X ⁻¹' E) * p := by
  let : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hj : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod ν := by
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hYlaw.map_eq]
  have hC : MeasurableSet {q : U × V | q.1 ∈ E ∧ q ∈ B} := (hE.preimage measurable_fst).inter hB
  have he : μ {ω | X ω ∈ E ∧ (X ω, Y ω) ∈ B} =
      ((μ.map X).prod ν) {q | q.1 ∈ E ∧ q ∈ B} := by
    rw [← hj, Measure.map_apply (hX.prodMk hY) hC]
    rfl
  rw [he]
  have h := prod_event_le_of_fiber (μ.map X) ν E hE B hB p hp
  rwa [Measure.map_apply hX hE] at h

theorem independent_kernel_event_real_le (μ : Measure Ω) (ν : Measure V)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → U) (Y : Ω → V) (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y μ) (hYlaw : HasLaw Y ν μ)
    (E : Set U) (hE : MeasurableSet E) (B : Set (U × V)) (hB : MeasurableSet B)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ u ∈ E, ν.real {v | (u, v) ∈ B} ≤ p) :
    μ.real {ω | X ω ∈ E ∧ (X ω, Y ω) ∈ B} ≤ μ.real (X ⁻¹' E) * p := by
  have hh := independent_kernel_event_le μ ν X Y hX hY hind hYlaw E hE B hB (ENNReal.ofReal p)
    (fun u hu => by
      rw [← ENNReal.ofReal_toReal (measure_ne_top ν {v | (u, v) ∈ B})]
      exact ENNReal.ofReal_le_ofReal (hp u hu))
  have ht := ENNReal.toReal_mono (by finiteness) hh
  simpa only [Measure.real_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0] using ht

end GapEntropy
