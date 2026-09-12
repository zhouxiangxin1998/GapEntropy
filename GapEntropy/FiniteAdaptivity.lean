import GapEntropy.PACRound
import Mathlib.Probability.Independence.Basic

/-!
# Uniform error bounds after a finite adaptive choice

The theorem `measure_adaptive_event_le` states that if a fresh experiment `X` is independent of a
finite-valued measurable choice `Z`, and every fixed bad set has probability at most `δ`, then
the event that `X` lands in the bad set selected by `Z` also has probability at most `δ`. The
proof expands the probability over the disjoint choice events and factors each term by
independence; no conditional tail bound is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators

namespace GapEntropy.FiniteAdaptivity

/-- A fresh independent experiment obeys its uniform error bound after a finite-valued
measurable choice made from the past. The proof expands the actual probability into
disjoint choice events; no conditional tail bound is assumed. -/
theorem measure_adaptive_event_le {Ω A B : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → A} {X : Ω → B}
    (hZ : Measurable Z) (hind : IndepFun Z X P) {bad : A → Set B}
    (hbad : ∀ a, MeasurableSet (bad a)) {δ : ℝ}
    (hbound : ∀ a, P.real (X ⁻¹' bad a) ≤ δ) :
    P.real {ω | X ω ∈ bad (Z ω)} ≤ δ := by
  classical
  let E : A → Set Ω := fun a => Z ⁻¹' {a}
  have hE : ∀ a, MeasurableSet (E a) := fun a => hZ (measurableSet_singleton a)
  have hdis : Pairwise (Disjoint on E) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have hcover : (⋃ a, E a) = Set.univ := by
    ext ω
    simp [E]
  have hmass : ∑ a, P.real (E a) = 1 := by
    rw [← measureReal_iUnion_fintype hdis hE, hcover, probReal_univ]
  have hsubset : {ω | X ω ∈ bad (Z ω)} ⊆ ⋃ a, E a ∩ X ⁻¹' bad a := by
    intro ω hω
    exact Set.mem_iUnion.mpr ⟨Z ω, rfl, hω⟩
  have hfactor (a : A) : P.real (E a ∩ X ⁻¹' bad a) =
      P.real (E a) * P.real (X ⁻¹' bad a) := by
    have h := hind.measure_inter_preimage_eq_mul {a} (bad a)
      (measurableSet_singleton a) (hbad a)
    simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h
  calc
    _ ≤ P.real (⋃ a, E a ∩ X ⁻¹' bad a) := measureReal_mono hsubset
    _ ≤ ∑ a, P.real (E a ∩ X ⁻¹' bad a) := measureReal_iUnion_fintype_le _
    _ = ∑ a, P.real (E a) * P.real (X ⁻¹' bad a) := Finset.sum_congr rfl (fun a _ => hfactor a)
    _ ≤ ∑ a, P.real (E a) * δ := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (hbound a) (measureReal_nonneg))
    _ = δ := by rw [← Finset.sum_mul, hmass, one_mul]

end GapEntropy.FiniteAdaptivity
