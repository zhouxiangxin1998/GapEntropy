import GapEntropy.UniversalFavorableCell
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Countable actual-call partition and finite chronological first-failure
aggregation. Every bound is derived from the real Gaussian sampling law. -/
noncomputable section
open MeasureTheory
open scoped Classical ENNReal BigOperators
namespace GapEntropy.UniversalAttempt
open UniversalSevereProcess
variable {n : ℕ}

def riskRate (c : Config) : Option (Accepted c n) → ℝ≥0∞
  | none => 0
  | some a => ENNReal.ofReal (callRisk c a)

theorem measurable_riskRate (c : Config) : Measurable (riskRate (n := n) c) := measurable_of_countable _

theorem badAt_le_lintegralRisk (I : Instance n) (c : Config) (hδ : ValidConfidence c.confidence) (r : ℕ) :
    sampleLawOfMeans I.mean {ω | BadAt I c r ω} ≤
      ∫⁻ ω, riskRate c (choice c r ω) ∂sampleLawOfMeans I.mean := by
  let μ := sampleLawOfMeans I.mean
  have hchoice : Measurable (choice c (n := n) r) :=
    (choice_adapted c r).mono ((callFiltration c).le r) le_rfl
  have hsum : (∑' a : Accepted c n, μ {ω | choice c r ω = some a} * ENNReal.ofReal (callRisk c a)) ≤
      ∫⁻ ω, riskRate c (choice c r ω) ∂μ := by
    rw [← lintegral_map (measurable_riskRate c) hchoice, lintegral_countable']
    calc
      _ = ∑' a : Accepted c n, riskRate c (some a) * (μ.map (choice c r)) {some a} := by
        apply tsum_congr
        intro a
        rw [Measure.map_apply hchoice (measurableSet_singleton (some a))]
        exact mul_comm _ _
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective (Accepted c n)) _
  rw [badAt_eq_union]
  exact ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun a => badCell_le I c hδ r a))).trans hsum

theorem finite_bad_union_le_lintegralRisk (I : Instance n) (c : Config)
    (hδ : ValidConfidence c.confidence) (T : ℕ) :
    sampleLawOfMeans I.mean (⋃ r ∈ Finset.range T, {ω | BadAt I c r ω}) ≤
      ∫⁻ ω, ∑ r ∈ Finset.range T, riskRate c (choice c r ω) ∂sampleLawOfMeans I.mean := by
  have hmeas (r : ℕ) : Measurable (fun ω : SampleSpace n => riskRate c (choice c r ω)) :=
    (measurable_riskRate c).comp ((choice_adapted c r).mono ((callFiltration c).le r) le_rfl)
  calc
    _ ≤ ∑ r ∈ Finset.range T, sampleLawOfMeans I.mean {ω | BadAt I c r ω} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.range T, ∫⁻ ω, riskRate c (choice c r ω) ∂sampleLawOfMeans I.mean :=
      Finset.sum_le_sum (fun r _ => badAt_le_lintegralRisk I c hδ r)
    _ = _ := (lintegral_finsetSum _ (fun r _ => hmeas r)).symm

end GapEntropy.UniversalAttempt
