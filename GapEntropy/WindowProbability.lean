import GapEntropy.EarlyReturn
import GapEntropy.MarkedConfidence
import GapEntropy.StoppingWindows

/-!
# Source probability of the actual designated-arm stopping window

The lower-tail bound is averaged over actual relabeled experiments. The upper
tail is controlled by Markov using the actual marked count integral. Correctness
and a union bound then leave more than half the mass in the stopping window.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy

private theorem average_const {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ≥0∞) :
    (∑ _i : ι, c) / Fintype.card ι = c := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right (by simp) (by simp)

/-- Averaging preserves the proved early-return estimate, with the lower
threshold attached to the original designated arm identity. -/
theorem marked_early_return_measure_le (A : Algorithm) {n : ℕ} (I : Instance n)
    (d : Fin n) (hd : d ≠ I.best) {δ : ℝ} (hδ : δ ≤ 1) (hA : DeltaCorrect A δ) :
    markedSampleLaw I.mean d ((A n).markedReturnedNotEvent I.two_le ∩
      {p | (A n).markedArmSamples I.two_le p < ENNReal.ofReal (I.weight d / 100)}) ≤
      ENNReal.ofReal (δ + 1 / 20) := by
  have hE : MeasurableSet ((A n).markedReturnedNotEvent I.two_le ∩
      {p | (A n).markedArmSamples I.two_le p < ENNReal.ofReal (I.weight d / 100)}) :=
    ((A n).measurableSet_markedReturnedNotEvent I.two_le).inter
      (measurableSet_lt ((A n).measurable_markedArmSamples I.two_le) measurable_const)
  rw [markedSampleLaw_apply _ _ _ hE]
  rw [← average_const (ι := Equiv.Perm (Fin n)) (ENNReal.ofReal (δ + 1 / 20))]
  apply ENNReal.div_le_div_right
  apply Finset.sum_le_sum
  intro π _
  have hp : π d ≠ (I.permute π).best := fun h => hd (π.injective h)
  have h := (A n).early_return_measure_le (I.permute π) (π d) hp hδ (hA n)
  have hg : (I.permute π).gap (π d) = I.gap d := by simp
  rw [hg] at h
  have hx : (1 / 100 : ℝ) * (I.gap d ^ 2)⁻¹ = I.weight d / 100 := by
    unfold Instance.weight
    ring
  rw [hx] at h
  exact h

/-- B.9 makes the finite original source expectation strictly positive. -/
theorem permutationArmSamples_toReal_pos (A : Algorithm) {n : ℕ} (I : Instance n)
    {δ : ℝ} (hδ : ValidConfidence δ) (hA : DeltaCorrect A δ)
    (hfin : permutationAverage A I ≠ ⊤) (d : Fin n) (hd : d ≠ I.best) :
    0 < (permutationArmSamples A I d).toReal := by
  have hδ1 : δ < 1 := by have := hδ.2; linarith
  have hlog : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ.1).mpr hδ1)
  have hcost := hlog.trans_le (log_inv_le_normalizedArmCost A I hδ hA hfin d hd)
  by_contra hp
  have hz : (permutationArmSamples A I d).toReal = 0 :=
    le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
  simp [normalizedArmCost, hz] at hcost

/-- Markov's upper tail uses the expectation of the actual marked full count. -/
theorem marked_armSamples_upper_tail_le (A : Algorithm) {n : ℕ} (I : Instance n)
    {δ : ℝ} (hδ : ValidConfidence δ) (hA : DeltaCorrect A δ)
    (hfin : permutationAverage A I ≠ ⊤) (d : Fin n) (hd : d ≠ I.best) :
    markedSampleLaw I.mean d
      {p | ENNReal.ofReal (16 * (permutationArmSamples A I d).toReal) <
        (A n).markedArmSamples I.two_le p} ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
  have hepos := permutationArmSamples_toReal_pos A I hδ hA hfin d hd
  have htpos : 0 < 16 * (permutationArmSamples A I d).toReal := by positivity
  have hmarkov := meas_ge_le_lintegral_div
    ((A n).measurable_markedArmSamples I.two_le).aemeasurable
    (ENNReal.ofReal_pos.mpr htpos).ne' ENNReal.ofReal_ne_top
      (μ := markedSampleLaw I.mean d)
  rw [lintegral_markedArmSamples_eq_permutationArmSamples] at hmarkov
  have hratio : permutationArmSamples A I d /
      ENNReal.ofReal (16 * (permutationArmSamples A I d).toReal) = ENNReal.ofReal (1 / 16 : ℝ) := by
    nth_rw 1 [← ENNReal.ofReal_toReal (permutationArmSamples_ne_top A I hfin d)]
    rw [← ENNReal.ofReal_div_of_pos htpos]
    congr 1
    field_simp [hepos.ne']
  rw [hratio] at hmarkov
  have hs : {p : MarkedSampleSpace n |
      ENNReal.ofReal (16 * (permutationArmSamples A I d).toReal) < (A n).markedArmSamples I.two_le p} ⊆
      {p | ENNReal.ofReal (16 * (permutationArmSamples A I d).toReal) ≤
        (A n).markedArmSamples I.two_le p} := by
    intro p hp
    change ENNReal.ofReal (16 * (permutationArmSamples A I d).toReal) <
      (A n).markedArmSamples I.two_le p at hp
    exact le_of_lt hp
  exact (measure_mono hs).trans hmarkov

/-- The explicit real lower bound before using the confidence range. -/
theorem marked_count_interval_real_lower_bound (A : Algorithm) {n : ℕ} (I : Instance n)
    {δ : ℝ} (hδ : ValidConfidence δ) (hA : DeltaCorrect A δ)
    (hfin : permutationAverage A I ≠ ⊤) (d : Fin n) (hd : d ≠ I.best) :
    1 - 2 * δ - 1 / 20 - 1 / 16 ≤
      (markedSampleLaw I.mean d).real {p | p ∈ (A n).markedReturnedNotEvent I.two_le ∧
        ENNReal.ofReal (I.weight d / 100) ≤ (A n).markedArmSamples I.two_le p ∧
        (A n).markedArmSamples I.two_le p ≤
          ENNReal.ofReal (16 * (permutationArmSamples A I d).toReal)} := by
  let μ := markedSampleLaw I.mean d
  let R := (A n).markedReturnedNotEvent I.two_le
  let lo := ENNReal.ofReal (I.weight d / 100)
  let hi := ENNReal.ofReal (16 * (permutationArmSamples A I d).toReal)
  let f := (A n).markedArmSamples I.two_le
  let L : Set (MarkedSampleSpace n) := R ∩ {p | f p < lo}
  let U : Set (MarkedSampleSpace n) := {p | hi < f p}
  let W : Set (MarkedSampleSpace n) := {p | p ∈ R ∧ lo ≤ f p ∧ f p ≤ hi}
  have hδ1 : δ ≤ 1 := by have := hδ.2; linarith
  have hR : 1 - δ ≤ μ.real R := by
    have h := ENNReal.toReal_mono (measure_ne_top μ R)
      (marked_source_returnedNotEvent_ge_correct A I d hd hA)
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1), measureReal_def] using h
  have hL : μ.real L ≤ δ + 1 / 20 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (marked_early_return_measure_le A I d hd hδ1 hA)
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ δ + 1 / 20 by have := hδ.1; linarith),
      measureReal_def] using h
  have hU : μ.real U ≤ 1 / 16 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (marked_armSamples_upper_tail_le A I hδ hA hfin d hd)
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16), measureReal_def] at h
    exact h
  have hcover : R ⊆ (W ∪ L) ∪ U := by
    intro p hp
    by_cases hl : lo ≤ f p
    · by_cases hh : f p ≤ hi
      · exact Or.inl (Or.inl ⟨hp, hl, hh⟩)
      · exact Or.inr (lt_of_not_ge hh)
    · exact Or.inl (Or.inr ⟨hp, lt_of_not_ge hl⟩)
  have hm : μ.real R ≤ μ.real ((W ∪ L) ∪ U) := measureReal_mono hcover
  have hu₁ : μ.real ((W ∪ L) ∪ U) ≤ μ.real (W ∪ L) + μ.real U := measureReal_union_le _ _
  have hu₂ : μ.real (W ∪ L) ≤ μ.real W + μ.real L := measureReal_union_le _ _
  change 1 - 2 * δ - 1 / 20 - 1 / 16 ≤ μ.real W
  linarith

/-- B.4: the source stopping window has strictly more than half the probability
mass under the original marked permutation experiment. -/
theorem stoppingWindow_source_prob_gt_half (A : Algorithm) {n : ℕ} (I : Instance n)
    {δ : ℝ} (hδ : ValidConfidence δ) (hA : DeltaCorrect A δ)
    (hfin : permutationAverage A I ≠ ⊤) (d : Fin n) (hd : d ≠ I.best) :
    ENNReal.ofReal (1 / 2 : ℝ) < markedSampleLaw I.mean d (stoppingWindow A I hfin d) := by
  apply (ENNReal.ofReal_lt_iff_lt_toReal (by norm_num)
    (measure_ne_top (markedSampleLaw I.mean d) _)).mpr
  have hw : 1 - 2 * δ - 1 / 20 - 1 / 16 ≤
      (markedSampleLaw I.mean d).real (stoppingWindow A I hfin d) :=
    marked_count_interval_real_lower_bound A I hδ hA hfin d hd
  change (1 / 2 : ℝ) < (markedSampleLaw I.mean d).real (stoppingWindow A I hfin d)
  have := hδ.2
  linarith

end GapEntropy
