import GapEntropy.FallbackGaussian

/-!
# The fallback's unconditional wrong-return bound

The simultaneous confidence failure has probability at most `δ/2`. This proves
an unconditional bound on incorrect finite returns of the actual policy.
Almost-sure finite return is a separate termination obligation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.Fallback

def roundBad {n : ℕ} (I : Instance n) (δ : ℝ) (r : ℕ) : Set (SampleSpace n) :=
  {ω | ∃ i, radius n δ r < |empiricalMean r i ω - I.mean i|}

def badConfidence {n : ℕ} (I : Instance n) (δ : ℝ) : Set (SampleSpace n) :=
  ⋃ r, roundBad I δ r

theorem roundBad_real_le {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (r : ℕ) :
    (sampleLaw I).real (roundBad I δ r) ≤ δ / (4 * ((r : ℝ) + 1)^2) := by
  have he : roundBad I δ r = ⋃ i : Fin n,
      {ω | radius n δ r < |empiricalMean r i ω - I.mean i|} := by
    ext ω
    simp [roundBad]
  rw [he]
  calc
    _ ≤ ∑ i : Fin n, (sampleLaw I).real
        {ω | radius n δ r < |empiricalMean r i ω - I.mean i|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, δ / (4 * (n : ℝ) * ((r : ℝ) + 1)^2) :=
      Finset.sum_le_sum (fun i _ => empiricalMean_confidence_tail I.two_le I.mean hδ hδ1 r i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by have := I.two_le; omega : n ≠ 0)
      have hr0 : (r : ℝ) + 1 ≠ 0 := by positivity
      field_simp

/-- A telescoping majorant avoids using the exact Basel sum. -/
def confidenceBudget (δ : ℝ) (r : ℕ) : ℝ :=
  (δ / 2) * (1 / ((r : ℝ) + 1) - 1 / ((r : ℝ) + 2))

theorem confidenceBudget_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (r : ℕ) :
    0 ≤ confidenceBudget δ r := by
  apply mul_nonneg (by positivity)
  apply sub_nonneg.mpr
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem confidenceBudget_ge {δ : ℝ} (hδ : 0 ≤ δ) (r : ℕ) :
    δ / (4 * ((r : ℝ) + 1)^2) ≤ confidenceBudget δ r := by
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  have hr2 : (r : ℝ) + 2 ≠ 0 := by positivity
  have he : confidenceBudget δ r = δ / (2 * ((r : ℝ) + 1) * ((r : ℝ) + 2)) := by
    unfold confidenceBudget
    field_simp
    ring
  rw [he]
  apply div_le_div_of_nonneg_left hδ (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

theorem sum_confidenceBudget (δ : ℝ) (T : ℕ) :
    ∑ r ∈ Finset.range T, confidenceBudget δ r =
      (δ / 2) * (1 - 1 / ((T : ℝ) + 1)) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [confidenceBudget, Nat.cast_add, Nat.cast_one]
      ring

theorem tsum_confidenceBudget_le {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑' r, ENNReal.ofReal (confidenceBudget δ r) ≤ ENNReal.ofReal (δ / 2) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro T
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => confidenceBudget_nonneg hδ r)]
  apply ENNReal.ofReal_le_ofReal
  rw [sum_confidenceBudget]
  nlinarith [mul_nonneg (show 0 ≤ δ / 2 by positivity)
    (show 0 ≤ 1 / ((T : ℝ) + 1) by positivity)]

theorem badConfidence_measure_le {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    sampleLaw I (badConfidence I δ) ≤ ENNReal.ofReal (δ / 2) := by
  calc
    _ ≤ ∑' r, sampleLaw I (roundBad I δ r) := measure_iUnion_le _
    _ ≤ ∑' r, ENNReal.ofReal (confidenceBudget δ r) := by
      apply ENNReal.tsum_le_tsum
      intro r
      rw [← ENNReal.ofReal_toReal (measure_ne_top (sampleLaw I) _)]
      exact ENNReal.ofReal_le_ofReal ((roundBad_real_le I hδ hδ1 r).trans (confidenceBudget_ge hδ.le r))
    _ ≤ ENNReal.ofReal (δ / 2) := tsum_confidenceBudget_le hδ.le

theorem wrong_return_subset_badConfidence {n : ℕ} (I : Instance n) (δ : ℝ) :
    (policy n δ).returnedNotEvent I.two_le I.best ⊆ badConfidence I δ := by
  rintro ω ⟨T, i, hi, hret⟩
  by_contra hbad
  have hgood : ∀ r j, |empiricalMean r j ω - I.mean j| ≤ radius n δ r := by
    intro r j
    apply le_of_not_gt
    intro hj
    exact hbad (Set.mem_iUnion.mpr ⟨r, j, hj⟩)
  exact hi (returned_eq_best_on_good_intervals I δ ω hgood T i hret)

/-- No correctness assumption about a modified policy is used: this is the
actual cumulative-doubling policy's incorrect finite-return probability. -/
theorem wrong_return_measure_le {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    sampleLaw I ((policy n δ).returnedNotEvent I.two_le I.best) ≤ ENNReal.ofReal (δ / 2) :=
  (measure_mono (wrong_return_subset_badConfidence I δ)).trans (badConfidence_measure_le I hδ hδ1)

end GapEntropy.Fallback
