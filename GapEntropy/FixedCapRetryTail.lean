import GapEntropy.FixedCapRetryBounds

/-!
# Actual retry expectation with an eventual geometric tail

For Appendix F, early attempts need no success guarantee. After an analysis-only
index, the supplied real bounded procedures have abort probability at most 1/4.
The conclusion charges the complete actual policy on all sample paths.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.FixedCapRetry
variable {n : ℕ} (R : ℕ → BoundedProcedure n (Option (Fin n)))
  (hpos : ∀ j, 0 < (R j).budget)

local instance : MeasurableSingletonClass (Option (Fin n)) := ⟨fun _ => trivial⟩

theorem measure_reach_succ (mean : Fin n → ℝ) (j : ℕ) :
    sampleLawOfMeans mean (reach R hpos (j + 1)) =
      sampleLawOfMeans mean (reach R hpos j) *
        GaussianBlocks.blockLaw mean (R j).budget {x | (R j).evaluate x = none} := by
  rw [measure_reach_eq_prod, measure_reach_eq_prod, Finset.prod_range_succ]

/-- Earlier attempts may abort with probability one. Their reach factor can only
reduce the geometric bound after the threshold. -/
theorem measure_reach_tail_le_pow (mean : Fin n → ℝ) (j₀ : ℕ) {r : ℝ≥0∞}
    (habort : ∀ j, j₀ ≤ j → GaussianBlocks.blockLaw mean (R j).budget
      {x | (R j).evaluate x = none} ≤ r) (t : ℕ) :
    sampleLawOfMeans mean (reach R hpos (t + j₀)) ≤ r ^ t := by
  induction t with
  | zero => simpa only [zero_add, pow_zero] using
      (prob_le_one : sampleLawOfMeans mean (reach R hpos j₀) ≤ 1)
  | succ t ih =>
      rw [show t + 1 + j₀ = (t + j₀) + 1 by omega,
        measure_reach_succ, pow_succ]
      exact mul_le_mul' ih (habort (t + j₀) (by omega))

private theorem sum_two_pow_le (j₀ : ℕ) :
    (∑ j ∈ Finset.range j₀, (2 : ℝ) ^ j) ≤ 2 ^ j₀ := by
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num

private theorem tail_charge_identity (K : ℝ) (j₀ t : ℕ) :
    K * 2 ^ (t + j₀) * (1 / 4 : ℝ) ^ t = K * 2 ^ j₀ * (1 / 2 : ℝ) ^ t := by
  calc
    _ = K * 2 ^ j₀ * ((2 : ℝ) ^ t * (1 / 4 : ℝ) ^ t) := by rw [pow_add]; ring
    _ = _ := by rw [← mul_pow]; norm_num

/-- F.13–F.14 for the actual deterministic-block retry policy. `j₀` is used only
in this theorem, and need not be known to the policy. -/
theorem expectedSamples_le_dyadic_tail (I : Instance n) (j₀ : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (hcap : ∀ j, ((R j).budget : ℝ) ≤ K * 2 ^ j)
    (habort : ∀ j, j₀ ≤ j → GaussianBlocks.blockLaw I.mean (R j).budget
      {x | (R j).evaluate x = none} ≤ 1 / 4) :
    (policy R hpos).expectedSamples I ≤ ENNReal.ofReal (3 * K * 2 ^ j₀) := by
  let charge : ℕ → ℝ≥0∞ := fun j => (R j).budget * sampleLaw I (reach R hpos j)
  have hcap' (j : ℕ) : ((R j).budget : ℝ≥0∞) ≤ ENNReal.ofReal (K * 2 ^ j) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hcap j)
  have hearly : (∑ j ∈ Finset.range j₀, charge j) ≤ ENNReal.ofReal (K * 2 ^ j₀) := by
    calc
      _ ≤ ∑ j ∈ Finset.range j₀, ENNReal.ofReal (K * 2 ^ j) := by
        apply Finset.sum_le_sum
        intro j _
        exact (mul_le_mul' (hcap' j) (prob_le_one : sampleLaw I (reach R hpos j) ≤ 1)).trans_eq
          (mul_one _)
      _ = ENNReal.ofReal (K * ∑ j ∈ Finset.range j₀, (2 : ℝ) ^ j) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.mul_sum]
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (sum_two_pow_le j₀) hK)
  have htail : (∑' t, charge (t + j₀)) ≤ ENNReal.ofReal (2 * K * 2 ^ j₀) := by
    calc
      _ ≤ ∑' t, ENNReal.ofReal (K * 2 ^ j₀ * (1 / 2 : ℝ) ^ t) := by
        apply ENNReal.tsum_le_tsum
        intro t
        have hreach := measure_reach_tail_le_pow R hpos I.mean j₀ habort t
        have h := mul_le_mul' (hcap' (t + j₀)) hreach
        apply h.trans_eq
        have he : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by simp
        rw [he, ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_mul (by positivity), tail_charge_identity]
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
          (hasSum_geometric_two.mul_left (K * 2 ^ j₀)).summable,
          (hasSum_geometric_two.mul_left (K * 2 ^ j₀)).tsum_eq]
        congr 1
        ring
  apply (expectedSamples_le_reach_sum R hpos I).trans
  change (∑' j, charge j) ≤ _
  rw [← (ENNReal.summable (f := fun t => charge (t + j₀))).sum_add_tsum_nat_add']
  apply (add_le_add hearly htail).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem expectedSamples_lt_top_of_dyadic_tail (I : Instance n) (j₀ : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (hcap : ∀ j, ((R j).budget : ℝ) ≤ K * 2 ^ j)
    (habort : ∀ j, j₀ ≤ j → GaussianBlocks.blockLaw I.mean (R j).budget
      {x | (R j).evaluate x = none} ≤ 1 / 4) :
    (policy R hpos).expectedSamples I < ⊤ :=
  (expectedSamples_le_dyadic_tail R hpos I j₀ hK hcap habort).trans_lt ENNReal.ofReal_lt_top

end GapEntropy.FixedCapRetry
