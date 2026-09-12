import GapEntropy.CoreFamilyRisk
import GapEntropy.Problem
import Mathlib.Analysis.PSeries

/-! Numerical and countable-union budgets in D.10, E.4, E.19, and E.20.
The event estimates are explicit premises until instantiated by the actual policy. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace GapEntropy.UniversalErrorBudget

def indexWeight (r j : ℕ) : ℝ := 1 / (j + 1 : ℝ) ^ r

theorem indexWeight_nonneg (r j : ℕ) : 0 ≤ indexWeight r j := by
  unfold indexWeight
  positivity

theorem indexWeight_summable {r : ℕ} (hr : 2 ≤ r) : Summable (indexWeight r) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (show 1 < r by omega))
  convert! h using 1
  ext j
  simp only [indexWeight, Nat.cast_add, Nat.cast_one]

private theorem square_weight_le_telescope (j : ℕ) :
    indexWeight 2 j ≤ 2 / (j + 1 : ℝ) - 2 / (j + 2 : ℝ) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  unfold indexWeight
  apply (le_sub_iff_add_le).mpr
  rw [div_add_div _ _ (by positivity : (j + 1 : ℝ)^2 ≠ 0)
    (by positivity : (j + 2 : ℝ) ≠ 0)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

private theorem sum_square_weight_range_le (N : ℕ) :
    (∑ j ∈ Finset.range N, indexWeight 2 j) ≤ 2 - 2 / (N + 1 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := add_le_add ih (square_weight_le_telescope N)
      push_cast
      convert! h using 1
      ring

theorem tsum_indexWeight_le_two {r : ℕ} (hr : 2 ≤ r) :
    (∑' j, indexWeight r j) ≤ 2 := by
  have hs2 := indexWeight_summable (r := 2) le_rfl
  have hs2le : (∑' j, indexWeight 2 j) ≤ 2 := hs2.tsum_le_of_sum_range_le fun N =>
    (sum_square_weight_range_le N).trans (sub_le_self _ (by positivity))
  apply ((indexWeight_summable hr).tsum_le_tsum (fun j => ?_) hs2).trans hs2le
  unfold indexWeight
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) j; linarith) hr

/-- The independent reference allocation β in D.6. -/
def referenceConfidence (δ : ℝ) (j k : ℕ) : ℝ :=
  δ / (64 * (j + 1 : ℝ) ^ 2 * (k + 1 : ℝ) ^ 2)

theorem referenceConfidence_eq (δ : ℝ) (j k : ℕ) :
    referenceConfidence δ j k = (δ / 64 * indexWeight 2 j) * indexWeight 2 k := by
  unfold referenceConfidence indexWeight
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem referenceConfidence_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (j k : ℕ) :
    0 ≤ referenceConfidence δ j k := by
  rw [referenceConfidence_eq]
  exact mul_nonneg (mul_nonneg (div_nonneg hδ (by norm_num))
    (indexWeight_nonneg _ _)) (indexWeight_nonneg _ _)

/-- D.10, including all attempt-scale pairs whether visited or not. -/
theorem tsum_referenceConfidence_le {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑' jk : ℕ × ℕ, ENNReal.ofReal (referenceConfidence δ jk.1 jk.2)) ≤
      ENNReal.ofReal (δ / 16) := by
  have he : (∑' j, ENNReal.ofReal (indexWeight 2 j)) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (indexWeight_nonneg 2)
      (indexWeight_summable (r := 2) le_rfl)]
    exact ENNReal.ofReal_le_ofReal (tsum_indexWeight_le_two le_rfl)
  have hfac : ∀ j k, ENNReal.ofReal (referenceConfidence δ j k) =
      ENNReal.ofReal (δ / 64) * ENNReal.ofReal (indexWeight 2 j) *
        ENNReal.ofReal (indexWeight 2 k) := by
    intro j k
    rw [referenceConfidence_eq,
      ENNReal.ofReal_mul (mul_nonneg (div_nonneg hδ (by norm_num)) (indexWeight_nonneg 2 j)),
      ENNReal.ofReal_mul (div_nonneg hδ (by norm_num))]
  simp_rw [hfac]
  rw [ENNReal.tsum_prod (f := fun j k => ENNReal.ofReal (δ / 64) *
    ENNReal.ofReal (indexWeight 2 j) * ENNReal.ofReal (indexWeight 2 k))]
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  apply (mul_le_mul' (mul_le_mul' le_rfl he) he).trans_eq
  rw [← ENNReal.ofReal_mul (div_nonneg hδ (by norm_num)),
    ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hδ (by norm_num)) (by norm_num))]
  congr 1
  ring

/-- E.4's summation across all attempts. -/
theorem tsum_small_error_le {η : ℝ} (hη : 0 ≤ η) :
    (∑' j, ENNReal.ofReal (7 * η ^ 25 * indexWeight 50 j)) ≤
      ENNReal.ofReal (14 * η ^ 25) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by
    exact mul_nonneg (by positivity) (indexWeight_nonneg _ _))
    ((indexWeight_summable (r := 50) (by norm_num)).mul_left _), tsum_mul_left]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left
    (tsum_indexWeight_le_two (r := 50) (by norm_num)) (show 0 ≤ 7 * η ^ 25 by positivity)
  nlinarith

/-- The manuscript's common Bernoulli envelope. -/
def severeProbability (η : ℝ) : ℝ := 2 * η ^ 25

theorem severeProbability_nonneg {η : ℝ} (hη : 0 ≤ η) : 0 ≤ severeProbability η := by
  unfold severeProbability
  positivity

theorem severeProbability_le {δ : ℝ} (hδ : ValidConfidence δ) :
    severeProbability (δ / 131072) ≤ 1 / 16 := by
  have hη : 0 ≤ δ / 131072 := by linarith [hδ.1]
  have hη1 : δ / 131072 ≤ 1 := by linarith [hδ.2]
  have hp := pow_le_pow_of_le_one hη hη1 (show 1 ≤ 25 by omega)
  norm_num only [pow_one] at hp
  unfold severeProbability
  linarith [hδ.2]

/-- E.20 is strictly below δ; all constants are fixed independently of the instance. -/
theorem total_error_lt {δ : ℝ} (hδ : ValidConfidence δ) :
    let η := δ / 131072
    let p := severeProbability η
    δ / 16 + 14 * η ^ 25 + 40 * p + 15 * η ^ 2 * Real.sqrt p < δ := by
  dsimp only
  let η := δ / 131072
  have hη : 0 ≤ η := by dsimp [η]; linarith [hδ.1]
  have hη1 : η ≤ 1 := by dsimp [η]; linarith [hδ.2]
  have hp25 : η ^ 25 ≤ η := by
    simpa using pow_le_pow_of_le_one hη hη1 (show 1 ≤ 25 by omega)
  have hp2 : η ^ 2 ≤ η := by
    simpa using pow_le_pow_of_le_one hη hη1 (show 1 ≤ 2 by omega)
  have hs : Real.sqrt (severeProbability η) ≤ 1 :=
    Real.sqrt_le_one.mpr ((severeProbability_le hδ).trans (by norm_num))
  have hscharge := mul_le_mul_of_nonneg_left hs (show 0 ≤ 15 * η ^ 2 by positivity)
  change δ / 16 + 14 * η ^ 25 + 40 * (2 * η ^ 25) +
    15 * η ^ 2 * Real.sqrt (severeProbability η) < δ
  have heq : η = δ / 131072 := rfl
  nlinarith [hδ.1]

/-- Full numerical union-bound endpoint. The three actual-event estimates are
explicit inputs, to be supplied by the universal algorithm's execution proofs. -/
theorem incorrect_event_lt_confidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (Wrong Ref Small : Set Ω) (Core : Finset (Fin n) → Set Ω)
    (hcover : Wrong ⊆ Ref ∪ Small ∪ ⋃ B ∈ I.terminalCoreFamily, Core B)
    (href : μ Ref ≤ ENNReal.ofReal (δ / 16))
    (hsmall : μ Small ≤ ENNReal.ofReal (14 * (δ / 131072) ^ 25))
    (hcore : ∀ B ∈ I.terminalCoreFamily,
      μ (Core B) ≤ ENNReal.ofReal
        (10 * coreRisk (severeProbability (δ / 131072)) (B.card - 1) +
          3 * (δ / 131072) ^ 2 *
            Real.sqrt (coreRisk (severeProbability (δ / 131072)) (B.card - 1)))) :
    μ Wrong < ENNReal.ofReal δ := by
  have hδ0 := hδ.1
  have hη : 0 ≤ δ / 131072 := by linarith [hδ.1]
  have hp := severeProbability_nonneg hη
  have hc := I.measure_terminalCoreFamily_union_le μ Core hp (severeProbability_le hδ) hcore
  have hsum := add_le_add (add_le_add href hsmall) hc
  have hμ := (measure_mono hcover).trans
    ((measure_union_le (Ref ∪ Small) _).trans
      (add_le_add (measure_union_le (μ := μ) Ref Small) le_rfl))
  apply (hμ.trans hsum).trans_lt
  rw [← ENNReal.ofReal_add (by linarith [hδ.1]) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply (ENNReal.ofReal_lt_ofReal_iff hδ0).mpr
  simpa only [add_assoc] using total_error_lt hδ

end GapEntropy.UniversalErrorBudget
