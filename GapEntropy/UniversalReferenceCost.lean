import GapEntropy.UniversalEnvelopeCost
import GapEntropy.UniversalCallGuarantees

/-! F.8: the complete deterministic reference sample reservations, including ceilings. -/
noncomputable section
open scoped BigOperators
namespace GapEntropy.UniversalReferenceCost
open UniversalCall

/-- The largest gap scale contributes only the positive iterated logarithm. -/
theorem log_lastBucket_le {n : ℕ} (I : Instance n) :
    Real.log (I.lastBucket + 1 : ℝ) ≤ 2 + iteratedLog I.twoArmHardness := by
  have hD0 : 0 < I.twoArmHardness := by linarith [I.one_le_twoArmHardness]
  have hlogD : 0 ≤ Real.log I.twoArmHardness := Real.log_nonneg I.one_le_twoArmHardness
  have hfour : (1 : ℝ) ≤ Real.log 4 := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h4 := Real.log_pow (2 : ℝ) 2
    norm_num at h2 h4
    linarith
  have hfour2 : Real.log (4 : ℝ) ≤ 2 := by
    have h4 := Real.log_pow (2 : ℝ) 2
    norm_num at h4
    linarith [TargetAttempt.log_two_le_one]
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 4 ^ I.lastBucket)
    I.lastBucket_power_le_four_twoArmHardness
  rw [Real.log_pow, Real.log_mul (by norm_num) hD0.ne'] at h
  have hk : (0 : ℝ) ≤ I.lastBucket := Nat.cast_nonneg _
  have harg : (I.lastBucket + 1 : ℝ) ≤ 3 * (1 + Real.log I.twoArmHardness) := by nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < I.lastBucket + 1) harg
  rw [Real.log_mul (by norm_num) (by linarith : 1 + Real.log I.twoArmHardness ≠ 0)] at hlog
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith [UniversalCapAnalysis.log_one_add_log_le_iteratedLog I.one_le_twoArmHardness]

theorem sum_four_pow_le {n : ℕ} (I : Instance n) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), (4 : ℝ) ^ k) ≤ (16 / 3) * I.twoArmHardness := by
  change WorkEnvelope.powerSum I.lastBucket ≤ _
  rw [← WorkEnvelope.pow_mul_geometricSum]
  have h := mul_le_mul_of_nonneg_left (WorkEnvelope.geometricSum_le_four_thirds I.lastBucket)
    (show 0 ≤ (4 : ℝ) ^ I.lastBucket by positivity)
  have h' := mul_le_mul_of_nonneg_right I.lastBucket_power_le_four_twoArmHardness
    (show (0 : ℝ) ≤ 4 / 3 by norm_num)
  nlinarith

/-- The weighted finite scale series in F.8. -/
theorem reference_series_le {n : ℕ} (I : Instance n) {L : ℝ} (hL : 1 ≤ L) (j : ℕ) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), (4 : ℝ) ^ k *
      (L + 1 + Real.log (j + 1 : ℝ) + Real.log (k + 1 : ℝ))) ≤
      24 * I.twoArmHardness * (L + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness) := by
  have hj : 0 ≤ Real.log (j + 1 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hD0 : 0 < I.twoArmHardness := by linarith [I.one_le_twoArmHardness]
  have hell := iteratedLog_pos hD0.le
  have hsum : (∑ k ∈ Finset.range (I.lastBucket + 1), (4 : ℝ) ^ k *
      (L + 1 + Real.log (j + 1 : ℝ) + Real.log (k + 1 : ℝ))) ≤
      (∑ k ∈ Finset.range (I.lastBucket + 1), (4 : ℝ) ^ k) *
        (L + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness + 3) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    have hkK : k ≤ I.lastBucket := by simpa using Finset.mem_range.mp hk
    have hl := (Real.log_le_log (by positivity : (0 : ℝ) < k + 1)
      (by exact_mod_cast Nat.add_le_add_right hkK 1)).trans (log_lastBucket_le I)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpow := mul_le_mul_of_nonneg_right (sum_four_pow_le I)
    (show 0 ≤ L + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness + 3 by linarith)
  have hfactor : L + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness + 3 ≤
      4 * (L + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness) := by linarith
  have hfac := mul_le_mul_of_nonneg_left hfactor (show 0 ≤ (16 / 3) * I.twoArmHardness by positivity)
  have hprod : 0 ≤ I.twoArmHardness *
      (L + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness) := by positivity
  nlinarith

theorem log_reference_error {δ : ℝ} (hδ : 0 < δ) (j k : ℕ) :
    Real.log (2 / referenceError δ j k) = Real.log δ⁻¹ + Real.log 128 +
      2 * Real.log (j + 1 : ℝ) + 2 * Real.log (k + 1 : ℝ) := by
  have he : 2 / referenceError δ j k =
      δ⁻¹ * 128 * (j + 1 : ℝ) ^ 2 * (k + 1 : ℝ) ^ 2 := by
    unfold referenceError
    field_simp
    ring
  rw [he, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_pow]
  norm_num

/-- A single complete reference reservation at scale k. The tolerance equality
is numerical, so it also applies to the controller's integer-power syntax. -/
theorem referenceBudget_le {δ d : ℝ} (hδ : ValidConfidence δ) (j k : ℕ)
    (hd : (d ^ 2)⁻¹ = (4 : ℝ) ^ k) :
    (referenceBudget d (referenceError δ j k) : ℝ) ≤
      4096 * (4 : ℝ) ^ k *
        (confidenceCost δ + 1 + Real.log (j + 1 : ℝ) + Real.log (k + 1 : ℝ)) := by
  have hL := UniversalCapAnalysis.one_le_confidenceCost hδ
  have hj : 0 ≤ Real.log (j + 1 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hk : 0 ≤ Real.log (k + 1 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hlog := log_reference_error hδ.1 j k
  have h128 : Real.log (128 : ℝ) ≤ 7 := by
    rw [TargetAttempt.log_128_eq]
    linarith [TargetAttempt.log_two_le_one]
  have h1280 : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog0 : 0 ≤ Real.log (2 / referenceError δ j k) := by
    unfold confidenceCost at hL
    linarith
  unfold referenceBudget
  rw [hd]
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 512 * (4 : ℝ) ^ k *
    Real.log (2 / referenceError δ j k) by positivity)).le
  have hp : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hb : Real.log (2 / referenceError δ j k) ≤
      7 * (confidenceCost δ + 1 + Real.log (j + 1 : ℝ) + Real.log (k + 1 : ℝ)) := by
    unfold confidenceCost
    unfold confidenceCost at hL
    linarith
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 512 * (4 : ℝ) ^ k by positivity)
  have hb1 : 1 ≤ confidenceCost δ + 1 + Real.log (j + 1 : ℝ) + Real.log (k + 1 : ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_left hb1 (show 0 ≤ (4 : ℝ) ^ k by positivity)
  nlinarith

/-- The sum includes one entire reference budget at every scale, so it also
bounds any favorable prefix's prospective reference reservations. -/
theorem total_referenceBudget_le {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (j : ℕ) (d : ℕ → ℝ)
    (hd : ∀ k, (d k ^ 2)⁻¹ = (4 : ℝ) ^ k) :
    (∑ k ∈ Finset.range (I.lastBucket + 1),
      (referenceBudget (d k) (referenceError δ j k) : ℝ)) ≤
      100000 * I.twoArmHardness *
        (confidenceCost δ + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness) := by
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (I.lastBucket + 1)) =>
    referenceBudget_le hδ j k (hd k))
  have hseries := mul_le_mul_of_nonneg_left
    (reference_series_le I (UniversalCapAnalysis.one_le_confidenceCost hδ) j)
    (show (0 : ℝ) ≤ 4096 by norm_num)
  have hrewrite : (∑ k ∈ Finset.range (I.lastBucket + 1),
      4096 * (4 : ℝ) ^ k *
        (confidenceCost δ + 1 + Real.log (j + 1 : ℝ) + Real.log (k + 1 : ℝ))) =
      4096 * (∑ k ∈ Finset.range (I.lastBucket + 1), (4 : ℝ) ^ k *
        (confidenceCost δ + 1 + Real.log (j + 1 : ℝ) + Real.log (k + 1 : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hrewrite] at hsum
  have hD0 : 0 < I.twoArmHardness := by linarith [I.one_le_twoArmHardness]
  have hL := confidenceCost_pos hδ
  have hj : 0 ≤ Real.log (j + 1 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hell := iteratedLog_pos hD0.le
  have hp : 0 ≤ I.twoArmHardness *
      (confidenceCost δ + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness) := by positivity
  nlinarith

end GapEntropy.UniversalReferenceCost
