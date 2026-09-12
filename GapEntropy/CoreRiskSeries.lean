import GapEntropy.RetryBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Summing the fixed-core error risks in E.19, with the manuscript's constants. -/
noncomputable section
open scoped BigOperators

namespace GapEntropy

/-- Core cardinality is `k+1`; singleton cores require one flag. -/
def coreRisk (p : ℝ) (k : ℕ) : ℝ := (k + 1) * p ^ max 1 k

private def riskEnvelope (p : ℝ) (k : ℕ) : ℝ := if k = 0 then p else (2 * p) ^ k

private theorem cardinal_le_pow_two (k : ℕ) : (k + 2 : ℝ) ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      push_cast
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      nlinarith

private theorem hasSum_riskEnvelope {p : ℝ} (hp : 0 ≤ p) (hp2 : p < 1 / 2) :
    HasSum (riskEnvelope p) (p + 2 * p / (1 - 2 * p)) := by
  have hn : ‖2 * p‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; linarith
  have hg := (hasSum_geometric_of_norm_lt_one hn).mul_left (2 * p)
  have ht : HasSum (fun k => riskEnvelope p (k + 1)) (2 * p / (1 - 2 * p)) := by
    convert! hg using 1
    · ext k
      simp only [riskEnvelope, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, pow_succ']
  have h := (hasSum_nat_add_iff 1).mp ht
  simpa only [Finset.sum_range_one, riskEnvelope, ↓reduceIte, add_comm] using h

private theorem coreRisk_le_envelope {p : ℝ} (hp : 0 ≤ p) (k : ℕ) :
    coreRisk p k ≤ riskEnvelope p k := by
  cases k with
  | zero => simp [coreRisk, riskEnvelope]
  | succ k =>
      have hk := cardinal_le_pow_two k
      have h := mul_le_mul_of_nonneg_right hk (pow_nonneg hp (k + 1))
      simpa only [coreRisk, riskEnvelope, Nat.succ_eq_add_one,
        Nat.max_eq_right (Nat.succ_le_succ (Nat.zero_le k)), Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ↓reduceIte, Nat.cast_add, Nat.cast_one, ← mul_pow, add_assoc, one_add_one_eq_two] using h

private theorem sqrt_coreRisk_le_envelope {p : ℝ} (hp : 0 ≤ p) (k : ℕ) :
    Real.sqrt (coreRisk p k) ≤ riskEnvelope (Real.sqrt p) k := by
  cases k with
  | zero => simp [coreRisk, riskEnvelope]
  | succ k =>
      have hk : (k + 2 : ℝ) ≤ 4 ^ (k + 1) := (cardinal_le_pow_two k).trans
        (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
      have h := mul_le_mul_of_nonneg_right hk (pow_nonneg hp (k + 1))
      have he : ((2 * Real.sqrt p) ^ (k + 1)) ^ 2 = 4 ^ (k + 1) * p ^ (k + 1) := by
        rw [← pow_mul, Nat.mul_comm (k + 1) 2, pow_mul, mul_pow, Real.sq_sqrt hp]
        norm_num [mul_pow]
      simp only [riskEnvelope, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ↓reduceIte]
      apply (Real.sqrt_le_left (by positivity)).mpr
      rw [he]
      simpa only [coreRisk, Nat.succ_eq_add_one,
        Nat.max_eq_right (Nat.succ_le_succ (Nat.zero_le k)), Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h

theorem coreRisk_nonneg {p : ℝ} (hp : 0 ≤ p) (k : ℕ) : 0 ≤ coreRisk p k := by
  unfold coreRisk
  positivity

theorem coreRisk_summable {p : ℝ} (hp : 0 ≤ p) (hp2 : p < 1 / 2) :
    Summable (coreRisk p) :=
  (hasSum_riskEnvelope hp hp2).summable.of_nonneg_of_le
    (coreRisk_nonneg hp) (coreRisk_le_envelope hp)

theorem sum_coreRisk_le {p : ℝ} (hp : 0 ≤ p) (hp16 : p ≤ 1 / 16) :
    (∑' k, coreRisk p k) ≤ 4 * p := by
  have hp2 : p < 1 / 2 := by linarith
  apply ((coreRisk_summable hp hp2).tsum_le_tsum (coreRisk_le_envelope hp)
    (hasSum_riskEnvelope hp hp2).summable).trans
  rw [(hasSum_riskEnvelope hp hp2).tsum_eq]
  have hfrac : 2 * p / (1 - 2 * p) ≤ 3 * p :=
    (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  linarith

theorem sqrt_coreRisk_summable {p : ℝ} (hp : 0 ≤ p) (hp16 : p ≤ 1 / 16) :
    Summable (fun k => Real.sqrt (coreRisk p k)) := by
  have ht : Real.sqrt p ≤ 1 / 4 := (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith)
  exact (hasSum_riskEnvelope (Real.sqrt_nonneg p) (by linarith)).summable.of_nonneg_of_le
    (fun k => Real.sqrt_nonneg _) (sqrt_coreRisk_le_envelope hp)

theorem sum_sqrt_coreRisk_le {p : ℝ} (hp : 0 ≤ p) (hp16 : p ≤ 1 / 16) :
    (∑' k, Real.sqrt (coreRisk p k)) ≤ 5 * Real.sqrt p := by
  have ht : Real.sqrt p ≤ 1 / 4 := (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith)
  have ht0 := Real.sqrt_nonneg p
  have ht2 : Real.sqrt p < 1 / 2 := by linarith
  apply ((sqrt_coreRisk_summable hp hp16).tsum_le_tsum (sqrt_coreRisk_le_envelope hp)
    (hasSum_riskEnvelope ht0 ht2).summable).trans
  rw [(hasSum_riskEnvelope ht0 ht2).tsum_eq]
  have hfrac : 2 * Real.sqrt p / (1 - 2 * Real.sqrt p) ≤ 4 * Real.sqrt p :=
    (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  linarith

end GapEntropy
