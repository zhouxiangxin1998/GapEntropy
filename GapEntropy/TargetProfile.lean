import GapEntropy.WorkEntropy
import GapEntropy.MedianElimination

/-!
# Target-profile counts, tolerances, and confidences

For a fixed target instance, `targetCount k` is C.2's hard-coded count of the best arm plus the
arms in dyadic buckets strictly beyond scale `k`, `targetTolerance k` is `(1/2)^k`, and the
per-scale and per-call confidences are `scaleConfidence ε k = (ε/2) · workMass k` and
`callConfidence ε k r = scaleConfidence ε k · (1/2)^(r+1)`. The scale work at scale `k + 1`
equals `4^(k+1) · targetCount k`, the scale confidences sum to `ε/2`, and all call confidences
together with the final `ε/2` sum to at most `ε`.
-/

noncomputable section
open scoped BigOperators

namespace GapEntropy.Instance
variable {n : ℕ} (I : Instance n)

/-- C.2's hard-coded count of the best plus buckets strictly beyond the scale. -/
def targetCount (k : ℕ) : ℕ :=
  1 + ∑ t ∈ Finset.range (I.lastBucket + 1), if k < t then I.bucketCount t else 0

def targetTolerance (_I : Instance n) (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k
def scaleConfidence (ε : ℝ) (k : ℕ) : ℝ := (ε / 2) * I.workMass k
def callConfidence (ε : ℝ) (k r : ℕ) : ℝ := I.scaleConfidence ε k * (1 / 2 : ℝ) ^ (r + 1)

theorem targetCount_pos (k : ℕ) : 0 < I.targetCount k := by unfold targetCount; omega

theorem targetCount_last : I.targetCount I.lastBucket = 1 := by
  unfold targetCount
  have hzero : ∑ t ∈ Finset.range (I.lastBucket + 1),
      (if I.lastBucket < t then I.bucketCount t else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg (by have := Finset.mem_range.mp ht; omega)]
  rw [hzero, add_zero]

theorem sum_bucketCount : (∑ t ∈ Finset.range (I.lastBucket + 1), I.bucketCount t) = n - 1 := by
  have hmaps : ∀ i ∈ I.suboptimal, I.bucket i ∈ Finset.range (I.lastBucket + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (I.bucket_le_lastBucket hi))
  have h := Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : ℕ))
  simpa [bucketCount, gapGroup, suboptimal] using h

theorem targetTolerance_pos (k : ℕ) : 0 < I.targetTolerance k := by
  unfold targetTolerance
  positivity

theorem targetTolerance_le_one (k : ℕ) : I.targetTolerance k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem targetTolerance_inv_square (k : ℕ) : (I.targetTolerance k ^ 2)⁻¹ = (4 : ℝ) ^ k := by
  unfold targetTolerance
  rw [← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
  norm_num

theorem scaleWork_pos (k : ℕ) : 0 < I.scaleWork k := by
  unfold scaleWork WorkEnvelope.work
  have hnon : 0 ≤ ∑ t ∈ Finset.range (I.lastBucket + 1),
      if k ≤ t then (I.bucketCount t : ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> positivity
  positivity

theorem scaleWork_zero : I.scaleWork 0 = n := by
  have hn := I.two_le
  have hsum : (∑ t ∈ Finset.range (I.lastBucket + 1), (I.bucketCount t : ℝ)) = (n - 1 : ℕ) := by
    exact_mod_cast I.sum_bucketCount
  simp only [scaleWork, WorkEnvelope.work, pow_zero, Nat.zero_le, if_true, one_mul]
  rw [hsum]
  have heq : (n - 1 : ℕ) + 1 = n := by omega
  exact_mod_cast (by omega : 1 + (n - 1) = n)

theorem scaleWork_succ (k : ℕ) :
    I.scaleWork (k + 1) = (4 : ℝ) ^ (k + 1) * I.targetCount k := by
  simp only [scaleWork, WorkEnvelope.work, targetCount, Nat.cast_add, Nat.cast_one,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  congr 2

theorem workMass_pos (k : ℕ) : 0 < I.workMass k :=
  div_pos (I.scaleWork_pos k) I.workEnvelope_pos

theorem workMass_le_one {k : ℕ} (hk : k ≤ I.lastBucket) : I.workMass k ≤ 1 := by
  apply (div_le_one I.workEnvelope_pos).mpr
  rw [I.workEnvelope_eq_sum]
  exact Finset.single_le_sum (fun t _ => (I.scaleWork_pos t).le)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem scaleConfidence_pos {ε : ℝ} (hε : 0 < ε) (k : ℕ) : 0 < I.scaleConfidence ε k :=
  mul_pos (by positivity) (I.workMass_pos k)

theorem scaleConfidence_le {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ} (hk : k ≤ I.lastBucket) :
    I.scaleConfidence ε k ≤ ε / 2 := by
  unfold scaleConfidence
  exact mul_le_of_le_one_right (by positivity) (I.workMass_le_one hk)

theorem sum_scaleConfidence (ε : ℝ) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), I.scaleConfidence ε k) = ε / 2 := by
  simp only [scaleConfidence, ← Finset.mul_sum, I.sum_workMass, mul_one]

theorem callConfidence_pos {ε : ℝ} (hε : 0 < ε) (k r : ℕ) : 0 < I.callConfidence ε k r :=
  mul_pos (I.scaleConfidence_pos hε k) (by positivity)

theorem callConfidence_le {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ} (hk : k ≤ I.lastBucket) (r : ℕ) :
    I.callConfidence ε k r ≤ ε / 2 := by
  have h := GapEntropy.MedianElimination.roundBeta_le
    (mul_nonneg (show 0 ≤ ε / 2 by positivity) (I.workMass_pos k).le) r
  exact h.trans (I.scaleConfidence_le hε hk)

theorem sum_callConfidence_le {ε : ℝ} (hε : 0 ≤ ε) (k R : ℕ) :
    (∑ r ∈ Finset.range R, I.callConfidence ε k r) ≤ I.scaleConfidence ε k :=
  GapEntropy.MedianElimination.cumulative_confidence
    (mul_nonneg (by positivity) (I.workMass_pos k).le) R

theorem all_callConfidence_le {ε : ℝ} (hε : 0 ≤ ε) (R : ℕ) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), ∑ r ∈ Finset.range R, I.callConfidence ε k r) + ε / 2 ≤ ε := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range (I.lastBucket + 1)) => I.sum_callConfidence_le hε k R)
  rw [I.sum_scaleConfidence] at h
  linarith

end GapEntropy.Instance
