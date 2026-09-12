import GapEntropy.TargetAttempt
import GapEntropy.TargetEntropyBudget

/-!
# C.2 sample-cost bounds for the finite target attempt

Each loop call at scale `k` and round `r` costs at most
`26000000 · scaleWork k · log(1/scaleConfidence ε k) · (r + 9) · (3/4)^r`, so the per-scale
total, including a possible final aborting invocation, is at most
`1248000000 · scaleWork k · log(1/scaleConfidence ε k)`. The final call on at most four arms
costs at most `936000000 · hardness · log(1/ε)`. Combining these with the A.5 entropy envelope of
`TargetEntropyBudget` gives C.2(3): every oracle trajectory has total cost at most
`1000000000000 · hardness · (log(1/ε) + gapEntropy)`. The statistical oracle need not have the
target's means or gap profile.
-/

noncomputable section
open scoped BigOperators

namespace GapEntropy.TargetAttempt
variable {n : ℕ} (I : Instance n)

theorem loopCost_le {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (oracle : Oracle n) {k : ℕ} (hk : k ≤ I.lastBucket) (r : ℕ) :
    (loopCost I ε oracle k r : ℝ) ≤
      26000000 * I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹ *
        ((r : ℝ) + 9) * (3 / 4 : ℝ) ^ r := by
  have hη := I.scaleConfidence_pos hε k
  have hW := I.scaleWork_pos k
  have hη3 : I.scaleConfidence ε k ≤ 1 / 3 := (I.scaleConfidence_le hε.le hk).trans (by linarith)
  have hlog := one_le_log_inv hη hη3
  unfold loopCost
  cases hreq : loopRequest I oracle k r with
  | none => simp only [Nat.cast_zero]; positivity
  | some S =>
    have hα := I.callConfidence_pos hε k r
    have hα1 : I.callConfidence ε k r ≤ 1 := (I.callConfidence_le hε.le hk r).trans (by linarith)
    have hp := GapEntropy.EliminationTape.declaredCost_le (loopRequest_nonempty hreq).card_pos
      (I.targetTolerance_pos k) (I.targetTolerance_le_one k) hα hα1
    have hw := loopRequest_work_bound hreq
    have hl : Real.log (128 / I.callConfidence ε k r) ≤
        ((r : ℝ) + 9) * Real.log (I.scaleConfidence ε k)⁻¹ := log_call_le hη hη3 r
    have hlpos := (GapEntropy.EliminationTape.one_le_elimination_log hα hα1).trans'
      (by norm_num : (0 : ℝ) ≤ 1)
    have hm := mul_le_mul_of_nonneg_right hw hlpos
    have hm2 := mul_le_mul_of_nonneg_left hl
      (show 0 ≤ 4 * I.scaleWork k * (3 / 4 : ℝ) ^ r by positivity [I.scaleWork_pos k])
    nlinarith

/-- C.2's per-scale deterministic charge, including a possible final aborting invocation. -/
theorem scaleCost_le {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (oracle : Oracle n) {k : ℕ} (hk : k ≤ I.lastBucket) :
    (∑ r ∈ Finset.range n, (loopCost I ε oracle k r : ℝ)) ≤
      1248000000 * I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹ := by
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range n) => loopCost_le I hε hε10 oracle hk r)
  have hη3 : I.scaleConfidence ε k ≤ 1 / 3 := (I.scaleConfidence_le hε.le hk).trans (by linarith)
  have hlog := one_le_log_inv (I.scaleConfidence_pos hε k) hη3
  have hseries := mul_le_mul_of_nonneg_left (scale_series_le n)
    (show 0 ≤ 26000000 * I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹ by
      positivity [I.scaleWork_pos k])
  have heq : (∑ r ∈ Finset.range n,
      26000000 * I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹ *
        ((r : ℝ) + 9) * (3 / 4 : ℝ) ^ r) =
      (26000000 * I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹) *
        ∑ r ∈ Finset.range n, ((r : ℝ) + 9) * (3 / 4 : ℝ) ^ r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [heq] at hsum
  nlinarith

theorem finalCost_le {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (oracle : Oracle n) :
    (finalCost I ε oracle : ℝ) ≤ 936000000 * I.hardness * Real.log ε⁻¹ := by
  have hL := one_le_log_inv hε (by linarith)
  have hH := I.hardness_pos
  unfold finalCost
  cases hreq : finalRequest I oracle with
  | none => simp only [Nat.cast_zero]; positivity
  | some S =>
    have hS := finalRequest_some hreq
    have hp := GapEntropy.EliminationTape.declaredCost_le hS.1.card_pos
      (I.targetTolerance_pos I.lastBucket) (I.targetTolerance_le_one I.lastBucket)
      (show 0 < ε / 2 by positivity) (show ε / 2 ≤ 1 by linarith)
    rw [I.targetTolerance_inv_square] at hp
    have hsR : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS.2.2
    have hpower : (4 : ℝ) ^ I.lastBucket ≤ 4 * I.hardness :=
      I.lastBucket_power_le_four_twoArmHardness.trans
        (mul_le_mul_of_nonneg_left I.twoArmHardness_le_hardness (by norm_num))
    have hsize := mul_le_mul hsR hpower (by positivity : (0 : ℝ) ≤ 4 ^ I.lastBucket) (by norm_num : (0 : ℝ) ≤ 4)
    have hlog := final_log_le hε hε10
    have hlogpos : 0 ≤ Real.log (128 / (ε / 2)) :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (GapEntropy.EliminationTape.one_le_elimination_log
        (by positivity) (by linarith))
    have hm := mul_le_mul_of_nonneg_right hsize hlogpos
    have hm2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16 * I.hardness by positivity)
    nlinarith

/-- C.2(3): every oracle trajectory obeys the fixed target's deterministic work bound.
The statistical oracle need not have the target's means or gap profile. -/
theorem totalCost_le {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (oracle : Oracle n) :
    (totalCost I ε oracle : ℝ) ≤
      1000000000000 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy) := by
  have hs := Finset.sum_le_sum (fun k (hk : k ∈ Finset.range (I.lastBucket + 1)) =>
    scaleCost_le I hε hε10 oracle (k := k) (by have := Finset.mem_range.mp hk; omega))
  have heq : (∑ k ∈ Finset.range (I.lastBucket + 1),
      1248000000 * I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹) =
      1248000000 * ∑ k ∈ Finset.range (I.lastBucket + 1),
        I.scaleWork k * Real.log (I.scaleConfidence ε k)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq] at hs
  have hb := mul_le_mul_of_nonneg_left (profile_log_budget_le I hε hε10)
    (by norm_num : (0 : ℝ) ≤ 1248000000)
  have hf := finalCost_le I hε hε10 oracle
  have hL := one_le_log_inv hε (by linarith)
  have hH := I.hardness_pos
  have hE := I.gapEntropy_nonneg
  have hHE : 0 ≤ I.hardness * I.gapEntropy := by positivity
  have hHL : 0 ≤ I.hardness * Real.log ε⁻¹ := by positivity
  simp only [totalCost, Nat.cast_add, Nat.cast_sum]
  nlinarith

end GapEntropy.TargetAttempt
