import GapEntropy.MedianElimination
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The deterministic sample cost of median elimination

The round schedules of `MedianElimination` are analysed explicitly: the tolerance `roundEpsilon`
shrinks by `3/4` per round, the confidence `roundBeta` halves, and the active count
`cardinalSchedule` is at most `2s · (1/2)^r` while at least two arms remain. Each round's cost is
bounded by a term proportional to `(r + 2) · (8/9)^r` plus a term proportional to `(1/2)^r`, and
the two series are bounded by `90` and `2`. The declared cost of the whole procedure on `s` arms
is at most `100000 · s · ε⁻² · log(8/β)`, the manuscript's fixed deterministic PAC sample budget
with an explicit universal constant.
-/

noncomputable section
open scoped BigOperators

namespace GapEntropy.MedianElimination

theorem roundEpsilon_inv_square (ε : ℝ) (r : ℕ) :
    (roundEpsilon ε r ^ 2)⁻¹ = 64 * (ε ^ 2)⁻¹ * (16 / 9 : ℝ) ^ r := by
  unfold roundEpsilon
  rw [mul_pow, mul_inv_rev]
  have hpow : (((3 / 4 : ℝ) ^ r) ^ 2)⁻¹ = (16 / 9 : ℝ) ^ r := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
    norm_num
  rw [hpow]
  simp [div_pow, inv_div]
  ring

theorem log_roundBeta {β : ℝ} (hβ : 0 < β) (r : ℕ) :
    Real.log (8 / roundBeta β r) = Real.log (8 / β) + (r + 1 : ℕ) * Real.log 2 := by
  unfold roundBeta
  rw [Real.log_div (by norm_num) (mul_ne_zero hβ.ne' (pow_ne_zero _ (by norm_num))),
    Real.log_mul hβ.ne' (pow_ne_zero _ (by norm_num)), Real.log_pow,
    Real.log_div (by norm_num) hβ.ne']
  have hl : Real.log (1 / 2 : ℝ) = -Real.log 2 := by simp [one_div]
  rw [hl]
  ring

theorem one_le_budget_log {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1 ≤ Real.log (8 / β) := by
  apply (Real.le_log_iff_exp_le (div_pos (by norm_num) hβ)).mpr
  apply Real.exp_one_lt_three.le.trans
  exact (le_div_iff₀ hβ).mpr (by linarith)

theorem log_roundBeta_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (r : ℕ) :
    Real.log (8 / roundBeta β r) ≤ ((r : ℝ) + 2) * Real.log (8 / β) := by
  have hl : Real.log 2 ≤ Real.log (8 / β) := by
    apply Real.log_le_log (by norm_num)
    exact (le_div_iff₀ hβ).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ r + 1 by positivity)
  rw [log_roundBeta hβ]
  push_cast
  linarith

theorem cardinalSchedule_real_work_bound {s r : ℕ} (hs : 0 < s)
    (hr : 2 ≤ cardinalSchedule s r) :
    (cardinalSchedule s r : ℝ) ≤ 2 * (s : ℝ) * (1 / 2 : ℝ) ^ r := by
  have h : (2 : ℝ) ^ r * (cardinalSchedule s r : ℝ) ≤ 2 * (s : ℝ) := by
    exact_mod_cast cardinalSchedule_work_bound hs hr
  have hid : (2 : ℝ) ^ r * (1 / 2 : ℝ) ^ r = 1 := by rw [← mul_pow]; norm_num
  calc
    (cardinalSchedule s r : ℝ) = ((2 : ℝ) ^ r * cardinalSchedule s r) * (1 / 2 : ℝ) ^ r := by
      nlinarith [hid]
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

theorem round_cost_le {s r : ℕ} (hs : 0 < s) {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (hr : 2 ≤ cardinalSchedule s r) :
    (cardinalSchedule s r : ℝ) * roundSamples ε β r ≤
      (1024 * (s : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β)) *
        ((r : ℝ) + 2) * (8 / 9 : ℝ) ^ r + (2 * s) * (1 / 2 : ℝ) ^ r := by
  have hc := cardinalSchedule_real_work_bound hs hr
  have hm := (roundSamples_lt_budget_add_one hε hβ hβ1 r).le
  have hb := (roundBudget_pos hε hβ hβ1 r).le
  have hprod := mul_le_mul hc hm (by positivity : (0 : ℝ) ≤ roundSamples ε β r)
    (by positivity : (0 : ℝ) ≤ 2 * s * (1 / 2 : ℝ) ^ r)
  have hlog := log_roundBeta_le hβ hβ1 r
  have hgeom : (1 / 2 : ℝ) ^ r * (16 / 9 : ℝ) ^ r = (8 / 9 : ℝ) ^ r := by
    rw [← mul_pow]
    norm_num
  have heq : (2 * (s : ℝ) * (1 / 2 : ℝ) ^ r) * (roundBudget ε β r + 1) =
      (1024 * (s : ℝ) * (ε ^ 2)⁻¹ * (8 / 9 : ℝ) ^ r) *
        Real.log (8 / roundBeta β r) + (2 * s) * (1 / 2 : ℝ) ^ r := by
    rw [roundBudget, roundEpsilon_inv_square]
    calc
      _ = (1024 * (s : ℝ) * (ε ^ 2)⁻¹ *
          ((1 / 2 : ℝ) ^ r * (16 / 9 : ℝ) ^ r)) * Real.log (8 / roundBeta β r) +
            (2 * s) * (1 / 2 : ℝ) ^ r := by ring
      _ = _ := by rw [hgeom]
  rw [heq] at hprod
  have hlogprod := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 1024 * (s : ℝ) * (ε ^ 2)⁻¹ * (8 / 9 : ℝ) ^ r by positivity)
  nlinarith

theorem arithmetic_geometric_sum_le (R : ℕ) :
    (∑ r ∈ Finset.range R, ((r : ℝ) + 2) * (8 / 9 : ℝ) ^ r) ≤ 90 := by
  have hmoment := sum_le_hasSum (Finset.range R) (fun r _ => by positivity)
    (hasSum_coe_mul_geometric_of_norm_lt_one (r := (8 / 9 : ℝ)) (by norm_num))
  have hgeom := sum_le_hasSum (Finset.range R) (fun r _ => by positivity)
    (hasSum_geometric_of_norm_lt_one (ξ := (8 / 9 : ℝ)) (by norm_num))
  norm_num at hmoment hgeom
  simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

theorem half_geometric_sum_le (R : ℕ) :
    (∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r) ≤ 2 := by
  have h := geom_sum_mul_neg (1 / 2 : ℝ) R
  have hp : 0 ≤ (1 / 2 : ℝ) ^ R := by positivity
  linarith

/-- The manuscript's fixed deterministic PAC sample budget, with an explicit universal constant. -/
theorem declaredCost_le {s : ℕ} (hs : 0 < s) {ε β : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (declaredCost s ε β : ℝ) ≤ 100000 * (s : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β) := by
  have hlog := one_le_budget_log hβ hβ1
  have hεinv : 1 ≤ (ε ^ 2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos hε)).mpr (by nlinarith)
  have hsum : (declaredCost s ε β : ℝ) ≤
      (1024 * (s : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β)) *
        ∑ r ∈ Finset.range s, ((r : ℝ) + 2) * (8 / 9 : ℝ) ^ r +
      (2 * s) * ∑ r ∈ Finset.range s, (1 / 2 : ℝ) ^ r := by
    simp only [declaredCost, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : 2 ≤ cardinalSchedule s r
    · simpa only [if_pos hr, Nat.cast_mul, mul_assoc] using round_cost_le hs hε hβ hβ1 hr
    · simp only [if_neg hr, Nat.cast_zero]
      positivity
  have hfirst := mul_le_mul_of_nonneg_left (arithmetic_geometric_sum_le s)
    (show 0 ≤ 1024 * (s : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β) by positivity)
  have hsecond := mul_le_mul_of_nonneg_left (half_geometric_sum_le s)
    (show (0 : ℝ) ≤ 2 * s by positivity)
  have hscale : (s : ℝ) ≤ (s : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β) := by
    have ha := mul_le_mul_of_nonneg_left hεinv (show (0 : ℝ) ≤ s by positivity)
    have hb := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ (s : ℝ) * (ε ^ 2)⁻¹ by positivity)
    nlinarith
  nlinarith

end GapEntropy.MedianElimination
