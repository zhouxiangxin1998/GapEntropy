import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The work-proportional batch allocation inequality (E.17)

A logarithmic proof uses log η ≤ -3, log x ≤ x-1, and log U ≥ log x
when x≥1. It handles the real exponent max(25,2x) uniformly and avoids any
unproved monotonicity or numerical derivative estimate.
-/

namespace GapEntropy

private theorem log_eta_le_neg_three {η : ℝ} (hη : 0 < η) (hη1280 : η ≤ 1 / 1280) :
    Real.log η ≤ -3 := by
  have hsmall : η ≤ (1 / 2 : ℝ) ^ 6 := hη1280.trans (by norm_num)
  have hlog := Real.log_le_log hη hsmall
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2 : ℝ))
  norm_num at htwo
  rw [Real.log_pow] at hlog
  simp only [one_div, Real.log_inv] at hlog
  norm_num at hlog
  linarith

/-- E.17, with all allocation and work-cap assumptions explicit. -/
theorem batch_allocation_bound {η U x : ℝ}
    (hη : 0 < η) (hη1280 : η ≤ 1 / 1280) (hU : 1 ≤ U)
    (hx : 0 < x) (hxU : x ≤ U) :
    (η * x / U) ^ (max 25 (2 * x)) ≤ (η / U) ^ (4 : ℕ) * x := by
  have hU0 : 0 < U := by linarith
  have hηU : 0 < η / U := div_pos hη hU0
  have hbase : 0 < η * x / U := div_pos (mul_pos hη hx) hU0
  have ha := log_eta_le_neg_three hη hη1280
  have hb : 0 ≤ Real.log U := Real.log_nonneg hU
  have he25 : (25 : ℝ) ≤ max 25 (2 * x) := le_max_left _ _
  have he2x : 2 * x ≤ max 25 (2 * x) := le_max_right _ _
  have he4 : 0 ≤ max 25 (2 * x) - 4 := by linarith
  have he1 : 0 ≤ max 25 (2 * x) - 1 := by linarith
  have hlog : (max 25 (2 * x) - 4) * (Real.log η - Real.log U) +
      (max 25 (2 * x) - 1) * Real.log x ≤ 0 := by
    by_cases hx1 : x ≤ 1
    · have hc : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos he4 (by linarith))
        (mul_nonpos_of_nonneg_of_nonpos he1 hc)
    · have hc : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      have hcb : Real.log x ≤ Real.log U := Real.log_le_log hx hxU
      have hcX := Real.log_le_sub_one_of_pos hx
      have hmain := mul_le_mul_of_nonneg_left (show Real.log η - Real.log U ≤
        -3 - Real.log x by linarith) he4
      have hex : x ≤ max 25 (2 * x) - 4 := by
        by_cases hxx : x ≤ 21
        · linarith
        · linarith
      nlinarith
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hbase _)
    (mul_pos (pow_pos hηU _) hx)).mp
  rw [Real.log_rpow hbase, Real.log_mul (pow_pos hηU _).ne' hx.ne', Real.log_pow,
    Real.log_div hη.ne' hU0.ne', Real.log_div (mul_pos hη hx).ne' hU0.ne',
    Real.log_mul hη.ne' hx.ne']
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- The same allocation estimate in the exponential form delivered by the
actual Gaussian batch-collapse theorem, allowing a smaller actual confidence. -/
theorem batch_allocation_exp_bound {η U x ρ : ℝ}
    (hη : 0 < η) (hη1280 : η ≤ 1 / 1280) (hU : 1 ≤ U)
    (hx : 0 < x) (hxU : x ≤ U) (hρ : 0 < ρ) (hρalloc : ρ ≤ η * x / U) :
    Real.exp (max 25 (2 * x) * Real.log ρ) ≤ (η / U) ^ (4 : ℕ) * x := by
  rw [mul_comm (max 25 (2 * x)), ← Real.rpow_def_of_pos hρ]
  exact (Real.rpow_le_rpow hρ.le hρalloc (by positivity)).trans
    (batch_allocation_bound hη hη1280 hU hx hxU)

/-- Per-call E.17 normalized directly by its deterministic work reservation.
Summing these charges over a path with total work at most M gives E.12. -/
theorem batch_reserved_charge_bound {η h M w ρ : ℝ}
    (hη : 0 < η) (hη1280 : η ≤ 1 / 1280) (hh : 0 < h) (hhM : h ≤ M)
    (hw : 0 < w) (hwM : w ≤ M) (hρ : 0 < ρ) (hρalloc : ρ ≤ η * w / M) :
    3 * Real.exp (max 25 (2 * (w / h)) * Real.log ρ) ≤
      (3 * η ^ (4 : ℕ) * (h / M) ^ (3 : ℕ)) * (w / M) := by
  have hM : 0 < M := hh.trans_le hhM
  have hU : 1 ≤ M / h := (le_div_iff₀ hh).mpr (by simpa using hhM)
  have hxU : w / h ≤ M / h := div_le_div_of_nonneg_right hwM hh.le
  have halloc : ρ ≤ η * (w / h) / (M / h) := by
    convert hρalloc using 1
    field_simp
  have h := batch_allocation_exp_bound hη hη1280 hU (div_pos hw hh) hxU hρ halloc
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 3)).trans_eq
  field_simp

end GapEntropy
