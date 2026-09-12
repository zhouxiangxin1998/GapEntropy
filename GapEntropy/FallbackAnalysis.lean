import GapEntropy.FallbackCorrectness
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Analytic finiteness of fallback round bounds

The squared confidence radius is bounded by a polynomial times a geometric
sequence. The double-exponential round tail is a subsequence of the standard
summable sequence `m * exp(-c*m)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace GapEntropy.Fallback

theorem radius_sq_le_geometric {n : ℕ} (hn : 2 ≤ n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (r : ℕ) :
    radius n δ r ^ 2 ≤ (16 * (n : ℝ) / δ) * (((r : ℝ) + 1)^2 * (1 / 2 : ℝ)^r) := by
  rw [radius_sq hn hδ hδ1 r]
  have hq : 0 < 8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ :=
    lt_of_lt_of_le (by norm_num) (confidence_ratio_ge_one hn hδ hδ1 r)
  have hlog : Real.log (8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ) ≤
      8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ := by
    linarith [Real.log_le_sub_one_of_pos hq]
  calc
    _ ≤ (2 / (roundSamples r : ℝ)) * (8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by
      simp only [roundSamples, Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow]
      field_simp
      ring

theorem summable_radius_majorant (n : ℕ) (δ : ℝ) :
    Summable (fun r : ℕ => (16 * (n : ℝ) / δ) * (((r : ℝ) + 1)^2 * (1 / 2 : ℝ)^r)) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 2 (r := (1 / 2 : ℝ)) (by norm_num)
  have ht := (hs.comp_injective Nat.succ_injective).mul_left (2 : ℝ)
  have hshift : Summable (fun r : ℕ => ((r : ℝ) + 1)^2 * (1 / 2 : ℝ)^r) := by
    convert! ht using 1
    funext r
    simp only [Function.comp_def, Nat.cast_succ, pow_succ]
    ring
  exact hshift.mul_left _

theorem radius_eventually_le {n : ℕ} (hn : 2 ≤ n) {δ g : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hg : 0 < g) :
    ∀ᶠ r : ℕ in atTop, radius n δ r ≤ g / 8 := by
  have ht := (summable_radius_majorant n δ).tendsto_atTop_zero
  have he : ∀ᶠ r : ℕ in atTop,
      (16 * (n : ℝ) / δ) * (((r : ℝ) + 1)^2 * (1 / 2 : ℝ)^r) < (g / 8)^2 :=
    ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [he] with r hr
  have hs := radius_sq_le_geometric hn hδ hδ1 r
  have hnon : 0 ≤ radius n δ r := Real.sqrt_nonneg _
  nlinarith

theorem summable_doubling_exp {c : ℝ} (hc : 0 < c) :
    Summable (fun r : ℕ => (roundSamples r : ℝ) * Real.exp (-c * roundSamples r)) := by
  have hexp : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hexp).summable
  have ht := hs.comp_injective (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)))
  convert! ht using 1
  funext r
  simp only [Function.comp_def, roundSamples]
  rw [← Real.exp_nat_mul]
  congr 1
  congr 1
  ring

theorem exists_gap_lower_bound {n : ℕ} (I : Instance n) :
    ∃ g : ℝ, 0 < g ∧ ∀ j, j ≠ I.best → g ≤ I.gap j := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image I.suboptimal I.gap I.suboptimal_nonempty
  exact ⟨I.gap i, I.gap_pos ((I.mem_suboptimal i).mp hi),
    fun j hj => hmin j ((I.mem_suboptimal j).mpr hj)⟩

end GapEntropy.Fallback
